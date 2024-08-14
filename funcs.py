#!/usr/bin/env python3

import hashlib
import sys

import verystable.core.key
import verystable.core.messages
import verystable.core.script
import verystable.core.secp256k1

from element import Element, ALLOCATOR, ATOM, CONS, ERROR, FUNC, REF, SerDeser, nil

def get_env(n, env):
    if n < 0:
        raise Exception("env argument out of range: %s" % (n,))
    while n > 1:
        if not env.is_cons():
            raise Exception("invalid env path %d" % (n,))
        n, x = divmod(n, 2)
        env = env.val2 if x else env.val1
    return env

class Tree:
    def __init__(self):
        self.tree = []

    @classmethod
    def dbl_n(cls, n, offset=0, size=0):
        assert offset >= 0 and (offset >> size) == 0
        r = [1]
        while n > 0:
            r = [a*2 for a in r] + [a*2+1 for a in r]
            n -= 1
        if size > 0:
            r = [(a << size) + offset for a in r]
        return r

    @classmethod
    def get_values(cls, n, offset=0, size=0):
        k, v = 0,1
        while v < n:
            k += 1
            v *= 2
        values = []
        while n > 0:
            while v > n:
                k -= 1
                v //= 2
            values.extend(cls.dbl_n(k, offset, size))
            offset = (offset * 2) + 1
            size += 1
            n -= v
        return values

    @classmethod
    def get_values_pair(cls, n1, n2):
        if n1 == 0:
            return [], cls.get_values(n2)
        elif n2 == 0:
            return cls.get_values(n1), []
        else:
            return (cls.get_values(n1, offset=0, size=1),
                    cls.get_values(n2, offset=1, size=1))

    def add(self, element):
        i = 0
        while i < len(self.tree):
            if self.tree[i] is None:
                self.tree[i] = element
                return
            element = Element.Cons(self.tree[i], element)
            self.tree[i] = None
            i += 1
        self.tree.append(element)

    def resolve(self):
        x = None
        for el in self.tree:
            if el is None: continue
            if x is None:
                x = el
            else:
                x = Element.Cons(el, x)
        return x

# we have two sorts of FUNC Element:
#  - fn_foo which subclasses Function directly which is for
#    internal handling
#  - op_foo which subclasses Operator which is for opcodes,
#    and handles one operand at a time in order to allow
#    the (partial ...) opcode to work

class Function:
    def __init__(self):
        pass # setup internal state

    def abandon(self):
        return [] # return list of elements to abandon

    def resolve(self, el):
        el.set_error("resolve unimplemented")
        return None

    def set_error_improper_list(self, el, what="program"):
        el.set_error(f"{what} specified as improper list (non-nil terminator)")

class fn_tree(Function):
    """for lazily constructing a minimal binary tree from elements in
       a list"""

    @classmethod
    def merge_one(cls, treeish):
        if treeish.kind != CONS: return None
        if treeish.val2.kind != CONS: return None
        a = treeish.val1
        b = treeish.val2.val1
        assert a.kind == CONS and b.kind == CONS
        assert a.val1.kind == ATOM and b.val1.kind == ATOM
        an, bn = a.val1.atom_as_u64(), b.val1.atom_as_u64()
        assert an <= bn
        if an < bn:
            return None
        nt = Element.Cons(
                Element.Cons(
                   Element.Atom(an + 1),
                   Element.Cons(b.val2.bumpref(), a.val2.bumpref())
                ),
                treeish.val2.val2.bumpref()
             )
        return nt

    @classmethod
    def merge(cls, el):
        # FUNC( CONS( treeish, args ), .. )
        if el.kind != FUNC or el.val1.kind != CONS: return
        while True:
            t2 = cls.merge_one(el.val1.val1)
            if t2 is None: break
            el.replace_func_state(Element.Cons( t2, el.val1.val2.bumpref() ))

    def collapse(self, el):
        assert el.kind == FUNC and el.val2 is self
        assert el.val1.kind == CONS
        assert el.val1.val1.kind == CONS # built something
        t = el.val1.val1
        assert t.kind == CONS
        assert t.val1.kind == CONS
        res = t.val1.val2.bumpref()
        while t.val2.kind == CONS:
            t = t.val2
            res = Element.Cons(t.val1.val2.bumpref(), res)
        if res.kind == CONS:
            el.replace(CONS, res.val1.bumpref(), res.val2.bumpref())
            res.deref()
        else:
            el.replace(REF, res)

    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        # CONS( nil|cons(cons(atom,none)) , nil|cons(none,none) )
        r = check_complete(el.val1, xCO(xANY(), xATCO(xANY(), xANY())), "tree")
        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None
        if r.right.el.is_atom():
            if r.right.el.is_nil():
                self.collapse(el)
            else:
                self.set_error_improper_list(el, "tree")
            return None
        else:
            sofar = r.left.el.bumpref()
            add = Element.Cons(Element.Atom(0), r.right.left.el.bumpref())
            later = r.right.right.el.bumpref()
            new = Element.Cons( Element.Cons(add, sofar), later)
            el.replace_func_state(new)
            self.merge(el)
            return None

class xANY:
    err = None
    want = None

    def __str__(self):
        return f"{self.__class__} {self.err} {self.want} {getattr(self, 'el', None)}"
    def ok(self, el): return True
    def set(self, el):
        self.el = el
        return self.sub()
    def sub(self): return []

    def set_error(self, err):
        self.err = err
    def set_want(self, want):
        self.want = want

class xAT(xANY):
    def ok(self, el): return el.kind == ATOM

class xATCO(xANY):
    def ok(self, el): return el.kind == CONS or el.kind == ATOM
    def __init__(self, left, right):
        self.left = left
        self.right = right
    def sub(self):
        if self.el.kind == CONS:
            return [(self.left, self.el.val1), (self.right, self.el.val2)]
        else:
            return []

class xCO(xATCO):
    def ok(self, el): return el.kind == CONS

def check_complete(el, basespec, who):
    orig = el
    queue = [(basespec, el)]
    while queue:
        spec, el = queue.pop(0)
        if not spec.ok(el):
            elcmp = el.get_complete()
            if elcmp is None:
                basespec.set_want(el)
                break
            elif elcmp.kind == ERROR:
                basespec.set_error(elcmp.bumpref())
                break
            elif not spec.ok(elcmp):
                basespec.set_error(Element.Error(f"unexpected kind in {who} {elcmp.kind} {spec.__class__.__name__} {elcmp} from {orig} line {sys._getframe(1).f_lineno}"))
                break
            el = elcmp
        queue.extend(spec.set(el))
    return basespec

class fn_eval(Function):
    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1,
                xCO(xATCO(xATCO(xANY(), xANY()), xANY()), xANY()),
                "eval"
        )

        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None

        if r.left.el.is_atom():
            # CONS(ATOM,None)  -- env lookup (0->nil; 1->env; 1+->split env)
            return self.env_access(el, r.left.el, r.right.el)
        elif r.left.left.el.is_atom():
            # CONS(CONS(ATOM,None),None) -- program lookup
            return self.eval_opcode(el, r.left.left.el, r.left.right.el, r.right.el)
        else:
            # CONS(CONS(CONS,None),None) -- eval program to determine program
            return self.eval_op_program(el, r.left.left.el, r.left.right.el, r.right.el)

    def env_access(self, el, exp, env):
        assert exp.kind == ATOM
        n = exp.atom_as_u64_short()
        if n is None:
            el.set_error("invalid value for env lookup")
            return None
        if n == 0:
            # nil goes to nil
            el.replace(REF, Element.Atom(0))
            return None
        while n > 1:
            c_env = env.get_complete()
            if c_env is None:
                return env
            if c_env.kind != CONS:
                el.set_error("invalid env path")
                return None
            env = c_env.val1 if n % 2 == 0 else c_env.val2
            n //= 2
            el.replace_func_state(Element.Cons(Element.Atom(n), env.bumpref()))
        el.replace(REF, env.bumpref())
        return None

    def eval_opcode(self, el, opcode_id, opcode_args, env):
        assert opcode_id.kind == ATOM
        if opcode_id.val2 > 8:
            el.set_error("env lookup out of range")
            return None
        opcode_num = opcode_id.atom_as_u64_short()
        if opcode_num is None:
            el.set_error("function id out of range")
            return None
        if opcode_num == 0:
            # q! special case
            el.replace(REF, opcode_args.bumpref())
            return None
        op = Op_FUNCS.get(opcode_num, None)
        if op is None:
            el.set_error("unknown opcode")
            return None
        args = Element.Func(Element.Cons(opcode_args.bumpref(), env.bumpref()), fn_eval_list())
        if opcode_num == 1:
            # special case so that (a X) == (a X 1)
            el.replace(FUNC, Element.Cons(env.bumpref(), args), op())
        else:
            el.replace(FUNC, args, op())
        return None

    def eval_op_program(self, el, prog, args, env):
        assert prog.kind == CONS
        prog = Element.Func(Element.Cons(prog.bumpref(), env.bumpref()), fn_eval())
        progargs = Element.Cons(prog, args.bumpref())
        el.replace_func_state(Element.Cons(progargs, env.bumpref()))
        return prog

class fn_eval_list(Function):
    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, xCO(xATCO(xANY(), xANY()), xANY()), "eval_list")

        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None

        if r.left.el.is_atom():
            el.replace(REF, r.left.el.bumpref())
            return None
        else:
            env = r.right.el
            a,b = r.left.left.el, r.left.right.el
            head = Element.Func(Element.Cons(a.bumpref(), env.bumpref()), fn_eval())
            tail = Element.Func(Element.Cons(b.bumpref(), env.bumpref()), fn_eval_list())
            el.replace(CONS, head, tail)
            return None

# Probably want some variants of Operator?
#   ability to have a hidden "state" Element or not (cat, substr, etc?)
#     ie func( cons( state, args ), self )
#     maybe it should always have a state, and just use nil if not
#     needed? then optimise it later if desired?
#   not everything needs the operand resolved to atom/cons:
#     op_a just passes the first argument to fn_eval, and the rest
#       to op_tree. which is a super intriguing thing to think about
#       wrt partial becoming an optimisation? not sure if op_tree is
#       correct for its state having multiple references? it's also
#       currently fn_tree
# Functionality
#   three functions can be called:
#      __init__() -- setup state
#      argument() -- passes in an atom/cons for processing
#      finish()   -- indicates all arguments have been passed in and
#                   the nil end of list has been reacheda
#   responses from finish():
#      update el (currently by returning it, which is lame)
#      or return a list which is used to update el (also lame)
#   responses from argument():
#      currently nothing, but probably should be able to say "skip
#        next argument (if present)" so (i c t e) can skip t or e
#        and (sf n p) can skip p depending on n, etc?
#        -- want to query a bool as to whether `el` needs evaluating...
#      should also be able to say "replace me with x", for (c x y z),
#        since that's cons(x, cons(y, z)) so by the time you see y
#        you can spit out cons(x, [something])
#        no -- i think should be able to say "skip remaining arguments"
#        but that just results in the argument list being evaluated until
#        the nil terminator (with error if non-nil term), and the replacement
#        still happening in finish()

class Operator(Function):
    state = 0
    def __init__(self):
        # do any special setup
        pass

    def argspec(self, argspec):
        return self.argument(argspec.el)

    def argument(self, el):
        # handle an argument
        raise Exception("BUG: argument handling unimplemented")

    def finish(self):
        # return the result
        raise Exception("BUG: finish unimplemented")

    def finalize(self, el):
        fin = self.finish()
        if isinstance(fin, list):
            newenv, program = fin
            el.replace(FUNC, Element.Cons(program, newenv), fn_eval())
        else:
            assert fin._refs > 0
            if fin._refs == 1:
                el.replace(fin.kind, fin.val1, fin.val2)
                ALLOCATOR.realloc(fin.alloc_size(), 24, fin)
                fin.set(ATOM, 0, 0)
                fin.deref()
            else:
                el.replace(REF, fin)

    def resolve_spec(self):
        return xATCO(xANY(), xANY())

    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, xATCO(self.resolve_spec(), xANY()), self.__class__.__name__)
        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None

        if r.el.is_atom():
            if r.el.is_nil():
                self.finalize(el)
            else:
                self.set_error_improper_list(el)
            ALLOCATOR.record_work(30)
            return None
        else:
            hspec = r.left
            t = r.right.el
            hspec.el.bumpref()
            try:
                self.argspec(hspec)
                el.replace_func_state(t.bumpref())
            except AssertionError:
                raise # This is a bug, so don't worry about memory management
            except Exception as exc:
                if exc.__class__ != Exception: raise
                hspec.el.deref() # Buggy to throw an exception after deref'ing, fine to throw beforehand
                if len(str(exc)) <= 8: raise exc
                el.set_error(str(exc))
            return None

class op_b(Operator):
    save = None
    def argument(self, el):
        if self.save is not None:
            # (would be cool to make a tree of trees)
            raise Exception("b: only supports one argument")
        self.save = el

    def finish(self):
        if self.save is None: return Element.Atom(0)
        tree_args = Element.Cons(Element.Atom(0), self.save)
        self.save = None
        return Element.Func(tree_args, fn_tree())

    def abandon(self):
       return [self.save] if self.save is not None else []

class op_a(Operator):
    # if given multiple arguments, builds them up into a tree,
    # biased to the left
    def __init__(self):
        self.tree = Tree()
        self.state = 0
    def argument(self, el):
        if self.state == 0:
            self.i = el
            self.state = 1
        else:
            self.tree.add(el)
    def finish(self):
        if self.state == 0:
            return Element.Error("a: requires at least one argument")
        env = self.tree.resolve()
        return [env, self.i]

    def resolve(self, el):
        # (env app tree...)
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, xCO(xANY(), xCO(xANY(), xATCO(xANY(), xANY()))), "a")
        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None
        env = r.left.el
        program = r.right.left.el
        if r.right.right.el.is_atom():
            if r.right.right.el.is_nil():
                el.replace(FUNC, Element.Cons(program.bumpref(), env.bumpref()), fn_eval())
            else:
                self.set_error_improper_list(el)
            return None

        tree_args = Element.Cons(Element.Atom(0), r.right.right.el.bumpref())
        tree = Element.Func(tree_args, fn_tree())
        el.replace(FUNC, Element.Cons(program.bumpref(), tree), fn_eval())
        return None

class op_x(Operator):
    def __init__(self):
        self.x = []
    def argument(self, el):
        self.x.append(repr(i))
        el.deref()
    def finish(self):
        raise Exception(" ".join(self.x))

class op_i(Operator):
    def resolve_spec(self):
        # each arg should be either an atom, or a pair of atoms
        if self.state == 0:
            return xATCO(xANY(), xANY())
        else:
            return xANY()

    def argspec(self, argspec):
        if self.state == 0:
            self.then = not argspec.el.is_nil()
            argspec.el.deref()
        elif self.state == 1:
            if self.then:
                self.result = argspec.el
            else:
                self.result = Element.Atom(0)
                argspec.el.deref()
        elif self.state == 2:
            if not self.then:
                self.result.deref()
                self.result = argspec.el
            else:
                argspec.el.deref()
        else:
            raise Exception("i: too many arguments")
        self.state += 1

    def argument(self, el):
        if self.state == 0:
            self.then = not el.is_nil()
            el.deref()
        elif self.state == 1:
            if self.then:
                self.result = el
            else:
                self.result = Element.Atom(0)
                el.deref()
        elif self.state == 2:
            if not self.then:
                self.result.deref()
                self.result = el
            else:
                el.deref()
        else:
            raise Exception("i: too many arguments")
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("i: must provide condition argument")
        if self.state == 1:
            raise Exception("i: must provide then argument")
        self.state = -1 # done!
        return self.result

    def abandon(self):
       if self.state > 1:
           return [self.result]
       return []

class op_softfork(Operator):
    def argument(self, el):
        el.deref()
    def finish(self):
        return Element.Atom(True)

class op_h(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("h: too many arguments")
        if el.is_atom():
            raise Exception("h: received non-list argument %s" % (el,))
        self.r = el.val1.bumpref()
        assert el.val1._refs > 1
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("h: must provide list argument")
        self.state = -1
        return self.r

    def abandon(self):
       assert self.state == -1
       return [self.r] if self.state > 0 else []

class op_t(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("t: too many arguments")
        if el.is_atom():
            raise Exception("t: received non-list argument %s" % (el,))
        self.r = el.val2.bumpref()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("t: must provide list argument")
        self.state = -1
        return self.r

    def abandon(self):
       return [self.r] if self.state > 0 else []

class op_l(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("l: too many arguments")
        self.r = el.is_cons()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("l: must provide list argument")
        return Element.Atom(self.r)

class op_c(Operator):
    # (c head tail), (c h1 h2 h3 tail)
    # this may mean you often want to have "nil" as the last arg,
    # if you're constructing a list from scratch

    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, xATCO(xANY(), xATCO(xANY(), xANY())), "c")
        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None

        improper_list = False
        if r.el.is_atom():
            improper_list = not r.el.is_nil()
        elif r.right.el.is_atom():
            improper_list = not r.right.el.is_nil()

        if improper_list:
            self.set_error_improper_list(el)
        elif r.el.is_atom():
            el.replace(REF, Element.Atom(0))
        elif r.right.el.is_atom():
            el.replace(REF, r.left.el.bumpref())
        else:
            el.replace(CONS, r.left.el.bumpref(), Element.Func(r.right.el.bumpref(), op_c()))
        ALLOCATOR.record_work(30)
        return None

class op_nand(Operator):
    # aka are any false?
    def __init__(self):
        self.b = False
    def argument(self, el):
        if el.is_nil():
            self.b = True
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_and(Operator):
    # aka are all true?
    def __init__(self):
        self.b = True
    def argument(self, el):
        if el.is_nil():
            self.b = False
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_or(Operator):
    # aka are any true?
    def __init__(self):
        self.b = False
    def argument(self, el):
        if not el.is_nil():
            self.b = True
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_eq(Operator):
    def __init__(self):
        self.h = None
        self.ok = True
    def argument(self, el):
        if not self.ok:
            el.deref()
        else:
            if self.h is None:
                self.h = el
                return
            else:
                if not Element.check_equal([(self.h, el)]):
                    self.h.deref()
                    self.h, self.ok = None, False
                el.deref()
    def finish(self):
        if self.h is not None:
            self.h.deref()
            self.h = None
        return Element.Atom(self.ok)
    def abandon(self):
       return [self.h] if self.h is not None else []

class op_strlen(Operator):
   def __init__(self):
       self.v = 0
   def argument(self, el):
        if not el.is_atom():
            raise Exception("len: not an atom")
        self.v += el.val2
        el.deref()
   def finish(self):
        return Element.Atom(self.v)

class op_cat(Operator):
    def __init__(self):
        self.build = None
    def argument(self, el):
        if not el.is_atom(): raise Exception("cat: argument not an atom")
        if self.build is None:
            self.build = el
            if self.build._refs > 1:
                self.build = self.build.dupe_atom()
        else:
            assert self.build._refs == 1
            new_size = self.build.val2 + el.val2
            if new_size <= 8:
                self.build.val1 += (el.val1 << (8*self.build.val2))
                self.build.val2 = new_size
            else:
                old_alloc = self.build.alloc_size()
                if self.build.val2 <= 8:
                    self.build.val1 = self.build.atom_as_bytes()
                self.build.val1 += el.atom_as_bytes()
                self.build.val2 = new_size
                ALLOCATOR.realloc(old_alloc, self.build.alloc_size(), self.build)
            el.deref()

    def finish(self):
        if self.build is None: return Element.Atom(0)
        b = self.build
        self.build = None
        return b

    def abandon(self):
       return [self.build] if self.build is not None else []

class op_substr(Operator):
    def __init__(self):
        self.el = None
        self.start = None
        self.end = None
    def argument(self, el):
        if not el.is_atom(): raise Exception("substr: arguments must be atoms")
        if self.el is None:
            self.el = el
        elif self.start is None:
            self.start = el.atom_as_u64()
            el.deref()
        elif self.end is None:
            self.end = el.atom_as_u64()
            el.deref()
        else:
            raise Exception("substr: too many arguments")
    def finish(self):
        el = self.el
        self.el = None

        if el is None: return Element.Atom(0)
        if self.start is None: return el
        if self.start == 0:
            if self.end is None: return el
            if self.end >= el.val2: return el
        if self.end is None:
            self.end = el.val2
        if self.start > el.val2:
            el.deref()
            return Element.Atom(0)
        if el.val2 <= 8:
            m = 0xFFFF_FFFF_FFFF_FFFF
            n = el.val1
            assert n <= m
            q = ((m^(m<<(self.end*8))) & n) >> (self.start*8)
            assert 0 <= q
            assert q <= m
            print("XXX", hex(q), self.end-self.start)
            s = Element.Atom(q, self.end-self.start)
        else:
            s = Element.Atom(el.val1[self.start:self.end])
        el.deref()
        return s

    def abandon(self):
       return [self.el] if self.el is not None else []

class op_add_u64(Operator):
    def __init__(self):
        self.i = 0

    def argument(self, el):
        self.i += el.atom_as_u64()
        self.i %= 0x1_0000_0000_0000_0000
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_mul_u64(Operator):
    def __init__(self):
        self.i = 1

    def argument(self, el):
        if not el.is_atom(): raise Exception("mul: arguments must be atoms")
        self.i *= el.atom_as_u64()
        self.i %= 0x1_0000_0000_0000_0000
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_mod_u64(Operator):
    def __init__(self):
        self.i = None
        self.state = 0

    def argument(self, el):
        if not el.is_atom(): raise Exception("mod: arguments must be atoms")
        if self.i is None:
            self.i = el.atom_as_u64()
        elif self.state == 0:
            self.i %= el.atom_as_u64()
            self.state = 1
        else:
            raise Exception("mod: too many arguments")
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_nand_u64(Operator):
    def __init__(self):
        self.i = 0xFFFF_FFFF_FFFF_FFFF
        self.state = 0

    def argument(self, el):
        if not el.is_atom(): raise Exception("and: arguments must be atoms")
        self.i &= el.atom_as_u64()
        el.deref()

    def finish(self):
        return Element.Atom(0xFFFF_FFFF_FFFF_FFFF ^ self.i)

class op_and_u64(Operator):
    def __init__(self):
        self.i = 0xFFFF_FFFF_FFFF_FFFF
        self.state = 0

    def argument(self, el):
        if not el.is_atom(): raise Exception("and: arguments must be atoms")
        self.i &= el.atom_as_u64()
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_or_u64(Operator):
    def __init__(self):
        self.i = 0
        self.state = 0

    def argument(self, el):
        if not el.is_atom(): raise Exception("or: arguments must be atoms")
        self.i |= el.atom_as_u64()
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_xor_u64(Operator):
    def __init__(self):
        self.i = 0
        self.state = 0

    def argument(self, el):
        if not el.is_atom(): raise Exception("xor: arguments must be atoms")
        self.i ^= el.atom_as_u64()
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_sub_u64(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        if not el.is_atom(): raise Exception("sub: arguments must be atoms")
        n = el.atom_as_u64()
        el.deref()
        if self.i is None:
            self.i = n
        else:
            self.i -= n
            self.i %= 0x1_0000_0000_0000_0000 # turns negatives back to positive

    def finish(self):
        if self.i is None:
            raise Exception("sub: missing arguments")
        return Element.Atom(self.i)

# op_mod / op_divmod
class op_div_u64(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        if not el.is_atom(): raise Exception("div: arguments must be atoms")
        n = el.atom_as_u64()
        el.deref()
        if self.i is None:
            self.i = n
        else:
            ## if el >= 2**64 should we just set i to 0?
            if n == 0:
                raise Exception("div: attempted div by 0")
            self.i //= n

    def finish(self):
        if self.i is None:
            raise Exception("div: missing arguments")
        return Element.Atom(self.i)

class op_lt_str(Operator):
    def __init__(self):
        self.last = None
        self.ok = True

    @classmethod
    def lt(cls, a, b):
        return a < b

    def argument(self, el):
        if not self.ok:
            el.deref()
            return

        if self.last is None:
            self.last = el
        else:
            self.ok = self.lt(self.last.atom_as_bytes(), el.atom_as_bytes())
            self.last.deref()
            if self.ok:
                self.last = el
            else:
                el.deref()
                self.last = None

    def finish(self):
        if self.last is not None:
            self.last.deref()
            self.last = None
        return Element.Atom(self.ok)

    def abandon(self):
        return [self.last] if self.last is not None else []

class op_lt_lendian(op_lt_str):
    @classmethod
    def lt(cls, a, b):
        lena = len(a)
        lenb = len(b)
        i = max(lena, lenb)
        while i > 0:
            i -= 1
            ca = a[i] if i < lena else 0
            cb = b[i] if i < lenb else 0
            if ca < cb: return True
            if ca > cb: return False
        return False

class op_list_read(Operator):
    def __init__(self):
        self.el = None

    def argument(self, el):
        if self.el is not None:
            raise Exception("rd: too many arguments")
        if not el.is_atom():
            raise Exception("rd: argument must be atom")
        self.el = el

    def abandon(self):
        return [self.el] if self.el is not None else []

    def finish(self):
        if self.el is None:
            return Element.Error(f"rd: argument required")
        edeser = SerDeser().Deserialize(self.el.atom_as_bytes())
        self.el.deref()
        self.el = None
        return edeser

class op_list_write(Operator):
    def __init__(self):
        self.el = None

    def argument(self, el):
        if self.el is not None:
            raise Exception("rd: too many arguments")
        self.el = el

    def abandon(self):
        return [self.el] if self.el is not None else []

    def finish(self):
        if self.el is None:
            return Element.Error(f"rd: argument required")
        eser = SerDeser().Serialize(self.el)
        self.el.deref()
        self.el = None
        return Element.Atom(eser)

class op_sha256(Operator):
    def __init__(self):
        self.st = hashlib.sha256()
        self.w = b""

    def argument(self, el):
        if not el.is_atom():
            raise Exception("sha256: cannot hash list")
        self.st.update(el.atom_as_bytes())
        self.w += el.atom_as_bytes()
        ALLOCATOR.record_work((el.val2 + 63)//64 * 256)
        el.deref()

    def finish(self):
        return Element.Atom(self.st.digest())

class op_hash160(op_sha256):
    def finish(self):
        x = hashlib.new("ripemd160")
        x.update(self.st.digest())
        ALLOCATOR.record_work(256)
        return Element.Atom(x.digest())

class op_hash256(op_sha256):
    def finish(self):
        x = hashlib.sha256()
        x.update(self.st.digest())
        ALLOCATOR.record_work(256)
        return Element.Atom(x.digest())

class op_secp256k1_muladd(Operator):
    """(secp256k1_muladd a (b) (c . d) (1 . e) (nil . f))
       checks that a*G - b*G + c*D + E - F = 0
       Script aborts otherwise.

       That is, an atom on its own is interpreted as a scalar and
       multiplied by G; a cons pair is interpreted as a scalar followed
       by a point; if the point is nil, it is interpreted as -G; if the
       scalar is nil, it is treated as -1.

       Scalars are interpreted as little endian. 33-byte values for the
       point are treated as compressed points, 32-byte values for the
       points are evaluated via BIP340's lift_x().

       BIP340 validation is thus equivalent to:
           (secp256k1_muladd ('1 . R) (e . P) (s))
       where e is H(R,P,m) as per BIP340.
    """

    def __init__(self):
        self.aps = []

    def resolve_spec(self):
        # each arg should be either an atom, or a pair of atoms
        return xATCO(xAT(), xAT())

    def argspec(self, argspec):
        if argspec.el.is_atom():
            ### XXX we use big-endian integers here, not little!!
            b = argspec.el.atom_as_bytes()
            if len(b) > 32: raise Exception("secp256k1_muladd: int out of range")
            val = int.from_bytes(b, byteorder='big', signed=False) % verystable.core.secp256k1.FE.SIZE
            pt = verystable.core.secp256k1.G
        else:
            b = argspec.left.el.atom_as_bytes()
            if len(b) > 32: raise Exception("secp256k1_muladd: int out of range")
            if argspec.left.el.val2 == 0:
                val = verystable.core.secp256k1.FE.SIZE - 1
            else:
                val = int.from_bytes(b, byteorder='big', signed=False) % verystable.core.secp256k1.FE.SIZE

            b = argspec.right.el.atom_as_bytes()
            if len(b) == 32:
                pt = verystable.core.secp256k1.GE.from_bytes_xonly(b)
            elif len(b) == 33:
                pt = verystable.core.secp256k1.GE.from_bytes(b)
            elif len(b) == 0:
                pt = -verystable.core.secp256k1.G
            else:
                raise Exception("secp256k1_muladd: point out of range")
            if pt is None:
                raise Exception("secp256k1_muladd: invalid point")
        self.aps.append((val, pt))
        argspec.el.deref()

    def finish(self):
        x = verystable.core.secp256k1.GE.mul(*self.aps)
        if not x.infinity:
            print("XXX muladd", [(a, p.to_bytes_compressed().hex()) for (a,p) in self.aps])
            return Element.Error(f"secp256k1_muladd: did not sum to inf {x.to_bytes_compressed().hex()}")
        return Element.Atom(1)

class op_bip340_verify(Operator):
    def __init__(self):
        self.args = []

    def argument(self, el):
        if not el.is_atom():
            raise Exception("bip340_verify: argument must be atom")
        if len(self.args) < 3:
            self.args.append(el)
        else:
            raise Exception("bip340_verify: too many arguments")

    def finish(self):
        # XXX probably buggy to raise without freeing pk/m/sig?
        if len(self.args) != 3:
            raise Exception("bip340_verify: too few arguments")
        pk, m, sig = self.args
        if pk.val2 != 32 or m.val2 != 32 or sig.val2 != 64:
            r = False
        else:
            r = verystable.core.key.verify_schnorr(key=pk.val1, sig=sig.val1, msg=m.val1)
        fail = (not r and sig.val2 != 0)
        pk.deref()
        m.deref()
        sig.deref()
        if fail:
            return Element.Error("bip340_verify: invalid, non-empty signature")
        else:
            return Element.Atom(r)

class op_bip342_txmsg(Operator):
    def __init__(self):
        self.sighash = None

    def argument(self, el):
        if self.sighash is not None:
            raise Exception("bip342_txmsg: too many arguments")
        if not el.is_atom() or el.val2 > 1:
            raise Exception("bip342_txmsg: expects a single sighash byte")
        if el.val2 == 1 and el.val1 not in [0x01, 0x02, 0x03, 0x81, 0x82, 0x83]:
            raise Exception("bip342_txmsg: unknown sighash byte")
        self.sighash = el.atom_as_u64()
        el.deref()

    def finish(self):
        if self.sighash is None: self.sighash = 0
        annex = None
        if len(GLOBAL_TX.wit.vtxinwit) > 0:
            w = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            if len(w) > 0 and w[-1][0] == 0x50:
                annex = w[-1]
        r = verystable.core.script.TaprootSignatureHash(txTo=GLOBAL_TX, spent_utxos=GLOBAL_UTXOS, hash_type=self.sighash, input_index=GLOBAL_TX_INPUT_IDX, scriptpath=True, annex=annex, script=GLOBAL_TX_SCRIPT)
        return Element.Atom(r)

class op_tx(Operator):
    def __init__(self):
        # build up r as we go, by updating last_cons
        self.r = None
        self.last_cons = None

    def resolve_spec(self):
        # each arg should be either an atom, or a pair of atoms
        return xATCO(xAT(), xAT())

    def argspec(self, argspec):
        if argspec.el.is_atom():
            code = argspec.el.atom_as_u64()
            which = None
        else:
            code = argspec.left.el.atom_as_u64()
            which = argspec.right.el.atom_as_u64()
        result = self.get_tx_info(code, which)
        if self.r is None:
            self.r = result
        elif self.last_cons is None:
            # XXX should release this progressively like op_c
            self.last_cons = Element.Cons(result, Element.Atom(0))
            self.r = Element.Cons(self.r, self.last_cons)
        else:
            assert self.last_cons.is_cons()
            assert self.last_cons.val2.is_atom()
            assert self.last_cons.val2.val2 == 0
            self.last_cons.val2 = Element.Cons(result, self.last_cons.val2)
            self.last_cons = self.last_cons.val2
        argspec.el.deref()

    def get_tx_info(self, code, which):
        if 0 <= code <= 9:
            if which is not None: raise Exception(f"tx: {code} should be an atom not a pair")
            return self.get_tx_global_info(code)
        elif 10 <= code <= 19:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vin):
                raise Exception(f"tx: {code} invalid input index")
            return self.get_tx_input_info(code, which)
        elif 20 <= code <= 29:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vout):
                raise Exception(f"tx: {code} requires valid output index")
            return self.get_tx_output_info(code, which)
        else:
            raise Exception(f"tx: {code} out of range")

    def get_bip341info(self):
        wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
        n = len(wit) - 1
        if n > 0 and wit[n][0] == 0x50: n -= 1 # skip annex
        if n <= 0 or len(wit[n]) == 0: return None, None # key spend, or no witness data

        cb = wit[n]
        leafver = cb[0] & 0xFE
        sign = cb[0] & 0x01
        if len(cb) % 32 == 1:
            ipk = cb[1:33]
            path = [cb[i:i+32] for i in range(33, len(cb), 32)]
        else:
            ipk = path = None
        return leafver, sign, ipk, path

    def get_tx_global_info(self, code):
        if code == 0:
            return Element.Atom(GLOBAL_TX.nVersion, 4)
        elif code == 1:
            return Element.Atom(GLOBAL_TX.nLockTime, 4)
        elif code == 2:
            return Element.Atom(len(GLOBAL_TX.vin))
        elif code == 3:
            return Element.Atom(len(GLOBAL_TX.vout))
        elif code == 4:
            return Element.Atom(GLOBAL_TX_INPUT_IDX)
        elif code == 5:
            return Element.Atom(GLOBAL_TX.serialize_without_witness())
        elif code == 6:
            # the TapLeaf hash for the current script
            wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            n = len(wit) - 1
            if n >= 0 and wit[n][0] == 0x50: n -= 1 # skip annex
            if n >= 1 and len(wit[n]) > 0:
                v = (wit[n][0] & 0xFE)
                s = wit[n-1]
                h = verystable.core.key.TaggedHash("TapLeaf", bytes([v]) + verystable.core.messages.ser_string(s))
                return Element.Atom(h)
            else:
                return Element.Atom(0)
        elif code == 7:
            # taproot internal pubkey
            raise Exception("unimplemented")
        elif code == 8:
            # taproot merkle path
            raise Exception("unimplemented")
        # should also be able to pull out control block information,
        # eg merkle path and internal pubkey
        else:
            return Element.Atom(0)

    def get_tx_input_info(self, code, which):
        txin = GLOBAL_TX.vin[which]
        wit = GLOBAL_TX.wit.vtxinwit[which].scriptWitness.stack
        coin = GLOBAL_UTXOS[which]
        if code == 10:
             return Element.Atom(txin.nSequence, 4)
        elif code == 11:
             return Element.Atom(verystable.core.messages.ser_uint256(txin.prevout.hash))
        elif code == 12:
             return Element.Atom(txin.prevout.n, 4)
        elif code == 13:
             return Element.Atom(txin.scriptSig)
        elif code == 14:
             # annex, including 0x50 prefix
             if len(wit) > 0 and len(wit[-1]) > 0 and wit[-1][0] == 0x50:
                 return Element.Atom(wit[-1])
             else:
                 return Element.Atom(0)
        elif code == 15:
             return Element.Atom(coin.nValue, 8)
        elif code == 16:
             return Element.Atom(coin.scriptPubKey)
        else:
             return Element.Atom(0)

    def get_tx_output_info(self, code, which):
        out = GLOBAL_TX.vout[which]
        if code == 20:
             return Element.Atom(out.nValue, 8)
        elif code == 21:
             return Element.Atom(out.scriptPubKey)
        else:
             return Element.Atom(0)

    def finish(self):
        if self.r is None: return Element.Atom(0)
        r = self.r
        self.r = None
        return r

    def abandon(self):
        return [self.r] if self.r is not None else []

FUNCS = [
  (b'', "q", None), # quoting indicator, special

  (0x01, "a", op_a),  # apply
#  (0x99, "partial", op_partial),  # partially apply the following function
     ## can be continued by being used as an opcode, or be another op_partial
     ## means i need to make argument()/finish() the standard way of doing
     ## "everything" though?
     ## XXX note that this implies the ability to deep-copy the state of
     ## any functions that are partial'ed
  (0x02, "x", op_x),  # exception
  (0x03, "i", op_i),  # eager-evaluated if
  (0x04, "sf", op_softfork),
     ## should this be magic as in (sf '99 (+ 3 4)) treats "+" according
     ## to "99" softfork rules, or should it be more like (a '(+ 3 4))
     ## where you're expected to quote it first?

  (0x05, "c", op_c), # construct a list, last element is a list
  (0x06, "h", op_h), # head / car
  (0x07, "t", op_t), # tail / cdr
  (0x08, "l", op_l), # is cons?
  (0x39, "b", op_b), # convert list to binary tree

  (0x09, "not", op_nand),
  (0x0a, "all", op_and),
  (0x0b, "any", op_or),

  (0x0c, "=", op_eq),
  (0x0d, "<s", op_lt_str),
  (0x0e, "strlen", op_strlen),
  (0x0f, "substr", op_substr),
  (0x10, "cat", op_cat),

  # not really convinced these make sense as u64 (vs generic bitwise ops)
  # (eg, (~ 0x80) becomes 0x7FFF_FFFF_FFFF_FFFF which is weird)
  (0x11, "~", op_nand_u64),
  (0x12, "&", op_and_u64),
  (0x13, "|", op_or_u64),
  (0x14, "^", op_xor_u64),

  (0x17, "+", op_add_u64),
  (0x18, "-", op_sub_u64),
  (0x19, "*", op_mul_u64),
  (0x1a, "%", op_mod_u64),
#  (0x1b, "/%", op_divmod_u64), # (/ a b) => (h (/% a b))
#  (0x1c, "<<", op_lshift_u64),
#  (0x1d, ">>", op_rshift_u64),

  (0x1e, "<", op_lt_lendian),   # not restricted to u64
#  (0x1f, "log2b42", op_log2b42_u64),  # returns floor(log_2(x) * 2**42)
      ## allow this to apply to arbitrary atoms?
      ## (log of a 500kB atoms will fit into a u64)

  (0x22, "rd", op_list_read), # read bytes to Element
  (0x23, "wr", op_list_write), # write Element as bytes

  (0x24, "sha256", op_sha256),
 # (0x25, "ripemd160", op_ripemd160),
  (0x26, "hash160", op_hash160),
  (0x27, "hash256", op_hash256),
  (0x28, "bip340_verify", op_bip340_verify),
#  (0x29, "ecdsa_verify", op_ecdsa_verify),
  (0x2a, "secp256k1_muladd", op_secp256k1_muladd),

  (0x2b, "tx", op_tx),
  (0x2c, "bip342_txmsg", op_bip342_txmsg),
#  (0x2d, "bip345_accrue", op_bip345_accrue),
      ## for simulating op_vault, add the ability to assert that
      ## funds from this input have been distributed to a given output
]

def _Do_FUNCS():
    se = {}
    op = {}
    for (val, name, fn) in FUNCS:
        assert name not in se
        assert val not in op
        se[name] = val
        op[val] = fn
    return se, op
SExpr_FUNCS, Op_FUNCS = _Do_FUNCS()

def Set_GLOBAL_TX(tx):
    global GLOBAL_TX
    GLOBAL_TX = tx

def Set_GLOBAL_TX_INPUT_IDX(idx):
    global GLOBAL_TX_INPUT_IDX
    GLOBAL_TX_INPUT_IDX = idx

def Set_GLOBAL_TX_SCRIPT(scr):
    global GLOBAL_TX_SCRIPT
    GLOBAL_TX_SCRIPT = scr

def Set_GLOBAL_UTXOS(utxos):
    global GLOBAL_UTXOS
    GLOBAL_UTXOS = utxos

