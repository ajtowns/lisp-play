#!/usr/bin/env python3

import sys
import re
import hashlib
import verystable.core.key
import verystable.core.messages
import verystable.core.script

class Allocator:
    """simple object to monitor how much space is used up by
       currently allocated objects"""
    def __init__(self):
        self.x = 0
        self.max = 0
        self.allocated = dict()
        self.limit = 500000
        self.effort = 0
        self.effort_limit = 100000 #*10000000
        self.counter = 0
        self.freed = dict()

    def reset_work(self):
        self.effort = 0
        self.freed = dict()

    def record_work(self, effort):
        self.effort += effort

    def over_limit(self):
        return self.max > self.limit or self.effort > self.effort_limit

    def alloc(self, n, w):
        assert n >= 0
        self.x += n
        if self.x > self.max:
            self.max = self.x
        lines = []
        frame = sys._getframe(1)
        while frame.f_back is not None:
            lines.append(frame.f_lineno)
            frame = frame.f_back
        self.counter += 1
        self.allocated[w] = [n, (self.counter, lines)]

    def realloc(self, old, new, w):
        assert w in self.allocated
        assert self.allocated[w][0] == old, f"realloc size mismatch expected {self.allocated[w][0]} got {old} for {w}"
        self.x += (new - old)
        self.allocated[w][0] = new
        if self.x > self.max:
            self.max = self.x

    def free(self, n, w):
        assert n >= 0
        if w not in self.allocated and w in self.freed:
            print(f"DOUBLE-FREE {w} // {self.freed[w]}")
        assert w in self.allocated
        assert self.allocated[w][0] == n, f"free size mismatch expected {self.allocated[w][0]} got {n} for {w}"
        self.x -= n
        #self.freed[w] = self.allocated[w]
        del self.allocated[w]

class Function:
    def __init__(self):
        pass # setup internal state

    def abandon(self):
        return [] # return list of elements to abandon

    def resolve(self, el):
        el.set_error("resolve unimplemented")
        return None

    def set_error_open_list(self, el):
        el.set_error("program specified as open list (non-nil terminator)")

ALLOCATOR = Allocator()

# kinds
ATOM=255
CONS=254
ERROR=253
REF=252
FUNC=251

class Element:
    re_printable = re.compile(b"^[a-zA-Z0-9 _(),:'-]+$")
    _nil = None
    _one = None

    def __init__(self, kind, val1, val2=None):
        ALLOCATOR.alloc(24, self)
        self._refs = 1
        self.set(kind, val1, val2)

    def alloc_size(self):
        if self.kind != ATOM or self.val2 <= 8: return 24
        return 24 + 16 + ((self.val2+15) // 16) * 16

    def set(self, kind, val1, val2):
        ## previous contents should already have been derefed
        if kind == ATOM:
            assert isinstance(val2, int)
            assert (isinstance(val1, int) and 0 <= val2 <= 8) or (isinstance(val1, bytes) and val2 > 8 and val2 == len(val1))
        elif kind == CONS:
            assert isinstance(val1, Element) and isinstance(val2, Element)
        elif kind == ERROR:
            assert isinstance(val1, Element) and val2 is None
            assert val1.kind != ATOM or val1.val2 > 8
        elif kind == REF:
            assert isinstance(val1, Element) and val2 is None
        elif kind == FUNC:
            assert isinstance(val1, Element) and val2 is not None
        else:
            assert False, "invalid kind"

        self.kind = kind
        self.val1 = val1
        self.val2 = val2
        if kind == ATOM and val2 > 8:
            ALLOCATOR.realloc(24, self.alloc_size(), self)

    def bumpref(self):
        assert self._refs > 0
        self._refs += 1
        return self

    @classmethod
    def deref_stack(cls, stk):
        while stk:
            f = stk.pop()
            assert f._refs >= 1, f"double-free of {f}"
            f._refs -= 1
            if f._refs == 0:
                f.deref_parts(stk)
                ALLOCATOR.free(f.alloc_size(), f)

    @classmethod
    def toderef(cls, stk, *els):
        for el in els:
            if el._refs > 1:
                el._refs -= 1
            else:
                stk.append(el)
        return stk

    def deref_parts(self, stk):
        if self.kind == ATOM:
            pass
        elif self.kind == CONS:
            if self.val2.kind == ATOM:
                self.toderef(stk, self.val1, self.val2)
            else:
                self.toderef(stk, self.val2, self.val1)
        elif self.kind == FUNC:
            self.toderef(stk, self.val1)
            assert not hasattr(self.val2, "abandoned")
            self.val2.abandoned = 1
            for sub_el in self.val2.abandon():
                self.toderef(stk, sub_el)
        else: # REF, ERROR, FN
             self.toderef(stk, self.val1)
             assert not isinstance(self.val2, Element)
        return stk

    def deref(self):
        self.deref_stack(self.toderef([], self))

    def replace(self, kind, val1, val2=None):
        assert self.kind == REF or self.kind == FUNC
        self.deref_stack(self.deref_parts([]))
        if self.kind == ATOM and self.val2 > 8:
            ALLOCATOR.realloc(self.alloc_size(), 24, self)
        self.set(kind, val1, val2)

    def replace_func_state(self, new_val1):
        assert self.kind == FUNC
        self.val1.deref()
        self.val1 = new_val1

    def set_error(self, msg):
        if isinstance(msg, (str, bytes)):
            msg = Element.Atom(msg)
        self.replace(ERROR, msg)

    def is_nil(self):
        return self.kind == ATOM and self.val1 == 0 and self.val2 == 0

    @classmethod
    def Nil(cls):
        if cls._nil is None:
            cls._nil = cls(ATOM, 0, 0)
            cls._nil.bumpref()
        return cls._nil.bumpref()

    @classmethod
    def One(cls):
        if cls._one is None:
            cls._one = cls(ATOM, 1, 1)
            cls._one.bumpref()
        return cls._one.bumpref()

    @classmethod
    def Atom(cls, data, length=None):
        if length is not None:
            assert isinstance(data, int) and data > 0 and data <= 0xFFFF_FFFF_FFFF_FFFF
            assert length >= (data.bit_length() + 7) // 8
            assert length <= 8
            if length == 0: return cls.Nil()
            if length == 1 and data == 1: return cls.One()
            return cls(ATOM, data, length)
        if data == False or data == 0 or data is None or data == '' or data == b'':
            return cls.Nil()
        if data == True or data == 1 or data == '\x01' or data == b'\x01':
            return cls.One()

        if isinstance(data, str):
            data = data.encode('utf8')
        elif isinstance(data, int):
            assert data > 0 and data <= 0xFFFF_FFFF_FFFF_FFFF
            bl = (data.bit_length() + 7)//8
            return cls(ATOM, data, bl)
        assert isinstance(data, bytes)
        if len(data) <= 8:
            i = int.from_bytes(data, byteorder='little', signed=False)
            return cls(ATOM, i, len(data)) # in place
        else:
            return cls(ATOM, data, len(data))

    @classmethod
    def Cons(cls, left, right):
        return cls(CONS, left, right)

    @classmethod
    def Ref(cls, ref):
        return cls(REF, ref)

    @classmethod
    def Error(cls, msg):
        if isinstance(msg, (str, bytes)):
            msg = cls.Atom(msg)
        return cls(ERROR, msg)

    @classmethod
    def Func(cls, args, fn):
        assert isinstance(fn, Function)
        return cls(FUNC, args, fn)

    def dupe_atom(self):
        assert self.kind == ATOM
        assert self._refs > 1
        v = self.val1
        if isinstance(v, bytes):
            v = v[:] # copy
        else:
            assert isinstance(v, int) # don't need to copy
        replace = Element(ATOM, v, self.val2)
        self.deref()
        return replace

    def is_atom(self):
        return self.kind == ATOM

    def is_cons(self):
        return self.kind == CONS

    def is_error(self):
        return self.kind == ERROR

    def get_complete(self):
        if self.kind == REF:
            self = self.val1
        if self.kind in [ATOM,CONS,ERROR]:
            return self
        return None

    def atom_as_bytes(self):
        assert self.kind == ATOM
        if self.val2 <= 8:
            return self.val1.to_bytes(self.val2, byteorder='little', signed=False)
        else:
            return self.val1

    def atom_as_u64_short(self):
        assert self.kind == ATOM
        if self.val2 > 8: return None
        if self.val2 != (self.val1.bit_length() + 7)//8: return None
        return self.val1

    def atom_as_u64(self):
        assert self.kind == ATOM
        if self.val2 <= 8:
            assert isinstance(self.val1, int) and 0 <= self.val1 <= 0xFFFF_FFFF_FFFF_FFFF
            return self.val1
        else:
            return int.from_bytes(self.val1[:8], byteorder='little', signed=False)

    def __repr__(self): return f"El<{self}>"
    def __str__(self):
        if self.kind == REF:
            n = 0
            while self.kind == REF:
                self = self.val1
                n += 1
            return "*"*n + str(self)
        if self.is_nil():
            return "nil"
        elif self.is_atom():
            if self.val2 == 0 or (self.val1 != 0 and self.val2 == 1):
                return str(self.val1)
            else:
                v = self.atom_as_bytes()
                if self.re_printable.match(v):
                    return '"%s"' % (v.decode('utf8'),)
                else:
                    return "0x%s" % (v.hex(),)
        elif self.is_cons():
            x = []
            while self.val2.is_cons():
                x.append(self.val1)
                self = self.val2
            x.append(self.val1)
            if not self.val2.is_nil():
                x.append(".")
                x.append(self.val2)
            return "(%s)" % " ".join(map(str, x))
        elif self.is_error():
            return "ERR(%s)" % (str(self.val1))
        else:
            return "FN(%s,%s)" % (self.val2.__class__.__name__, str(self.val1))

class Tree:
    def __init__(self):
        self.tree = []

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

class fn_tree(Function):
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
        r = check_complete(el.val1,
               {CONS: (None, {ATOM: None, CONS: None})}
            )
        if True in r:
            return r[True]
        if False in r:
            el.replace(REF, r[False])
            return None
        if ATOM in r[CONS,2]:
            if r[CONS,2][ATOM].is_nil():
                self.collapse(el)
            else:
                self.set_error_open_list(el)
            return None
        else:
            sofar = el.val1.val1.bumpref()
            add = Element.Cons(Element.Atom(0), r[CONS,2][CONS].val1.bumpref())
            later = r[CONS,2][CONS].val2.bumpref()
            new = Element.Cons( Element.Cons(add, sofar), later)
            el.replace_func_state(new)
            self.merge(el)
            return None

# spec would be a constexpr template argument in c++
# so recursion on "spec" is fine
def __check_complete(el, spec):
    r = check_complete(el, spec)
    print(f"from {el} looking for {spec} got {r}")
    return r

def check_complete(el, spec):
    fin = {}
    queue = [(el, spec, fin)]
    while queue:
        el, spec, result = queue.pop(0)
        if spec is None:
            result[0] = el
            continue
        elcmp = el.get_complete()
        if elcmp is None:
            return {True: el}
        if elcmp.kind == ERROR:
            return {False: el.bumpref()}
        valid = spec.keys() if isinstance(spec, dict) else [spec]
        if elcmp.kind not in valid:
            return {False: Element.Error("unexpected kind")}
        k = elcmp.kind
        v = spec[k] if isinstance(spec, dict) else None
        result[k] = elcmp
        if k == ATOM:
            assert v is None
        elif v is not None:
            if isinstance(v, (tuple, list)):
                assert len(v) == 2
                result[k,1] = {}
                result[k,2] = {}
                queue.append( (elcmp.val1, v[0], result[k,1]) )
                queue.append( (elcmp.val2, v[1], result[k,2]) )
            else:
                result[k,1] = {}
                queue.append( (elcmp.val1, v, result[k,1]) )
    return fin

class fn_eval(Function):
    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1,
               {CONS: (
                  {ATOM: None,
                   CONS: ({ATOM: None, CONS: None}, None)},
                  None)}
            )
        if True in r:
            return r[True]
        if False in r:
            el.replace(REF, r[False])
            return None

        if ATOM in r[CONS,1]:
            # CONS(ATOM,None)  -- env lookup (0->nil; 1->env; 1+->split env)
            return self.env_access(el, r[CONS,1][ATOM], r[CONS,2][0])
        elif ATOM in r[CONS,1][CONS,1]:
            # CONS(CONS(ATOM,None),None) -- program lookup
            return self.eval_opcode(el, r[CONS,1][CONS,1][ATOM], r[CONS,1][CONS,2][0], r[CONS,2][0])
        else:
            # CONS(CONS(CONS,None),None) -- eval program to determine program
            return self.eval_op_program(el, r[CONS,1][CONS,1][CONS], r[CONS,1][CONS,2][0], r[CONS,2][0])

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
        r = check_complete(el.val1, {CONS: ({CONS: None, ATOM: None}, None)})
        if True in r:
            return r[True]
        if False in r:
            el.replace(REF, r[False])
            return None
        if ATOM in r[CONS,1]:
            if r[CONS,1][ATOM].is_nil():
                el.replace(REF, r[CONS,1][ATOM].bumpref())
            else:
                self.set_error_open_list(el)
            return None
        else:
            env = r[CONS,2][0]
            c = r[CONS,1][CONS]
            head = Element.Func(Element.Cons(c.val1.bumpref(), env.bumpref()), fn_eval())
            tail = Element.Func(Element.Cons(c.val2.bumpref(), env.bumpref()), fn_eval_list())
            el.replace(CONS, head, tail)
            return None

class Operator(Function):
    state = 0
    def __init__(self):
        # do any special setup
        pass

    def argument(self, el):
        # handle an argument
        raise Exception("BUG: argument handling unimplemented")

    def finish(self):
        # return the result
        raise Exception("BUG: finish unimplemented")

    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, {CONS: ({ATOM: None, CONS: None}, None), ATOM: None})
        if True in r:
            return r[True]
        if False in r:
            el.replace(REF, r[False])
            return None

        if ATOM in r:
            if r[ATOM].is_nil():
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
            else:
                self.set_error_open_list(el)
            ALLOCATOR.record_work(30)
            return None
        else:
            h = r[CONS,1][CONS] if CONS in r[CONS,1] else r[CONS,1][ATOM]
            t = r[CONS,2][0]
            assert h._refs > 0
            h.bumpref()
            try:
                self.argument(h)
                el.replace_func_state(t.bumpref())
            except AssertionError:
                raise # This is a bug, so don't worry about memory management
            except Exception as exc:
                h.deref() # Buggy to throw an exception after deref'ing, fine to throw beforehand
                if len(str(exc)) <= 8: raise exc
                el.set_error(str(exc))
            return None

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
        r = check_complete(el.val1, {CONS: (None, {CONS: (None, {ATOM: None, CONS: None})})})
        if True in r:
            return r[True]
        if False in r:
            el.replace(REF, r[False])
            return None
        env = r[CONS,1][0]
        program = r[CONS,2][CONS,1][0]
        if ATOM in r[CONS,2][CONS,2]:
            if r[CONS,2][CONS,2][ATOM].is_nil():
                el.replace(FUNC, Element.Cons(program.bumpref(), env.bumpref()), fn_eval())
            else:
                el.set_error_open_list(el)
            return None

        tree_args = Element.Cons(Element.Atom(0), r[CONS,2][CONS,2][CONS].bumpref())
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

    res = None
    last_cons = None

    def argument(self, el):
        if self.res is None:
            self.res = el
        elif self.last_cons is None:
            self.res = self.last_cons = Element.Cons(self.res, el)
        else:
            self.last_cons.val2 = Element.Cons(self.last_cons.val2, el)
            self.last_cons = self.last_cons.val2

    def finish(self):
        if self.res is None:
            return Element.Atom(0)
        r = self.res
        self.res = None
        return r

    def abandon(self):
       if self.res is not None:
           return [self.res]
       return []

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
        if el.val2 <= 8:
            m = 0xFFFF_FFFF_FFFF_FFFF
            n = el.val1
            s = Element.Atom(((m^(m<<(self.end*8))) & n) >> (self.start*8), self.end-self.start)
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
            self.i %= 0x1_0000_0000_0000_0000

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

class op_sha256(Operator):
    def __init__(self):
        self.st = hashlib.sha256()

    def argument(self, el):
        if not el.is_atom():
            raise Exception("sha256: cannot hash list")
        self.st.update(el.atom_as_bytes())
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
        if len(self.args) != 3:
            raise Exception("bip340_verify: too few arguments")
        pk, m, sig = self.args
        if pk.val2 != 32 or m.val2 != 32 or sig.val2 != 64:
            r = False
        else:
            r = verystable.core.key.verify_schnorr(key=pk.val1, sig=sig.val1, msg=m.val1)
        pk.deref()
        m.deref()
        sig.deref()
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

    def argument(self, el):
        # el is either an atom giving info about the tx as a whole
        # or a pair of what info is requested, plus what input/output idx
        #  we want info about
        if el.is_atom():
            code = el.atom_as_u64()
            which = None
        elif el.is_cons():
            if not el.val1.is_atom() or not el.val2.is_atom():
                raise Exception("tx: expects atoms or pairs of atoms")
            code = el.val1.atom_as_u64()
            which = el.val2.atom_as_u64()
        result = self.get_tx_info(code, which)
        if self.r is None:
            self.r = result
        elif self.last_cons is None:
            self.last_cons = Element.Cons(result, Element.Atom(0))
            self.r = Element.Cons(self.r, self.last_cons)
        else:
            assert self.last_cons.is_cons()
            assert self.last_cons.val2.is_atom()
            assert self.last_cons.val2.val2 == 0
            self.last_cons.val2 = Element.Cons(result, self.last_cons.val2)
            self.last_cons = self.last_cons.val2
        el.deref()

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
  (0x02, "x", op_x),  # exception
  (0x03, "i", op_i),  # eager-evaluated if
  (0x04, "sf", op_softfork),

  (0x05, "c", op_c), # construct a list, last element is a list
  (0x06, "h", op_h), # head / car
  (0x07, "t", op_t), # tail / cdr
  (0x08, "l", op_l), # is cons?

  (0x09, "not", op_nand),
  (0x0a, "all", op_and),
  (0x0b, "any", op_or),

  (0x0c, "=", op_eq),
  (0x0d, "<s", op_lt_str),
  (0x0e, "strlen", op_strlen),
  (0x0f, "substr", op_substr),
  (0x10, "cat", op_cat),

#  (0x11, "~",op_bit_not),
#  (0x12, "&", op_bit_and),
#  (0x13, "|", op_bit_or),
#  (0x14, "^", op_bit_xor),
  (0x17, "+", op_add_u64),
  (0x18, "-", op_sub_u64),
  (0x19, "*", op_mul_u64),
  (0x1a, "%", op_mod_u64),
#  (0x1b, "/%", op_divmod_u64), # (/ a b) => (h (/% a b))
#  (0x1d, "<<", op_lshift_u64),
#  (0x1e, ">>", op_rshift_u64),

  (0x1c, "<", op_lt_lendian),   # not restricted to u64
#  (0x1f, "log2b42", op_log2b42_u64),  # returns floor(log_2(x) * 2**42)
      ## allow this to apply to arbitrary atoms?
      ## (log of a 500kB atoms will fit into a u64)

#  (0x20, "rd_csn", op_csn_read),  # convert CScriptNum to u64?
#  (0x21, "wr_csn", op_csn_write), # convert u64 to CScriptNum?
#  (0x22, "rd_list", op_list_read), # read bytes to Element
#  (0x23, "wr_list", op_list_write), # write Element as bytes

  (0x24, "sha256", op_sha256),
 # (0x25, "ripemd160", op_ripemd160),
  (0x26, "hash160", op_hash160),
  (0x27, "hash256", op_hash256),
  (0x28, "bip340_verify", op_bip340_verify),
#  (0x29, "ecdsa_verify", op_ecdsa_verify),
#  (0x2a, "secp256k1_muladd", op_secp256k1_muladd),

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

class SExpr:
    re_parse = re.compile("(?P<ws>\s+)|(?P<open>[(])|(?P<close>[)])|(?P<dot>[.])|(?P<tick>['])|(?P<atom>[^'()\s.]+)")
    re_int = re.compile("^-?\d+$")
    re_hex = re.compile("^0x[0-9a-fA-F]+$")
    re_quote = re.compile('^"[^"]*"$')

    @staticmethod
    def list_to_element(l):
        if len(l) >= 3 and l[-2] is None:
            t = l[-1]
            l = l[:-2]
        else:
            t = Element.Atom(0)
        assert None not in l
        for h in reversed(l):
            t = Element.Cons(h, t)
        return t

    @classmethod
    def get_token(cls, s):
        m = cls.re_parse.match(s)
        if m is None:
            raise Exception("failed to parse at \"%s\"" % (s,))
        return s[m.end():], m

    @classmethod
    def parse(cls, s, many=False):
        where = 0
        end = len(s)
        parstack = [[]]

        while s != "":
            s, m = cls.get_token(s)

            g = m.groupdict()
            if g["ws"]:
                pass
            elif g["open"]:
                parstack.append([])
            elif g["close"]:
                if len(parstack) <= 1 or (parstack[-1] and parstack[-1][-1] is None) or (parstack[-1] and parstack[-1][0] == "tick"):
                    raise Exception("unexpected )")
                q = parstack.pop()
                parstack[-1].append(cls.list_to_element(q))
            elif g["dot"]:
                if len(parstack[-1]) == 0:
                    raise Exception("must have one or more elements before . in list")
                parstack[-1].append(None)
            elif g["tick"]:
                parstack.append(["tick"])
            elif g["atom"]:
                a = g["atom"]
                if a in SExpr_FUNCS:
                    a = SExpr_FUNCS[a]
                elif a == "nil":
                    a = 0
                elif cls.re_hex.match(a):
                    a = bytes.fromhex(a[2:])
                elif cls.re_int.match(a):
                    a = int(a, 10)
                elif cls.re_quote.match(a):
                    a = a[1:-1]
                else:
                    raise Exception("unparsable/unknown atom %r" % (a,))
                if a == b'' or a == 0:
                    parstack[-1].append(Element.Atom(0))
                else:
                    parstack[-1].append(Element.Atom(a))
            else:
                raise Exception("BUG: unhandled match")

            while len(parstack[-1]) > 1 and parstack[-1][0] == "tick":
                assert len(parstack[-1]) == 2
                q = parstack.pop()
                parstack[-1].append(Element.Cons(Element.Atom(0), q[1]))

            if len(parstack[-1]) > 3 and parstack[-1][-3] is None:
                raise Exception("cannot have multiple elements after . in list")

        if parstack and parstack[-1] and parstack[-1][0] == "tick":
            raise Exception("tick without following element")

        if len(parstack) > 1:
            raise Exception("missing )")

        if not many:
            if len(parstack[0]) > 1:
                raise Exception("multiple unbracketed entries")
            return parstack[0][0]

        else:
            return cls.list_to_element(parstack[0])

def steal_list(l):
    assert isinstance(l, Element) and l.is_cons()
    h, t = l.val1.bumpref(), l.val2.bumpref()
    l.deref()
    return h, t

def get_env(n, env):
    if n < 0:
        raise Exception("env argument out of range: %s" % (n,))
    while n > 1:
        if not env.is_cons():
            raise Exception("invalid env path %d" % (n,))
        n, x = divmod(n, 2)
        env = env.val2 if x else env.val1
    return env

def eager_eval(baseenv, inst, debug):
   assert isinstance(baseenv, Element)
   assert isinstance(inst, Element)

   work = [(0, baseenv.bumpref(), None, inst.bumpref())] # stage, env, generator, remaining args to evaluate

   if debug:
       print(f'ENV={baseenv}')
       print(f'GOAL={inst}')

   while work:
       if ALLOCATOR.over_limit():
           raise Exception("used too much memory")

       (what, env, gen, args) = work.pop()

       if debug:
           if env is baseenv:
               print(f'  depth={len(work)} ENV {gen} {args}')
           else:
               print(f'  depth={len(work)} <{env}> {gen} {args}')
           for xd, (xw, xe, xg, xa) in enumerate(work):
               if xe is baseenv: xe = "ENV"
               print(f' &depth={xd} <{xe}> {xg} {xa}')

       assert isinstance(args, Element)
       result = None

       if args.is_nil():
           if gen is None:
               result = args.bumpref()
           else:
               result = gen.finish()
               assert result is not None
       elif args.is_atom():
           if gen is None:
               n = args.atom_as_u64()
               result = get_env(n, env).bumpref()
           else:
               raise Exception("args terminated with non-nil atom")
       else:
           arg, args = steal_list(args)

           if gen is None:
               if arg.is_cons():
                   work.append( (what, env, gen, args) )
                   work.append( (1, env.bumpref(), None, arg) )
               else:
                   opcode = arg.atom_as_u64()
                   huh = arg.val1,arg.val2
                   arg.deref()
                   if opcode == 0:
                       # nil / q
                       result = args.bumpref()
                       assert result is not None
                   else:
                       o = Op_FUNCS.get(opcode, None)
                       if o is None:
                           raise Exception("unknown operator: %x %s" % (opcode,huh))
                       if debug: print("DOING OP %s" % (o.__name__))
                       gen = o()
                       work.append( (what, env, gen, args) )
           else:
               if arg.is_atom():
                   if arg.is_nil():
                       gen.argument(arg)
                   else:
                       n = arg.atom_as_u64()
                       arg.deref()
                       gen.argument(get_env(n, env).bumpref())
                   work.append( (what, env, gen, args) )
               else:
                   work.append( (what, env, gen, args) )
                   work.append( (2, env.bumpref(), None, arg) )

       if result is None: continue

       # tail call (a)
       if not isinstance(result, list):
           if debug: print(f'  fin --> {result}')
       else:
           if debug: print(f'  fin --> {" // ".join(map(str,result))}')
           if result[0] is not None:
               env.deref()
               env, args = result
           else:
               args = result[1]
           work.append( (what, env, None, args) )
           continue

       assert isinstance(result, Element)
       env.deref()
       args.deref()

       if what == 0:
           # finish!
           assert len(work) == 0
           return result

       assert len(work) > 0
       if debug: print(f"RES {what} {result} {gen}")
       if what == 1:
           # recursion to decide instruction
           if result.is_cons():
               raise Exception("non-atomic instruction after evaluation: %s" % (result,))
           (_w, _e, _g, _a) = work.pop()
           assert _g is None
           work.append( (_w, _e, _g, Element.Cons(result, _a)) )
           continue
       elif what == 2:
           # recursion to resolve argument
           assert work[-1][2] is not None
           work[-1][2].argument(result)
           continue

       assert False, "BUG: unreachable"
   assert False, "BUG: unreachable"


def lazy_eval(env, sexpr, debug):
    result = Element.Func(Element.Cons(sexpr.bumpref(), env.bumpref()), fn_eval())
    stack = [(True, result)]
    error = None
    while stack:
        assert error is None
        ALLOCATOR.record_work(1)
        if ALLOCATOR.over_limit(): break
        dfs, work = stack.pop()
        if debug: print(f"{len(stack)}/{0+dfs}:{ALLOCATOR.effort}: {work}")
        if work.kind == REF:
            if work.val1.kind == REF:
                work.replace(REF, work.val1.val1.bumpref())
                stack.append((dfs, work))
                continue
            else:
                work = work.val1
                # pass through
        if work.kind == ERROR:
            # early exit
            error = work.bumpref()
            break
        if work.kind == ATOM: continue
        if work.kind == CONS:
            if work.val1.kind == ERROR:
                stack.append((dfs, work.val1))
            elif work.val2.kind == ERROR:
                stack.append((dfs, work.val2))
            elif dfs:
                if work.val2.kind != ATOM: stack.append((dfs, work.val2))
                if work.val1.kind != ATOM: stack.append((dfs, work.val1))
            continue
        assert work.kind == FUNC
        stack.append((dfs, work))
        x = work.val2.resolve(work)
        if ALLOCATOR.over_limit(): break
        if x is not None:
            assert isinstance(x, Element)
            stack.append((False, x))

    if ALLOCATOR.over_limit():
        assert error is None
        #result.bumpref()
        error = Element.Error("exceeded execution limits")
    if error is not None:
        result.deref()
        result = error
    return result

class Rep:
    def __init__(self, env, debug=False, lazy=True):
        self.env = env
        self.debug = debug
        self.lazy = lazy

    def __call__(self, program, debug=None):
        if debug is None: debug = self.debug
        if debug: print("PROGRAM: %s" % (program,))
        p = SExpr.parse(program, many=False)
        ALLOCATOR.max = 0
        ALLOCATOR.reset_work()
        init_x = ALLOCATOR.x
        before_x = set(ALLOCATOR.allocated)
        try:
            if self.lazy:
                r = lazy_eval(self.env, p, debug=debug)
            else:
                r = eager_eval(self.env, p, debug=debug)
            print("MAX=%s WORK=%s ; %s -> %s" % (ALLOCATOR.max, ALLOCATOR.effort, program, r))
            r.deref()
        except:
            print("%s -> FAILED" % (program,))
            raise
            ## need some proper way of freeing memory so that REPL can
            ## continue after a failure. difficult because we don't want
            ## to free the original environment, but do want to free
            ## everything else
            ##
            ## perhaps should restructure to set a flag in ALLOCATOR
            ## or similar for normal execution failures, and only raise
            ## for BUG scenarios? need to count "execution load" somewhere
            ## as well
        if ALLOCATOR.x != init_x:
            print("=======================")
            print("leaked:")
            for el,ln in ALLOCATOR.allocated.items():
                if el not in before_x:
                    print(el._refs, ln, el)
            print("=======================")
            print("pre-existing:")
            for el,ln in ALLOCATOR.allocated.items():
                if el in before_x:
                    print(el._refs, ln, el)
            print("=======================")
            print("missing:")
            for el in before_x:
                if el not in ALLOCATOR.allocated:
                    print("...", el)
            print("=======================")
        assert ALLOCATOR.x == init_x, "memory leak: %d -> %d (%d)" % (init_x, ALLOCATOR.x, ALLOCATOR.x - init_x)
        p.deref()

nil = Element.Atom(0)
one = Element.Atom(1)

rep = Rep(SExpr.parse("((55 . 33) . (22 . 8))"))
print("\nBasic syntax -- Env: %s" % (rep.env))


rep("1")
rep("(q . 1)")
rep("(q . q)")
rep("'1")
rep("'(1)")
rep("'\"q\"")
rep("(+ '2 '2 . 0)")
rep("(+ (q . 2) '2)")
rep("(a '1 '1 '2 '3 '4)")
rep("(a '1 '1 '2 '3 '4 '5)")
rep("(a '1 '1 '2 '3 '4 '5 '6)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7 '8)")
rep("(a '(+ '2 '2))")
rep("(h '(4 5 6))")
rep("(t '(4 5 6))")
rep("(+ 7 '3)")
rep("(a '(+ 7 '3))")
rep("(a '(+ 7 '3) 1)")
rep("(a '(+ 7 '3) '((1 . 2) . (3 . 4)))")
rep("(c 1 ())")
rep("(c 4 ())")
rep("(c 4 6 5 7 nil)")
#rep("(- '77 (* '3 (/ '77 '3)))")
rep("(c '1 '2 '3 '4 (c '5 '(6 7)))")
rep("(a '(+ 7 '3) (c '(1 . 2) 3))")
rep("(c '2 '2)")
rep("(c '2 (sf . '(1 2 3 4 5)))")
rep("(c (l ()) (l '1) (l '(1 2 3)) ())")
rep("(all '1 '2 '3 '4)")
rep("(not '1 '2 '3 '4)")
rep("(all '1 '2 '0 '4)")
rep("(not '1 '2 '0 '4)")
rep("(any '0 '0 '5 '0)")
rep("(< '1 '2 '3 '4 '5)")
rep("(< '1 '2 '4 '4 '5)")
rep("(<)")
rep("(< '1)")
rep("(< '1 '2)")
rep("(< '2 '1)")
rep("(+ '1 '2 . '3)")
rep("(<s)")
rep("(<s '1)")
rep("(<s '99 '66 '88)")
rep("(<s '1 '2 '3)")
rep("(<s nil '0x00 '0x0001 '0x01 '0x02)")
rep("(<s '0x00 '0x0001 '0x01 '0x0002)")
rep("(c (<s '254 '255) (< '254 '255) nil)")
rep("(c (<s '255 '256) (< '255 '256) nil)")
rep("(%)")
rep("(% '100 '3)")
rep("(% '100 '3 '2)")

# factorial
# n=2, fn=3
# `if 2 (a 3 (- 2 '1) 3)
rep = Rep(SExpr.parse("(a (i 2 '(* 2 (a 3 (- 2 '1) 3)) ''1))"))
print("\nInefficient factorial -- Env: %s" % (rep.env))
rep("(a 1 '3 1)")
rep("(a 1 '10 1)")
rep("(a 1 '40 1)")
#rep("(a 1 '150 1)")
#rep("(a 1 (c '15000 1))")

# factorial but efficient
rep = Rep(SExpr.parse("(a (i 2 '(a 7 (c (- 2 '1) (* 5 2) 7)) '(c 5)))"))
print("\nEfficient (?) factorial -- Env: %s" % (rep.env))
rep("(a 1 (c '3 '1 1))")
rep("(a 1 (c '10 '1 1))")
rep("(a 1 (c '40 '1 1))")
rep("(a 1 (c '150 '1 1))")  # nil since 66! == 0 (mod 2**64)
rep("(a 1 (c '15000 '1 1))")

# sum factorial (+ 1! 2! 3! 4! ... n!)
# (proxy for (sha256 1! 2! .. n!)
# f 1 1 n
# f a! a b = 
# 4=fn 6=(a-1)! 5=a 7=left!

rep = Rep(SExpr.parse("(a (i 7 '(c (c nil 6) (a 4 4 (* 6 5) (+ 5 '1) (- 7 '1))) '(c nil)))"))
print("\nSum factorial (1! + 2! + .. + n!) -- Env: %s" % (rep.env))
#rep("(a 1 1 '1 '1 '10)")
rep("(c '+ (a 1 1 '1 '1 '10))")
rep("(a (c '+ (a 1 1 '1 '1 '10)))")

# fibonacci


# 0 1 1 2 3 5 ...
# 0 1 2 3 4 5

# fib n = fib n 0 1
# fib 0 a b = a; fib n a b = fib (n-1) b (a+b)
# env = (n a b FIB) ; n=2, a=5, b=11, FIB=15

rep = Rep(SExpr.parse("(a (i 2 '(a 15 (c (- 2 '1) 11 (+ 5 11) 15)) '(c 5)))"))
print("\nFibonacci 1 -- Env: %s" % (rep.env))
rep("(a 1 (c '300 '0 '1 1))")
rep("(a 1 (c '500 '0 '1 1))")

rep = Rep(SExpr.parse("(a (i 4 '(a 7 (- 4 '1) 5 (+ 6 5) 7) '(c 6)))"))
print("\nFibonacci 2 -- Env: %s" % (rep.env))
rep("(a 1 '300 '0 '1 1)")
rep("(a 1 '500 '0 '1 1)")

rep = Rep(SExpr.parse("0x0200000015a20d97f5a65e130e08f2b254f97f65b96173a7057aef0da203000000000000887e309c02ebdddbd0f3faff78f868d61b1c4cff2a25e5b3c9d90ff501818fa0e7965d508bdb051a40d8d8f7"))
print("\nHash a transaction -- Env: %s" % (rep.env))
rep("(sha256 (sha256 1))")
rep("(hash256 1)")


bip340_tests = [
"F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9,0000000000000000000000000000000000000000000000000000000000000000,E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0,TRUE",
"DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A,TRUE",
"DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8,7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C,5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7,TRUE",
"25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517,FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3,TRUE",
"D69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9,4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703,00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4,TRUE",
"EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B,FALSE",
"DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2,FALSE",
]
for x in bip340_tests:
    key, msg, sig, result = x.split(",")
    result = 1 if result == "TRUE" else 0
    rep(f"(c (bip340_verify '0x{key} '0x{msg} '0x{sig}) '{result} nil)")

GLOBAL_TX = verystable.core.messages.tx_from_hex("f0ccee2a000101ebf2f9fc896e70145c84116fae33d0242f8c146e1a07deecd9a98d9cc03f4fb70d000000002badf3fb01126b8c01000000001976a914551b850385def11149727e72c4470ffaeae5cdf288ac04402c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b712220256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac21c0cdb18e708d5164ecbd681797623cb8f9be34dd1765ef0b63788d18ca4db18478025073ee1a6e46")
GLOBAL_TX_INPUT_IDX = 0
GLOBAL_TX_SCRIPT = bytes.fromhex("20256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac")
GLOBAL_UTXOS = [
    verystable.core.messages.from_hex(verystable.core.messages.CTxOut(), "1fc6d101000000002251203240405372856fe921522eca27514e2669f0aa4c46d52c78cfe608174828f937")
]

rep("(bip342_txmsg)")
rep("(bip340_verify '0x256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963f (bip342_txmsg) '0x2c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b71)")

rep("(tx '0 '1 '2 '3 '4)")
rep("(tx '10 '11 '12 '13 '14 '15 '16)")
rep("(tx '(10 . 0) '(11 . 0) '(12 . 0) '(13 . 0) '(14 . 0) '(15 . 0) '(16 . 0))")
rep("(tx '(20 . 0) '(21 . 0))")
rep("(- (tx '15) (tx '(20 . 0)))")

rep("(hash256 (tx '5))")

rep("(a '1 '1 '2 '3 '4 '5)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7 '8 '9 '10)")

for a in [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,20,21]:
    rep("(tx '%d)" % (a,))

# acc fn 0 n nil -> acc fn 1 (- n 1) (cat nil (fn 0))
#  8  12 10 14 3
rep = Rep(SExpr.parse("(a (i 14 '(a 8 8 12 (+ 10 '1) (- 14 '1) (cat 3 (a 12 10))) '3))"))
print("\nBIP342 calculated manually -- Env: %s" % (rep.env))
rep("(bip342_txmsg)")

# implement sighash_all, codesep_pos=-1, len(scriptPubKey) < 253
rep("(a '(sha256 4 4 '0x00 6 3) (sha256 '\"TapSighash\") (cat '0x00 (tx '0) (tx '1) (sha256 (a 1 1 '(cat (tx (c '11 1)) (tx (c '12 1))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '15 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(a '(cat (strlen 1) 1) (tx (c '16 '0))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '10 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(cat (tx (c '20 1)) (a '(cat (strlen 1) 1) (tx (c '21 1)))) '0 (tx '3) 'nil)) (i (tx '14) '0x03 '0x01) (substr (cat (tx '4) '0x00000000) 'nil '4) (i (tx '14) (sha256 (a '(cat (strlen 1) 1) (tx '14))) 'nil)) (cat (tx '6) '0x00 '0xffffffff))")

rep("(cat '0x1122 '0x3344)")


# levels:
#   bytes/hex
#   (c (q . 1) (q . 0xCAFEBABE) (q . "hello, world") (q . nil))
#   \' and aliases? (car,head = h, etc)
#   symbols; let/defun (compile to env access)
#   \` and \,  (quote and unquote / macros)

# notation?
#   'foo  = (q . foo)
#   '(a b c) = (q a b c)
#   `(a ,b c) = (c (q . a) b (q . c) nil)
#
# would be nice to have a "compiler" that can deal with a symbol table
# (for named ops).
