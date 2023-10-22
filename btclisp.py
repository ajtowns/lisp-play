#!/usr/bin/env python3

import re

class Allocator:
    """simple object to monitor how much space is used up by
       currently allocated objects"""
    def __init__(self):
        self.x = 0
        self.max = 0
        self.alloced = set()
        self.limit = 500000

    def over_limit(self):
        return self.max > self.limit

    def alloc(self, n, w):
        assert n >= 0
        self.x += n
        if self.x > self.max:
            self.max = self.x
        self.alloced.add(w)

    def free(self, n, w):
        assert n >= 0
        self.x -= n
        self.alloced.remove(w)

ALLOCATOR = Allocator()

class Element:
    def __init__(self, *, n=None, h=None, t=None):
        assert (n is None) != (h is None and t is None)
        self.refs = 1

        if isinstance(n, str):
            n = n.encode('utf8')
        elif isinstance(n, int):
            if n == 0:
                n = b''
            else:
                bl = (n.bit_length() + 8)//8
                n = n.to_bytes(bl, byteorder='big', signed=True)
        assert n is None or isinstance(n, bytes)

        if h is not None:
            assert isinstance(h, Element)
            assert isinstance(t, Element)

        self.n = n
        self.h = h
        self.t = t

        ALLOCATOR.alloc(self.alloc_size(), self)

    re_printable = re.compile(b"^[a-z]+$")
    _nil = None

    @classmethod
    @property
    def nil(cls):
        if cls._nil is None:
            cls._nil = cls(n=0)
        return cls._nil.bumpref()

    def alloc_size(self):
        if self.n is None:
            return 12
        else:
            return (len(self.n)//8)*8 + 16

    def bumpref(self):
        assert self.refs >= 1
        self.refs += 1
        return self

    def deref(self):
        s = [self]
        while s:
            f = s.pop()
            assert f.refs >= 1, f"double-free of {f}"
            f.refs -= 1
            if f.refs == 0:
                ALLOCATOR.free(f.alloc_size(), f)
                if f.is_list():
                    if f.h.is_atom():
                        s.append(f.t)
                        s.append(f.h)
                    else:
                        s.append(f.h)
                        s.append(f.t)

    def is_nil(self):
        return self.n == b''

    def is_atom(self):
        return self.n is not None

    def is_list(self):
        return self.n is None

    def __str__(self):
        if self.is_nil():
            return "nil"
        elif self.is_atom():
            if self.re_printable.match(self.n):
                return '"%s"' % (self.n.decode('utf8'),)
            elif len(self.n) == 1:
                return str(self.as_int(None))
            else:
                return "0x%s" % (self.n.hex(),)
        else:
            x = []
            while self.t.is_list():
                x.append(self.h)
                self = self.t
            x.append(self.h)
            if not self.t.is_nil():
                x.append(".")
                x.append(self.t)
            return "(%s)" % " ".join(map(str, x))

    def __repr__(self):
        if self.is_nil():
            return "Element(n=0)"
        elif self.is_atom():
            return "Element(n=0x%s)" % (self.n.hex())
        else:
            return "Element(h=%r, t=%r)" % (self.h, self.t)

    def as_int(self, fn):
        if self.n is None:
            raise Exception(f"{fn}: not a number: {self}")
        return int.from_bytes(self.n, byteorder='big', signed=True)

class Operator:
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

def build_tree(tree, element):
    i = 0
    while i < len(tree):
        if tree[i] is None:
            tree[i] = element
            return
        element = Element(h=tree[i], t=element)
        tree[i] = None
        i += 1
    tree.append(element)

def resolve_tree(tree):
    x = None
    for el in tree:
        if el is None: continue
        if x is None:
             x = el
        else:
             x = Element(h=el, t=x)
    return x

class op_a(Operator):
    # if given multiple arguments, builds them up into a tree,
    # biased to the left
    def __init__(self):
        self.tree = []
    def argument(self, el):
        if self.state == 0:
            self.i = el
            self.env = None
            self.state = 1
        else:
            build_tree(self.tree, el)
    def finish(self):
        if self.state == 0:
            raise Exception("a: requires at least one argument")
        env = resolve_tree(self.tree)
        return [env, self.i]

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
                self.result = Element.nil
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
        return self.result

class op_h(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("h: too many arguments")
        if el.is_atom():
            raise Exception("h: received non-list argument %s" % (el,))
        self.r = el.h.bumpref()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("h: must provide list argument")
        return self.r

class op_t(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("t: too many arguments")
        if el.is_atom():
            raise Exception("t: received non-list argument %s" % (el,))
        self.r = el.t.bumpref()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("t: must provide list argument")
        return self.r

class op_l(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("l: too many arguments")
        self.r = el.is_list()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("l: must provide list argument")
        if self.r:
            return Element(n=1)
        else:
            return Element.nil

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
            self.res = self.last_cons = Element(h=self.res, t=el)
        else:
            self.last_cons.t = Element(h=self.last_cons.t, t=el)
            self.last_cons = self.last_cons.t

    def finish(self):
        if self.res is None:
            return Element.nil
        return self.res

class op_add(Operator):
    def __init__(self):
        self.i = 0

    def argument(self, el):
        self.i += el.as_int("add")
        el.deref()

    def finish(self):
        return Element(n=self.i)

class op_mul(Operator):
    def __init__(self):
        self.i = 1

    def argument(self, el):
        self.i *= el.as_int("mul")
        el.deref()

    def finish(self):
        return Element(n=self.i)

class op_sub(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        n = el.as_int("sub")
        el.deref()
        if self.i is None:
            self.i = n
        else:
            self.i -= n

    def finish(self):
        if self.i is None:
            raise Exception("sub: missing arguments")
        return Element(n=self.i)

class op_div(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        n = el.as_int("div")
        el.deref()
        if self.i is None:
            self.i = n
        else:
            self.i //= n

    def finish(self):
        if self.i is None:
            raise Exception("div: missing arguments")
        return Element(n=self.i)

class op_softfork(Operator):
    def argument(self, el):
        el.deref()
    def finish(self):
        return Element(n=1)

FUNCS = [
  (b'', "q", None), # quoting indicator, special

  (0x01, "a", op_a),  # apply
  (0x02, "x", op_x),  # exception
  (0x03, "i", op_i),  # eager-evaluated if
  (0x04, "sf", op_softfork),

  (0x05, "c", op_c), # construct a list, last element is a list
  (0x06, "h", op_h), # head / car
  (0x07, "t", op_t), # tail / cdr
  (0x08, "l", op_l), # is cons?

#  (0x09, "not", op_none),
#  (0x0a, "all", op_all),
#  (0x0b, "any", op_any),

#  (0x0c, "=", op_eq),
# (0x0d, "<s", op_str_lt),
# (0x0e, "len", op_length),
# (0x0f, "sub", op_substr),
# (0x10, "cat", op_cat),

#  (0x11, "~",op_bit_not),
#  (0x12, "&", op_bit_and),
#  (0x13, "|", op_bit_or),
#  (0x14, "^", op_bit_xor),
#  (0x15, "b<<", op_bit_lshift),
#  (0x16, "b>>", op_bit_rshift),

  (0x17, "+", op_add),
  (0x18, "-", op_sub),
  (0x19, "*", op_mul),
  (0x1a, "/", op_div),
#  (0x17, "+", op_add_u64),
#  (0x18, "-", op_sub_u64),
#  (0x19, "*", op_mul_u64),
#  (0x1a, "%", op_mod_u64),
#  (0x1b, "/%", op_divmod_u64), # (/ a b) => (h (/% a b))
#  (0x1c, "<", op_lt_u64),
#  (0x1d, "<<", op_lshift_u64),
#  (0x1e, ">>", op_rshift_u64),
#  (0x1f, "log2e42", op_log2e42_u64),

#  (0x20, "bn+", op_add_bn),
#  (0x21, "bn-", op_sub_bn),
#  (0x22, "bn*", op_mul_bn),
#  (0x23, "bn%", op_mod_bn),
#  (0x24, "bn/%", op_divmod_bn), # (/ a b) => (h (/% a b))
#  (0x25, "bn<", op_lt_bn),
#  (0x26, "bn<<", op_lshift_bn),
#  (0x27, "bn>>", op_rshift_bn),
#  (0x28, "bnlog2e42", op_log2e42_bn),

#  (0x29, "rd_csn", op_csn_read),
#  (0x2a, "wr_csn", op_csn_write),
#  (0x2b, "rd_list", op_list_read),
#  (0x2c, "wr_list", op_list_write),

#  (0x2d, "sha256", op_sha256),
#  (0x2e, "ripemd160", op_ripemd160),
#  (0x2f, "hash160", op_hash160),
#  (0x30, "hash256", op_hash256),
#  (0x31, "bip340_verify", op_bip340_verify),
#  (0x32, "ecdsa_verify", op_ecdsa_verify),
#  (0x33, "secp256k1_muladd", op_secp256k1_muladd),

#  (0x34, "tx", op_tx),
#  (0x35, "bip341_tx", op_bip341_tx),
#  (0x36, "bip342_txmsg", op_bip342_txmsg),
#  (0x37, "bip345_vault", op_bip345_vault),
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
            t = Element.nil
        assert None not in l
        for h in reversed(l):
            t = Element(h=h, t=t)
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
                    a = bytes.from_hex(a[2:])
                elif cls.re_int.match(a):
                    a = int(a, 10)
                elif cls.re_quote.match(a):
                    a = a[1:-1]
                else:
                    raise Exception("unparsable/unknown atom %r" % (a,))
                if a == b'' or a == 0:
                    parstack[-1].append(Element.nil)
                else:
                    parstack[-1].append(Element(n=a))
            else:
                raise Exception("BUG: unhandled match")

            while len(parstack[-1]) > 1 and parstack[-1][0] == "tick":
                assert len(parstack[-1]) == 2
                q = parstack.pop()
                parstack[-1].append(Element(h=Element.nil, t=q[1]))

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
    assert isinstance(l, Element) and l.is_list()
    h, t = l.h.bumpref(), l.t.bumpref()
    l.deref()
    return h, t

def get_env(n, env):
    if n < 0:
        raise Exception("env argument out of range: %s" % (n,))
    while n > 1:
        if not env.is_list():
            raise Exception("invalid env path %d" % (n,))
        n, x = divmod(n, 2)
        env = env.t if x else env.h
    return env

def eval(baseenv, inst, debug):
   assert isinstance(baseenv, Element)
   assert isinstance(inst, Element)

   work = [(0, baseenv.bumpref(), None, inst.bumpref())] # stage, env, generator, remaining args to evaluate

   while work:
       if ALLOCATOR.over_limit():
           raise Exception("used too much memory")

       (what, env, gen, args) = work.pop()

       if debug:
           if env is baseenv:
               print(f'  depth={len(work)} ENV {args} {gen}')
           else:
               print(f'  depth={len(work)} <{env}> {args} {gen}')

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
               result = args.bumpref()
               assert result is not None
           else:
               raise Exception("args terminated with non-list")
       else:
           arg, args = steal_list(args)

           if gen is None:
               if arg.is_list():
                   work.append( (what, env, gen, args) )
                   work.append( (1, env.bumpref(), None, arg) )
               else:
                   opcode = arg.n
                   arg.deref()
                   if len(opcode) == 0:
                       # nil / q
                       result = args.bumpref()
                       assert result is not None
                   else:
                       o = Op_FUNCS.get(opcode[0], None) if len(opcode) == 1 else None
                       if o is None:
                           raise Exception("unknown operator: %s" % (opcode.hex(),))
                       gen = o()
                       work.append( (what, env, gen, args) )
           else:
               if arg.is_atom():
                   if arg.is_nil():
                       gen.argument(arg)
                   else:
                       n = arg.as_int("env")
                       arg.deref()
                       gen.argument(get_env(n, env).bumpref())
                   work.append( (what, env, gen, args) )
               else:
                   work.append( (what, env, gen, args) )
                   work.append( (2, env.bumpref(), None, arg) )

       if result is None: continue

       if debug: print(f'  fin --> {result}')
       # tail call (a)
       if isinstance(result, list):
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
       if debug: print(f"RES {what} {result}")
       if what == 1:
           # recursion to decide instruction
           if result.is_list():
               raise Exception("non-atomic instruction after evaluation: %s" % (result,))
           (_w, _e, _g, _a) = work.pop()
           assert _g is None
           work.append( (_w, _e, _g, Element(h=result, t=_a)) )
           continue
       elif what == 2:
           # recursion to resolve argument
           assert work[-1][2] is not None
           work[-1][2].argument(result)
           continue

       assert False, "BUG: unreachable"
   assert False, "BUG: unreachable"

class Rep:
    def __init__(self, env, debug=False):
        self.env = env
        self.debug = debug

    def __call__(self, program, debug=None):
        if debug is None: debug = self.debug
        ALLOCATOR.max = 0
        init_x = ALLOCATOR.x
        p = SExpr.parse(program, many=False)
        try:
            r = eval(self.env, p, debug=debug)
            print("MAX=%s ; %s -> %s" % (ALLOCATOR.max, program, r))
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
        p.deref()
        assert ALLOCATOR.x == init_x, "memory leak: %d -> %d (%d)" % (init_x, ALLOCATOR.x, ALLOCATOR.x - init_x)

nil = Element.nil

rep = Rep(SExpr.parse("((55 . 33) . (22 . 8))"))
print("Env: %s" % (rep.env))
rep("1")
rep("(q . 1)")
rep("(q . q)")
rep("'1")
rep("'(1)")
rep("'\"q\"")
rep("(+ '2 '2 . 0)")
rep("(+ (q . 2) '2)")
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
rep("(- '77 (* '3 (/ '77 '3)))")
rep("(c '1 '2 '3 '4 (c '5 '(6 7)))")
rep("(a '(+ 7 '3) (c '(1 . 2) 3))")
rep("(c '2 '2)")
rep("(c '2 (sf . '(1 2 3 4 5)))")
rep("(c (l ()) (l '1) (l '(1 2 3)) ())")

# factorial
rep = Rep(SExpr.parse("(a (i 2 '(* 2 (a 3 (c (- 2 '1) 3))) '1))"))
rep("(a 1 (c '150 1))")
#rep("(a 1 (c '15000 1))")

# factorial but efficient
rep = Rep(SExpr.parse("(a (i 2 '(a 7 (c (- 2 '1) (* 5 2) 7)) '(c 5)))"))
rep("(a 1 (c '150 '1 1))")
#rep("(a 1 (c '15000 '1 1))")

# sum factorial (+ 1! 2! 3! 4! ... n!)
# (proxy for (sha256 1! 2! .. n!)
# f 1 1 n
# f a! a b = 
# 4=fn 6=(a-1)! 5=a 7=left!

rep = Rep(SExpr.parse("(a (i 7 '(c (c nil 6) (a 4 4 (* 6 5) (+ 5 '1) (- 7 '1))) '(c nil)))"))
#rep("(a 1 1 '1 '1 '10)")
rep("(c '+ (a 1 1 '1 '1 '10))")
rep("(a (c '+ (a 1 1 '1 '1 '10)))", debug=True)
xxx

# fibonacci


# 0 1 1 2 3 5 ...
# 0 1 2 3 4 5

# fib n = fib n 0 1
# fib 0 a b = a; fib n a b = fib (n-1) b (a+b)
# env = (n a b FIB) ; n=2, a=5, b=11, FIB=15

rep = Rep(SExpr.parse("(a (i 2 '(a 15 (c (- 2 '1) 11 (+ 5 11) 15)) '(c 5)))"))
rep("(a 1 (c '300 '0 '1 1))")

rep = Rep(SExpr.parse("(a (i 4 '(a 7 (- 4 '1) 5 (+ 6 5) 7) '(c 6)))"))
rep("(a 1 '300 '0 '1 1)")

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
