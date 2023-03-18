#!/usr/bin/env python3

import re

class Allocator:
    def __init__(self):
        self.x = 0
        self.max = 0
        self.alloced = set()
    def alloc(self, n, w):
        self.x += n
        if self.x > self.max:
            self.max = self.x
        self.alloced.add(w)
    def free(self, n, w):
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
            return "()"
        elif self.is_atom():
            if self.re_printable.match(self.n):
                return self.n.decode('utf8')
            elif len(self.n) == 1:
                return str(self.as_int(None))
            else:
                return self.n.hex()
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

class SExpr:
    re_parse = re.compile('(?P<ws>\s+)|(?P<open>[(])|(?P<close>[)])|(?P<dot>[.])|(?P<atom>[^()\s.]+)')
    re_int = re.compile("^-?\d+$")
    re_hex = re.compile("^0x[0-9a-fA-F]+$")

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
                if len(parstack) <= 1 or (parstack[-1] and parstack[-1][-1] is None):
                    raise Exception("unexpected )")
                q = parstack.pop()
                parstack[-1].append(cls.list_to_element(q))
            elif g["dot"]:
                if len(parstack[-1]) == 0:
                    raise Exception("must have one or more elements before . in list")
                parstack[-1].append(None)
            elif g["atom"]:
                a = g["atom"]
                if cls.re_hex.match(a):
                    a = bytes.from_hex(a[2:])
                elif cls.re_int.match(a):
                    a = int(a, 10)
                parstack[-1].append(Element(n=a))
            else:
                raise Exception("BUG: unhandled match")

            if len(parstack[-1]) > 3 and parstack[-1][-3] is None:
                raise Exception("cannot have multiple elements after . in list")

        if len(parstack) > 1:
            raise Exception("missing )")

        if not many:
            if len(parstack[0]) > 1:
                raise Exception("multiple unbracketed entries")
            return parstack[0][0]

        else:
            return cls.list_to_element(parstack[0])

class GenArgs:
    def __init__(self):
        self.n = None

    def check(self):
        self.n = yield None

    def get_arg(self, err):
        a = self.n
        if a is not None:
            self.n = yield None
        elif err is not None:
            raise Exception(err)
        return a

    def assert_end(self, err):
        if self.n is not None:
            raise Exception(err)

    def __iter__(self):
        return self

    def __next__(self):
        if self.n is None:
            raise StopIteration
        n = self.n
        self.n = None
        return n

def op_a():
    gargs = GenArgs()
    yield from gargs.check() # start!
    i = yield from gargs.get_arg(err="a: requires at least one argument")
    env = yield from gargs.get_arg(err=None)
    gargs.assert_end(err="a: too many arguments")
    yield [env, i]

def op_x():
    gargs = GenArgs()
    yield from gargs.check() # start!
    x = []
    for i in gargs:
        x.append(repr(i))
        i.deref()
        yield from gargs.check()
    if x == []:
        x = ["x: explicit exception"]
    raise Exception(" ".join(x))

def op_i():
    gargs = GenArgs()
    yield from gargs.check() # start!
    c = yield from gargs.get_arg(err="i: must provide condition argument")
    branch = False if c.is_nil() else True
    c.deref()
    t = yield from gargs.get_arg(err="i: must provide then argument")
    result = t.bumpref() if not t.is_nil() else Element.nil
    t.deref()
    f = yield from gargs.get_arg(err=None)
    if f is not None:
        if not branch:
            result = f
        else:
            f.deref()
    gargs.assert_end(err="i: too many arguments")
    yield result

def op_f():
    gargs = GenArgs()
    yield from gargs.check() # start!
    l = yield from gargs.get_arg(err="f: must provide list argument")
    if l.is_atom():
        raise Exception("f: received non-list argument %s" % (l,))
    gargs.assert_end(err="f: too many arguments")
    h = l.h.bumpref()
    l.deref()
    yield h

def op_r():
    gargs = GenArgs()
    yield from gargs.check() # start!
    l = yield from gargs.get_arg(err="r: must provide list argument")
    if l.is_atom():
        raise Exception("r: received non-list argument %s" % (l,))
    gargs.assert_end(err="r: too many arguments")
    t = l.t.bumpref()
    l.deref()
    yield t

def op_c():
    gargs = GenArgs()
    yield from gargs.check() # start!
    res = None
    last_cons = None
    for i in gargs:
        if res is None:
            res = i
        elif last_cons is None:
            res = last_cons = Element(h=res, t=i)
        else:
            last_cons.t = Element(h=last_cons.t, t=i)
            last_cons = last_cons.t
        yield from gargs.check()

    if res is None:
        res = Element.nil
    e = res if last_cons is None else last_cons.t

    yield res

def op_add():
    gargs = GenArgs()
    yield from gargs.check() # start!
    i = 0
    for k in gargs:
        i += k.as_int("add")
        k.deref()
        yield from gargs.check()
    yield Element(n=i)

def op_mul():
    gargs = GenArgs()
    yield from gargs.check() # start!
    i = 1
    for k in gargs:
        i *= k.as_int("mul")
        k.deref()
        yield from gargs.check()
    yield Element(n=i)

def op_sub():
    gargs = GenArgs()
    yield from gargs.check() # start!
    k = yield from gargs.get_arg(err="sub: missing arguments")
    i = k.as_int("sub")
    k.deref()
    for k in gargs:
        i -= k.as_int("sub")
        k.deref()
        yield from gargs.check()
    yield Element(n=i)

def op_div():
    gargs = GenArgs()
    yield from gargs.check() # start!
    k = yield from gargs.get_arg(err="div: missing arguments")
    i = k.as_int("div")
    k.deref()
    for k in gargs:
        i -= k.as_int("div")
        k.deref()
        yield from gargs.check()
    yield Element(n=i)

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
       (what, env, gen, args) = work.pop()

       if debug:
           if env is baseenv:
               print(f'  depth={len(work)} ENV {args} {gen}')
           else:
               print(f'  depth={len(work)} <{env}> {args} {gen}')

       assert isinstance(args, Element)
       result = None

       if args.is_nil():
           if gen is not None:
               result = gen.send(None)
           else:
               result = args.bumpref()
       elif args.is_atom():
           if gen is not None:
               raise Exception("args terminated with non-list")
           else:
               raise Exception("huh")
       else:
           arg, args = steal_list(args)

           if gen is None:
               if arg.is_list():
                   work.append( (what, env, gen, args) )
                   work.append( (1, env.bumpref(), None, arg) )
                   continue

               opcode = arg.n.decode('utf8')
               arg.deref()
               if opcode == "q":
                   result = args.bumpref()
               else:
                   o = "op_" + opcode
                   if not o in globals():
                       raise Exception("unknown operator: %s" % (o,))
                   gen = globals()[o]()
                   gen.send(None)
                   work.append( (what, env, gen, args) )
                   continue
           else:
               if arg.is_atom():
                   if arg.is_nil():
                       gen.send(arg)
                   else:
                       n = arg.as_int("env")
                       arg.deref()
                       gen.send(get_env(n, env).bumpref())
                   work.append( (what, env, gen, args) )
               else:
                   work.append( (what, env, gen, args) )
                   work.append( (2, env.bumpref(), None, arg) )
               continue

       assert result is not None

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
           work[-1][2].send(result)
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
        p = SExpr.parse(program, many=False)
        try:
            r = eval(self.env, p, debug=debug)
            print("MAX=%s ; %s -> %s" % (ALLOCATOR.max, program, r))
            r.deref()
        except:
            print("%s -> FAILED" % (program,))
            raise
        p.deref()

rep = Rep(SExpr.parse("((55 . 33) . (22 . 8))"))
print("Env: %s" % (rep.env))
rep("(add (q . 2) (q . 2) . 0)")
rep("(add (q . 2) (q . 2))")
rep("(a (q add (q . 2) (q . 2)))")
rep("(c 1 ())")
rep("(c 4 ())")
rep("(c 4 6 5 7 0)")
rep("(sub (q . 77) (mul (q . 3) (div (q . 77) (q . 3))))")
rep("(c (q . 1) (q . 2) (q . 3) (q . 4) (c (q . 5) (q 6 7)))")
rep("(f (q 4))")
rep("(add 7 (q . 3))")
rep("(a (q add 7 (q . 3)))")
rep("(a (q add 7 (q . 3)) 1)")
rep("(a (q add 7 (q . 3)) (c (q 1 . 2) 3))")
rep("(a (q add 7 (q . 3)) (q (1 . 2) . (3 . 4)))")
rep("(add (q . 2) (q . 2))")
rep("(c (q . 2) (q . 2))")

# factorial

rep = Rep(SExpr.parse("(a (i 2 (q mul 2 (a 3 (c (sub 2 (q . 1)) 3))) (q mul)))"))
rep("(a 1 (c (q . 150) 1))")


rep = Rep(SExpr.parse("(a (i 2 (q a 7 (c (sub 2 (q . 1)) (mul 5 2) 7)) (q c 5)))"))
rep("(a 1 (c (q . 150) (q . 1) 1))")
# 4 = arg 6 = acc 3 = factorial

# fibonacci


