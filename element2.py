#!/usr/bin/env python3

import re
import sys

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

ALLOCATOR = Allocator()

# kinds
ATOM=255
CONS=254
ERROR=253
FUNC=252

SYMBOL=251
SYMDEF=250


def int_to_bytes(i):
    if i == 0:
        return b''
    neg = (i < 0)
    if neg:
        i = -i
    s = (i.bit_length() + 7)//8
    b = i.to_bytes(s, byteorder='little', signed=False)
    if b[-1] < 0x80:
        b, d = b[:-1], b[-1]
    else:
        d = 0
    if neg:
        b += bytes([d+0x80])
    else:
        b += bytes([d])
    return b

def bytes_to_int(b):
    if b == b'':
        return 0
    i, m = 0, 1
    for v in b[:-1]:
        i += v*m
        m *= 256
    i += (b[-1] % 0x80)*m
    if b[-1] >= 0x80:
        i = -i
    return i

class Element:
    kind = None
    def __init__(self, val1, val2):
        assert self.kind is not None
        if hasattr(self, "refcnt"): return
        self.refcnt = 1
        self.val1 = val1
        self.val2 = val2
        ALLOCATOR.alloc(self.alloc_size(), self)

    def alloc_size(self):
        raise NotImplementedError

    def child_elements(self):
        raise NotImplementedError

    @staticmethod
    def deref_add_to_stack(stk, els):
        for el in els:
            assert el.refcnt > 0
            el.refcnt -= 1
            if el.refcnt <= 0:
                stk.append(el)
        return stk

    @classmethod
    def deref_stack(cls, stk):
        while stk:
            el = stk.pop()
            assert el.refcnt == 0
            cls.deref_add_to_stack(stk, el.child_elements())
            ALLOCATOR.free(el.alloc_size(), el)

    def deref(self):
        self.deref_stack(self.deref_add_to_stack([], [self]))

    def bumpref(self):
        assert self.refcnt > 0
        self.refcnt += 1
        return self

    def __repr__(self): return f"El<{self}>"
    def __str__(self): raise Exception(f"unimplemented {self.__class__}.__str__()")

    def is_atom(self):
        return self.kind == ATOM
    def is_nil(self):
        return self.kind == ATOM and self.val1 == 0
    def is_cons(self):
        return self.kind == CONS
    def is_error(self):
        return self.kind == ERROR
    def is_func(self):
        return self.kind == FUNC
    def is_symbol(self):
        return self.kind == SYMBOL
    def is_symdef(self):
        return self.kind == SYMDEF

    def PyList(self):
        e, l = self, []
        while e.is_cons():
            l.append(e.val1)
            e = e.val2
        if e.is_nil():
            return l
        return None

class Store(Element):
    def __init__(self, value):
        super().__init__(len(value), value)

    def alloc_size(self):
        return 24 + 16 + ((self.val1+15) // 16) * 16

    def child_elements(self):
        return []

class Pair(Element):
    def __init__(self, left, right):
        super().__init__(left, right)

    def alloc_size(self):
        return 24

    def child_elements(self):
        return [self.val1, self.val2]

    def steal_children(self):
        r = (self.val1.bumpref(), self.val2.bumpref())
        self.deref()
        return r

class Atom(Store):
    re_printable = re.compile(b"^[a-zA-Z0-9 _()<>,.\"*:'/%+-]+$")
    kind = ATOM

    nil = None
    one = None

    def __new__(cls, value):
        if isinstance(value, int):
            value = int_to_bytes(value)
        assert isinstance(value, bytes)
        is_nil = (value == b'')
        is_one = (value == b'\x01')
        if is_nil and cls.nil is not None:
            return cls.nil.bumpref()
        if is_one and cls.one is not None:
            return cls.one.bumpref()
        el = super().__new__(cls)
        if is_nil:
            cls.nil = el
        if is_one:
            cls.one = el
        return el

    def __init__(self, value):
        if isinstance(value, int):
            value = int_to_bytes(value)
        super().__init__(value)

    def __str__(self):
        if self.val1 == 0:
            return "nil"
        elif self.val1 < 3:
            return "%d" % self.as_int()
        else:
            if self.re_printable.match(self.val2):
                return '"%s"' % (self.val2.decode('utf8'),)
            else:
                return "0x%s" % (self.val2.hex(),)

    def as_int(self):
        return bytes_to_int(self.val2)

class Error(Store):
    kind = ERROR
    def __str__(self):
        return "ERR(%s)" % (self.val1)

class Symbol(Store):
    kind = SYMBOL
    def __str__(self):
        return "<%s>" % (self.val2)

class Cons(Pair):
    kind = CONS

    def __str__(self):
        x = []
        while self.val2.is_cons():
            x.append(self.val1)
            self = self.val2
        x.append(self.val1)
        if not self.val2.is_nil():
            x.append(".")
            x.append(self.val2)
        return "(%s)" % " ".join(map(str, x))

class Func(Pair):
    kind = FUNC
    def child_elements(self):
        return [self.val1]

    def __str__(self):
        return "FN(%s,%s)" % (self.val2.__class__.__name__, str(self.val1))

class SerDeser:
    MAX_QUICK_ONEBYTE = 51
    MAX_QUICK_MULTIBYTE = 64
    MAX_QUICK_LIST = 5

    # nil = 0
    # quick onebyte = 1..max_quick_onebyte
    # leftovers = max_quick_onebyte+1
    # quick multibyte = max_quick_onebyte+2..max_quick_onebyte+max_quick_multibyte
    # slow multibyte = max_quick_onebyte+max_quickmultibyte+1
    # quick proper list = mqob+mqmb+1..mqob+mqmb+mql
    # quick improper list = mqob+mqmb+mql+1..mqob+mqmb+2*mql

    QUICK_LEFTOVER = MAX_QUICK_ONEBYTE+1
    QUICK_MULTIBYTE_OFFSET = MAX_QUICK_ONEBYTE
    SLOW_MULTIBYTE = MAX_QUICK_ONEBYTE + MAX_QUICK_MULTIBYTE + 1
    QUICK_PROPER_OFFSET = SLOW_MULTIBYTE
    QUICK_IMPROPER_OFFSET = QUICK_PROPER_OFFSET + MAX_QUICK_LIST
    SLOW_LIST = 127

    assert QUICK_IMPROPER_OFFSET + MAX_QUICK_LIST + 1 == SLOW_LIST, f"{QUICK_IMPROPER_OFFSET} + {MAX_QUICK_LIST} + 1 != {SLOW_LIST}"

    def __init__(self):
        self.b = None
        self.i = None

    def _read(self, n):
        assert self.i + n <= len(self.b), f"{self.i} + {n} > {len(self.b)}"
        x = self.b[self.i:self.i+n]
        self.i += n
        return x

    def Deserialize(self, b):
        self.b, self.i = b, 0
        el = self._Deserialize()
        if self.i != len(self.b):
            raise Exception(f"incomplete deserialization {self.i} != {len(self.b)}")
        self.b = self.i = None
        return el

    def _Deserialize(self):
        code = self._read(1)[0]
        if code & 0x80:
            quoted = True
            code &= 0x7F
        else:
            quoted = False
        if code == 0:
            el = Atom(0)
        elif code <= self.MAX_QUICK_ONEBYTE:
            el = Atom(code)
        elif code == self.QUICK_LEFTOVER:
            code2 = self._read(1)[0]
            if code2 == 0 or code2 > self.MAX_QUICK_ONEBYTE:
                el = Atom(bytes([code2]))
            else:
                s = code2 + self.MAX_QUICK_MULTIBYTE
                el = Atom(self._read(s))
        elif code < self.SLOW_MULTIBYTE:
            s = code - self.QUICK_MULTIBYTE_OFFSET
            el = Atom(self._read(s))
        elif code == self.SLOW_MULTIBYTE:
            s = 0
            while (x := self._read(1)[0]) == 255:
                s += x
            s += x
            el = Atom(self._read(s))
        else:
            # cons!
            if code <= self.QUICK_IMPROPER_OFFSET:
                s = code - self.QUICK_PROPER_OFFSET
                closed = True
            elif code < self.SLOW_LIST:
                s = code - self.QUICK_IMPROPER_OFFSET
                closed = False
            else:
                code2 = self._read(1)[0]
                closed = (code2 & 0x80) == 0
                code2 = code2 & 0x7F
                s = self.MAX_QUICK_LIST + 1
                if code2 < 0x7F:
                    s += code2
                else:
                    s += 0x7F
                    while (x := self._read(1)[0]) == 255:
                        s += x
                    s += x
            ls = []
            for _ in range(s):
                e = self._Deserialize()
                ls.append(e)
            # naughty if not quoted and ls[0]=nil

            if closed:
                el = Atom(0)
            else:
                el = self._Deserialize()
                # naughty if el=nil
            for e in reversed(ls):
                el = Cons(e, el)
        if quoted:
            el = Cons(Atom(0), el)
        return el

    def Serialize(self, el):
        self.b = b''
        self._Serialize(el)
        r = self.b
        self.b = None
        return r

    def _Serialize(self, el):
        if el.kind == CONS and el.val1.is_nil():
            v = 0x80
            el = el.val2
        else:
            v = 0

        if el.kind == ATOM:
            k = el.atom_as_bytes()
            assert len(k) == el.val2
            if el.is_nil():
                self.b += bytes([v|0x00])
                return
            elif el.val2 == 1:
                if 1 <= k[0] <= self.MAX_QUICK_ONEBYTE:
                    self.b += bytes([v|k[0]])
                else:
                    self.b += bytes([v|(self.QUICK_LEFTOVER), k[0]])
                return
            elif el.val2 >= 2 and el.val2 <= self.MAX_QUICK_MULTIBYTE:
                self.b += bytes([v|(self.QUICK_MULTIBYTE_OFFSET+el.val2)])
                self.b += k
                return
            elif el.val2 <= self.MAX_QUICK_MULTIBYTE + self.MAX_QUICK_ONEBYTE:
                assert el.val2 > self.MAX_QUICK_MULTIBYTE
                self.b += bytes([v|(self.QUICK_LEFTOVER), el.val2 - self.MAX_QUICK_MULTIBYTE])
                self.b += k
                return
            else:
                l = el.val2 - self.MAX_QUICK_MULTIBYTE - 1
                assert l >= 0
                self.b += bytes([v|(self.SLOW_MULTIBYTE)])
                while l >= 255:
                    self.b += b'\ff'
                    l -= 255
                b.append(bytes([l]))
                self.b += bytes(b)
                self.b += k
                return
        elif el.kind == CONS:
            size = 1
            fin = el
            while True:
                if fin.val2.kind == ATOM: break
                if fin.val2.kind != CONS:
                    raise Exception("not serializable")
                size += 1
                fin = fin.val2
            closed = fin.val2.is_nil()
            if size <= self.MAX_QUICK_LIST:
                offset = self.QUICK_PROPER_OFFSET if closed else self.QUICK_IMPROPER_OFFSET
                self.b += bytes([v|(offset+size)])
            else:
                self.b += bytes([v|self.SLOW_LIST])
                size -= self.MAX_QUICK_LIST + 1
                closed_tag = 0x00 if closed else 0x80
                if size < 127:
                    self.b += bytes([closed_tag|size])
                else:
                    self.b += bytes([closed_tag|63])
                    size -= 127
                    while size >= 255:
                        self.b += bytes([255])
                        size -= 255
                    self.b += bytes([size])
            chk = el
            while True:
                if chk.kind == CONS:
                    self._Serialize(chk.val1)
                    chk = chk.val2
                else:
                    assert chk.kind == ATOM
                    if not closed:
                        self._Serialize(chk)
                    break
            return
        else:
            raise Exception("not serializable")
        assert False, "this line should be unreachable"

class SExpr:
    re_parse = re.compile("(?P<ws>\s+)|(?P<open>[(])|(?P<close>[)])|(?P<dot>[.])|(?P<tick>['])|(?P<atom>[^'()\s.]+)")
    re_int = re.compile("^-?\d+$")
    re_hex = re.compile("^0x[0-9a-fA-F]+$")
    re_quote = re.compile('^"[^"]*"$')
    re_sym = re.compile('^[a-zA-Z0-9_<>=~&|^+*/%-]+$')

    @staticmethod
    def list_to_element(l):
        if len(l) >= 3 and l[-2] is None:
            t = l[-1]
            l = l[:-2]
        else:
            t = Atom(0)
        assert None not in l
        for h in reversed(l):
            t = Cons(h, t)
        return t

    @classmethod
    def get_token(cls, s):
        m = cls.re_parse.match(s)
        if m is None:
            raise Exception("failed to parse at \"%s\"" % (s,))
        return s[m.end():], m

    @classmethod
    def parse(cls, s, many=False, manypy=False):
        where = 0
        end = len(s)
        parstack = [[]]

        if manypy: many = True

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
                is_sym = False
                if a == "nil":
                    a = 0
                elif cls.re_hex.match(a):
                    a = bytes.fromhex(a[2:])
                elif cls.re_int.match(a):
                    a = int(a, 10)
                elif cls.re_quote.match(a):
                    a = a[1:-1]
                elif cls.re_sym.match(a):
                    is_sym = True
                else:
                    raise Exception("unparsable/unknown atom %r" % (a,))
                if is_sym:
                    parstack[-1].append(Symbol(a))
                elif a == b'' or a == 0:
                    parstack[-1].append(Atom(0))
                else:
                    parstack[-1].append(Atom(a))
            else:
                raise Exception("BUG: unhandled match")

            while len(parstack[-1]) > 1 and parstack[-1][0] == "tick":
                assert len(parstack[-1]) == 2
                q = parstack.pop()
                parstack[-1].append(Cons(Symbol('q'), q[1]))

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
        elif manypy:
            return parstack[0]
        else:
            return cls.list_to_element(parstack[0])

nil = Atom(0)
one = Atom(1)
