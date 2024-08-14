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
REF=252
FUNC=251
SYMBOL=250  # not needed post-macro evaluation

class Element:
    re_printable = re.compile(b"^[a-zA-Z0-9 _()<>,.\"*:'/%+-]+$")
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
        elif kind == SYMBOL:
            # no memory management of val1 is done
            assert isinstance(val1, str) and val2 is None
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
        elif self.kind == SYMBOL:
            pass
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
            assert isinstance(data, int) and data >= 0 and data <= 0xFFFF_FFFF_FFFF_FFFF
            assert data == 0 or length >= (data.bit_length() + 7) // 8
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

    def cons_to_pylist(self):
        l = []
        while self.kind == CONS:
            l.append(self.val1)
            self = self.val2
        if not self.is_nil(): return None
        return l

    @classmethod
    def Symbol(cls, sym):
        return cls(SYMBOL, sym)

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

    def is_symbol(self):
        return self.kind == SYMBOL

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
        if self.is_symbol():
            return "<%s>" % (self.val1)
        elif self.is_nil():
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
            el = Element.Atom(0)
        elif code <= self.MAX_QUICK_ONEBYTE:
            el = Element.Atom(code)
        elif code == self.QUICK_LEFTOVER:
            code2 = self._read(1)[0]
            if code2 == 0 or code2 > self.MAX_QUICK_ONEBYTE:
                el = Element.Atom(code2, 1)
            else:
                s = code2 + self.MAX_QUICK_MULTIBYTE
                el = Element.Atom(self._read(s))
        elif code < self.SLOW_MULTIBYTE:
            s = code - self.QUICK_MULTIBYTE_OFFSET
            el = Element.Atom(self._read(s))
        elif code == self.SLOW_MULTIBYTE:
            s = 0
            while (x := self._read(1)[0]) == 255:
                s += x
            s += x
            el = Element.Atom(self._read(s))
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
                el = Element.Atom(0)
            else:
                el = self._Deserialize()
                # naughty if el=nil
            for e in reversed(ls):
                el = Element.Cons(e, el)
        if quoted:
            el = Element.Cons(Element.Atom(0), el)
        return el

    def Serialize(self, el):
        self.b = b''
        self._Serialize(el)
        r = self.b
        self.b = None
        return r

    def _Serialize(self, el):
        while el.kind == REF: el = el.val1

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
                while fin.kind == REF:
                    fin = fin.val2
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
                while chk.kind == REF:
                    chk = chk.val2
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

nil = Element.Atom(0)
one = Element.Atom(1)
