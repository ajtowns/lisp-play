#!/usr/bin/env python3

import hashlib
import re
import sys
import time

import verystable.core.key
import verystable.core.messages
import verystable.core.script
import verystable.core.secp256k1

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
    # quick closed list = mqob+mqmb+1..mqob+mqmb+mql
    # quick open list = mqob+mqmb+mql+1..mqob+mqmb+2*mql

    QUICK_LEFTOVER = MAX_QUICK_ONEBYTE+1
    QUICK_MULTIBYTE_OFFSET = MAX_QUICK_ONEBYTE
    SLOW_MULTIBYTE = MAX_QUICK_ONEBYTE + MAX_QUICK_MULTIBYTE + 1
    QUICK_CLOSED_OFFSET = SLOW_MULTIBYTE
    QUICK_OPEN_OFFSET = QUICK_CLOSED_OFFSET + MAX_QUICK_LIST
    SLOW_LIST = 127

    assert QUICK_OPEN_OFFSET + MAX_QUICK_LIST + 1 == SLOW_LIST, f"{QUICK_OPEN_OFFSET} + {MAX_QUICK_LIST} + 1 != {SLOW_LIST}"

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
            if code <= self.QUICK_OPEN_OFFSET:
                s = code - self.QUICK_CLOSED_OFFSET
                closed = True
            elif code < self.SLOW_LIST:
                s = code - self.QUICK_OPEN_OFFSET
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
                offset = self.QUICK_CLOSED_OFFSET if closed else self.QUICK_OPEN_OFFSET
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

    def set_error_open_list(self, el, what="program"):
        el.set_error(f"{what} specified as open list (non-nil terminator)")

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
                self.set_error_open_list(el, "tree")
            return None
        else:
            sofar = r.left.el.bumpref()
            add = Element.Cons(Element.Atom(0), r.right.left.el.bumpref())
            later = r.right.right.el.bumpref()
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
                self.set_error_open_list(el)
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
                self.set_error_open_list(el)
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
    # ... really this should be (c head . tail) or (c h1 h2 h3 . tail)
    # ... because (a) you skip specifying nil, (b) adding a dot is nbd,
    # ... (c) it's more aligned with (q), (d) it's easier to code, (e)
    # ... it's slightly more efficient

    def resolve(self, el):
        assert el.kind == FUNC and el.val2 is self
        r = check_complete(el.val1, xATCO(xANY(), xATCO(xANY(), xANY())), "c")
        if r.want is not None:
            return r.want
        if r.err is not None:
            el.replace(REF, r.err)
            return None

        open_list = False
        if r.el.is_atom():
            open_list = not r.el.is_nil()
        elif r.right.el.is_atom():
            open_list = not r.right.el.is_nil()

        if open_list:
            self.set_error_open_list(el)
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

#  (0x22, "rd", op_list_read), # read bytes to Element
#  (0x23, "wr", op_list_write), # write Element as bytes

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

class SExpr:
    re_parse = re.compile("(?P<ws>\s+)|(?P<open>[(])|(?P<close>[)])|(?P<dot>[.])|(?P<tick>['])|(?P<atom>[^'()\s.]+)")
    re_int = re.compile("^-?\d+$")
    re_hex = re.compile("^0x[0-9a-fA-F]+$")
    re_quote = re.compile('^"[^"]*"$')
    re_sym = re.compile('^[a-zA-Z0-9_<>=~&|^+*/%-]+$')
    # re_sym doesn't match (< 1 2) and other mathsy ops

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
    def demacro_module(cls, e):
        symtable = {}
        l = e.cons_to_pylist()
        if l is None:
            return Element.Error(f"argument to module not a list")
        for e in l:
            dfn = e.cons_to_pylist()
            if not dfn or dfn[0].kind != SYMBOL or dfn[0].val1 != "define" or len(dfn) != 3:
                return Element.Error(f"invalid module entry {e}")
            name = dfn[1].cons_to_pylist()
            if not name or name[0].kind != SYMBOL:
                return Element.Error(f"invalid module entry {e}")
            if name[0].val1 in symtable:
                return Element.Error(f"duplicate symbol {name[0]}")
            if name[0].val1 in SExpr_FUNCS:
                return Element.Error(f"define {name[0]} duplicates opcode")
            args = []
            for a in name[1:]:
                if a.kind != SYMBOL:
                    return Element.Error(f"define arg name must be symbol, not {a}")
                if a.val1 in SExpr_FUNCS:
                    return Element.Error(f"argument {a} duplicates opcode")
                args.append(a.val1)
            symtable[name[0].val1] = (args, dfn[2])
        names = symtable.keys()
        if "main" not in names:
            return Element.Error("no main function in module")
        defs = list(symtable.keys())
        envpos = {a: b for a,b in zip(defs, Tree.get_values_pair(len(symtable), 1)[0])}
        defcons = Element.Atom(0)
        for d in reversed(defs):
            argpos = {a: b for a,b in zip(symtable[d][0], Tree.get_values_pair(1, len(symtable[d][0]))[1])}
            argpos.update(envpos)
            defcons = Element.Cons(
                cls.demacro(symtable[d][1], argpos),
                defcons)

        # (a (a <main>) (b ...) 1)
        return Element.Cons(Element.Atom(SExpr_FUNCS['a']),
               Element.Cons(
                   Element.Cons(Element.Atom(SExpr_FUNCS['q']),
                   Element.Cons(Element.Atom(SExpr_FUNCS['a']),
                   Element.Cons(Element.Atom(envpos["main"]),
                   Element.Atom(0)))),
               Element.Cons(
                   Element.Cons(Element.Atom(SExpr_FUNCS['b']),
                   Element.Cons(
                      Element.Cons(Element.Atom(SExpr_FUNCS['q']), defcons),
                   Element.Atom(0))),
               Element.Cons(Element.Atom(1),
               Element.Atom(0)))))

    @classmethod
    def demacro_c_list(cls, e, extrasyms=None):
        orig = e
        if e.kind == ATOM: return e
        # (x y z) -> (c x y z nil)
        els = []
        while e.kind == CONS:
            els.append( cls.demacro(e.val1, extrasyms, midlist=True) )
            e = e.val2
        if not e.is_nil():
            return Element.Error("arg list {orig} not nil terminated")
        cons = Element.Cons(e, Element.Atom(0))
        for e in reversed(els):
            cons = Element.Cons(e, cons)
        cons = Element.Cons(Element.Atom(SExpr_FUNCS['c']), cons)
        return cons

    @classmethod
    def demacro(cls, e, extrasyms=None, midlist=False):
        if e.kind == ATOM: return e
        if e.kind == CONS:
            if e.val1.kind == SYMBOL and not midlist:
                if e.val1.val1 == "module":
                    return cls.demacro_module(e.val2)
                if extrasyms and e.val1.val1 in extrasyms:
                    # (foo bar baz) -> (a ENV 2 (b bar baz))
                    return Element.Cons(Element.Atom(SExpr_FUNCS['a']),
                           Element.Cons(Element.Atom(extrasyms[e.val1.val1]),
                           Element.Cons(Element.Atom(2),
                           Element.Cons(
                               Element.Cons(Element.Atom(SExpr_FUNCS['b']),
                               Element.Cons(
                                 cls.demacro_c_list(e.val2, extrasyms),
                               Element.Atom(0))),
                           Element.Atom(0)))))
            l = cls.demacro(e.val1, extrasyms, midlist=False)
            r = cls.demacro(e.val2, extrasyms, midlist=True)
            return Element.Cons(l, r)
        if e.kind == SYMBOL:
            if e.val1 in SExpr_FUNCS:
                return Element.Atom(SExpr_FUNCS[e.val1])
            if extrasyms and e.val1 in extrasyms:
                return Element.Atom(extrasyms[e.val1])
            return Element.Error(f"undefined symbol {e.val1} {extrasyms}")
        return Element.error(f"unexpected element {e}")

    @classmethod
    def compile(cls, s):
        e = cls.parse(s, many=False)
        return cls.demacro(e)

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
                    parstack[-1].append(Element.Symbol(a))
                elif a == b'' or a == 0:
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
        if debug: print(f"r: {result}")
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
        if work.kind == SYMBOL:
            error = Element.Error(f"unresolved symbol {work}")
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
            assert isinstance(x, Element), f"non-none,non-element {x} {work.val2}"
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
        eser = SerDeser().Serialize(self.env)
        edeser = SerDeser().Deserialize(eser)
        print(f"ENVSER: {eser.hex()}")
        assert str(edeser) == str(self.env)

    def __call__(self, program, debug=None):
        if debug is None: debug = self.debug
        if debug: print("PROGRAM: %s" % (program,))
        p = SExpr.compile(program)
        pser = SerDeser().Serialize(p)
        pdeser = SerDeser().Deserialize(pser)
        print("PROGHEX: %s" % (pser.hex()))
        print("DESER: %s" % (pdeser))
        assert str(pdeser) == str(p)
        ALLOCATOR.max = 0
        ALLOCATOR.reset_work()
        init_x = ALLOCATOR.x
        before_x = set(ALLOCATOR.allocated)
        try:
            t = time.time()
            if self.lazy:
                r = lazy_eval(self.env, p, debug=debug)
            else:
                r = eager_eval(self.env, p, debug=debug)
            elapsed = time.time() - t
            print("MAX=%s WORK=%s ELAPSED=%.1f ; %s -> %s" % (ALLOCATOR.max, ALLOCATOR.effort, elapsed, program, r))
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

rep = Rep(SExpr.compile("((55 . 33) . (22 . 8))"))
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
rep("(c)")
rep("(c . 1)")
rep("(c nil)")
rep("(c 1)")
rep("(c 1 nil)")
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
rep("(~ '7)")
rep("(~)")
rep("(~ 0)")
rep("(~ '1 '3 '5)")

# factorial
# n=2, fn=3
# `if 2 (a 3 (- 2 '1) 3)
rep = Rep(SExpr.compile("(a (i 2 '(* 2 (a 3 (- 2 '1) 3)) ''1))"))
print("\nInefficient factorial -- Env: %s" % (rep.env))
rep("(a 1 '3 1)")
rep("(a 1 '10 1)")
rep("(a 1 '40 1)")
#rep("(a 1 '150 1)")
#rep("(a 1 (c '15000 1))")

# factorial but efficient
rep = Rep(SExpr.compile("(a (i 2 '(a 7 (c (- 2 '1) (* 5 2) 7)) '(c 5)))"))
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

rep = Rep(SExpr.compile("(a (i 7 '(c (c nil 6) (a 4 4 (* 6 5) (+ 5 '1) (- 7 '1))) '(c nil)))"))
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

rep = Rep(SExpr.compile("(a (i 2 '(a 15 (c (- 2 '1) 11 (+ 5 11) 15)) '(c 5)))"))
print("\nFibonacci 1 -- Env: %s" % (rep.env))
rep("(a 1 (c '300 '0 '1 1))")
rep("(a 1 (c '500 '0 '1 1))")

rep = Rep(SExpr.compile("(a (i 4 '(a 7 (- 4 '1) 5 (+ 6 5) 7) '(c 6)))"))
print("\nFibonacci 2 -- Env: %s" % (rep.env))
rep("(a 1 '300 '0 '1 1)")
rep("(a 1 '500 '0 '1 1)")

rep = Rep(SExpr.compile("0x0200000015a20d97f5a65e130e08f2b254f97f65b96173a7057aef0da203000000000000887e309c02ebdddbd0f3faff78f868d61b1c4cff2a25e5b3c9d90ff501818fa0e7965d508bdb051a40d8d8f7"))
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
rep = Rep(SExpr.compile("(a (i 14 '(a 8 8 12 (+ 10 '1) (- 14 '1) (cat 3 (a 12 10))) '3))"))
print("\nBIP342 calculated manually -- Env: %s" % (rep.env))
rep("(bip342_txmsg)")

# implement sighash_all, codesep_pos=-1, len(scriptPubKey) < 253
rep("(a '(sha256 4 4 '0x00 6 3) (sha256 '\"TapSighash\") (cat '0x00 (tx '0) (tx '1) (sha256 (a 1 1 '(cat (tx (c '11 1)) (tx (c '12 1))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '15 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(a '(cat (strlen 1) 1) (tx '(16 . 0))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '10 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(cat (tx (c '20 1)) (a '(cat (strlen 1) 1) (tx (c '21 1)))) '0 (tx '3) 'nil)) (i (tx '14) '0x03 '0x01) (substr (cat (tx '4) '0x00000000) 'nil '4) (i (tx '14) (sha256 (a '(cat (strlen 1) 1) (tx '14))) 'nil)) (cat (tx '6) '0x00 '0xffffffff))")

rep("(cat '0x1122 '0x3344)")

rep("(secp256k1_muladd)")
rep("(secp256k1_muladd '1)")
rep("(secp256k1_muladd '(1))")
rep("(secp256k1_muladd '1 '(1))")


# (defun bip340check (R s e P) `(secp256k1_muladd ('1 . ,R) (,e . ,P) (,s)))
# (defun mkR (sig) `(substr ,sig 0 '32))
# (defun mkS (sig) `(substr ,sig '32 '64))
# (defun taghash (tag) `(a '(cat 1 1) (sha256 ,tag))
# (defun mkE (R P m) `(sha256 (taghash "BIP0340/challenge") ,R ,P ,m)
# (defun mybip340x (R s P m)
#        `(bip340check ,R ,s (mkE ,R ,P ,m) ,P))
# (defun mybip340 (sig P m) `(mybip340x (mkR ,sig) (mkS ,sig) ,P ,m)

bip340check = "(secp256k1_muladd (c '1 4) (c 5 7) (c 6 nil))"
  # expects R s e P
mkE = "(sha256 (a '(cat 1 1) (sha256 '\"BIP0340/challenge\")) 4 6 3)"
  # expects R p m
mybip340x = "(a 5 8 12 (a 7 8 10 14) 10)"
  # expects R s P m bip340check mkE
mybip340 = "(a 7 (substr 8 0 '32) (substr 8 '32 '64) 12 10 14 5)"
  # expects sig P m bip340check mkE mybip340x
sexpr = "((%s . %s) . (%s . %s))" % (bip340check, mkE, mybip340x, mybip340)
print(f"env={sexpr}")
rep = Rep(SExpr.compile(sexpr))
  # usage: (a 7 SIG P M 4 6 5)

# P = F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9
# m = 0000000000000000000000000000000000000000000000000000000000000000
# sig = E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0

rep("1")
rep("(a 7 '0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0 '0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9 '0x0000000000000000000000000000000000000000000000000000000000000000 4 6 5)")


# control block =  c1e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1
# script = 20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68
# scriptPK = 5120 c142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6

taghash = "(a '(sha256 2 2 3) (sha256 2) 3)"
  # expects tag contents
tapleaf = "(a 3 '\"TapLeaf\" (cat 4 (strlen 6) 6))"
  # expects v script taghash
tapbranch =  "(a 3 '\"TapBranch\" (i (<s 4 6) (cat 4 6) (cat 6 4)))"
  # expects a b taghash
tappath = "(i 12 (a 5 (a 14 8 (substr 12 '0 '32) 10) (substr 12 '32) 10 14 3) (a 10 '\"TapTweak\" (cat 7 8)))"
  # expects leaf:8 path:12 taghash:10 tapbranch:14 tappath:5 P:7
taproot = "(secp256k1_muladd (a 9 (a 11 (& 16 '0xfe) 24 15) 12 15 13 9 10) (c '1 10) (c (& 16 '1) 14))"
  # expects v:16 script:24 path:12 ipk:10 spk:14 tappath:9 tapbranch:13 tapleaf:11 taghash:15

sexpr = "(((%s . %s) . %s) . (%s . %s))" % (taproot, taghash, tapleaf, tapbranch, tappath)
print(f"env={sexpr}")
rep = Rep(SExpr.compile(sexpr))
  # usage: (a 8 '(V . SCRIPT) PATH IPK SPK 7 5 6 12)

rep("(a 8 '(0xc1 . 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68) nil '0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 '0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6 7 5 6 12)")

rep("(a 8 '(0xc1 . 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68) nil '0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 '0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6 7 5 6 12)")

# same as above, but this time the witness data is in the environment,
# and the program is passed in

rep = Rep(SExpr.parse("0xc1 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68 nil 0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6", many=True))
rep("(a '(a 16 (c 17 25) 21 29 7 6 28 20 24) (b '(%s %s %s %s %s)) (b 1))" % (taproot, taghash, tapleaf, tapbranch, tappath))

rep = Rep(SExpr.parse("12"))
rep("(module (define (_x _a _b) (* _a _b)) (define (main _a) (+ (_x _a _a) '1)))")
#print(exp)

rep = Rep(SExpr.parse("19"))
rep("(module (define (factorial _n accum) (i _n (factorial (- _n '1) (* _n accum)) accum)) (define (main _x) (factorial _x '1)))")

# test: (secp_muladd ,tt (1 ,p) (,x ,spk))
# tt: (a '(sha256 1 1 ,p ,root) (sha256 '"TapTweak"))
# tl: (a '(sha256 1 1 ,v (strlen ,scr) ,scr) (sha256 '"TapLeaf"))



# levels:
#   bytes/hex
#   (c (q . 1) (q . 0xCAFEBABE) (q . "hello, world") (q . nil))
#   \' and aliases? (car,head = h, etc)
#   symbols; let/defun (compile to env access)
#   \` and \,  (qq and unquote in chialisp / macros)

# notation?
#   'foo  = (q . foo)
#   '(a b c) = (q a b c)
#   `(a ,b c) = (c (q . a) b (q . c) nil)
#
# would be nice to have a "compiler" that can deal with a symbol table
# (for named ops).
