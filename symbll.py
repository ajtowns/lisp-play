#!/usr/bin/env python3

import functools

from dataclasses import dataclass, field
from typing import List

from element2 import Element, SExpr, Atom, Cons, Error, Func
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode

####

class SymbolTable:
    def __init__(self):
        self.refcnt = 1
        self.syms = {}

    def set(self, symname, value):
        # XXX: cope with parameters (and default values for parameters)
        assert isinstance(symname, str)
        if not isinstance(value, Element):
            assert isinstance(value, tuple) and len(value) == 2
            assert all(isinstance(v, Element) for v in value)

        if symname in self.syms:
            if isinstance(self.syms[symname], tuple):
                map(e.deref(), self.syms[symname])
            else:
                self.syms[symname].deref()
        self.syms[symname] = value

    def unset(self, symname):
        assert isinstance(symname, str), f"{repr(symname)} not a str?"
        if symname in self.syms:
            self.syms[symname].deref()
            del self.syms[symname]

    def bumpref(self):
        self.refcnt += 1
        return self

    def deref(self):
        self.refcnt -= 1
        if self.refcnt == 0:
            for _, v in self.syms.items():
                v.deref()
            self.syms = None

def ResolveSymbol(localsyms, globalsyms, symname):
    assert isinstance(symname, str)

    if symname == "if":
        return fn_if()

    if symname == "q":
        return fn_quote()

    if symname in SExpr_FUNCS:
        op = Op_FUNCS[SExpr_FUNCS[symname]]
        return fn_op(Func(op.initial_state(), op()))

    # locals override globals, but do not override builtins
    r = localsyms.syms.get(symname, None)
    if r is None:
        r = globalsyms.syms.get(symname, None)
    if r is None:
        return None

    if isinstance(r, Element):
        return r.bumpref()
    else:
        return fn_userfunc(r[0].bumpref(), r[1].bumpref())

    return None

#### evaluation model = workitem with continuations

class Functor:
    def step(self, workitem): raise NotImplementedError
    def feedback(self, workitem, value):
        # defaults to a no-op, discarding the passed in value
        value.deref()

    def deref(self):
        pass # deref any internal state

    def __repr__(self):
        return self.__class__.__name__

class fn_fin(Functor):
    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        if len(workitem.continuations) == 1:
            return
        cont = workitem.continuations[-1]
        if cont.args.is_error():
            workitem.continuations.pop()
            while workitem.continuations:
                workitem.popcont()
            workitem.continuations.append(cont)
            return
        v = cont.args.bumpref()
        workitem.popcont()
        pcont = workitem.continuations[-1]
        pcont.fn.feedback(workitem, v)

class fn_quote(Functor):
    def step(self, workitem):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self
        assert isinstance(cont.args, Element)
        if cont.args.is_bll():
            cont.fn = fn_fin()
            return cont.fn.step(workitem)
        else:
            workitem.error("cannot quote non-bll expression")

class fn_eval(Functor):
    def step(self, workitem):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self
        assert isinstance(cont.args, Element)
        if cont.args.is_atom() or cont.args.is_error():
            cont.fn = fn_fin()
            return cont.fn.step(workitem)
        elif cont.args.is_cons():
            op, cont.args = cont.args.steal_children()
            if op.is_symbol():
                r = ResolveSymbol(cont.localsyms, workitem.globalsyms, op.val2)
                op.deref()
                if r is None:
                    workitem.error("undefined symbol")
                    return
                if isinstance(r, Functor):
                     cont.fn = r
                     return
                else:
                     r.deref()
                     return
            op.deref()
            workitem.error("expression does not have a function/operator")
        elif cont.args.is_func():
            # not sure?
            workitem.error("BUG? expression with raw function??")
        elif cont.args.is_symbol():
            r = ResolveSymbol(cont.localsyms, workitem.globalsyms, cont.args.val2)
            if r is None:
                workitem.error("undefined symbol")
                return
            elif isinstance(r, Element):
                cont.fn = fn_fin()
                cont.args.deref()
                cont.args = r
            elif isinstance(r, Functor):
                workitem.error("opcode must be called")
                r.deref()
            else:
                workitem.error(f"BUG? symbol {cont.args}={r} isn't a functor or element")
        else:
            # internal error
            workitem.error("BUG? not sure what to eval")

class fn_op(Functor):
    @staticmethod
    def _get_type(obj):
        return obj if isinstance(obj, type) else type(obj)

    def __init__(self, opcode):
        assert isinstance(opcode, Element) and opcode.is_func()
        self.op_func = opcode

    def __repr__(self):
        return f"{self.op_func}"

    def deref(self):
        self.op_func.deref()

    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            f = self.op_func.val2.finish(self.op_func.val1)
            c = Continuation(fn=fn_fin(), args=f, localsyms=cont.localsyms.bumpref())
            workitem.popcont()
            workitem.continuations.append(c)
        elif cont.args.is_cons():
            w, cont.args = cont.args.steal_children()
            c = Continuation(fn=fn_eval(), args=w, localsyms=cont.localsyms.bumpref())
            workitem.continuations.append(c)
        else:
            workitem.error("argument to opcode is improper list")

    def feedback(self, workitem, value):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        assert isinstance(value, Element)

        if value.is_error():
            cont = workitem.continuations[-1]
            cont.args.deref()
            cont.fn = fn_fin()
            cont.args = value
            return
        if not value.is_bll():
            workitem.error("cannot pass non-bll value to opcode")

        nof = self.op_func.val2.argument(self.op_func.val1, value)
        value.deref()
        assert isinstance(nof, Element) and nof.is_func()
        assert issubclass(self._get_type(nof.val2), Opcode)
        self.op_func.deref()
        self.op_func = nof

class fn_if(Functor):
    def step(self, workitem):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self

        if not cont.args.is_cons():
            workitem.error("if requires at least one argument")
            return

        cond, cont.args = cont.args.steal_children()
        c = Continuation(fn=fn_eval(), args=cond, localsyms=cont.localsyms.bumpref())
        workitem.continuations.append(c)

    def feedback(self, workitem, value):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self

        if cont.args.is_cons():
            iftrue, cont.args = cont.args.steal_children()
        elif cont.args.is_nil():
            iftrue = Atom(1)

        if cont.args.is_cons():
            iffalse, cont.args = cont.args.steal_children()
        elif cont.args.is_nil():
            iffalse = Atom(0)

        if not cont.args.is_nil():
            iftrue.deref()
            iffalse.deref()
            value.deref()
            if cont.args.is_cons():
                worktree.error("if must have at most three arguments")
            else:
                worktree.error("argument to if are improper list")
            return

        if value.is_nil():
            iftrue.deref()
            c = Continuation(fn=fn_eval(), args=iffalse, localsyms=cont.localsyms.bumpref())
        else:
            iffalse.deref()
            c = Continuation(fn=fn_eval(), args=iftrue, localsyms=cont.localsyms.bumpref())
        workitem.popcont()
        workitem.continuations.append(c)
        value.deref()

class fn_userfunc(Functor):
    def __init__(self, params, expr):
        self.params = params
        self.expr = expr
        self.syms = SymbolTable()

    def __repr__(self):
        return f"{self.params}->{self.expr}"

    def deref(self):
        self.params.deref()
        self.expr.deref()
        self.syms.deref()

    def step(self, workitem):
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            if self.params.is_nil():
                # done!
                c = Continuation(fn=fn_eval(), args=self.expr.bumpref(), localsyms=self.syms.bumpref())
                workitem.popcont()
                workitem.continuations.append(c)
                return
            #elif self.params.is_cons() and self.params.val1.is_cons():
            #   XXX fill in default arguments
            else:
                workitem.error("insufficient arguments for user defined function")
                return
        elif cont.args.is_cons():
            if self.params.is_nil():
                workitem.error("too many arguments for user defined functions")
                return
            elif self.params.is_cons() and self.params.val1.is_symbol():
                param, cont.args = cont.args.steal_children()
                c = Continuation(fn=fn_eval(), args=param, localsyms=cont.localsyms.bumpref())
                workitem.continuations.append(c)
                return
            else:
                workitem.error("user defined function has non-symbol as param name?")
                return
        else:
            workitem.error("call to user defined function is not proper list")
            return

    def feedback(self, workitem, value):
        cont = workitem.continuations[-1]
        assert cont.fn is self
        assert self.params.is_cons() and self.params.val1.is_symbol()
        param, self.params = self.params.steal_children()
        self.syms.set(param.val2, value)
        param.deref()

@dataclass
class Continuation:
    fn: Functor
    args: Element           # (remaining) arguments to fn
    localsyms: SymbolTable

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        self.fn.deref()
        self.args.deref()
        self.localsyms.deref()

@dataclass
class WorkItem:
    globalsyms: SymbolTable
    continuations: List[Continuation]
    dummylocalsyms: SymbolTable = field(default_factory=SymbolTable)

    @classmethod
    def begin(cls, sexpr, syms):
        wi = WorkItem(globalsyms=syms, continuations=[])
        c = Continuation(fn=fn_eval(), args=sexpr, localsyms=wi.dummylocalsyms.bumpref())
        wi.continuations.append(c)
        return wi

    def error(self, msg):
        c = Continuation(fn=fn_fin(), args=Error(msg), localsyms=self.dummylocalsyms.bumpref())
        self.popcont()
        self.continuations.append(c)

    def popcont(self):
        last = self.continuations.pop()
        last.deref()

    def finished(self):
        return isinstance(self.continuations[0].fn, fn_fin)

    def get_result(self):
        assert self.finished()
        r = self.continuations[0].args.bumpref()
        self.popcont()
        return r

    def localsyms(self):
        if self.continuations:
            return self.continuations[-1].localsyms
        else:
            return self.dummylocalsyms

    def step(self):
        cont = self.continuations[-1].fn.step(self)

def symbolic_eval(sexpr, globalsyms):
    wi = WorkItem.begin(sexpr, globalsyms)

    while not wi.finished():
        wi.step()

    return wi.get_result()

SpecialBLLOps = {
    'q': 0,
    'a': 1,
    'sf': 2,
    'partial': 3,
}

def OpAtom(opcode):
    if opcode in SpecialBLLOps:
        return Atom(SpecialBLLOps[opcode])
    else:
        return Atom(SExpr_FUNCS[opcode])

class SymbolIndexes:
    def __init__(self, vals, offset=1):
        if isinstance(vals, SymbolTable):
            vals = vals.syms.keys()

        x = []
        for v in vals:
            self.add(x, v)

        m,a = 1,offset
        while offset > 1:
            m *= 2
            offset //= 2
        a -= m

        self.indexes = {n: (v*m+a) for (n, v) in self.finish(x)}

    def __getitem__(n):
        return self.indexes.get(n, None)

    @staticmethod
    def add(sofar, symname):
        sofar.append( (1, [(symname, 1)]) )

        while len(sofar) > 1 and sofar[-1][0] == sofar[-2][0]:
            cntb, b = sofar.pop()
            cnta, a = sofar.pop()
            c = [(n, v*2) for n,v in a] + [(n, v*2+1) for n,v in b]
            sofar.append( (cnta + cntb, c) )

    @staticmethod
    def finish(sofar):
        if len(sofar) == 0: return []
        res = sofar.pop()[1]
        while sofar:
            _, a = sofar.pop()
            res = [(n, v*2) for n,v in a] + [(n, v*2+1) for n,v in res]
        return res

def compile_expr(sexpr, globalsyms, localsyms):
    assert isinstance(sexpr, Element)
    assert isinstance(globalsyms, SymbolIndexes)
    assert isinstance(localsyms, SymbolIndexes)

    assert not sexpr.is_func() and not sexpr.is_error()

    if sexpr.is_nil():
        return sexpr.bumpref()
    elif sexpr.is_atom():
        return Cons(Atom(0), sexpr.bumpref())
    elif sexpr.is_symbol():
        raise NotImplementedError
    else:
        assert sexpr.is_cons()
        assert sexpr.val1.is_symbol()
        symname = sexpr.val1.val2
        if symname == 'q':
            assert sexpr.val2.is_bll()
            return Cons(Atom(0), sexpr.val2.bumpref())
        elif symname == 'if':
            assert sexpr.val2.is_cons()
            cond_expr = compile_expr(sexpr.val2.val1, globalsyms, localsyms)
            if not sexpr.val2.val2.is_cons():
                assert sexpr.val2.val2.is_nil()
                return SExpr.list_to_element([OpAtom("i"), cond_expr])
            elif not sexpr.val2.val2.val2.is_cons():
                assert sexpr.val2.val2.val2.is_nil()
                then_expr = compile_expr(sexpr.val2.val2.val1, globalsyms, localsyms)
                i_expr = SExpr.list_to_element([OpAtom("i"), cond_expr, then_expr])
                return SExpr.list_to_element([OpAtom("a"), i_expr])
            elif not sexpr.val2.val2.val2.val2.is_cons():
                assert sexpr.val2.val2.val2.val2.is_nil()
                then_expr = compile_expr(sexpr.val2.val2.val1, globalsyms, localsyms)
                else_expr = compile_expr(sexpr.val2.val2.val2.val1, globalsyms, localsyms)
                i_expr = SExpr.list_to_element([OpAtom("i"), cond_expr, then_expr, else_expr])
                return SExpr.list_to_element([OpAtom("a"), i_expr])
            else:
                raise Exception("invalid if expression")
        elif symname in SExpr_FUNCS:
            l = [OpAtom(symname)]
            args = sexpr.val2
            while args.is_cons():
                l.append(compile_expr(args.val1, globalsyms, localsyms))
                args = args.val2
            l = SExpr.list_to_element(l)
            if not args.is_nil():
                l.deref()
                raise Exception("opcode call via improper list")
            return l
        else:
            raise NotImplementedError
