#!/usr/bin/env python3

import abc
import functools

from dataclasses import dataclass, field
from typing import List, Optional

from element import Element, SExpr, Atom, Cons, Error, Func
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode

####

SpecialBLLOps = {
    'q': 0,
    'a': 1,
    'sf': 2,
    'partial': 3,
}

def OpAtom(opcode):
    if opcode in SpecialBLLOps:
        return Atom(SpecialBLLOps[opcode])
    elif opcode in SExpr_FUNCS:
        return Atom(SExpr_FUNCS[opcode])
    else:
        return None

def ResolveOpcode(opnum):
    if opnum == 0:
        return fn_quote()
    elif opnum == 1:
        return fn_apply()
    #elif opnum == 2:
    #    return fn_softfork()
    #elif opnum == 3:
    #    return fn_partial()
    else:
        op = Op_FUNCS.get(opnum, None)
        if op is None: return None
        return fn_op(op)

####

def ToBLL(sexpr):
    assert isinstance(sexpr, Element)
    if sexpr.is_bll() or sexpr.is_error():
        return sexpr.bumpref()

    if sexpr.is_symbol():
        a = OpAtom(sexpr.val2)
        if a is None:
            return Error(f"unknown symbol {sexpr.val2}")
        else:
            return a

    if sexpr.is_cons():
        v1 = ToBLL(sexpr.val1)
        if v1.is_error():
            return v1
        v2 = ToBLL(sexpr.val2)
        if v2.is_error():
            v1.deref()
            return v2
        return Cons(v1, v2)

    return Error("could not convert to bll")

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
        assert cont.args.is_error() or cont.args.is_bll(), f"{cont.args} not bll"
        if cont.args.is_error():
            cont.fn = fn_fin()
            return cont.fn.step(workitem)
        elif cont.args.is_atom():
            v = cont.args.as_int()
            if v >= 1:
                envarg = cont.ResolveEnv(v)
                cont.args.deref()
                cont.args = envarg
            cont.fn = fn_fin()
        elif cont.args.is_cons():
            op, cont.args = cont.args.steal_children()
            opcode = op.as_int() if op.is_atom() else None
            op.deref()
            opfn = ResolveOpcode(opcode)
            if opfn is None:
                workitem.error("invalid opcode")
            else:
                assert isinstance(opfn, Functor)
                cont.fn = opfn
        elif cont.args.is_func():
            # not sure?
            workitem.error("BUG? expression with raw function??")
        else:
            # internal error
            workitem.error("BUG? not sure what to eval")

class FunctorNormal(Functor):
    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            self.step_nil(workitem)
        elif cont.args.is_cons():
            w, cont.args = cont.args.steal_children()
            c = Continuation(fn=fn_eval(), args=w, env=cont.env.bumpref())
            workitem.continuations.append(c)
        else:
            workitem.error("argument to opcode is improper list")

    def step_nil(self, workitem):
        raise NotImplementedError

    def feedback(self, workitem, value):
        raise NotImplementedError

class fn_op(FunctorNormal):
    def __init__(self, opcls):
        self.op_func = Func(opcls, opcls.initial_int_state(), opcls.initial_state())

    def __repr__(self):
        return f"{self.op_func}"

    def deref(self):
        self.op_func.deref()

    def step_nil(self, workitem):
        cont = workitem.continuations[-1]
        assert cont.fn is self

        opcls, intst, st = self.op_func.cls_intst_st()
        f = opcls.finish(intst, st)

        c = Continuation(fn=fn_fin(), args=f, env=cont.env.bumpref())
        workitem.popcont()
        workitem.continuations.append(c)

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

        opcls, intst, st = self.op_func.cls_intst_st()
        (newst, newintst) = opcls.argument(intst, st, value)
        value.deref()
        if newst.is_error():
            workitem.error(nof.val2)
            nof.deref()
            return

        self.op_func.deref()
        self.op_func = Func(opcls, newintst, newst)

class fn_apply(FunctorNormal):
    def __init__(self):
        self.args = None
        self.env = None

    def __repr__(self):
        if self.args is None:
            return f"apply()"
        elif self.env is None:
            return f"apply({self.args})"
        else:
            return f"apply({self.args}; {self.env})"

    def deref(self):
        if self.args: self.args.deref()
        if self.env: self.env.deref()

    def step_nil(self, workitem):
        cont = workitem.continuations[-1]
        if self.args is None:
            workitem.error("too few args to apply")
            return
        env = cont.env if self.env is None else self.env
        c = Continuation(fn=fn_eval(), args=self.args.bumpref(), env=env.bumpref())
        workitem.popcont()
        workitem.continuations.append(c)

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

        if self.args is None:
            self.args = value
        elif self.env is None:
            self.env = value
        else:
            value.deref()
            workitem.error("too many args to apply")

@dataclass
class Continuation:
    fn: Functor
    args: Element           # (remaining) arguments to fn
    env: Element

    def ResolveEnv(self, idx):
        idxstart = idx
        env = self.env
        while idx > 1:
            if not env.is_cons():
                return Error(f"invalid env reference {idxstart} : {self.env}")
            if idx % 2 == 0:
                env = env.val1
            else:
                env = env.val2
            idx //= 2
        return env.bumpref()

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        self.fn.deref()
        self.args.deref()
        self.env.deref()

@dataclass
class WorkItem:
    continuations: List[Continuation]

    @classmethod
    def begin(cls, sexpr, env):
        wi = WorkItem(continuations=[
            Continuation(fn=fn_eval(), args=sexpr, env=env.bumpref())
        ])
        return wi

    def error(self, msg):
        c = Continuation(fn=fn_fin(), args=Error(msg), env=Atom(0))
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

    def step(self):
        cont = self.continuations[-1].fn.step(self)

def eval(sexpr, globalenv):
    wi = WorkItem.begin(sexpr, globalenv)

    while not wi.finished():
        wi.step()

    return wi.get_result()

