#!/usr/bin/env python3

from __future__ import annotations

import abc
import functools

from dataclasses import dataclass, field
from typing import List, Optional, Any

from element import Element, SExpr, Atom, Cons, Error, Func, FuncClass
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode

####

SpecialBLLOps = {
    'q': 0,
    'a': 1,
    'sf': 2,
    'partial': 3,
}

def OpAtom(opcode : str) -> Optional[Atom]:
    if opcode in SpecialBLLOps:
        return Atom(SpecialBLLOps[opcode])
    elif opcode in SExpr_FUNCS:
        return Atom(SExpr_FUNCS[opcode])
    else:
        return None

def ResolveOpcode(op : Element) -> Optional[Func]:
    if not isinstance(op, Atom):
        return None
    opnum = op.as_int()
    if opnum == 0:
        return Func(fn_quote, None, Atom(0))
    elif opnum == 1:
        return Func(fn_apply, None, Atom(0))
    #elif opnum == 2:
    #    return fn_softfork()
    #elif opnum == 3:
    #    return fn_partial()
    else:
        opcls = Op_FUNCS.get(opnum, None)
        if opcls is None: return None
        return Func(fn_op, (opcls, opcls.initial_int_state()), opcls.initial_state())

def ResolveEnv(baseenv : Element, idx : int) -> Element:
    idxstart = idx
    env = baseenv
    while idx > 1:
        if not isinstance(env, Cons):
            env.deref()
            return Error(f"invalid env reference {idxstart} : {baseenv}")
        left, right = env.steal_children()
        if idx % 2 == 0:
            env = left
            right.deref()
        else:
            env = right
            left.deref()
        idx //= 2
    return env

####

def ToBLL(sexpr : Element) -> Element:
    assert isinstance(sexpr, Element)
    if sexpr.is_bll() or isinstance(sexpr, Error):
        return sexpr.bumpref()

    if sexpr.is_symbol():
        a = OpAtom(sexpr.val2)
        if a is None:
            return Error(f"unknown symbol {sexpr.val2}")
        else:
            return a

    if isinstance(sexpr, Cons):
        v1 = ToBLL(sexpr.val1)
        if isinstance(v1, Error):
            return v1
        v2 = ToBLL(sexpr.val2)
        if isinstance(v2, Error):
            v1.deref()
            return v2
        return Cons(v1, v2)

    return Error("cannot convert to bll")

#### evaluation model = workitem with continuations

@FuncClass.implements_API
class fn_fin(FuncClass):
    @classmethod
    def step(cls, intstate : Any, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert intstate is None and state.is_nil()
        state.deref()
        env.deref()
        workitem.feedback(args)

@FuncClass.implements_API
class fn_quote(FuncClass):
    @classmethod
    def step(cls, intstate : Any, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert intstate is None and state.is_nil()
        state.deref()
        env.deref()
        if args.is_bll():
            workitem.feedback(args)
        else:
            args.deref()
            workitem.error("cannot quote non-bll expression")

@FuncClass.implements_API
class fn_blleval(FuncClass):
    @classmethod
    def step(cls, intstate : Any, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert intstate is None and state.is_nil()
        state.deref()

        if not isinstance(args, Error) and not args.is_bll():
            # XXX should handle partial funcs here i guess?
            workitem.error(f"tried to eval something weird {args}")
            args.deref()
            env.deref()
            return

        if isinstance(args, Error):
            env.deref()
            workitem.fin_value(args)
        elif isinstance(args, Atom):
            v = args.as_int()
            if v >= 1:
                envarg = ResolveEnv(env, v)
                args.deref()
            else:
                envarg = args
                env.deref()
            workitem.fin_value(envarg)
        elif isinstance(args, Cons):
            op, args = args.steal_children()
            opfunc = ResolveOpcode(op)
            op.deref()
            if opfunc is None:
                args.deref()
                env.deref()
                workitem.error("invalid opcode")
            else:
                workitem.new_continuation(opfunc, args, env)
        else:
            # internal error
            args.deref()
            env.deref()
            workitem.error("BUG? should be unreachable")

@FuncClass.implements_API
class fn_op(FuncClass):
    @classmethod
    def step(cls, intstate : Any, state : Element, args : Element, env : Any, workitem : Any) -> None:
        opcls, opintstate = intstate
        if args.is_nil():
            args.deref()
            env.deref()
            f = opcls.finish(opintstate, state)  # XXX should consider state owned
            state.deref()
            workitem.fin_value(f)
        elif isinstance(args, Cons):
            arg, rest = args.steal_children()
            workitem.new_continuation(Func(cls, intstate, state), rest, env)
            workitem.eval_arg(arg, env.bumpref())
        else:
            state.deref()
            args.deref()
            env.deref()
            workitem.error("argument to opcode is improper list")

    @classmethod
    def feedback(cls, intstate : Any, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert not isinstance(value, Error)

        if not value.is_bll():
            workitem.error(f"cannot pass non-bll value {value} to opcode")
            state.deref()
            value.deref()
            args.deref()
            env.deref()
            return

        opcls, opintst = intstate
        (newst, newintst) = opcls.argument(opintst, state, value) # XXX state/value owned
        state.deref()
        value.deref()

        if isinstance(newst, Error):
            workitem.fin_value(newst)
            args.deref()
            env.deref()
        else:
            workitem.new_continuation(Func(cls, (opcls, newintst), newst), args, env)

@FuncClass.implements_API
class fn_apply(FuncClass):
    # state structure:
    #   0 args: nil
    #   1 arg: Cons( nil, APPLY )
    #   2 args: Cons( 1, Cons( ENV, APPLY ) )

    @classmethod
    def step(cls, intstate : Any, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert intstate is None
        if args.is_nil():
            args.deref()
            if not isinstance(state, Cons):
                assert state.is_nil()
                apply_expr = state
                apply_env = env
            else:
                i, info = state.steal_children()
                if i.is_nil():
                    i.deref()
                    apply_expr = info
                    apply_env = env
                else:
                    assert isinstance(info, Cons)
                    assert i.is_atom() and i.val2 == b'\x01'
                    i.deref()
                    env.deref()
                    apply_env, apply_expr = info.steal_children()
            workitem.eval_arg(apply_expr, apply_env)
        elif isinstance(args, Cons):
            arg, rest = args.steal_children()
            workitem.new_continuation(Func(cls, intstate, state), rest, env)
            workitem.eval_arg(arg, env.bumpref())
        else:
            workitem.error("argument to opcode is improper list")

    @classmethod
    def feedback(cls, intstate : Any, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert intstate is None
        assert not isinstance(value, Error)

        if not value.is_bll():
            workitem.error(f"cannot pass non-bll value {value} to apply")
            state.deref()
            value.deref()
            return

        if not isinstance(state, Cons):
            assert state.is_nil()
            newst = Cons(state, value)
        else:
            left, apply_el = state.steal_children()
            if left.is_nil():
                left.deref()
                newst = Cons(Atom(1), Cons(value, apply_el))
            else:
                left.deref()
                apply_el.deref()
                value.deref()
                args.deref()
                env.deref()
                workitem.error("too many args to apply")
                return

        workitem.new_continuation(Func(cls, intstate, newst), args, env)

@dataclass
class Continuation:
    fn: Func
    args: Element           # (remaining) arguments to fn
    env: Element

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
    def begin(cls, sexpr : Element, env : Element) -> WorkItem:
        wi = WorkItem(continuations=[])
        wi.eval_arg(sexpr, env)
        return wi

    def new_continuation(self, fn : Func, args : Element, env : Element) -> None:
        self.continuations.append(Continuation(fn, args, env))

    def fin_value(self, value : Element) -> None:
        self.new_continuation(Func(fn_fin, None, Atom(0)), value, Atom(0))

    def eval_arg(self, args : Element, env : Element) -> None:
        self.new_continuation(Func(fn_blleval, None, Atom(0)), args, env)

    def error(self, msg : str) -> None:
        self.fin_value(Error(msg))

    def feedback(self, value : Element) -> None:
        if isinstance(value, Error):
            for c in self.continuations:
                c.deref()
            self.continuations = []

        if self.continuations:
            c = self.continuations.pop()
            fncls, intstate, state = c.fn.steal_cls_istate_state()
            fncls.feedback(intstate, state, value, c.args, c.env, self)
        else:
            self.fin_value(value)

    def finished(self) -> bool:
        return len(self.continuations) == 1 and self.continuations[0].fn.val1[0] == fn_fin

    def get_result(self) -> Element:
        assert self.finished()
        r = self.continuations[0].args.bumpref()
        self.continuations.pop().deref()
        return r

    def step(self) -> None:
        cont = self.continuations.pop()
        fncls, intstate, state = cont.fn.steal_cls_istate_state()
        fncls.step(intstate, state, cont.args, cont.env, self)

def eval(sexpr : Element, globalenv : Element) -> Element:
    wi = WorkItem.begin(sexpr, globalenv)

    while not wi.finished():
        wi.step()

    return wi.get_result()

