#!/usr/bin/env python3

from __future__ import annotations

import abc
import functools

from dataclasses import dataclass, field
from typing import Type, List, Optional, Any

from element import Element, SExpr, Atom, Cons, Error, Func, FuncClass
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode

####

@FuncClass.implements_API
class fn_fin(FuncClass):
    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert state.is_nil()
        state.deref()
        env.deref()
        workitem.feedback(args)

@FuncClass.implements_API
class fn_quote(FuncClass):
    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert state.is_nil()
        state.deref()
        env.deref()
        workitem.feedback(args)

@FuncClass.implements_API
class fn_op():
    def __init__(self, opcls : Type[Opcode], opintstate):
        self.opcls = opcls
        self.opintstate = opintstate

    @classmethod
    def getname(cls, opclsistate):
        opcls, opintstate = opclsistate
        name = opcls.__name__
        if opintstate is not None:
            name += ",**"
        return name

    def __repr__(self):
        return self.opcls.__name__

    def step(self, state : Element, args : Element, env : Any, workitem : Any) -> None:
        if args.is_nil():
            f = self.opcls.finish(self.opintstate, state)  # XXX should consider state owned
            env.deref()
            Element.deref_all(state, args)
            workitem.fin_value(f)
        elif isinstance(args, Cons):
            arg, rest = args.steal_children()
            workitem.new_continuation(Func(self.__class__, (self.opcls, self.opintstate), state), rest, env)
            workitem.eval_arg(arg, env.bumpref())
        else:
            env.deref()
            Element.deref_all(state, args)
            workitem.error("argument to opcode is improper list")

    def feedback(self, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert not isinstance(value, Error)

        if not value.is_bll():
            workitem.error(f"cannot pass non-bll value {value} to opcode")
            env.deref()
            Element.deref_all(state, value, args)
            return

        (newst, newintst) = self.opcls.argument(self.opintstate, state, value) # XXX state/value owned
        Element.deref_all(state, value)

        if isinstance(newst, Error):
            workitem.fin_value(newst)
            env.deref()
            args.deref()
        else:
            workitem.new_continuation(Func(self.__class__, (self.opcls, newintst), newst), args, env)

