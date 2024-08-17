#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

from dataclasses import dataclass
from typing import Optional, Tuple, Any, Self

from element import Element, SExpr, nil, ATOM, CONS, ERROR, REF, SYMBOL, FUNC
from funcs import SExpr_FUNCS, Op_FUNCS, Operator

####

def handle_exc(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except Exception:
            traceback.print_exc()
    return wrapper

####

def list_takes_tail(head, tail):
     l = Element.Cons(head, tail)
     tail.deref()
     return l

def quote(value):
     return list_takes_tail(Element.Symbol('q'), value)

def steal_list(l):
    assert isinstance(l, Element) and l.is_cons()
    h, t = l.val1.bumpref(), l.val2.bumpref()
    l.deref()
    return h, t

####

class SymbolTable:
    def __init__(self):
        self.syms = []

    def lookup(self, sym):
        if sym in SExpr_FUNCS:
            op = Op_FUNCS[SExpr_FUNCS[sym]]
            return Element.Func(nil.bumpref(), op())

        for t in self.syms:
            if sym in t: return t[sym]

        return None

@dataclass
class Continuation:
    args: Element      # remaining arguments
    symbols: SymbolTable
    parent: Optional[Self]
    fn: Optional[Element] = None

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        if isinstance(self.fn, Element): self.fn.deref()
        if isinstance(self.args, Element): self.args.deref()

    def deref_all(self):
        c = self
        while c is not None:
            c.deref()
            c = c.parent

@dataclass
class WorkItem:
    value: Element
    symbols: SymbolTable
    continuation: Optional[Continuation]
    is_result: bool = False

    def feedback(self):
        if self.continuation is None:
            return self.value

        cont = self.continuation
        if cont.fn is None:
            cont.fn = self.value
        else:
            cont.fn.val2.argument(self.value)

        if cont.args.kind == CONS:
            self.value, cont.args = steal_list(cont.args)
            self.is_result = False
            return self

        assert cont.args.is_nil()

        if cont.fn is None:
            return Element.Error("function without operator??")
        fin = cont.fn.val2.finish()
        if isinstance(fin, Element):
            self.value = fin
            self.is_result = True
            self.symbols = cont.symbols
        else:
            env, fin = fin
            if env is None:
                self.value = fin
                self.is_result = False
                self.symbols = cont.symbols
            else:
                self.value = Element.Error("cannot specify environment with a in symbolic mode")
                fin.deref()
                self.is_result = True
                self.symbols = cont.symbols

        p = cont.parent
        self.continuation.deref()
        self.continuation = p
        return self

    def finished(self):
        if self.is_result and self.continuation is None:
            return True

    def step(self):
        if self.value.kind == SYMBOL and self.value.val1 == 'q' and self.continuation is not None and self.continuation.fn is None:
            self.value.deref()
            self.value = self.continuation.args
            self.is_result = True
            self.symbols = self.continuation.symbols
            self.continuation = self.continuation.parent
            return

        if self.value.kind == ERROR:
            if self.continuation is not None: self.continuation.deref_all()
            self.is_result = True
        elif self.value.kind == ATOM or self.value.kind == FUNC:
            self.is_result = True

        if self.is_result:
            self.feedback()
            return

        if self.value.kind == CONS:
             h, t = steal_list(self.value)
             newcon = Continuation(args=t, symbols=self.symbols, parent=self.continuation)
             self.continuation = newcon
             self.value = h
        elif self.value.kind == REF:
            x = self.value.val1.bumpref()
            self.value.deref()
            self.value = x
        elif self.value.kind == SYMBOL:
            x = self.value.val1
            y = self.symbols.lookup(x)
            self.value = y
            return
        else:
            raise Exception(f"unknwon element kind {self.value.kind}")

def symbolic_eval(sexpr, symbols):
    wi = WorkItem(value=sexpr.bumpref(), symbols=symbols, continuation=None)

    while not wi.finished():
        wi.step()

    return wi.value

class BTCLispRepl(cmd.Cmd):
    def __init__(self, prompt=None):
        self.prompt = ">>> " if prompt is None else prompt
        self.symbols = SymbolTable()
        self.wi = None

        cmd.Cmd.__init__(self)

    def show_state(self):
        if self.wi is None: return
        print(f" --- {self.wi.value}")
        c = self.wi.continuation
        while c is not None:
            print(f"   -- {c.fn}    {c.args}")
            c = c.parent

    def do_exit(self, arg):
        return True

    def do_EOF(self, arg):
        if self.prompt != "": print()
        return True

    @handle_exc
    def do_eval(self, arg):
        s = SExpr.parse(arg)
        r = symbolic_eval(s, self.symbols)
        print(r)
        r.deref()
        s.deref()

    @handle_exc
    def do_debug(self, arg):
        if self.wi is not None:
            print("Already debugging an expression")
            return
        sexpr = SExpr.parse(arg)
        self.wi = WorkItem(value=sexpr, symbols=self.symbols, continuation=None)
        self.show_state()

    @handle_exc
    def do_step(self, arg):
        if self.wi is None:
            print("No expression being debugged")
            return
        elif self.wi.finished():
            print(f"Result: {self.wi.value}")
            self.wi.value.deref()
            self.wi = None
            return

        self.wi.step()
        self.show_state()

    @handle_exc
    def do_cont(self, arg):
        if self.wi is None:
            print("No expression being debugged")
            return

        while not self.wi.finished():
            self.wi.step()

        print(f"Result: {self.wi.value}")
        self.wi.value.deref()
        self.wi = None
        return

    @handle_exc
    def do_def(self, arg):
        s = SExpr.parse(arg, manypy=True)
        if len(s) != 2:
            raise Exception("expected symbol name (plus parameters) and definition")
        print(s)

if __name__ == "__main__":
    if os.isatty(sys.stdin.fileno()):
        repl = BTCLispRepl()
    else:
        repl = BTCLispRepl(prompt="")
    repl.cmdloop()

