#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

from dataclasses import dataclass
from typing import Optional, Tuple, Any, Self

from element2 import Element, SExpr, nil, ATOM, CONS, ERROR, SYMBOL, FUNC
from opcodes import SExpr_FUNCS, Op_FUNCS, Operator

##########

# To do:
#
#  * funcv2.py
#  * drop lazy eval
#  * have FUNC's use their data element more often
#  * have them have a better repr()
#  * implement op_partial
#
#  * make def work at all
#  * separate symbols into  pre-defined, global, local
#  * make function calls work
#
#  * make bll evaluation work
#  * make compilation work
#  * make symbolic evaluation work when invoked with compiled code
#    (does the first argument to a contain symbols? symbolic, no env. else,
#     bll, potentially with env)
#
#  * add tx/utxo commands
#
#  * do stuff about costs?
#  * do stuff about ensuring refcounting is correct?
#
#  * add tui debugger (via "textual" module?)
#
# possibly:
#    def (factorial x (= acc 1))  (a (i x '(factorial (- x 1) (* acc x)) 'acc))
#    eval (factorial 7)

##########

# how does compilation work?
# i guess i want something that will interpret from just numbers?

#    def (foo a b c) (* (+ a b) (+ a c) 3)
#    ; (foo 1 2 3)

#    $foo = (* (+ 9 13) (+ 9 7) (nil . 3))    ## whatever values * and + are

#    def (bar a) (foo a (+ a 1) (+ a 2))
#    def (qux a) (+ a 2)

#    $bar = (a 8 2 (b 3 (+ 3 (q . 1)) (+ 3 (q . 2))))

#    (a (i X bar qux) 9)
#    (a (i X 12 6) (q . 9))

#    that's basically the "if" construction anyway? except with arguments

# if we did elements2.py, perhaps we could tag elements as to whether they
# reference a symbol/function/etc?, or are bll-compatible?
# if we did that, should continuations become elements? with a special type, or
# just semi-structured?

##########

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
        self.globals = {}
        self.locals = {}

    def lookup(self, sym):
        if sym in SExpr_FUNCS:
            op = Op_FUNCS[SExpr_FUNCS[sym]]
            return Element.Func(nil.bumpref(), op())

        # locals override globals, but do not override builtins
        if sym in self.locals: return self.locals[sym].bumpref()
        if sym in self.globals: return self.globals[sym].bumpref()

        return None

    def set_global(self, sym, value):
        assert isinstance(sym, str)

        if self.locals: raise Exception("trying to set global when locals are set")
        if sym in SExpr_FUNCS: return False

        self.globals[sym] = value
        return True

    def set_local(self, sym, value):
        assert isinstance(sym, str)

        if sym in SExpr_FUNCS: return False

        self.locals[sym] = value
        return True


#### evaluation model = workitem with continuations

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
        # rewriting
        # (eval x) -> *x
        # (q x y z) --> (x y z) done
        # (if a b c) --> (eval (i a (q . b) (q . c)))

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

    def default(self, line):
        if line.strip().startswith(";"):
            # comment
            return
        return super().default(line)

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
            print("Expected symbol name (plus parameters) and definition")
            for e in s: e.deref()
            return
        sym, val = s
        if sym.kind == SYMBOL:
            self.symbols.set_global(sym.val1, val.bumpref())
        elif sym.kind == CONS and sym.val1.kind == SYMBOL:
            self.symbols.set_global(sym.val1.val1, [sym.val2.bumpref(), val.bumpref()])
        else:
            print("Expected symbol name (plus parameters) and definition")
            for e in s: e.deref()
            return
        for e in s: e.deref()

if __name__ == "__main__":
    if os.isatty(sys.stdin.fileno()):
        repl = BTCLispRepl()
    else:
        repl = BTCLispRepl(prompt="")
    repl.cmdloop()

