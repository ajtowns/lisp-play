

# bllsh - A bullish shell for a bitcoin lisp language

## bll - The Basic Bitcoin Lisp Language

To start: bll is the basic bitcoin lisp language. It has only two concepts: atoms
and pairs; atoms are byte-strings, and pairs are two elements, each of which may
be an atom or a pair. A list is either the zero-length byte string (aka nil),
or a pair, of which the second element is also a list.

Any atom or pair (expression) can be evaluated. The result of evaluation
an expression is:

 * if the expression is nil, the result is nil
 * if the expression is some other atom, the result is the value in the environment
   keyed upon the atom
 * if the expression is a pair, and its first element is nil, the result is
   the second element (this is called "quoting" the second element)
 * otherwise, the first element must be an atom that is the id of a valid opcode,
   and the second element must be a list. each element in that list is evaluated
   and the result of that evaluation is fed into the opcode as an argument, and
   the overall result is the result of that opcode.

## simbll - The Simple Symbolic Bitcoin Lisp Language

Writing code for bll is kind-of a pain; working with the environment
is annoying, and having to quote things by pairing them with nil to
get any literals is also annoying. To ameliorate this, we introduce a
second language that's designed to be easier to program in while also
being straightforward to translate to bll. We call this language simbll;
which is intended to be reminiscent of "simple" or "symbol", and is
pronounced like "cymbal".

Expressions in the language may be symbols, atoms or pairs; with atoms
being the same as in bll, symbols being alphanumeric strings, and pairs
consist of two sub-expressions, which can each be either symbols, atoms
or pairs. A list is either the empty atom, or a pair of which the second
sub-expression is a list.

As far as evaluating simbll expressions goes, the first major change in
comparsion to bll expressions is that the "environment" is replaced by
a symbol table.

What symbols are there?

 * There is a quoting symbol ("q").
 * There is a symbol for each bll opcode
 * There is an "if" symbol.
 * There will someday be quasiquote ("qq") and un-quasiquote ("uq") symbols.

 * Constant symbols can be defined, which map directly to a bll expression.
 * Parameterised symbols can be defined, which ???? (these are functions)


