
# A lisp-y interpretor

## Design

### Element

 - Everything is an "Element".
 - Elements are either an atom (containing a byte vector, intepretable
   as an integer when desired), or a list containing a head and tail,
   both of which contain an Element.
 - The empty byte vector is also treated as 0 and the empty list (nil).
 - Allocation is tracked by reference counting.

### Allocator

 - Tracks the memory usage needed by Elements during program execution

### SExpr

 - Given a string defining a program, SExpr.parse() will turn it into
   a list.

### GenArgs, `op_*()`

 - Implement operators as python generators, that can progressively
   process their arguments. For example `(+ 1 2 3)` will be progressively
   executed by invoking `op_add` when the `+` is seen, then passing `1`
   in, at which point the generator's internal state will be updated
   to hold a sum of `1`, then when `2` is passed in the state will be
   updated to `3`, then when `3` is passed in the state will become `6`,
   and when the end of list is reached, the generator will complete,
   yielding a new element with value `6`.

### `get_env`

 - Following clvm's example, we treat the environment Element as a
   binary tree. When asked for element `1` we return the whole thing.
   When asked for element `2` we return the left sub tree, when asked
   for element `3` we return the right subtree. Every positive integer
   gives a unique subtree of the environment (provided there are enough
   elements).

### eval

 - Takes an environment and a program
 - Evaluates the program in the context of the environment
 - Lists are recursively evaluated, eg, `(* (+ 1 2) (+ 3 4))`
   is treated as `(* 3 7)`.
 - All state is stored in the `work` recursion stack, which
   stores the environment `env`, the opcode generator state `gen`,
   any remaining unprocessed args `args`, and a modal parameter
   `what` which controls the recursion (0 to back out, 1 to resolve
   an opcode, 2 to resolve an argument)

### Rep

 - Creates a read-eval-print object.

### Op codes

 - `(a LIST ENV)` - "apply" -- evaluate `LIST` with the environemnt `ENV`.
 - `(x ...)` - "exception" -- fail execution with an error message
 - `(i COND TRUE FALSE) - "if" -- if `COND` is not nil evaluates as `TRUE`;
   otherwise evaluates as `FALSE` if supplied, or `nil` otherwise.
 - `(f LIST)` - "first" -- returns the first element of `LIST`
 - `(r LIST)` - "rest" -- returns the tail of `LIST`
 - `(c EL1 EL2 .. TAIL)` - "concat" -- returns a LIST where the first
   elements are EL1, EL2, etc and the remainder is TAIL. Note that `(c T)`
   just returns `T`.
 - `(add N1 N2 ..)` -- adds numbers, returns 0 if no numbers
 - `(mul N1 N2 ..)` -- multiplies numbers, returns 1 if no numbers
 - `(sub K N1 N2...)` -- subtracts numbers from `K`, `K` must be provided
 - `(div K N1 N2...)` -- integer division of `K`, `K` must be provided

### Example

We can calculate a factorial recursively or iteratively. Recursively,
this looks like:

   `f(n) = n == 0 ? 0 : n * f(n-1)`

This is not amenable to tail recursion, so builds up a stack of n elements
(n, n-1, n-2, ..) then multiplies them together.

Iteratively, it looks like:

   `f(n, acc) = n == 0 ? acc : f(n-1, acc*n)`

This is amenable to tail recursion, so can be interpreted more efficiently.

We implement the plain recursive version as follows:

 * We setup the environment as `(n . f)` (`f` is the program, `n` is the
   number we're calculating the factorial of. This means we access `n` as
   `2` and `f` as `3`.

 * We do the condition as `(a (i 2 (...) (...))` evaluating the left branch
   when `n` is non-zero and the right branch when `n` is zero. This means
   we need to quote both branches to avoid eager evaluation.

 * The base case (right branch) we write as `(q . 1)` which just evaluates
   to `1`.

 * The recursive case (left branch) we write as `(q mul 2 ...)`, that is
   we will multiply `n` by a recursive formula. The recursive formula is
   `(a 3 (c (sub 2 (q . 1)) 3))` -- which is just running our program
   `f` in a new environment, where the left subtree (`n`) is replaced by
   `n-1`.

 * We then call this by invoking `(a 1 (c (q . 150) 1))`

The iterative/tail-recursive approach is implemented similarly:

 * We setup the environment as `(n acc . f)` so `n` is again accessed as
   `2`, `acc` is accessed as `5` and `f` is accessed as `7`.

 * We have the same condition, namely `(a (i 2 (...) (...))`.

 * The recursive step is now mostly a matter of updating the environment,
   which we do by constructing it as `(c (sub 2 (q . 1)) (mul 5 2) 7)`,
   then recursing `(q a 7 ...)`.

 * The base case now requires returning the accumulated value, so it
   becomes `(q c 5)`.

 * We then call this by invoking `(a 1 (c (q . 150) (q . 1) 1))`
