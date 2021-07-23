Issues with TLA language:
* ugly Latex-based syntax of operators (backslashes, `----`, etc.)
* whitespace-based parsing of `\/` and `/\`
* unclear error messages e.g.
```
Apply(op(_, _), s, val) ==
  LET ApplyImpl[i \in Nat] == IF i == 0 THEN -1 ELSE i IN ApplyImpl(Len(s))
```
will abort with
```
Encountered "Beginning of definition" at line 22, column 34 and token "IF"
```
whereas the real error is usage of `()` instead of `[]`
* complicated recursive definitions (`CHOOSE`, no mutual recursion, `RECURSIVE`, no recursion in higher-order operators)
* no REPL for TLA (not TLC) except the clumsy `Print` hack
* TLC handles only a small subset of TLA e.g. the following do not work:
  * no `\EE`
  * only one `[]`
  * heterogeneous sets
  * unbounded `CHOOSE`
* TLC treats some TLA constructs differently from language spec e.g.
  * failing `CHOOSE` causes an error (instead of selecting random value, same true for `CASE`)
  * order of operands in `P /\ Q` is significant
* all definitions are exported by default which causes namespace pollution on import
* no way to limit imported symbols in `EXTENDS` or `INSTANCE`
