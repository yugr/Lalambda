Issues with TLA language:
* ugly Latex-based syntax of operators (backslashes, `----`, etc.)
* no control over symbol imports in `EXTENDS` => high chance of conflicts
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
* complicated recursive definitions (CHOOSE, no mutual recursion, RECURSIVE, no recursion in higher-order operators)
* no REPL
