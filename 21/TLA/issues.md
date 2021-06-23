Issues with TLA language:
* ugly Latex-based syntax of operators (backslashes, `----`, etc.)
* no control over symbol imports in `EXTENDS` => high chance of conflicts
* whitespace-based parsing of `\/` and `/\`
* unclear error messages
* complicated recursive definitions (CHOOSE, no mutual recursion, RECURSIVE)
* operator operand must be the first operand of higher recursive operator: this works:
```
RECURSIVE Apply(_, _)
Apply(op(_), s) == op(Head(s))
```
but this does not
```
Apply(s, op(_)) == op(Head(s))
```
