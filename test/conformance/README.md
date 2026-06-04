# R5RS Conformance Fixtures

`upstream/r5rs_pitfall.scm` is the SISC R5RS Pitfalls suite from:

https://sisc-scheme.org/r5rs_pitfall.scm

The upstream header states that the collected tests are placed in the
public domain.

The full upstream suite exercises subtle R5RS behavior, including
`syntax-rules`, quasiquote, characters, `display`, `equal?`, and other
features that `r5rs-denot` does not fully support yet. CI therefore runs
the supported fixtures in `pass/`. As the interpreter grows, move cases
from the upstream suite into runnable fixtures before gating on them.
