# Exponential derivative ratios

## Abstract

Signed derivatives of two exponential reciprocals and their consecutive ratios.

**Definition 1.1 (The first signed derivative family).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.F`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(i,t) is (-1)^i times the i-th derivative of 1/(exp(t)-1).

**Definition 1.2 (The second signed derivative family).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.G`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G(i,t) is (-1)^i times the i-th derivative of 1/(1-exp(-t)).

**Definition 1.3 (The first consecutive ratio).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.ratioF`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.ratioF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio is F(i+1,t)/F(i,t).

**Definition 1.4 (The second consecutive ratio).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.ratioG`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.ratioG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio is G(i+1,t)/G(i,t).

**Definition 1.5 (Complete monotonicity).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.CompletelyMonotoneOn`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.CompletelyMonotoneOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real function is smooth on the positive half-line and every signed iterated derivative (-1)^k h^(k)(t) is nonnegative there.

**Definition 1.6 (The assertion for all indices).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Defs.claim`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural index both consecutive ratios are completely monotone on the positive half-line.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.CompletelyMonotoneOn`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.F`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.G`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.claim`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.ratioF`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Defs.ratioG`
