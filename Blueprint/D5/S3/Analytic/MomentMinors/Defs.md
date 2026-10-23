# Probability laws and parameter intervals

## Abstract

Moment gaps and their second minors.

**Definition 1.1 (The first moment).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.mean`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean of a real law is the integral of the identity function.

**Definition 1.2 (The moment assumptions).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.Admissible`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An admissible law is a Borel probability measure concentrated on strictly positive real values, with integrable first moment. Every real power indexed by I is integrable. The logarithmic moment and the first logarithmic moment are integrable when I contains zero and one, respectively.

**Definition 1.3 (The normalized moment gap).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.lam`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.lam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s different from zero and one, lambda(s) is the difference between the power moment and the power of the mean, divided by s(s-1). At zero it is the logarithm of the mean minus the logarithmic moment. At one it is the first logarithmic moment minus the mean times its logarithm.

**Definition 1.4 (The second principal minor).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.xi`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.xi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value xi(s,t) is lambda(s)lambda(t) minus the square of lambda((s+t)/2).

**Definition 1.5 (The iterated second minor).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.phi`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value phi(s,t,u,v) is xi(s,t)xi(u,v) minus the square of the alternating difference xi((s+u)/2,(t+v)/2)-xi((s+v)/2,(t+u)/2).

**Definition 1.6 (Pairs with common displacement).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.sigma`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value sigma(a,x) is xi(x,x+a).

**Definition 1.7 (The displaced midpoint minor).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.theta`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value theta(a,x,y) is sigma(a,x)sigma(a,y) minus the square of sigma(a,(x+y)/2).

**Definition 1.8 (The eight-parameter inequality).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.claim1`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.claim1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every admissible law and every eight endpoint parameters in an interval, the product of the two phi values is at least the square of the alternating product of cross entries. Each cross entry is the alternating xi difference for the corresponding endpoint pairs. The exact source statement retains all eight independent parameters and their index order.

**Definition 1.9 (The displaced-parameter inequality).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.claim2`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.claim2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every admissible law, interval and common displacement a, the product theta(a,x,y)theta(a,z,v) is at least the square of theta(a,(x+z)/2,(y+v)/2)-theta(a,(x+v)/2,(y+z)/2). The four endpoints and their translates by a belong to the interval, which also contains every required midpoint.

**Definition 1.10 (Both inequalities).**

Lean statement: `D5/S3/Analytic/MomentMinors/Defs.claim`

*Formalization.* `D5/S3/Analytic/MomentMinors/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The combined claim is the conjunction of the eight-parameter inequality and the displaced-parameter inequality.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.Admissible`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.claim`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.claim1`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.claim2`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.lam`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.mean`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.phi`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.sigma`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.theta`
- Truth anchor: `D5/S3/Analytic/MomentMinors/Defs.xi`
