# Joint Reciprocal Scalar Coordinate

## Abstract

Scalar integral coordinates, their smooth positive derivative and endpoint surjectivity support the exact joint reciprocal variational construction.

**Definition 1.1 (The scalar denominator).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.polynomial`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For real b and v, polynomial(b,v) is 2*b+3*(1-b)*v-6*v^2.

**Definition 1.2 (The positive denominator root).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.upperRoot`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.upperRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For real b, upperRoot(b) is [3(1-b)+sqrt(9(1-b) squared+48b)]/12.

**Definition 1.3 (The negative root magnitude).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.lowerRoot`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.lowerRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For real b, lowerRoot(b) is [sqrt(9(1-b) squared+48b)-3(1-b)]/12.

**Definition 1.4 (The original integral coordinate).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For real b and v, coordinate(b,v) is the oriented Lebesgue integral from 0 to v of (2b+6s)/polynomial(b,s).

**Definition 1.5 (The left coordinate radius).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b, radius(b) is min(lowerRoot(b)/2,b/6). This is a neighborhood size for the scalar coordinate, not a hypothesis on a competitor.

**Definition 1.6 (The open coordinate domain).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinateDomain`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinateDomain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b, coordinateDomain(b) is the open real interval (-radius(b),upperRoot(b)).

**Theorem 1.7 (The two denominator roots).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.roots`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, upperRoot(b)>0 and lowerRoot(b)>0, their difference is (1-b)/2 and their product is b/3. The explicit quadratic formulas prove these identities and positivity. The constructed profile consumes these facts.

**Theorem 1.8 (A positive neighborhood radius).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, radius(b)>0. The inverse construction and root uniqueness consume this neighborhood estimate.

**Theorem 1.9 (Zero lies inside the domain).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, zero lies in coordinateDomain(b). This anchors the integral and the chosen inverse.

**Theorem 1.10 (Positive denominator and coordinate derivative).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1 and every real v in coordinateDomain(b), polynomial(b,v)>0, 2*b+6*v>0 and v+lowerRoot(b)>0. Factoring the quadratic and using the left radius proves these inequalities. The coordinate derivative and the explicit profile consume them.

**Theorem 1.11 (The coordinate derivative).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1 and every real v in coordinateDomain(b), coordinate(b) has derivative (2*b+6*v)/polynomial(b,v) at v. Continuity on the oriented integration interval supplies the fundamental theorem of calculus. The smooth inverse construction consumes this exact derivative.

**Theorem 1.12 (Smoothness of the coordinate).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1 and every real v in coordinateDomain(b), coordinate(b) is infinitely continuously differentiable at v. The rational integrand is smooth on this open domain and is the coordinate derivative. Smooth local inversion consumes this result.

**Theorem 1.13 (Strict monotonicity on the open domain).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, coordinate(b) is strictly increasing on coordinateDomain(b), since its derivative is positive there. Root uniqueness and inverse uniqueness consume this result.

**Theorem 1.14 (Every value above an attained coordinate is attained).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_surj_from`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_surj_from` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, all real a and t with a in coordinateDomain(b) and coordinate(b,a)<=t admit a real v in coordinateDomain(b) with coordinate(b,v)=t. A logarithmic antiderivative diverges to positive infinity at upperRoot(b); the intermediate value theorem on the connected domain gives the result. The unique scalar root and actual inverse curve consume this endpoint surjectivity.

## References

- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinateDomain`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_contDiff`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_strictMono`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_surj_from`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_positive`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_zero`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.lowerRoot`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.polynomial`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius_pos`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.roots`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.upperRoot`
