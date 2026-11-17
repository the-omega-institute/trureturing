# The bounded quadratic generator and positive-operator Jensen supplier

## Abstract

The bounded quadratic generator and positive-operator Jensen supplier

The quadratic generator and its canonical optimality are known antecedents of the Hiai maximal-divergence theory. The source proves the finite matrix Jensen supplier from positive components; it does not count that antecedent as a newly solved conjecture.

**Definition 1.1 (starGenerator).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starGenerator`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

starGenerator u=(u-1)^2/(u+1) is the fixed reference generator. The compact coordinate turns its perspective into a polynomial on [0,1].

**Definition 1.2 (starPerspective).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starPerspective`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starPerspective` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

starPerspective p q=(p-q)^2/(p+q), with Lean real division giving zero at p=q=0. For nonnegative p,q this is the closed quadratic perspective including both axes.

**Theorem 1.3 (star perspective compact).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.star_perspective_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.star_perspective_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For 0<x<1, (1-x) starGenerator(x/(1-x))=(2x-1)^2. Quadratic preparation and trace estimates use the same compact-coordinate polynomial.

**Theorem 1.4 (square jensen).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For a finite family of PSD matrices E_i with sum 1 and arbitrary real r_i, (sum r_i E_i)^2 <= sum r_i^2 E_i in Loewner order. A sum of positive variance terms proves the inequality. compact_quadratic_jensen consumes it.

**Theorem 1.5 (square jensen subunital).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen_subunital`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen_subunital` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

The same square inequality holds when sum E_i<=1. Adding the positive remainder with coefficient zero reduces to the unital case. QuadraticBound uses the actual normalized preparation components.

**Theorem 1.6 (compact quadratic jensen).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_jensen`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_jensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD E_i summing to 1 and arbitrary real x_i, (2 sum x_i E_i-1)^2 <= sum (2x_i-1)^2 E_i. The trace bound consumes this compact-coordinate Jensen inequality.

**Theorem 1.7 (compact quadratic trace bound).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_trace_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD S and PSD E_i summing to 1, the trace of S times the square in compact_quadratic_jensen is at most sum (2x_i-1)^2 Re Tr(S E_i). No bounds on the real x_i or normalization of S are assumed. This supplies the canonical quadratic cost comparison.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_jensen`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.compact_quadratic_trace_bound`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.square_jensen_subunital`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starGenerator`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.starPerspective`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.star_perspective_compact`
