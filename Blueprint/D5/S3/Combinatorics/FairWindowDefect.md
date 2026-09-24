# A Lower Bound for Deterministic Fair-Input Window Rules

## Abstract

An odd-parity cycle forces a transport defect, while each proper context is fair.

**Definition 1.1 (A complete defect context).**

$$\forall R \in \mathrm{Nat},\; \forall f \in (Fin\left(2\right)^{Fin\left(R\right)}\to Fin\left(2\right)),\; \forall v \in Fin\left(2\right)^{Fin\left(R + 1\right)},\; defect\left(f, v\right) = 1_{sigma\left(f\left(tail\left(v\right)\right)\right) \ne sigma\left(last\left(v\right)\right) \cdot sigma\left(f\left(head\left(v\right)\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/FairWindowDefect.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let sigma send zero to minus one and one to one. A table f maps an R-bit word to one bit. For a context v indexed from zero through R, head(v) has coordinates v(i), tail(v) has coordinates v(i+1), and last(v) is v(R). The indicator is zero when the last relation bit transports the first output to the second, and one otherwise. Thus relation zero reverses the output and relation one preserves it.

**Definition 1.2 (The exact fair-input probability).**

$$\forall R \in \mathrm{Nat},\; \forall f \in (Fin\left(2\right)^{Fin\left(R\right)}\to Fin\left(2\right)),\; fairDefect\left(R, f\right) = \frac{\sum_{v\in Fin\left(2\right)^{Fin\left(R + 1\right)}}defect\left(f, v\right)}{2^{R + 1}}$$

*Formalization.* `D5/S3/Combinatorics/FairWindowDefect.fairDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All R+1 relation bits are independent and fair. Every complete context therefore has mass one over two to the power R+1. This finite average is the exact cylinder probability of a defect for the same fixed table at consecutive times.

**Definition 1.3 (The finite optimum).**

$$\forall R \in \mathrm{Nat},\; optimalFairDefect\left(R\right) = \min_{f\in(Fin\left(2\right)^{Fin\left(R\right)}\to Fin\left(2\right))}fairDefect\left(R, f\right)$$

*Formalization.* `D5/S3/Combinatorics/FairWindowDefect.optimalFairDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set T(R) of all maps from binary R-words to one bit is finite and nonempty. Its minimum defect is attained by a deterministic table.

**Theorem 1.4 (Every table obeys the lower bound).**

$$\forall R \in \mathrm{Nat},\; \left(\forall f \in (Fin\left(2\right)^{Fin\left(R\right)}\to Fin\left(2\right)),\; \frac{1}{R + 2} \le fairDefect\left(R, f\right)\right) \land \frac{1}{R + 2} \le optimalFairDefect\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FairWindowDefect.fair_window_defect_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take binary cycles of length R+2 with an odd number of zero relations. Deleting any coordinate, after any permutation of the coordinates, is a bijection onto all binary words of length R+1: the omitted bit is uniquely forced by parity: the product at the other positions is one or minus one, and exactly one bit makes the full product minus one. Permuting coordinates preserves the odd parity law by a bijection; in particular its cyclic rotations preserve it. Consequently every cyclic defect context, including one crossing the seam, has precisely the fair joint law. If all defects vanished, multiplying the transport equations around the cycle would make the nonzero product of output signs equal its negative. Each cycle therefore contributes at least one defect. Summing over cycles and positions gives (R+2) times the fair defect at least one. The statement also includes R equal to zero. It establishes the lower bound; an upper construction and its asymptotics are separate.

## References

- Truth anchor: `D5/S3/Combinatorics/FairWindowDefect.defect`
- Truth anchor: `D5/S3/Combinatorics/FairWindowDefect.fairDefect`
- Truth anchor: `D5/S3/Combinatorics/FairWindowDefect.fair_window_defect_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/FairWindowDefect.optimalFairDefect`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments](../Analytic/ReflectedSpectrum/ParityConditionedMoments.md)
