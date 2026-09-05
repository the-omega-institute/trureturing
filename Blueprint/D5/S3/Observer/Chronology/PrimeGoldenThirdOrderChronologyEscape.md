# Prime-Golden Third-Order Chronology Escape

## Abstract

Two prime-golden words can share bidegree, complete scalar trajectory, and the full step-two signature while a cubic ordered moment separates their chronology.

**Theorem 1.1 (A cubic ordered moment escapes a nontrivial step-two fiber).**

$$\begin{gathered}\forall f, \forall u, \forall w,\\{}\operatorname{f}(u) \cdot \operatorname{f}(w) \cdot \operatorname{f}(w) + 2 \cdot (\operatorname{f}(u) \cdot \operatorname{f}(w) \cdot \operatorname{f}(u)) + \operatorname{f}(w) \cdot \operatorname{f}(w) \cdot \operatorname{f}(u) \neq \operatorname{f}(w) \cdot \operatorname{f}(u) \cdot \operatorname{f}(u) + 2 \cdot (\operatorname{f}(w) \cdot \operatorname{f}(u) \cdot \operatorname{f}(w)) + \operatorname{f}(u) \cdot \operatorname{f}(u) \cdot \operatorname{f}(w) \Rightarrow\\{}\operatorname{primeGoldenBidegree}([u, w, w, u]) = \operatorname{primeGoldenBidegree}([w, u, u, w]) \land \operatorname{sameScalarTrajectory}([u, w, w, u], [w, u, u, w]) \land\\{}\operatorname{chronologicalSignature}(f, [u, w, w, u]) = \operatorname{chronologicalSignature}(f, [w, u, u, w]) \land\\{}\operatorname{thirdOrderReadout}(f, [u, w, w, u]) \neq \operatorname{thirdOrderReadout}(f, [w, u, u, w]).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape.prime_golden_third_order_chronology_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The words ABBA and BAAB contain the same event multiset, have the same prime-golden bidegree, and give the same complete scalar Euler trajectory.

Their full step-two chronological signatures agree in every associative ring representation.

Whenever the displayed cubic ordered products differ, a degree-three moment distinguishes the two histories. This supplies an explicit boundary of step-two Magnus reconstruction.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape.prime_golden_third_order_chronology_escape`
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation](PrimeGoldenChronologyFiberSeparation.md)
