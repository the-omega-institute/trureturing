# Prime-Golden Chronology Fiber Separation

## Abstract

Scalar prime-golden observation is constant on a bidegree fiber, while a noncommutative second-Magnus readout can separate chronology inside that fiber.

**Theorem 1.1 (Magnus separates swapped histories hidden by scalar observation).**

$$\begin{gathered}\forall f, \forall u, \forall w, \operatorname{commutator}(\operatorname{f}(u), \operatorname{f}(w)) \neq \operatorname{commutator}(\operatorname{f}(w), \operatorname{f}(u)) \Rightarrow\\{}\operatorname{primeGoldenBidegree}([u, w]) = \operatorname{primeGoldenBidegree}([w, u]) \land\\{}\operatorname{sameScalarTrajectory}([u, w], [w, u]) \land\\{}\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [u, w])) \neq \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [w, u])).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation.prime_golden_chronology_fiber_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed-prime scalar endpoint factors through the prime-event and short-step bidegree, so every word in one bidegree fiber has the same complete scalar trajectory.

A two-event word and its reversal share that bidegree and scalar trajectory.

When the two oriented commutators differ, the degree-two Magnus coordinate distinguishes the reversed histories inside the same scalar fiber.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation.prime_golden_chronology_fiber_separation`
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation](PrimeGoldenBidegreePhaseSeparation.md)
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalSignature](StepTwoChronologicalSignature.md)
