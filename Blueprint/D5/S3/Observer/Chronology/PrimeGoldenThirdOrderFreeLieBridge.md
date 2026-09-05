# Prime-Golden Third-Order Free-Lie Bridge

## Abstract

A nonzero degree-three free-Lie primitive strictly refines an explicit prime-golden step-two chronology fiber.

**Theorem 1.1 (A concrete degree-three observer escapes a full step-two fiber).**

$$\begin{gathered}\operatorname{primeGoldenBidegree}([A, B, B, A]) = \operatorname{primeGoldenBidegree}([B, A, A, B]) \land \operatorname{sameScalarTrajectory}([A, B, B, A], [B, A, A, B]) \land\\{}\operatorname{chronologicalSignature}(g, [A, B, B, A]) = \operatorname{chronologicalSignature}(g, [B, A, A, B]) \land\\{}\operatorname{thirdOrderReadout}(g, [A, B, B, A]) \neq \operatorname{thirdOrderReadout}(g, [B, A, A, B]).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenThirdOrderFreeLieBridge.explicit_degree_three_strict_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ABBA and BAAB histories have the same prime-golden bidegree, the same scalar Euler trajectory at every time, and the same complete step-two chronological signature under the explicit integer-matrix observation.

Their cubic difference is the represented free-Lie primitive minus the bracket of the sum with the first commutator. The E12 and E21 representation evaluates it to a concrete nonzero integer matrix.

This proves strict refinement for one genuine residual fiber. It does not assert that degree three separates every finite chronology.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenThirdOrderFreeLieBridge.explicit_degree_three_strict_refinement`
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape](PrimeGoldenThirdOrderChronologyEscape.md)
- Dependency: [D5/S3/Observer/Chronology/StepTwoFreeLieBridge](StepTwoFreeLieBridge.md)
