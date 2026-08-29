# Smooth External Moment Elimination

## Abstract

An even smooth correction supported outside a finite interval cancels every prescribed even moment through a fixed order.

**Theorem 1.1 (Smooth exterior cancellation of finitely many even moments).**

$$\forall L \in \operatorname{Real}\left(\right), K \in \operatorname{Natural}\left(\right), epsilon \in \operatorname{SignedMeasure}\left(\operatorname{Real}\left(\right)\right),\; \left(\operatorname{restrict}\left(\operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(epsilon\right)\right), \operatorname{Icc}\left(-2L, 2 \cdot L\right)\right) = \operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(epsilon\right)\right) \land \operatorname{restrict}\left(\operatorname{negPart}\left(\operatorname{toJordanDecomposition}\left(epsilon\right)\right), \operatorname{Icc}\left(-2L, 2 \cdot L\right)\right) = \operatorname{negPart}\left(\operatorname{toJordanDecomposition}\left(epsilon\right)\right)\right) \Rightarrow \left(\exists kappa \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{Even}\left(kappa\right) \land \left(\operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), kappa\right) \land \left(\operatorname{HasCompactSupport}\left(kappa\right) \land \left(\operatorname{tsupport}\left(kappa\right) \subseteq \operatorname{compl}\left(\operatorname{Icc}\left(-2L, 2 \cdot L\right)\right) \land \left(\forall j \in \operatorname{Natural}\left(\right),\; j \le K \Rightarrow \operatorname{signedIntegral}\left(u, \operatorname{pow}\left(u, 2 \cdot j\right), epsilon\right) + \operatorname{integral}\left(u, \operatorname{pow}\left(u, 2 \cdot j\right) \cdot kappa\left(u\right), \operatorname{volume}\left(\right)\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/SmoothExternalMomentElimination.smooth_external_finite_moment_elimination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflected pairs of even derivatives of one compact bump form a lower triangular moment family. Integration by parts makes its diagonal nonzero, so the inverse finite moment matrix supplies the displayed even correction without entering the source interval.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/SmoothExternalMomentElimination.smooth_external_finite_moment_elimination`
