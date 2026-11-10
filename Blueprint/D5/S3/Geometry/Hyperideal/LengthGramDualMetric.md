# Inverse-Gram Dual Metric

## Abstract

Inverse-Gram dual vectors pair by the inverse-Gram metric.

For a realizing matrix M of the six-length Gram matrix G, the dual vectors obtained from rows of G inverse have Lorentz pairings equal to the corresponding entries of G inverse. This is the metric identity behind the dual basis construction.

**Theorem 1.1 (The dual vectors recover the inverse-Gram metric).**

$$\forall l \in Length6,\; \forall M \in Mat4,\; \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{row}\left(M, i\right), \operatorname{row}\left(M, j\right)\right) = \operatorname{entry}\left(\operatorname{lengthGram}\left(l\right), i, j\right)\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{lengthGram}\left(l\right)\right) < 0 \Rightarrow \left(\forall i \in Fin4,\; \forall j \in Fin4,\; \operatorname{lorentz}\left(\operatorname{dualVector}\left(\operatorname{lengthGram}\left(l\right), M, i\right), \operatorname{dualVector}\left(\operatorname{lengthGram}\left(l\right), M, j\right)\right) = \operatorname{entry}\left(\operatorname{inv}\left(\operatorname{lengthGram}\left(l\right)\right), i, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramDualMetric.dual_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the first dual vector by its inverse-Gram coefficients. Lorentz symmetry and the already proved dual-pairing identity collapse the finite sum to the (i,j) entry of G inverse.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramDualMetric.dual_metric`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramDualPairing](LengthGramDualPairing.md)
