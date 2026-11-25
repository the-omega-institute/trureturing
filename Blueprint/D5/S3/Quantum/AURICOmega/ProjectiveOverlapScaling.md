# Projective overlap under positive scaling

## Abstract

Scale invariance of the Chapter 39 projective overlap.

**Theorem 1.1 (Common positive scales preserve overlap).**

$$\forall p \in \mathbb{N}, q \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{kappa}\left(p \cdot \left(k + 1\right), q \cdot \left(k + 1\right)\right), \operatorname{kappa}\left(p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/ProjectiveOverlapScaling.kappa_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the book's Chapter 39 overlap of the integer homogeneous coordinates [P:Q], take p and q to be the magnitudes of P and Q. The scale k+1 ranges over all positive natural numbers.

The overlap kappa(p,q) is the exact ratio with numerator q squared and denominator p squared plus q squared. Equivalent compares finite ratios by cross multiplication and relates the undefined value to itself. The pair (0,0) therefore remains in the theorem, with undefined readings before and after scaling.

This is the direct application of Omega.Projective.kappa_scale to p, q, and k.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveOverlapScaling.kappa_scale`
