# Separation from a fixed frequency

## Abstract

Local separation of the actual root modes

**Theorem 1.1 (Positive gap outside the matching frequency).**

$$\forall r \in \mathbb{R},\; 0 < r \Rightarrow \left(\forall w \in \mathbb{C},\; \exists d \in \mathbb{R},\; 0 < d \land \left(\forall k \in \mathbb{N},\; \operatorname{v}\left(r, k\right) \ne w \Rightarrow d \le \left\lVert \operatorname{v}\left(r, k\right) - w \right\rVert\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier.actual_frequency_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write v(r,k)=(ρₖ−1/2)/r, where ρₖ runs over actual nontrivial zeta zero occurrences with analytic multiplicity.

A mode within distance 1 of w comes from a zero in the closed disk of radius r(1+‖w‖) about 1/2. The distinct zeros in that disk form a finite set. Remove w from its rescaled image and take a ball centered at w in the open complement. Cap the radius of that ball at 1 to include all remaining modes in the estimate.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier.actual_frequency_gap`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum](RootSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean](../RHPrimeWindowMean.md)
