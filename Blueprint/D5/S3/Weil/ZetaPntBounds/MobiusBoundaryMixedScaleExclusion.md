# Zero pairs at two scales near the unattained zeta abscissa

## Abstract

Finite critical Möbius energy excludes pairs of high zeta zeros with separate distance bounds.

**Theorem 1.1 (Exclusion for the exponent sum u + 2v).**

$$\theta-\operatorname{Re} \rho>|t|^{-u}\quad\lor \operatorname{dist}(\theta+it,\sigma)>|t|^{-v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusBoundaryMixedScaleExclusion.no_mixedScaleZeroPair_atHighOrdinate_of_unattainedZeroAbscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let θ < 1 be the unattained supremum of the real parts of nontrivial zeta zeros. Let S(x) be the sum of μ(n)/n over positive integers n ≤ x. Assume (S(x) − S(2x))² x^(1−2θ) is integrable over x > 1. Fix real exponents 0 < v ≤ u with u + 2v > 2.

There is a positive T such that the following holds for every zero ρ strictly to the left of θ with t = Im ρ and |t| ≥ T. If θ − Re ρ ≤ |t|^(−u), then no distinct zero σ lies at distance at most |t|^(−v) from θ + it.

Select one unit of multiplicity at each zero and divide out these two factors. The integral uses the window of radius θ − Re ρ around t. The first factor gives this window a single inverse power of its width. The second gives an inverse square in the distance to σ plus that width. The disk growth estimate and the finite energy bound make a pair with the stated scales impossible at sufficiently large |t|.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusBoundaryMixedScaleExclusion.no_mixedScaleZeroPair_atHighOrdinate_of_unattainedZeroAbscissa`
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion](MobiusBoundaryClusterExclusion.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary](MobiusDyadicBoundary.md)
