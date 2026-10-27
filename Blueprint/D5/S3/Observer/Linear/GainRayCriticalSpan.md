# Critical scalar identities have three source directions

## Abstract

Critical scalar identities have three source directions

**Theorem 1.1 (Polynomial multiplication forces dimension growth).**

Lean statement: `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota be any finite type, t:iota to the reals injective, and V,K real linear subspaces of real functions on iota. Suppose a belongs to V and every a(i) is nonzero. If for every v in V and every natural j at most d the function v(i)*t(i)^j belongs to K, then dim(K) is at least min(card(iota),dim(V)+d). Repeatedly enlarge V by its image under coordinatewise multiplication by t. An enlargement that stops is invariant under that multiplication. It contains all clock powers of a, and Lagrange interpolation then makes it the entire function space. Thus each proper enlargement increases dimension by at least one. This argument supplies the critical scalar-span contradiction with a scalar-kernel observation space, including restriction away from its identically zero coordinates.

**Theorem 1.2 (A nonzero universal scalar identity forces cumulative span three).**

Lean statement: `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every declared degree d at least one, every legal Boolean word w containing both M and J with exactly 2*(d+1)+1 initial-inclusive original-clock reads, and every fixed whole-coefficient readout C, suppose C annihilates constant drift, its auxiliary response at every real 2 by 2 matrix T equals scalarFunctional(T) times the identity, and this functional is nonzero. Then the real span of all actual cumulative matrices acquisition(take(i,w)) has dimension exactly three. The hypotheses are the original GainRay response and scalar functional, with every original prefix and clock retained.

Mixedness already gives dimension at least three. If the span were four, trace pairing would make the scalar-kernel observation map injective, with three-dimensional image. A single scalar-kernel source realizes exactly the coordinates Q whose cumulative matrices are proportional to the scalar representative. The even-word proportionality bound gives card(Q) at most d+1. On the complementary coordinates the image contains a vector with every coordinate nonzero. All its polynomial multiples through degree d come from responseMatrix and lie in the restricted readout kernel. When Q is empty this kernel has dimension at most d+2. When Q is nonempty the constant drift vector makes the subspace vanishing on Q proper, so its dimension is at most d+1. Polynomial dimension growth contradicts both bounds.

On the full original world domain, universal coefficient collinearity supplies drift annihilation and the auxiliary response identity by universal_scalar_identity. Success at one actual world supplies nonzeroness by successful_scalar_nonzero. These results retain every nonzero coefficient vector, including degree drops and sampled roots, and arbitrary real drift. This theorem is the critical scalar-span component; source partners, common adaptive histories and countable-palette exclusion require separate arguments.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span`
- Truth anchor: `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth`
- Dependency: [D5/S3/Observer/Linear/GainRayNuisance](GainRayNuisance.md)
