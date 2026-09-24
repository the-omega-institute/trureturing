# Mixing and measurable selection for the bilateral Parry source

## Abstract

Mixing and measurable selection for the bilateral Parry source.

**Theorem 1.1 (Strong mixing and an unattained zero defect infimum).**

Lean statement: `D5/S3/TotalVariation/ParryBilateralMixing.bilateral_parry_mixing`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryBilateralMixing.bilateral_parry_mixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite k >= 2, take the bilateral relation space in which every block of k bits contains a false bit. The stationary source measure mu, the signed state-path measure nu, and the measurable coding e retain all their exact cylinder and reconstruction identities. The state consists of an absolute sign and the actual preceding run of true relation bits. The coding sends the product of mu with a fair anchor to nu and intertwines the anchored shift T(a,r) = (a xor not r_0, relationShift r) with the integer-indexed state-path shift.

Write Q for the actual signed Parry transition matrix and pi for its stationary law. A word u on the block from ell to ell+a has mass L(u) = pi(u_0) times the product of its transition weights. For a word v on the block from ell+a+g to ell+a+g+b, let H(v) be its transition product. For every integer ell and every natural a, b and g, the joint mass is L(u) Q^g(u_a,v_0) H(v). At gap zero the identity matrix enforces the shared endpoint. Zero transition weights and forbidden words remain in the formula without division by cylinder probabilities.

For arbitrary events on these two finite blocks, the absolute difference between the joint probability and the product of their probabilities is at most (3/4)^(g/3), with natural-number division in the exponent. Summing the actual intervening state paths gives the joint law. The future-block channel has nonnegative rows summing to one, so applying it to the endpoint distributions contracts total variation. Finite cylinders approximate every measurable event in symmetric difference; shift preservation controls the approximation error at every time.

Consequently, for each fixed pair of measurable events A and B, nu(A intersect shift^(-n)(B)) tends to nu(A) nu(B). The exact coding transfers the same mixing statement to the fair anchored extension, which is therefore ergodic. A measurable relation selector h satisfying h(relationShift r) = h(r) xor not r_0 almost everywhere would give an almost invariant graph of product measure one half, contradicting ergodicity.

Define Delta(h) as the mu-probability that h(relationShift r) xor h(r) xor not r_0 is true. Every measurable h has strictly positive Delta(h), while the infimum of these values is zero. A rule on the R strictly preceding coordinates has exactly the finite stationary defect computed from the signed cylinder law. For R = 2(n+1), suitable fixed rules have defect at most 1/(n+3) + choose(n+3,2) p^n, where p is the Parry parameter and 0 < p < 1. The bound tends to zero by polynomial-geometric decay. Thus the zero infimum is not attained by any measurable relation selector.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryBilateralMixing.bilateral_parry_mixing`
- Dependency: [D5/S3/TotalVariation/ParryBilateralLaw](ParryBilateralLaw.md)
- Dependency: [D5/S3/TotalVariation/ParryWindowUpperBound](ParryWindowUpperBound.md)
