# Legal-word block growth

## Abstract

Native legal-word quadratic loads have a finite growth constant with matching infimum and supremum formulas.

For each natural length n, legalWordGraph(n) has all Boolean words of length n with no adjacent ones as vertices, and joins words differing at exactly one position. Write K(n)=kappa(legalWordGraph(n)), using the actual infimum over feasible quadratic edge allocations. The empty word is the sole vertex at length zero.

**Theorem 1.1 (Near additivity and the common growth constant).**

$$(\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(0\right)\right) = 0) \land ((\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; (\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n + m\right)\right) \le \mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right) + \mathrm{kappa}\left(\mathrm{legalWordGraph}\left(m\right)\right)) \land (\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right) + \mathrm{kappa}\left(\mathrm{legalWordGraph}\left(m\right)\right) \le \mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n + m + 1\right)\right))) \land (\exists c \in \mathrm{Real},\; (\mathrm{Tendsto}\left((\lambda n: \mathrm{Nat}, \frac{\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right)}{\mathrm{castReal}\left(n\right)}), \mathrm{atTop}, \mathrm{nhds}\left(c\right)\right)) \land (((c = \mathrm{sInf}\left(\mathrm{image}\left((\lambda n: \mathrm{Nat}, \frac{\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right)}{\mathrm{castReal}\left(n\right)}), \mathrm{Ici}\left(1\right)\right)\right)) \land (c = \mathrm{sSup}\left(\mathrm{range}\left((\lambda n: \mathrm{Nat}, \frac{\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right)}{\mathrm{castReal}\left(n\right) + 1})\right)\right))) \land (\forall n \in \mathrm{Nat},\; (c \cdot \mathrm{castReal}\left(n\right) \le \mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right)) \land (\mathrm{kappa}\left(\mathrm{legalWordGraph}\left(n\right)\right) \le c \cdot \left(\mathrm{castReal}\left(n\right) + 1\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/BlockGrowth.growth_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting a word of length n+m into its first n and last m letters is an injective adjacency-preserving map into the Cartesian graph. Conversely, inserting one zero between two legal words gives an injective adjacency-preserving map from that Cartesian graph into the length n+m+1 graph. These maps are defined at zero lengths as well. Applying native injective transport and Cartesian additivity proves both inequalities. There are no edges at length zero, so K(0)=0; all native loads are nonnegative.

Pinned Fekete convergence for the subadditive sequence K gives a finite real limit c and the infimum over n at least one. The estimate K(n) at most n K(1) bounds the ratios of u(j)=-K(j-1) below. The right block inequality makes u subadditive, including j=0. A second application of Fekete, together with n/(n+1) tending to one, identifies its limit as -c. Thus every K(n)/(n+1) is at most c, while these ratios converge to c, so their supremum is c. The infimum and supremum bounds give the two linear estimates for every natural n, including zero. No positive-mass restriction or auxiliary optimization is substituted for the native graph infimum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/BlockGrowth.growth_constant`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer](ConstrainedHarmonicOptimizer.md)
- Dependency: [D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport](../QuadraticLoad/NativeTransport.md)
