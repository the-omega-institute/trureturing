# Isometric extension of Gram-preserving permutations

## Abstract

A permutation of the index set of a spanning family in a real inner product space that preserves all pairwise inner products extends to exactly one linear isometry equivalence.

**Theorem 1.1 (Gram-preserving permutations extend uniquely to isometries).**

$$\forall \iota, E: \operatorname{Type}*, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall \varphi: \iota \to E, \operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(\varphi\right)\right) = \operatorname{top} \Rightarrow \forall \sigma: \operatorname{Perm}\left(\iota\right), (\forall a, b: \iota, \langle \varphi\left(\sigma\left(a\right)\right), \varphi\left(\sigma\left(b\right)\right) \rangle_{\mathbb{R}} = \langle \varphi\left(a\right), \varphi\left(b\right) \rangle_{\mathbb{R}}) \Rightarrow \exists! U: \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, E, E\right), \forall a: \iota, U\left(\varphi\left(a\right)\right) = \varphi\left(\sigma\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/GramIsometryExtension.existsUnique_linearIsometryEquiv_of_gram_preserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a real inner product space and let phi be a family of vectors of E, indexed by a type iota, whose range spans E as a real vector space; no finite dimensionality or completeness of E is assumed, and the span is the algebraic span, not its closure. Let sigma be a permutation of iota with <phi(sigma a), phi(sigma b)> = <phi a, phi b> for all indices a and b. Then there is exactly one linear isometry equivalence U of E onto itself with U(phi a) = phi(sigma a) for every index a. For existence, write L for the linear map sending a finitely supported coefficient function c on iota to the finite combination of the vectors phi a with coefficients c a, and L' for the same map built from the reindexed family a -> phi(sigma a). Bilinearity of the inner product and the hypothesis on sigma give <L' c, L' d> = <L c, L d> for all coefficient functions c and d, so L' c and L c have the same norm. Hence the kernel of L is contained in the kernel of L', and L' factors through L, which is surjective because the range of phi spans E. The induced linear map U of E onto itself satisfies U(L c) = L' c, preserves norms, and is surjective because the range of the reindexed family is again the range of phi; it is therefore a linear isometry equivalence, and evaluating at the coefficient function of a single index gives U(phi a) = phi(sigma a). For uniqueness, two linear maps that agree on a spanning set agree everywhere.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/GramIsometryExtension.existsUnique_linearIsometryEquiv_of_gram_preserving`
