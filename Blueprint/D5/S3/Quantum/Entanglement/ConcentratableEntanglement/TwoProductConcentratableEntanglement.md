# Subsystem inequalities for coherent two-product states

## Abstract

The actual generalized concentratable entanglement of a coherent two-product state is monotone and submodular for every real order above one.

**Theorem 1.1 (Monotonicity and submodularity of literal two-product GCE).**

$$\forall K \in \mathbb{R},\; \forall Q \in NonzeroTwoProductData,\; (1 < K) \Rightarrow ((\operatorname{Monotone}\left(\operatorname{C}\left(K, Q\right)\right)) \land (\forall A \in \operatorname{Subsets}\left(\operatorname{Sites}\left(Q\right)\right),\; \forall B \in \operatorname{Subsets}\left(\operatorname{Sites}\left(Q\right)\right),\; \operatorname{C}\left(K, Q, \operatorname{Intersection}\left(A, B\right)\right) + \operatorname{C}\left(K, Q, \operatorname{Union}\left(A, B\right)\right) \le \operatorname{C}\left(K, Q, A\right) + \operatorname{C}\left(K, Q, B\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConcentratableEntanglement/TwoProductConcentratableEntanglement.actual_two_product_gce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

A datum Ψ is a nonzero coherent sum of two finite tensor products of local complex unit vectors, with arbitrary complex coefficients and possibly different finite local dimensions. Its density matrix is normalized by the squared norm. C(K, Ψ, S) subtracts the mean of the real power traces of the actual reductions over subsets of S from one, then divides by K − 1.

The physical moment supplier relates every reduction to two spectral values and supplies the phase-dependent mass bound. For positive local overlap magnitudes the logarithms of their squared magnitudes make the cut parameter additive. A convex scalar spectral profile then gives supermodularity of the powerset-averaged moments. The continuous scalar boundary argument also covers zero overlaps. Complement symmetry equates the averages before and after the final site is added, so submodularity forces earlier increments to be nonnegative.

The stated domain is literal two-product sums, not arbitrary pure states, arbitrary states of cut rank at most two, or a secant-closure theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglement/TwoProductConcentratableEntanglement.actual_two_product_gce`
- Dependency: [D5/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments](PhysicalTwoProductMoments.md)
