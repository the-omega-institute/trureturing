# Maximality of Uniform Partition Symmetries

## Abstract

For finite nontrivial K and L, the uniform-partition automorphism subgroup is maximal in the full symmetric group on K times L.

The relation is equality of first coordinates on K times L. Aut is the full subgroup preserving and reflecting that relation. When K and L are finite and nontrivial, it is a coatom: adjoining any permutation outside Aut generates the whole symmetric group.

**Theorem 1.1 (The uniform partition subgroup is a coatom).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; [\operatorname{Finite}\left(K\right)] [\operatorname{Finite}\left(L\right)] [\operatorname{Nontrivial}\left(K\right)] [\operatorname{Nontrivial}\left(L\right)] \operatorname{IsCoatom}\left(\operatorname{Aut}\left(K, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/UniformPartitionMaximality.isCoatom_aut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A same-block transposition lies in Aut. If a subgroup contains Aut and a permutation q outside it, q or q inverse sends a same-block pair across blocks. Conjugating the corresponding same-block swap and transporting it across blocks yields every transposition. All transpositions generate the full symmetric group on a finite carrier; on an infinite carrier they generate only the finite-support permutations, while the full symmetric group also contains permutations of infinite support. The proof keeps both finite and nontrivial hypotheses, including the size-two boundary.

**Theorem 1.2 (Adjoining any outside permutation generates the full group).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; [\operatorname{Finite}\left(K\right)] [\operatorname{Finite}\left(L\right)] \forall q \in \operatorname{Perm}\left(\operatorname{Product}\left(K, L\right)\right),\; \left(\neg q \in \operatorname{Aut}\left(K, L\right)\right) \Rightarrow \operatorname{closure}\left(\operatorname{union}\left(\operatorname{Set}\left(\operatorname{Aut}\left(K, L\right)\right), \left\{q\right\}\right)\right) = \operatorname{top}\left(\operatorname{Subgroup}\left(\operatorname{Perm}\left(\operatorname{Product}\left(K, L\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/UniformPartitionMaximality.closure_aut_union_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite K and L, every q outside Aut satisfies closure (Aut union {q}) = top. The argument uses q or q inverse to expose a cross-block image, then conjugates one within-block swap and transports it across arbitrary ordered cross-block pairs. Generation uses all of Aut together with q. No nontriviality assumption is needed for this implication; when Aut is already the full group, there is no outside q.

For every n, a : Nat with n > 0, put g = gcd(n, a), ell = n/g and W = ZeroFamilyAut n a, a subgroup of Perm (Fin n). In the owning module D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries, the public APIs residueChart, sameCycle_iff_chart and zeroFamilyAut_eq_orbitAut identify the actual ambient subgroup, by conjugation through residueChart, with Aut (Fin g) (Fin ell), the first-coordinate partition subgroup. The abstract zeroFamilyEquiv alone does not identify this embedding. Transporting the results above therefore gives: if 1 < g < n, W is a coatom in the full symmetric group on Fin n; for every positive n and every q outside W, closure (W union {q}) = top. This generation uses all of W together with q. W stabilizes the whole family of actual zero subsets setwise and may exchange individual zero subsets. These are consequences of the cited arithmetic API and the generic theorems, with no additional canonical theorem. The outside-q implication retains a = 0, n = 1 and ell = 1; in these cases W is the full group and its outside-q premise is empty.

## References

- Truth anchor: `D5/S3/FiniteGroups/UniformPartitionMaximality.closure_aut_union_singleton`
- Truth anchor: `D5/S3/FiniteGroups/UniformPartitionMaximality.isCoatom_aut`
- Dependency: [D5/S3/FiniteGroups/UniformPartitionAutomorphisms](UniformPartitionAutomorphisms.md)
