# Recovering interleaved row subsets

## Abstract

Interleaved subsets with identical sector and pair-distance data differ by at most simultaneous ket-bra exchange and complement.

**Definition 1.1 (Tensor indices).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Index`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural numbers r and d, Index r d is the function type from Fin r to Fin d.

**Definition 1.2 (Density matrices).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.IsDensity`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.IsDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the existing predicate for a positive semidefinite complex matrix with trace one, on any finite index type.

**Definition 1.3 (Ket positions).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ket position of a factor k in Fin r is the element 2k of Fin (2r).

**Definition 1.4 (Bra positions).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bra position of a factor k in Fin r is the element 2k+1 of Fin (2r).

**Definition 1.5 (The factor of a position).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor containing a position p in Fin (2r) has index floor(p/2) in Fin r.

**Definition 1.6 (Interleaving row and column coordinates).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row and column functions a and b from Fin r to Fin d, merge a b at position p is a(floor(p/2)) when p is even, and b(floor(p/2)) when p is odd.

**Definition 1.7 (Reading an interleaved entry).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.entry`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an operator rho on Index r d and a flat coordinate function i, entry rho i is rho evaluated at the row k mapped to i(2k) and the column k mapped to i(2k+1).

**Definition 1.8 (The original index permutation).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute` (`✓ std3`).

*Citation.* Lieven Clarisse; Pawel Wocjan (2006). *On independent permutation separability criteria*. URL: <https://arxiv.org/abs/quant-ph/0504160v2>.

*Commentary.*

For every permutation sigma of Fin (2r), permute sigma rho at a,b is entry rho at the function p mapped to merge a b (sigma p). This is the source index-permutation convention, without an inverse permutation.

**Definition 1.9 (Dependence on every quantum state).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Dependent`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Dependent` (`✓ std3`).

*Citation.* Lieven Clarisse; Pawel Wocjan (2006). *On independent permutation separability criteria*. URL: <https://arxiv.org/abs/quant-ph/0504160v2>.

*Commentary.*

For natural r,d and permutations sigma,mu of Fin (2r), Dependent r d sigma mu means that for every complex operator rho on Index r d, positivity and trace one imply equality of traceNorm(permute sigma rho) and traceNorm(permute mu rho). The trace norm is real trace of the positive square root of the adjoint Gram matrix.

**Definition 1.10 (Original positions assigned to output rows).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.rowSet`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.rowSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a permutation sigma of Fin (2r), rowSet sigma contains precisely the positions p for which sigma p is even. It is the preimage of the even output positions.

**Theorem 1.11 (The factor of a ket slot).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_ketPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_ketPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and every factor k in Fin r, party(ketPos k) equals k.

**Theorem 1.12 (The factor of a bra slot).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_braPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_braPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and every factor k in Fin r, party(braPos k) equals k.

**Theorem 1.13 (The ket projection of interleaving).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_ketPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_ketPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, row and column indices a,b, and factors k, merge a b (ketPos k) equals a k.

**Theorem 1.14 (The bra projection of interleaving).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_braPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_braPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, row and column indices a,b, and factors k, merge a b (braPos k) equals b k.

**Theorem 1.15 (Recovering an even position).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos_party`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos_party` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and p in Fin (2r), if p is even then ketPos(party p) equals p.

**Theorem 1.16 (Recovering an odd position).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos_party`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos_party` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and p in Fin (2r), if p is not even then braPos(party p) equals p.

**Theorem 1.17 (Lossless splitting of flat coordinates).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_projections`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d and every flat coordinate function i, interleaving its even and odd projections recovers i as a function.

**Definition 1.18 (Simultaneous ket and bra exchange).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r, J r is the permutation of Fin (2r) that exchanges 2k with 2k+1 for every factor k.

**Theorem 1.19 (Exchange sends ket to bra).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_ketPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_ketPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and k in Fin r, J r (ketPos k) equals braPos k.

**Theorem 1.20 (Exchange sends bra to ket).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_braPos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_braPos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r and k in Fin r, J r (braPos k) equals ketPos k.

**Theorem 1.21 (Exchange swaps row and column indices).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_J`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, tensor indices a,b and positions p, merge a b (J r p) equals merge b a p.

**Theorem 1.22 (Output exchange is matrix transpose).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_output_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_output_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, permutations sigma and operators rho, permuting by J after sigma gives the ordinary transpose of permute sigma rho. No Hermitian hypothesis is required.

**Definition 1.23 (The interleaving equivalence).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.mergeEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.mergeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, mergeEquiv is the equivalence from pairs of tensor indices to flat coordinate functions, with inverse the even and odd projections.

**Definition 1.24 (Permutation on pairs of tensor indices).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.indexPermutation`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.indexPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural r,d and permutations sigma, indexPermutation sigma sends a,b to the two projections of the flat function p mapped to merge a b (sigma p). It is an equivalence, including for empty index types.

**Theorem 1.25 (Reading through the index equivalence).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every operator rho, permutation sigma, and indices a,b, permute sigma rho at a,b equals rho at the pair indexPermutation sigma (a,b).

**Theorem 1.26 (The image of a single nonzero entry).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural r,d, permutations sigma, indices a,b, and complex numbers z, permute sigma sends the matrix single a b z to the single entry of value z at the inverse image of a,b under indexPermutation sigma.

**Theorem 1.27 (Four possibilities for the interleaved subset).**

$$\forall r:\mathbb{N}, (\forall S:\operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot r\right)\right), (\forall T:\operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot r\right)\right), ((\forall k:\operatorname{Fin}\left(r\right), (\operatorname{sameSide}\left(\operatorname{rowLabels}\left(S, k\right)\right) \Leftrightarrow \operatorname{sameSide}\left(\operatorname{rowLabels}\left(T, k\right)\right))) \Rightarrow ((\forall i:\operatorname{Fin}\left(r\right), (\forall j:\operatorname{Fin}\left(r\right), (\operatorname{pairDistance}\left(\operatorname{rowLabels}\left(S, i\right), \operatorname{rowLabels}\left(S, j\right)\right) = \operatorname{pairDistance}\left(\operatorname{rowLabels}\left(T, i\right), \operatorname{rowLabels}\left(T, j\right)\right)))) \Rightarrow ((T = S) \lor ((T = \operatorname{compl}\left(S\right)) \lor ((T = \operatorname{map}\left(S, \operatorname{J}\left(r\right)\right)) \lor (T = \operatorname{compl}\left(\operatorname{map}\left(S, \operatorname{J}\left(r\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.recover_rowSets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every factor k, rowLabels(S,k) records membership of positions 2k and 2k+1 in S. Equal sector and distance data give the two global Boolean operations from recover_labels. Every interleaved position is a ket or bra position, so its label determines membership. Boolean complement is set complement, and exchange of the two labels is the image under J. The statement applies to all subsets, including unbalanced subsets and the empty carrier; no cardinality assumption is required.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Dependent`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.Index`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.IsDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_braPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.J_ketPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.braPos_party`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.entry`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.indexPermutation`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.ketPos_party`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.mergeEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_J`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_braPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_ketPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.merge_projections`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_braPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.party_ketPos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_output_exchange`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.permute_single`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.recover_rowSets`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery.rowSet`
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery](LabelRecovery.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../../Information/SLDSpectralEnergy.md)
