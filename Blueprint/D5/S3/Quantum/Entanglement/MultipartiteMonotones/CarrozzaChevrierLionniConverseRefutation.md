# A four-qubit counterexample to both converses of Corollary 7

## Abstract

A four-qubit cluster state is irreducible in the sense of Definition 1 and has zero ordered and color-averaged readouts at every integer order at least two.

**Definition 1.1 (The two universal converse assertions).**

$$claim \iff (\forall D \in \mathbb{N}_{\geq3}, \forall d:[D] \to \mathbb{N}_{>0}, \forall \psi \in \mathcal{H}_{d}, \forall n \in \mathbb{N}_{\geq2}, (\left\lVert \psi \right\rVert^{2} = 1 \land \mathrm{Irred}\left(\psi\right)) \implies (\forall \sigma \in S_{D}, R_{\sigma}^{(n)}(\psi) > 0)) \lor (\forall D \in \mathbb{N}_{\geq3}, \forall d:[D] \to \mathbb{N}_{>0}, \forall \psi \in \mathcal{H}_{d}, \forall n \in \mathbb{N}_{\geq2}, (\left\lVert \psi \right\rVert^{2} = 1 \land \mathrm{Irred}\left(\psi\right)) \implies (R^{(n)}(\psi) > 0))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.claim` (`✓ std3`).

*Citation.* Sylvain Carrozza; Johann Chevrier; Luca Lionni (2026). *Detection of genuine multipartite entanglement by means of entanglement monotones*. DOI: [10.48550/arXiv.2611.27660](https://doi.org/10.48550/arXiv.2611.27660). URL: <https://arxiv.org/abs/2611.27660v1>.

*Commentary.*

The sentence after Corollary 7 asks whether irreducibility implies strict positivity of the ordered readout or its color-symmetric version. Each disjunct universally quantifies over positive finite local dimensions, normalized complex pure states, and integer orders at least two. The ordered disjunct also universally quantifies over color permutations. In Lean, the parameter k is D minus three, d gives the local dimensions, and hd proves their positivity. H with subscript d is the tensor product of the complex spaces of dimensions d(i). Irred means the negation of ReducibleTensor.

**Theorem 1.2 (Both universal converses fail).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/carrozza-chevrier-lionni-2026-corollary-seven-converses` (refuted) by `D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"carrozza-chevrier-lionni-2026-corollary-seven-converses","declaration_gid":"D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sylvain Carrozza; Johann Chevrier; Luca Lionni (2026). *Detection of genuine multipartite entanglement by means of entanglement monotones*. DOI: [10.48550/arXiv.2611.27660](https://doi.org/10.48550/arXiv.2611.27660). URL: <https://arxiv.org/abs/2611.27660v1>.

*Acknowledgement.* Gilad Gour; Nolan R. Wallach (2010). *All Maximally Entangled Four Qubits States*. DOI: [10.1063/1.3511477](https://doi.org/10.1063/1.3511477). URL: <https://arxiv.org/abs/1006.0036v2>.

*Commentary.*

Use the four-qubit cluster state C1 of Gour and Wallach, Eq. (3). Its amplitudes are 1/2 on 0000, 0011 and 1100, −1/2 on 1111, and zero elsewhere. The four nonzero terms give squared norm one.

$$
\left\lVert \psi \right\rVert^{2} = 1 \land \mathrm{Irred}\left(\psi\right) \land (\forall n \in \mathbb{N}_{\geq2}, (\forall \sigma \in S_{4}, R_{\sigma}^{(n)}(\psi) = 0) \land R^{(n)}(\psi) = 0)
$$

The proof takes D = 4, all local dimensions equal to two and n = 2 in each putative universal assertion. The ordered vanishing holds for every permutation, so the same state also defeats strict positivity with an existential choice of order of the colors. The three-qubit restriction in Proposition 8 and the spectral-hypergraph-tensor restriction in Theorem 6 are separate source results.

Definition 1 and Eq. (9) correspond to ReducibleTensor in finite orthonormal bases. Each factor has a proper assigned support, with arbitrary positive finite dimensions on it and a normalized coefficient tensor. Outside its support a product unit leg can be compressed to dimension one using the isometry that sends the scalar unit to that leg. The empty support allows a unit scalar. The code uses a list of proper supports. An Eq. (9) family gives such a list by enumerating the proper subsets. Conversely, regroup factors with the same support, multiply their local dimensions and pad absent supports with unit scalar factors. Local reindexing is unitary. The two sets of matrices U and V are the local isometries into common spaces in the cited Definition 2.2 of local-unitary equivalence. Compose one set with the comparison unitary to obtain the exact equality of embedded tensors in ReducibleTensor. Conversely, that equality supplies the same local-unitary equivalence with identity comparison. This permits overlapping supports and arbitrary mixing of the regrouped factor legs within each party.

For any party cut, the grouped local maps act on the coefficient matrix M by L M R transpose. Left multiplication by the adjoint of L and right multiplication by the conjugate of R recover M, so the cut rank is invariant. The cut rank of a regrouped factor product is the product of the factor cut ranks. Every singleton cut of the cluster state has rank two. For every nonempty proper cut, select the constant zero and constant one coordinates on each side. The resulting minor has diagonal entries 1/2 and −1/2 and off-diagonal entries in {0, 1/2}. Its determinant is nonzero. Primality of two assigns each party to exactly one factor with singleton rank two. Every other factor has singleton rank one at that party. Each effective support lies within its assigned proper support. Stripping rank-one legs shows that the cut at a nonempty effective support has rank one in the grouped product, contradicting the minor bound.

For Eq. (24), the column is ket–dual and the row is dual–ket. The active pairs follow adjacent colors of the permutation. Within each pair, summing the spectator colors gives the corresponding two-color density matrix rho. Top and bottom labels exchange ket and bra roles between successive pairs. The terminal top label is the ket for even D and the dual for odd D, which accounts for the parity-dependent output swap in contraction. For D = 4 and order (a,b,c,d), the entry at row (j′,j) and column (i,i′) is the following sum.

$$
A_{\sigma}[(j',j),(i,i')] = \sum_{x,x',y,y'} \rho_{ab}[(i,x),(i',x')] \cdot \rho_{bc}[(x',y'),(x,y)] \cdot \rho_{cd}[(y,j),(y',j')]
$$

For every one of the 24 permutations the contraction gives A = e e transpose / 16 with e = (1,0,0,1) in the endpoint basis (00,01,10,11). Its Gram matrix X = A A adjoint is e e transpose / 128, has trace t = 1/64, and satisfies X squared = t X. The real part of the complex trace agrees with the real trace of powers of this positive semidefinite matrix. Hence tr(X^n) = t^n for every positive integer n. The logarithm in Eq. (30) has the positive argument one, and every term in Eq. (31) vanishes.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.result`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor](../../../Combinatorics/SubspaceCodes/MRDDensityColumnTensor.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../../Recovery/PurifiedLocalPath.md)
