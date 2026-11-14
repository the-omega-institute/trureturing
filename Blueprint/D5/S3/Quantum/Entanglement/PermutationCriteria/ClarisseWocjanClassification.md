# Complete classification of permutation norm dependence

## Abstract

Permutation criteria have equal trace norms on every density matrix exactly when their row-position sets differ by the four universal symmetries.

**Theorem 1.1 (Equal row subsets give equal trace norms).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.traceNorm_eq_of_rowSet`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.traceNorm_eq_of_rowSet` (`✓ std3`). ∎

*Citation.* Lieven Clarisse; Pawel Wocjan (2006). *On independent permutation separability criteria*. URL: <https://arxiv.org/abs/quant-ph/0504160v2>.

*Commentary.*

For all natural r and d, all permutations sigma and mu of the 2r interleaved positions, and every complex operator rho on the r-fold d-dimensional tensor index set, equality of rowSet(mu) and rowSet(sigma) implies traceNorm(permute(mu,rho))=traceNorm(permute(sigma,rho)). A row subset consists of the original positions which the permutation sends to even output positions. The permutation mu composed with the inverse of sigma preserves parity. Its restrictions to the even and odd positions induce independent bijections of the row and column tensor coordinates. The two permuted matrices therefore differ by independent reindexing. No positivity or trace assumption is required for this equality.

**Theorem 1.2 (The four row-subset symmetries preserve dependence).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.dependent_of_rowSet_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.dependent_of_rowSet_orbit` (`✓ std3`). ∎

*Citation.* Lieven Clarisse; Pawel Wocjan (2006). *On independent permutation separability criteria*. URL: <https://arxiv.org/abs/quant-ph/0504160v2>.

*Commentary.*

For all natural r and d and all permutations sigma and mu, the criteria are dependent whenever rowSet(mu) equals rowSet(sigma), its complement, its image under the simultaneous exchange J of each factor's ket and bra positions, or the complement of that image. Dependence means equality of the two permuted trace norms on every positive semidefinite operator of trace one. Complementing the output row positions transposes the permuted matrix. Applying J to the original positions complex-conjugates every entry because a density matrix is Hermitian. Transpose and entrywise conjugation preserve the trace norm. The equal-row-subset theorem then covers every permutation representing any of these four subsets. This sufficient direction concerns equality of norm functions. It does not establish incomparability of detection sets for criteria in different orbits.

**Theorem 1.3 (The four row-set symmetries are complete).**

$$\forall r \in \mathbb{N}, d \in \mathbb{N},\; \left(1 \le r \land 2 \le d\right) \Rightarrow \left(\forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot r\right)\right), mu \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot r\right)\right),\; \operatorname{Dependent}\left(r, d, sigma, mu\right) \Leftrightarrow \left(\operatorname{rowSet}\left(mu\right) = \operatorname{rowSet}\left(sigma\right) \lor \left(\operatorname{rowSet}\left(mu\right) = \operatorname{complement}\left(\operatorname{rowSet}\left(sigma\right)\right) \lor \left(\operatorname{rowSet}\left(mu\right) = \operatorname{map}\left(\operatorname{J}\left(r\right), \operatorname{rowSet}\left(sigma\right)\right) \lor \operatorname{rowSet}\left(mu\right) = \operatorname{complement}\left(\operatorname{map}\left(\operatorname{J}\left(r\right), \operatorname{rowSet}\left(sigma\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.result` (`✓ std3`). ∎

*Resolves.* `Problems/clarisse-wocjan-2005-permutation-criteria-classification` (proved) by `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"clarisse-wocjan-2005-permutation-criteria-classification","declaration_gid":"D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lieven Clarisse; Pawel Wocjan (2006). *On independent permutation separability criteria*. URL: <https://arxiv.org/abs/quant-ph/0504160v2>.

*Commentary.*

For every natural number r at least one, every natural local dimension d at least two, and every two permutations sigma and mu of Fin (2r), norm dependence holds if and only if rowSet(mu) equals rowSet(sigma), its complement, its image under J r, or the complement of that image. A matrix is indexed by functions Fin r to Fin d. It is a density matrix exactly when it is positive semidefinite and has trace one. Position 2k is ket and 2k+1 is bra; permute sigma rho at a,b is rho at the even and odd projections of p mapped to merge a b (sigma p). rowSet(sigma) is the preimage of the even output positions. J r exchanges 2k and 2k+1 for every k. Complements are taken in Fin (2r). Dependent quantifies over every such density matrix and asserts equality of the two real trace norms. The trace norm is real trace of sqrt(A adjoint times A); adjoint invariance also gives the source convention sqrt(A times A adjoint). Equal row sets give independent row and column permutations. Complementation gives transpose. Simultaneous ket-bra exchange gives entrywise conjugation on Hermitian inputs. A maximally mixed local qubit distinguishes equal-side from opposite-side positions. A Bell pair distinguishes the three pair distances between paired side labels, with norms 1, sqrt(2), and 2. Independent flips in the same-side and opposite-side sectors recover the row set up to the four symmetries. This settles equality of norm functions in Definition 1. It does not assert incomparability of the sets of states detected by the criteria, the stronger notion called truly independent in the source. The closed count of dependence classes requires an additional orbit-count argument.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.dependent_of_rowSet_orbit`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.traceNorm_eq_of_rowSet`
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses](BellWitnesses.md)
