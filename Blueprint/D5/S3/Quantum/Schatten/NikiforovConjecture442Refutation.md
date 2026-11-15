# Entrywise modulus does not determine a Schatten norm

## Abstract

The equality criterion in Nikiforov's Conjecture 4.42 fails for a complex tripartite matrix.

**Definition 1.1 (Nonempty common index parts).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{rPartite}\left(r, A\right) = \exists (c: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(r\right)), (\operatorname{Surjective}\left(c\right)) \land (\forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), (c\left(i\right) = c\left(j\right)) \Rightarrow (A\left(i, j\right) = 0))$$

*Formalization.* `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.rPartite` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Nikiforov (2016). *Beyond graph energy: norms of graphs and matrices*. DOI: [10.1016/j.laa.2016.05.011](https://doi.org/10.1016/j.laa.2016.05.011). URL: <https://arxiv.org/abs/1510.02850v2>.

*Commentary.*

The same surjective coloring is used on rows and columns. Its fibers are nonempty, pairwise disjoint and cover the index set. The private parts_iff bridge proves equivalence with a family of r nonempty finite sets, unique part membership and zero entries within every common part. No restriction is imposed on entries between parts.

**Definition 1.2 (The canonical complex Turán adjacency).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{turanMatrix}\left(n, r\right) = (\operatorname{SimpleGraph}.\operatorname{turanGraph}\left(n, r\right)).\operatorname{adjMatrix}\left(\mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.turanMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Nikiforov (2016). *Beyond graph energy: norms of graphs and matrices*. DOI: [10.1016/j.laa.2016.05.011](https://doi.org/10.1016/j.laa.2016.05.011). URL: <https://arxiv.org/abs/1510.02850v2>.

*Commentary.*

The graph is the pinned Mathlib SimpleGraph.turanGraph n r; vertices i and j are adjacent exactly when their residues modulo r differ. Its adjacency matrix has complex entries zero and one. For n ≥ r > 0 this is a complete graph between r nonempty balanced parts. The balanced_relabel bridge uses Finpartition.IsEquipartition.exists_partPreservingEquiv to represent every balanced finite partition by a simultaneous relabeling. The converse in modulus_partition_iff uses the graph's Turán-maximal partition, including its cardinality and equipartition laws.

**Definition 1.3 (The source equality condition).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{isTuranModulus}\left(r, A\right) = \exists (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \operatorname{ofReal}\left(\Vert A\left(i, j\right)\Vert \right) = \operatorname{turanMatrix}\left(n, r, e\left(i\right), e\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.isTuranModulus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Nikiforov (2016). *Beyond graph energy: norms of graphs and matrices*. DOI: [10.1016/j.laa.2016.05.011](https://doi.org/10.1016/j.laa.2016.05.011). URL: <https://arxiv.org/abs/1510.02850v2>.

*Commentary.*

The norm of each complex entry is embedded back into the complex numbers. A single permutation acts on both indices. The modulus_partition_iff bridge identifies this condition with adjacency across the parts of an arbitrary equipartition into r nonempty parts. Permuting vertices preserves the Schatten norm: schatten_reindex compares column-Gram characteristic polynomials and the ordered Hermitian eigenvalue lists, so balanced_norm also proves that the comparison graph's labeling is immaterial.

**Definition 1.4 (Conjecture 4.42 in full).**

$$\operatorname{claim} = \forall (p: \mathbb{R}), (2 < p) \Rightarrow (\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), (2 \le r) \Rightarrow ((r \le n) \Rightarrow (\forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \Vert A\left(i, j\right)\Vert  \le 1) \Rightarrow ((\operatorname{rPartite}\left(r, A\right)) \Rightarrow ((\operatorname{S}\left(p, A\right) \le \operatorname{S}\left(p, \operatorname{turanMatrix}\left(n, r\right)\right)) \land ((\operatorname{S}\left(p, A\right) = \operatorname{S}\left(p, \operatorname{turanMatrix}\left(n, r\right)\right)) \Leftrightarrow (\operatorname{isTuranModulus}\left(r, A\right))))))))$$

*Formalization.* `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.claim` (`✓ std3`).

*Citation.* Vladimir Nikiforov (2016). *Beyond graph energy: norms of graphs and matrices*. DOI: [10.1016/j.laa.2016.05.011](https://doi.org/10.1016/j.laa.2016.05.011). URL: <https://arxiv.org/abs/1510.02850v2>.

*Commentary.*

Nikiforov, Beyond graph energy: norms of graphs and matrices, arXiv:1510.02850v2, §4.5.1, Conjecture 4.42: Let p > 2, n ≥ r ≥ 2, and let A be an n × n complex matrix with max-norm at most one. If A is r-partite, its Schatten p-norm is at most that of T_r(n). Equality holds if and only if the entrywise absolute-value matrix is the adjacency matrix of T_r(n).

The formula retains the universal real exponent, both integer inequalities, all complex square matrices, every entry bound, multipartiteness, the upper bound and both directions of the equality criterion. Symmetry, Hermitianity and nonnegativity are absent. For n ≥ r ≥ 2 the index set is nonempty; max_bound_iff equates the pointwise bound with the maximum over all pairs of indices. Here S(p,A) denotes the public UpperBranchReduction.schattenNorm p A, the p-th root of the finite sum of singular-value p-th powers. Its schattenPow_eq_columnGram bridge includes zero eigenvalues. The source_equality bridge transports the sufficiency direction to any balanced partition without changing the matrix domain or the exponent.

**Theorem 1.5 (A three by three counterexample).**

$$\neg (\forall (p: \mathbb{R}), (2 < p) \Rightarrow (\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), (2 \le r) \Rightarrow ((r \le n) \Rightarrow (\forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \Vert A\left(i, j\right)\Vert  \le 1) \Rightarrow ((\operatorname{rPartite}\left(r, A\right)) \Rightarrow ((\operatorname{S}\left(p, A\right) \le \operatorname{S}\left(p, \operatorname{turanMatrix}\left(n, r\right)\right)) \land ((\operatorname{S}\left(p, A\right) = \operatorname{S}\left(p, \operatorname{turanMatrix}\left(n, r\right)\right)) \Leftrightarrow (\operatorname{isTuranModulus}\left(r, A\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nikiforov-2016-conjecture-4-42` (refuted) by `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nikiforov-2016-conjecture-4-42","declaration_gid":"D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Nikiforov (2016). *Beyond graph energy: norms of graphs and matrices*. DOI: [10.1016/j.laa.2016.05.011](https://doi.org/10.1016/j.laa.2016.05.011). URL: <https://arxiv.org/abs/1510.02850v2>.

*Commentary.*

Take p = 6, n = r = 3 and A = [[0,1,1],[-1,0,1],[-1,-1,0]]. Singleton parts certify multipartiteness and the identity permutation identifies its entrywise modulus with T_3(3). The public schattenPow_trace formula reduces the sixth-power sum to Re(trace((Aᴴ A)^3)), using cfc_pow_id on the Hermitian column Gram matrix. Exact finite arithmetic gives 54 for A and 66 for T_3(3). Equality sufficiency would equate their Schatten 6-norms; schattenNorm_rpow would then give 54 = 66.

The result negates the entire universal conjunction, through failure of equality sufficiency. The upper-bound-only proposition remains unresolved by this argument. No claim is made about a p = 3 obstruction, dimension minimality or a Hadamard family. The source provides the conjecture; the counterexample and formal derivation are repository results. The bounded literature screen does not establish global novelty.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.claim`
- Truth anchor: `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.isTuranModulus`
- Truth anchor: `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.rPartite`
- Truth anchor: `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.result`
- Truth anchor: `D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.turanMatrix`
- Dependency: [D5/S3/Quantum/NormCompression/SchattenContinuity](../NormCompression/SchattenContinuity.md)
