# Star matrices force large orthostochastic dimension

## Abstract

Star matrices contradict an eventual upper bound of three on Gutkin's internal dimension.

Rows and columns are indexed by Fin n, with values 0 through n − 1; the first index is the row. This corresponds to the upper index in Gutkin's notation, whose lower index denotes the column. EuclideanSpace ℝ (Fin d) is the real d-dimensional Euclidean space. The set Matrix.doublyStochastic ℝ (Fin n) consists of real n by n matrices with nonnegative entries and every row and column summing to one.

**Definition 1.1 (Norms and two orthogonality systems).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (P: Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), (\forall (V: Fin\left(n\right) \to (Fin\left(n\right) \to (EuclideanSpace\left(\mathbb{R}, Fin\left(d\right)\right)))), ((IsGutkinLift\left(P, V\right)) \Leftrightarrow ((\forall (r: Fin\left(n\right)), (\forall (c: Fin\left(n\right)), (\left\lVert V\left(r, c\right) \right\rVert^{2} = P\left(r, c\right)))) \land ((\forall (j: Fin\left(n\right)), (\forall (k: Fin\left(n\right)), (\sum_{(r: Fin\left(n\right))} \langle V\left(r, j\right), V\left(r, k\right)\rangle = \begin{cases}1&j = k\\0&j \ne k\end{cases}))) \land (\forall (j: Fin\left(n\right)), (\forall (k: Fin\left(n\right)), (\sum_{(c: Fin\left(n\right))} \langle V\left(j, c\right), V\left(k, c\right)\rangle = \begin{cases}1&j = k\\0&j \ne k\end{cases})))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.IsGutkinLift` (`✓ std3`).

*Citation.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

Lemma 1, equations (1)–(2), and the definition of Iso and ν prescribe the two orthogonality systems and the entrywise squared norms. The sum over r is column orthogonality, and the sum over c is row orthogonality. Both systems are required here; their equivalence is not assumed. The right-hand side is one for equal indices and zero otherwise.

**Definition 1.2 (Real d-orthostochastic matrices).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (P: Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), ((IsOrthostochasticOfDim\left(d, P\right)) \Leftrightarrow ((P \in \operatorname{Matrix.doublyStochastic}\left(\mathbb{R}, Fin\left(n\right)\right)) \land (\exists (V: Fin\left(n\right) \to (Fin\left(n\right) \to (EuclideanSpace\left(\mathbb{R}, Fin\left(d\right)\right)))), (IsGutkinLift\left(P, V\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.IsOrthostochasticOfDim` (`✓ std3`).

*Citation.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

Definition 1 calls a bistochastic matrix P real d-orthostochastic when P = ν(V) for a vector-valued matrix V in Iso(ℝ,n,d). Thus bistochasticity is required together with a lift satisfying the norm equations and both orthogonality systems.

**Definition 1.3 (The infimum of the universal dimensions).**

$$\forall (n: \mathbb{N}), (dMin\left(n\right) = sInf\left(\{(d: \mathbb{N}) \mid \forall (P: Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), ((P \in \operatorname{Matrix.doublyStochastic}\left(\mathbb{R}, Fin\left(n\right)\right)) \Rightarrow (IsOrthostochasticOfDim\left(d, P\right)))\}\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.dMin` (`✓ std3`).

*Citation.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

Conjecture 1 defines d_min(n) as the smallest internal dimension for which every bistochastic n by n matrix is d-orthostochastic. The formula uses the infimum in ℕ of exactly that set of dimensions. A nonempty subset of ℕ contains its infimum; the infimum of the empty set in ℕ is zero.

**Definition 1.4 (Gutkin's eventual dimension bound).**

$$(claim) \Leftrightarrow (\exists (n0: \mathbb{N}), (\forall (n: \mathbb{N}), ((n0 \le n) \Rightarrow ((2 \le dMin\left(n\right)) \land (dMin\left(n\right) \le 3)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.claim` (`✓ std3`).

*Citation.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

Conjecture 1 asserts that there exists a threshold n₀ such that 2 ≤ d_min(n) ≤ 3 for every n ≥ n₀, over the real field.

**Definition 1.5 (A symmetric star matrix).**

$$\forall (n: \mathbb{N}), (\forall (r: Fin\left(n\right)), (\forall (c: Fin\left(n\right)), (starMatrix\left(n\right)\left(r, c\right) = \begin{cases}0&(\operatorname{Fin.val}\left(r\right) = 0) \land (\operatorname{Fin.val}\left(c\right) = 0)\\\frac{1}{((n - 1: \mathbb{N}): \mathbb{R})}&(\operatorname{Fin.val}\left(r\right) = 0) \land (\operatorname{Fin.val}\left(c\right) \ne 0)\\\frac{1}{((n - 1: \mathbb{N}): \mathbb{R})}&(\operatorname{Fin.val}\left(r\right) \ne 0) \land (\operatorname{Fin.val}\left(c\right) = 0)\\1 - \frac{1}{((n - 1: \mathbb{N}): \mathbb{R})}&(\operatorname{Fin.val}\left(r\right) \ne 0) \land ((\operatorname{Fin.val}\left(c\right) \ne 0) \land (r = c))\\0&(\operatorname{Fin.val}\left(r\right) \ne 0) \land ((\operatorname{Fin.val}\left(c\right) \ne 0) \land (r \ne c))\end{cases})))$$

*Formalization.* `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.starMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

For n ≥ 2, put a = 1/(n − 1). The central diagonal entry is zero, every edge from the central index 0 has weight a, and every other diagonal entry has weight 1 − a. All remaining entries vanish. This matrix tests the universal dimension bound in Gutkin's conjecture. The formula defines it for every natural n: the subtraction n − 1 is performed in ℕ before coercion to ℝ, and real division by zero is zero.

**Theorem 1.6 (The eventual dimension bound is false).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gutkin-2013-orthostochastic-dimension-refutation` (refuted) by `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gutkin-2013-orthostochastic-dimension-refutation","declaration_gid":"D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eugene Gutkin (2013). *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*. DOI: [10.1016/j.geomphys.2013.06.009](https://doi.org/10.1016/j.geomphys.2013.06.009). URL: <https://arxiv.org/abs/1301.2537v1>.

*Commentary.*

For n ≥ 2 let S = starMatrix(n) and a = 1/(n − 1). Its entries are S₀₀ = 0, S₀ⱼ = Sⱼ₀ = a for j ≠ 0, Sⱼⱼ = 1 − a for j ≠ 0, and zero elsewhere. They are nonnegative. Row 0 sums to (n − 1)a = 1; every other row sums to a + (1 − a) = 1. Symmetry gives the same column sums, so S is bistochastic.

Suppose V lifts S in ℝᵈ. Fix distinct nonzero columns j and k. For a row r ≠ 0, if r = j then Sᵣₖ = 0, while if r ≠ j then Sᵣⱼ = 0. The norm equations make the corresponding vector zero, so every cross term ⟨Vᵣⱼ,Vᵣₖ⟩ vanishes except possibly the term in row 0. Column orthogonality therefore gives ⟨V₀ⱼ,V₀ₖ⟩ = 0.

For each j ≠ 0 the norm equation gives ‖V₀ⱼ‖² = a > 0. The n − 1 vectors V₀ⱼ are thus nonzero and pairwise orthogonal. They are linearly independent in the d-dimensional real Euclidean space, which forces n − 1 ≤ d.

Assume the conjectured threshold n₀ exists and take n = max(n₀,5). Then 2 ≤ dMin(n) ≤ 3. The set defining dMin(n) cannot be empty, since its infimum would then be zero. Its natural-number infimum belongs to it, so S has a lift in dimension dMin(n). The dimension bound gives 4 ≤ n − 1 ≤ dMin(n), contradicting dMin(n) ≤ 3.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.IsGutkinLift`
- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.IsOrthostochasticOfDim`
- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.dMin`
- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.starMatrix`
