# Two-conformal rigidity does not imply one-conformal rigidity

## Abstract

The graph K5 with one edge removed is two-conformally rigid and is not one-conformally rigid.

**Definition 1.1 (Undirected edges counted once).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Edge}\left(G\right) = \{e : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right) \mid (e.1 < e.2) \land (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, e.1, e.2\right))\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.Edge` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

The Introduction, printed page 1, states: “Let G = (V,E) be a simple, connected, undirected graph on n vertices with at least one edge, and let A := A(G) denote its adjacency matrix.” Vertices are Fin n; each undirected edge is represented by its two endpoints in strictly increasing order. The subtype retains exactly the adjacent pairs.

**Definition 1.2 (Uniform edge weights).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall e \in \operatorname{Edge}\left(G\right),\; \operatorname{uniform}\left(G, e\right) = 1$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.uniform` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

The Introduction, printed page 2, states: “For the remainder of the text, we shall use 1 to denote the all-ones vector with the appropriate dimension, which will be clear from the context.” Every edge has weight one.

**Definition 1.3 (The closed simplex of admissible weights).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; (\operatorname{ValidWeight}\left(G, w\right)) \Leftrightarrow ((\forall e \in \operatorname{Edge}\left(G\right),\; 0 \le w\left(e\right)) \land (\sum_{e : \operatorname{Edge}\left(G\right)} (w\left(e\right)) = (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Edge}\left(G\right)\right) : \mathrm{Real})))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.ValidWeight` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

The Introduction, printed page 2, states: “The simplex of valid edge weights is thus defined as Δ_E := {w ∈ ℝ^E: w ≥ 0, 1^T w = |E|}.” Zero edge weights are included. The natural edge cardinality is coerced to Real.

**Definition 1.4 (Increasing eigenvalues of the real Laplacian).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall h \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{Matrix}.\operatorname{of}\left((\lambda (row : \operatorname{Fin}\left(n\right)) (col : \operatorname{Fin}\left(n\right)) \mapsto \sum_{e : \operatorname{Edge}\left(G\right)} (w\left(e\right) \cdot (\operatorname{ite}\left(row = (\operatorname{val}\left(e\right)).1, 1, 0\right) - \operatorname{ite}\left(row = (\operatorname{val}\left(e\right)).2, 1, 0\right)) \cdot (\operatorname{ite}\left(col = (\operatorname{val}\left(e\right)).1, 1, 0\right) - \operatorname{ite}\left(col = (\operatorname{val}\left(e\right)).2, 1, 0\right))))\right)\right),\; \forall e \in (n = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Fin}\left(n\right)\right)),\; \operatorname{eigenvalue}\left(G, w, i\right) = h.\operatorname{eigenvalues}_{0}\left(\operatorname{Fin}.\operatorname{cast}\left(e, i.\operatorname{rev}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.eigenvalue` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

The Introduction, printed page 1, states: “For an edge ab ∈ E, we define z_ab := e_a − e_b, where e_a ∈ ℝ^V denotes the a-th canonical basis vector, and we also let L_ab := z_ab z_ab^T.” Equation (1) is ℒ(w) := ∑_{ab∈E} w_ab L_ab = ∑_{ab∈E} w_ab z_ab z_ab^T. Both endpoint differences are expanded in the matrix entries. The Introduction, printed page 2, states: “We shall order the eigenvalues of ℒ(w) as 0 = λ₁(w) ≤ λ₂(w) ≤ … ≤ λₙ(w).” The formula reverses the nonincreasing eigenvalues₀ order and uses zero-based indices. The proof h states that the real matrix is Hermitian; e identifies the two finite index sizes. Proof irrelevance makes their choices immaterial. Nonnegative normalized weights are required when using the source's positivity and zero-eigenvalue assertions.

**Definition 1.5 (The smallest nontrivial eigenvalue sum).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; \forall k \in \mathrm{Nat},\; \operatorname{smallestSum}\left(G, w, k\right) = \sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left((0 < \operatorname{val}\left(i\right)) \land (\operatorname{val}\left(i\right) \le k), \operatorname{eigenvalue}\left(G, w, i\right), 0\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.smallestSum` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

Definition 1.2, printed pages 2–3, states: “Let S_k(w) and s_k(w) denote the sum of the k largest and k smallest nontrivial eigenvalues of ℒ(w), respectively, for some k ∈ [n−1].” The Introduction specifies: “By the nontrivial eigenvalues of ℒ(w), we shall mean λ₂(w),…,λₙ(w).” Thus indices 1 through k are included, retaining any additional zero eigenvalues.

**Definition 1.6 (The largest eigenvalue sum).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; \forall k \in \mathrm{Nat},\; \operatorname{largestSum}\left(G, w, k\right) = \sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(n \le \operatorname{val}\left(i\right) + k, \operatorname{eigenvalue}\left(G, w, i\right), 0\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.largestSum` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

Definition 1.2, printed pages 2–3, states: “Let S_k(w) and s_k(w) denote the sum of the k largest and k smallest nontrivial eigenvalues of ℒ(w), respectively, for some k ∈ [n−1].” The cutoff n ≤ val i + k avoids natural-number subtraction. The rigidity predicate restricts k to 1 ≤ k < n.

**Definition 1.7 (Both extremal sums at the same uniform weights).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall k \in \mathrm{Nat},\; (\operatorname{KConformallyRigid}\left(G, k\right)) \Leftrightarrow ((1 \le k) \land ((k < n) \land (\forall w \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; \forall u \in \operatorname{Edge}\left(G\right) \to \mathrm{Real},\; (\operatorname{ValidWeight}\left(G, w\right)) \Rightarrow ((\operatorname{ValidWeight}\left(G, u\right)) \Rightarrow ((\operatorname{smallestSum}\left(G, w, k\right) \le \operatorname{smallestSum}\left(G, \operatorname{uniform}\left(G\right), k\right)) \land (\operatorname{largestSum}\left(G, \operatorname{uniform}\left(G\right), k\right) \le \operatorname{largestSum}\left(G, u, k\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.KConformallyRigid` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

Definition 1.2, printed pages 2–3, states: “We say that G is k-conformally rigid if, for any w,w′ ∈ Δ_E,” followed by s_k(w) ≤ s_k(1) and S_k(1) ≤ S_k(w′). The independent second weighting is called u here. The range 1 ≤ k < n and both simplex premises are explicit.

**Definition 1.8 (The Section 9 existence question).**

$$(\operatorname{claim}) \Leftrightarrow (\exists n \in \mathrm{Nat},\; \exists G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \land ((\exists a \in \operatorname{Fin}\left(n\right),\; \exists b \in \operatorname{Fin}\left(n\right),\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, a, b\right)) \land ((\operatorname{KConformallyRigid}\left(G, 2\right)) \land (\neg (\operatorname{KConformallyRigid}\left(G, 1\right))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.claim` (`✓ std3`).

*Citation.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

Section 9, printed page 20, asks: “Are there graphs that are 2-conformally rigid but not 1-conformally rigid?” The formula asks for a finite simple connected graph with an actual edge, satisfying precisely those two properties. The graph and its order are existential conclusions.

**Theorem 1.9 (An affirmative answer on five vertices).**

$$\exists n \in \mathrm{Nat},\; \exists G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \land ((\exists a \in \operatorname{Fin}\left(n\right),\; \exists b \in \operatorname{Fin}\left(n\right),\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, a, b\right)) \land ((\operatorname{KConformallyRigid}\left(G, 2\right)) \land (\neg (\operatorname{KConformallyRigid}\left(G, 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-acg2605cr` (proved) by `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-acg2605cr","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Henrique Assumpção, Gabriel Coutinho and Chris Godsil (2026). *Total Conformal Rigidity in Graphs*. DOI: [10.48550/arXiv.2605.08508](https://doi.org/10.48550/arXiv.2605.08508). URL: <https://arxiv.org/abs/2605.08508v2>.

*Commentary.*

Take K5 with the edge {0,1} removed. It has nine edges and a universal vertex. Its uniform increasing spectrum is [0,3,5,5,5]. A real symmetric matrix with decreasing spectrum [8/9,5/9,5/9,0,0] has edge quadratic value 10/9 on every edge. Consequently its trace pairing with every normalized weighted Laplacian is 10. The von Neumann trace inequality and eigenvalue monotonicity bound this pairing by the two largest eigenvalues. The Laplacian has trace 18 and is positive semidefinite, giving smallestSum ≤ 8 and 10 ≤ largestSum throughout the closed simplex; uniform weights attain both. Assigning 6/5 to the six edges meeting {0,1} and 3/5 to the other three gives increasing spectrum [0,18/5,21/5,21/5,6]. Its second eigenvalue exceeds the uniform value 3, so one-conformal rigidity fails. The trace-pairing estimate itself applies to every real Hermitian five by five matrix, without assuming that tested matrix is positive semidefinite.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.Edge`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.KConformallyRigid`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.ValidWeight`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.largestSum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.smallestSum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.uniform`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation](FiedlerResistanceInvariantWeightsRefutation.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer](FiedlerResistanceK2mOptimizer.md)
- Dependency: [D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths](../../StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.md)
