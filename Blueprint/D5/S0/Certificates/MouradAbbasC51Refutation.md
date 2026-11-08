# Mourad–Abbas Conjecture 5.1

## Abstract

An infinite family of positive-trace block matrices refutes Mourad–Abbas Conjecture 5.1.

**Definition 1.1 (The full symmetric polytope).**

$$\forall n \in \mathbb{N},\; DeltaSymm\left(n\right) = \{A:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right) \mid (A \in doublyStochastic\left(\mathbb{R}, Fin\left(n\right)\right)) \land (\operatorname{Matrix.IsSymm}\left(A\right))\}$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.DeltaSymm` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 1: ‘The set of all n×n doubly-stochastic matrices is denoted by Δ_n and the set of all the symmetric elements in Δ_n will be denoted by Δ^s_n.’ The entries are real, indexed by Fin n. doublyStochastic requires nonnegative entries and row and column sums equal to one.

**Definition 1.2 (A trace slice).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{R},\; traceSlice\left(n, a\right) = \{A:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right) \mid (A \in DeltaSymm\left(n\right)) \land (\operatorname{Matrix.trace}\left(A\right) = a)\}$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.traceSlice` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 1: ‘For 0≤a≤n, denote by Δ^s_n(a) to be the set of all elements of Δ^s_n with trace a.’ The set expression is defined for every real a; the inequalities on a occur in the conjecture.

**Definition 1.3 (The matrix C).**

$$\forall n \in \mathbb{N},\; C\left(n\right) = \operatorname{fun} (i:Fin\left(n\right)) \mapsto \operatorname{fun} (j:Fin\left(n\right)) \mapsto ite\left(i = j, 0, \frac{1}{(n:\mathbb{R})-1}\right)$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.C` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 1: ‘The third is C_n which denotes the n×n matrix whose diagonal entries are all zeroes and whose off-diagonal entries are equal to 1/(n−1) (here for n≥2).’ Division and subtraction in this formula are real operations; the order n is coerced to ℝ before subtraction.

**Definition 1.4 (Permutation similarity).**

$$\forall n \in \mathbb{N},\; \forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; \forall B \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (IsPermutationallySimilar\left(A, B\right)) \Leftrightarrow (\exists s \in \operatorname{Equiv.Perm}\left(Fin\left(n\right)\right),\; B = \operatorname{Matrix.transpose}\left(\operatorname{Equiv.Perm.permMatrix}\left(\mathbb{R}, s\right)\right) \cdot A \cdot \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{R}, s\right))$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.IsPermutationallySimilar` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 2: ‘Two matrices A and B are said to be permutationally similar if B=PᵀAP for some permutation matrix P.’ The permutation acts on Fin n; its real permutation matrix is Equiv.Perm.permMatrix.

**Definition 1.5 (Determination by spectra).**

$$\forall n \in \mathbb{N},\; \forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (IsDS\left(A\right)) \Leftrightarrow ((A \in DeltaSymm\left(n\right)) \land (\forall B \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (B \in DeltaSymm\left(n\right)) \Rightarrow ((IsConj\left(A, B\right)) \Rightarrow (IsPermutationallySimilar\left(A, B\right)))))$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.IsDS` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 2: ‘If in addition A is symmetric then A is said to be DS in Δ_n^s if B∈Δ_n^s is similar to A implies that B is permutationally similar to A.’ IsConj is ordinary similarity by an invertible real matrix. B ranges over every real symmetric doubly stochastic matrix of the same order.

**Definition 1.6 (Conjecture 5.1).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall a \in \mathbb{R},\; (0 < a) \Rightarrow ((a \le (n:\mathbb{R})) \Rightarrow (\forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (A \in traceSlice\left(n, a\right)) \Rightarrow ((IsDS\left(A\right)) \Rightarrow ((A \in segment\left(\mathbb{R}, (1:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), C\left(n\right)\right)) \lor (\exists P \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (P \in \operatorname{Set.extremePoints}\left(\mathbb{R}, DeltaSymm\left(n\right)\right)) \land ((A \in segment\left(\mathbb{R}, (1:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), P\right)) \lor (A \in segment\left(\mathbb{R}, C\left(n\right), P\right))))))))))$$

*Formalization.* `D5/S0/Certificates/MouradAbbasC51Refutation.claim` (`✓ std3`).

*Citation.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

Page 10, Conjecture 5.1: ‘For 0<a≤n, the only elements of Δ_n^s(a) that are DS in Δ_n^s are points on the line segments [I_n,C_n], [I_n,P] and [C_n,P] where P is a vertex of Δ_n^s.’ The word ‘only’ gives the necessary condition displayed here. The identity is the matrix 1, n≥2, all segments are closed, and extremePoints refers to the full symmetric polytope rather than its trace slice.

**Theorem 1.7 (Conjecture 5.1 is false).**

$$\neg (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall a \in \mathbb{R},\; (0 < a) \Rightarrow ((a \le (n:\mathbb{R})) \Rightarrow (\forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (A \in traceSlice\left(n, a\right)) \Rightarrow ((IsDS\left(A\right)) \Rightarrow ((A \in segment\left(\mathbb{R}, (1:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), C\left(n\right)\right)) \lor (\exists P \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right),\; (P \in \operatorname{Set.extremePoints}\left(\mathbb{R}, DeltaSymm\left(n\right)\right)) \land ((A \in segment\left(\mathbb{R}, (1:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{R}\right)), P\right)) \lor (A \in segment\left(\mathbb{R}, C\left(n\right), P\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MouradAbbasC51Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ma2013-dsspectral` (refuted) by `D5/S0/Certificates/MouradAbbasC51Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ma2013-dsspectral","declaration_gid":"D5/S0/Certificates/MouradAbbasC51Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bassam Mourad; Hassan Abbas (2013). *On the symmetric doubly stochastic matrices that are determined by their spectra*. DOI: [10.48550/arXiv.1310.1273](https://doi.org/10.48550/arXiv.1310.1273). URL: <https://arxiv.org/abs/1310.1273v1>.

*Commentary.*

For every k≥4, r≥2 and real 0<t<1/k², take r diagonal blocks of size k with diagonal t and off-diagonal (1−t)/(k−1), and zero entries between blocks. Put λ=(kt−1)/(k−1). For any similar symmetric doubly stochastic matrix B, the matrix (B−λ1)/(1−λ) is a nonnegative stochastic idempotent. A weighted sum of squared row differences shows that positive entries join equal rows. The support-size bound and trace then force equal blocks of size k, giving one permutation that aligns B with the original matrix. A cross-block zero excludes the segment involving C, while a four-cycle perturbation excludes every extreme point on an identity ray. The final contradiction takes k=4, r=2, t=1/40, hence order 8 and trace 1/5. The order-three classification and the two other questions in Section 5 are unaffected; the version restricted to irreducible matrices remains open.

## References

- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.C`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.DeltaSymm`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.IsDS`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.IsPermutationallySimilar`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.claim`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.result`
- Truth anchor: `D5/S0/Certificates/MouradAbbasC51Refutation.traceSlice`
