# Q-transversal representability

## Abstract

Every q-transversal rank function has a representation over a finite field extension.

**Definition 1.1 (IsPartialQTransversal).**

$$\forall (F: Type), [Field\left(F\right)] \forall (m: \mathbb{N}), \forall (k: \mathbb{N}), \forall (X: Fin\left(k\right) \to Submodule\left(F, Fin\left(m\right) \to F\right)), \forall (T: Submodule\left(F, Fin\left(m\right) \to F\right)), (IsPartialQTransversal\left(X, T\right)) \Leftrightarrow (\forall (s: Finset\left(Fin\left(m\right) \to F\right)), (LinearIndependent\left(F, (b: s \mapsto (b: Fin\left(m\right) \to F))\right)) \Rightarrow ((\operatorname{Submodule}.\operatorname{span}\left(F, (s: Set\left(Fin\left(m\right) \to F\right))\right) = T) \Rightarrow (\exists (f: s \to Fin\left(k\right)), (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \land (\forall (b: s), \neg ((b: Fin\left(m\right) \to F) \in X\left(f\left(b\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.IsPartialQTransversal` (`✓ std3`).

*Citation.* M. Saaltink (2025). *A theory of q-transversals*. DOI: [10.48550/arXiv.2503.12201](https://doi.org/10.48550/arXiv.2503.12201). URL: <https://arxiv.org/abs/2503.12201v1>.

*Commentary.*

Definition 14, page 8: “Let a vector space V be given, together with a family X = (X₁, …, X_n) of subspaces of V.” “A partial q-transversal is a dimension n subspace T where every vector basis of T is a partial avoiding transversal of X.” Here the family has k indices and the ambient space is Fin m → F. As in Theorems 15 and 18, partial q-transversals may have any dimension. A vector basis is a finite linearly independent set spanning T, and an avoiding injection sends each basis vector to an index of a subspace not containing it.

**Definition 1.2 (qTransversalRank).**

$$\forall (F: Type), [Field\left(F\right)] \forall (m: \mathbb{N}), \forall (k: \mathbb{N}), \forall (X: Fin\left(k\right) \to Submodule\left(F, Fin\left(m\right) \to F\right)), \forall (U: Submodule\left(F, Fin\left(m\right) \to F\right)), qTransversalRank\left(X, U\right) = sSup\left(\{d \mid \exists (T: Submodule\left(F, Fin\left(m\right) \to F\right)), (T \le U) \land ((IsPartialQTransversal\left(X, T\right)) \land (\operatorname{Module}.\operatorname{finrank}\left(F, T\right) = d))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.qTransversalRank` (`✓ std3`).

*Citation.* M. Saaltink (2025). *A theory of q-transversals*. DOI: [10.48550/arXiv.2503.12201](https://doi.org/10.48550/arXiv.2503.12201). URL: <https://arxiv.org/abs/2503.12201v1>.

*Commentary.*

Theorem 15, page 8: “Given a family X = (X_i : i ∈ I) where each X_i is a subspace of V, the set of partial q-transversals of X form the independent subspaces of a q-matroid.” The rank of U is the supremum of the dimensions of partial q-transversals contained in U. The set of dimensions is nonempty and bounded by Module.finrank F U.

**Definition 1.3 (representedRank).**

$$\forall (F: Type), [Field\left(F\right)] \forall (K: Type), [Field\left(K\right)] [Algebra\left(F, K\right)] \forall (r: \mathbb{N}), \forall (m: \mathbb{N}), \forall (G: Matrix\left(Fin\left(r\right), Fin\left(m\right), K\right)), \forall (U: Submodule\left(F, Fin\left(m\right) \to F\right)), representedRank\left(G, U\right) = \operatorname{Matrix}.\operatorname{rank}\left(G \cdot \operatorname{Matrix}.\operatorname{of}\left((j: Fin\left(m\right) \mapsto (i: Fin\left(\operatorname{Module}.\operatorname{finrank}\left(F, U\right)\right) \mapsto algebraMap\left(F, K\right)\left((\operatorname{Module}.\operatorname{finBasis}\left(F, U, i\right): Fin\left(m\right) \to F)\left(j\right)\right)))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.representedRank` (`✓ std3`).

*Citation.* M. Saaltink (2025). *A theory of q-transversals*. DOI: [10.48550/arXiv.2503.12201](https://doi.org/10.48550/arXiv.2503.12201). URL: <https://arxiv.org/abs/2503.12201v1>.

*Commentary.*

Section 3.2, page 7: “Given some n × m matrix G over a field K extending F_q, we can define the q-matroid represented by G as follows: if a subspace of F_q^m is the row space of matrix X, then its rank in the matroid is the rank of matrix G Xᵀ.” The columns of the second factor are the vectors of Module.finBasis F U, with each coordinate mapped to K by algebraMap. This is the transpose of the matrix whose rows form that basis.

**Definition 1.4 (claim).**

$$(claim) \Leftrightarrow (\forall (F: Type), [Field\left(F\right)] [Fintype\left(F\right)] \forall (m: \mathbb{N}), \forall (k: \mathbb{N}), \forall (X: Fin\left(k\right) \to Submodule\left(F, Fin\left(m\right) \to F\right)), \exists (K: Type), [Field\left(K\right)] [Algebra\left(F, K\right)] [FiniteDimensional\left(F, K\right)] \exists (r: \mathbb{N}), \exists (G: Matrix\left(Fin\left(r\right), Fin\left(m\right), K\right)), \forall (U: Submodule\left(F, Fin\left(m\right) \to F\right)), representedRank\left(G, U\right) = qTransversalRank\left(X, U\right))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.claim` (`✓ std3`).

*Citation.* M. Saaltink (2025). *A theory of q-transversals*. DOI: [10.48550/arXiv.2503.12201](https://doi.org/10.48550/arXiv.2503.12201). URL: <https://arxiv.org/abs/2503.12201v1>.

*Commentary.*

Section 4.2, page 14: “Conjecture 3. All q-transversal matroids are representable.” The field F is arbitrary and finite, X is an arbitrary finite family of subspaces, and the same G represents the ranks of every U. The field extension K is finite dimensional over F.

**Theorem 1.5 (result).**

$$\forall (F: Type), [Field\left(F\right)] [Fintype\left(F\right)] \forall (m: \mathbb{N}), \forall (k: \mathbb{N}), \forall (X: Fin\left(k\right) \to Submodule\left(F, Fin\left(m\right) \to F\right)), \exists (K: Type), [Field\left(K\right)] [Algebra\left(F, K\right)] [FiniteDimensional\left(F, K\right)] \exists (r: \mathbb{N}), \exists (G: Matrix\left(Fin\left(r\right), Fin\left(m\right), K\right)), \forall (U: Submodule\left(F, Fin\left(m\right) \to F\right)), representedRank\left(G, U\right) = qTransversalRank\left(X, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Saaltink (2025). *A theory of q-transversals*. DOI: [10.48550/arXiv.2503.12201](https://doi.org/10.48550/arXiv.2503.12201). URL: <https://arxiv.org/abs/2503.12201v1>.

*Commentary.*

One finite extension preserves a nonzero generic minor for every partial q-transversal. The rows are functionals vanishing on the corresponding subspaces. A determinant support matching gives the converse implication, and independent columns yield a subspace attaining the represented rank. Consequently the two rank functions agree on every subspace. The proof gives a finite extension; no sharp formula for its degree is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.IsPartialQTransversal`
- Truth anchor: `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.qTransversalRank`
- Truth anchor: `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.representedRank`
- Truth anchor: `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.result`
- Dependency: [D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian](../../Arith/DiophantineApproximation/GeneralizedWronskian.md)
- Dependency: [D5/S3/Combinatorics/Matroids/LinearRado](LinearRado.md)
