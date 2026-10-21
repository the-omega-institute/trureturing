# Graph quantum magic squares on C5

## Abstract

The C5 graph quantum magic squares strictly contain the matrix convex hull of graph quantum permutation matrices.

**Definition 1.1 (IsQMS).**

$$\forall (n : \mathbb{N}) , (\forall (s : \mathbb{N}) , (\forall (A : Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)) , (IsQMS\left(A\right) = ((\forall (i : Fin\left(n\right)) , (\forall (j : Fin\left(n\right)) , ((A\left(i, j\right)).\operatorname{PosSemidef}))) \land ((\forall (i : Fin\left(n\right)) , (\sum k : Fin\left(n\right) , A\left(i, k\right) = 1)) \land (\forall (j : Fin\left(n\right)) , (\sum k : Fin\left(n\right) , A\left(k, j\right) = 1)))))))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsQMS` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 2.1, page 4: “A quantum magic square of external size n and internal size s is a block matrix” with “Aij ∈ Psds(ℂ),” “such that, for every i, j,” the displayed row and column sums equal Is. External indices use Fin n, internal indices use Fin s, and the identity is the matrix 1. The encoding includes the zero-size level, which consists of the unique empty matrices.

**Definition 1.2 (IsGraphQMS).**

$$\forall (n : \mathbb{N}) , (\forall (s : \mathbb{N}) , (\forall (G : SimpleGraph\left(Fin\left(n\right)\right)) , ([DecidableRel\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] , \forall (X : Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)) , (IsGraphQMS\left(G, X\right) = ((IsQMS\left(X\right)) \land (\forall (i : Fin\left(n\right)) , (\forall (j : Fin\left(n\right)) , (\sum k \in \operatorname{Finset}.\operatorname{filter}\left((fun (k : Fin\left(n\right)) \mapsto \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, k, j\right)), \operatorname{Finset}.\operatorname{univ}\right) , X\left(i, k\right) = \sum k \in \operatorname{Finset}.\operatorname{filter}\left((fun (k : Fin\left(n\right)) \mapsto \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, k, i\right)), \operatorname{Finset}.\operatorname{univ}\right) , X\left(k, j\right)))))))))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsGraphQMS` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 3.1, page 8: “A quantum magic square X = (Xij)1≤i,j≤n ∈ Matn(Hers(ℂ)) is called a graph quantum magic square if” X(Is ⊗ AΓ) = (Is ⊗ AΓ)X. “This commutation condition can be written in terms of internal blocks as” Σk∼j Xik = Σk∼i Xkj “∀ i, j ∈ {1, . . . , n},” “where k ∼ j means that vertices k and j are adjacent in Γ.” The formula uses exactly these block sums, with vertices indexed from zero.

**Definition 1.3 (M).**

$$\forall (n : \mathbb{N}) , (\forall (G : SimpleGraph\left(Fin\left(n\right)\right)) , ([DecidableRel\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] , \forall (s : \mathbb{N}) , (M\left(G, s\right) = \{X : Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right) \mid IsGraphQMS\left(G, X\right)\})))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.M` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 3.2, pages 8–9: “Let Γ be a finite graph with adjacency matrix AΓ, and let s ≥ 1. We define the following sets of graph quantum magic squares:” M^(Γ)s := { X ∈ M^(n)s | X(Is ⊗ AΓ) = (Is ⊗ AΓ)X }. The predicate IsGraphQMS spells out this condition blockwise. The natural-number levels also include size zero.

**Definition 1.4 (P).**

$$\forall (n : \mathbb{N}) , (\forall (G : SimpleGraph\left(Fin\left(n\right)\right)) , ([DecidableRel\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] , \forall (s : \mathbb{N}) , (P\left(G, s\right) = \{X : Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right) \mid (IsGraphQMS\left(G, X\right)) \land (\forall (i : Fin\left(n\right)) , (\forall (j : Fin\left(n\right)) , ((X\left(i, j\right) \cdot X\left(i, j\right) = X\left(i, j\right)) \land (\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\left(i, j\right)\right) = X\left(i, j\right)))))\})))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.P` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 3.2, page 9 defines P^(Γ)s := { X ∈ M^(Γ)s | Xij² = Xij = Xij* for all i, j }. Idempotence and conjugate-transpose symmetry are the two displayed conjuncts. The graph is a SimpleGraph on Fin n.

**Definition 1.5 (IsMatrixConvex).**

$$\forall (n : \mathbb{N}) , (\forall (R : (s : \mathbb{N}) \to Set\left(Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)\right)) , (IsMatrixConvex\left(R\right) = (\forall (k : \mathbb{N}) , (\forall (sz : Fin\left(k\right) \to \mathbb{N}) , (\forall (A : (l : Fin\left(k\right)) \to Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(sz\left(l\right)\right), Fin\left(sz\left(l\right)\right), \mathbb{C}\right)\right)) , ((\forall (l : Fin\left(k\right)) , (A\left(l\right) \in R\left(sz\left(l\right)\right))) \to (\forall (t : \mathbb{N}) , (\forall (V : (l : Fin\left(k\right)) \to Matrix\left(Fin\left(sz\left(l\right)\right), Fin\left(t\right), \mathbb{C}\right)) , ((\sum l : Fin\left(k\right) , \operatorname{Matrix}.\operatorname{conjTranspose}\left(V\left(l\right)\right) \cdot V\left(l\right) = 1) \to ((fun (i : Fin\left(n\right)) \mapsto fun (j : Fin\left(n\right)) \mapsto \sum l : Fin\left(k\right) , \operatorname{Matrix}.\operatorname{conjTranspose}\left(V\left(l\right)\right) \cdot A\left(l, i, j\right) \cdot V\left(l\right)) \in R\left(t\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsMatrixConvex` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 2.3, page 5: “We say that R is matrix convex if” the normalized blockwise sums displayed there belong to Rt. “Here the conjugation acts blockwise” and “Equivalently, we say that R is closed under matrix-valued convex combinations.” A finite family is indexed by Fin k; sz gives each input size, and V l has sz l rows and t columns. Conjugate transposes and products are matrix operations.

**Definition 1.6 (mconv).**

$$\forall (n : \mathbb{N}) , (\forall (S : (s : \mathbb{N}) \to Set\left(Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)\right)) , (\forall (s : \mathbb{N}) , (mconv\left(S, s\right) = \{X : Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right) \mid \forall (R : (s : \mathbb{N}) \to Set\left(Fin\left(n\right) \to \left(Fin\left(n\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)\right)) , ((IsMatrixConvex\left(R\right)) \to ((\forall (t : \mathbb{N}) , (S\left(t\right) \subseteq R\left(t\right))) \to (X \in R\left(s\right))))\})))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.mconv` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Definition 2.3, page 5: “For a subset S ⊆ Matn(Hers(ℂ)), the matrix convex hull of S, denoted as mconv(S), is the smallest matrix convex set containing S.” The formula is membership in every matrix convex family containing S, at the same external size. It allows arbitrary finite input and output sizes.

**Definition 1.7 (claim).**

$$claim = ((\forall (s : \mathbb{N}) , (mconv\left(P\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right)\right), s\right) \subseteq M\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right), s\right))) \land (\exists (s : \mathbb{N}) , (\exists (X : Fin\left(5\right) \to \left(Fin\left(5\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)) , ((X \in M\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right), s\right)) \land (\neg (X \in mconv\left(P\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right)\right), s\right)))))))$$

*Formalization.* `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.claim` (`✓ std3`).

*Citation.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Question 1.3, page 3: “Given a graph Γ, does the matrix convex hull of its quantum permutation matrices P^(Γ) generate all graph quantum magic squares? That is, mconv(P^(Γ)) = M^(Γ)?” Section 4.1, page 20: “A natural class of candidates is vertex-transitive or symmetric graphs, such as the cycle C5, the Petersen graph, and, more generally, any k-regular graph with a large automorphism group.” The displayed proposition answers the question for SimpleGraph.cycleGraph 5: containment holds at every internal size, and some level contains an element outside the hull.

**Theorem 1.8 (Strict containment for C5).**

$$(\forall (s : \mathbb{N}) , (mconv\left(P\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right)\right), s\right) \subseteq M\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right), s\right))) \land (\exists (s : \mathbb{N}) , (\exists (X : Fin\left(5\right) \to \left(Fin\left(5\right) \to Matrix\left(Fin\left(s\right), Fin\left(s\right), \mathbb{C}\right)\right)) , ((X \in M\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right), s\right)) \land (\neg (X \in mconv\left(P\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(5\right)\right), s\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result` (`✓ std3`). ∎

*Resolves.* `Problems/la-piana-2025-c5-graph-quantum-magic-squares` (proved) by `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"la-piana-2025-c5-graph-quantum-magic-squares","declaration_gid":"D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Francesca La Piana (2025). *Graph Quantum Magic Squares and Free Spectrahedra*. DOI: [10.48550/arXiv.2512.08797](https://doi.org/10.48550/arXiv.2512.08797). URL: <https://arxiv.org/abs/2512.08797v3>.

*Commentary.*

Every graph quantum permutation matrix on C5 has commuting entries. Products of entries in its first two rows give positive families R and S with Xij = R(i−j) + S(i+j); the cycle recurrence extends this identity to all rows. This form is preserved by blockwise compression and finite sums. An internal-size-two graph quantum magic square has blocks (1/25) times [[5+a(i−j), b(i+j)], [b(i+j), 5−a(i−j)]], where a=(3,−3,0,0,0) and b=(4,−4,0,0,0). Four rank-one blocks force two R summands to vanish, contradicting their unequal top-left entries. Positivity and the row, column and graph relations are preserved by all normalized blockwise compressions, proving containment. Only C5 is asserted here.

## References

- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsGraphQMS`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsMatrixConvex`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.IsQMS`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.M`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.P`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.claim`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.mconv`
- Truth anchor: `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result`
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](Measurement/AntidistinguishabilityGram.md)
