# The Mesh-Pattern Basis of the Even Permutations

## Abstract

Every mesh-pattern basis of the even permutations consists exactly of fully shaded odd permutations.

**Definition 1.1 (Mesh patterns).**

$$\forall k \in \mathbb{N},\; \forall p \in Equiv.Perm\left(\operatorname{Fin}\left(k\right)\right),\; \forall R \in \operatorname{Set}\left(\operatorname{Fin}\left(k + 1\right) \times \operatorname{Fin}\left(k + 1\right)\right),\; MeshPattern.mk\left(k, p, R\right) : MeshPattern$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.MeshPattern` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

Ulfarsson writes: "This inspired West [Wes90] to define barred patterns, but we will use the more expressive mesh patterns of Brändén and Claesson [BC11], which allow us to forbid letters from occupying certain regions in a pattern." (Section 2, page 3.) The structure has exactly the fields k : Nat, p : Equiv.Perm (Fin k), and R : Set (Fin (k + 1) × Fin (k + 1)); its constructor is displayed below. The permutation indices are zero-based; the cell coordinates range from 0 through k.

**Definition 1.2 (Occurrence of a mesh pattern).**

$$\forall P \in MeshPattern,\; \forall n \in \mathbb{N},\; \forall s \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{Occurs}\left(P, s\right)) \Leftrightarrow (\exists e \in \operatorname{OrderEmbedding}\left(\operatorname{Fin}\left(P.k\right), \operatorname{Fin}\left(n\right)\right),\; (\forall i \in \operatorname{Fin}\left(P.k\right),\; \forall j \in \operatorname{Fin}\left(P.k\right),\; (s\left(e\left(i\right)\right) < s\left(e\left(j\right)\right)) \Leftrightarrow (P.p\left(i\right) < P.p\left(j\right))) \land (\forall x \in \operatorname{Fin}\left(n\right),\; (\neg (x \in Set.range\left(e\right))) \Rightarrow (\forall c \in \operatorname{Fin}\left(P.k + 1\right) \times \operatorname{Fin}\left(P.k + 1\right),\; (c \in P.R) \Rightarrow (\neg ((\operatorname{val}\left(c.1\right) = Finset.card\left(Finset.filter\left((i : \operatorname{Fin}\left(P.k\right) \mapsto e\left(i\right) < x), (Finset.univ : \operatorname{Finset}\left(\operatorname{Fin}\left(P.k\right)\right))\right)\right)) \land (\operatorname{val}\left(c.2\right) = Finset.card\left(Finset.filter\left((i : \operatorname{Fin}\left(P.k\right) \mapsto s\left(e\left(i\right)\right) < s\left(x\right)), (Finset.univ : \operatorname{Finset}\left(\operatorname{Fin}\left(P.k\right)\right))\right)\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Occurs` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

Ulfarsson writes: "This inspired West [Wes90] to define barred patterns, but we will use the more expressive mesh patterns of Brändén and Claesson [BC11], which allow us to forbid letters from occupying certain regions in a pattern." (Section 2, page 3.) The selected positions form an order embedding e. Their values have the relative order of P.p. For an unselected point x, the two cardinalities count selected positions to its left and selected values below its value. Their pair must not be a shaded cell. The symbol s denotes the containing permutation σ.

**Definition 1.3 (Avoidance over all lengths).**

$$\forall P \in \operatorname{Set}\left(MeshPattern\right),\; \operatorname{Av}\left(P\right) = \{s : \Sigma (n : \mathbb{N}), Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right) \mid \forall q \in MeshPattern,\; (q \in P) \Rightarrow (\neg (\operatorname{Occurs}\left(q, s.2\right)))\}$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Av` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

"We let S denote the set of all permutations and Av(P) denote the permutations that avoid all the patterns in a set P." (Basic definitions, page 2.) The dependent sum records every length, including zero, together with its permutation.

**Definition 1.4 (A basis for a set of permutations).**

$$\forall A \in \operatorname{Set}\left(\Sigma (n : \mathbb{N}), Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall P \in \operatorname{Set}\left(MeshPattern\right),\; (\operatorname{IsBasis}\left(A, P\right)) \Leftrightarrow ((\operatorname{Av}\left(P\right) = A) \land (\forall Q \in \operatorname{Set}\left(MeshPattern\right),\; (Q \subseteq P) \Rightarrow ((\operatorname{Av}\left(Q\right) = A) \Rightarrow (Q = P))))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.IsBasis` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

"Given a set of permutations A, we call a set of patterns P a basis for A if A = Av(P), and no subset of P has this property." (Section 2, page 2.) IsBasis states the equality in the symmetric orientation Av P = A and expresses minimality by quantifying over every subset Q of P.

**Definition 1.5 (The even permutations).**

$$Alt = \{s : \Sigma (n : \mathbb{N}), Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right) \mid Equiv.Perm.sign\left(s.2\right) = 1\}$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Alt` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

"Let A be the union of the alternating subgroups" (Conjecture 2.4.2, page 8). Alt contains the permutations of every length whose sign is 1. Permutations of lengths zero and one are included.

**Definition 1.6 (Conjecture 2.4.2).**

$$(claim) \Leftrightarrow (\forall P \in \operatorname{Set}\left(MeshPattern\right),\; (\operatorname{IsBasis}\left(Alt, P\right)) \Rightarrow (P = \{q : MeshPattern \mid (q.R = Set.univ) \land (Equiv.Perm.sign\left(q.p\right) \ne 1)\}))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.claim` (`✓ std3`).

*Citation.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

"Let A be the union of the alternating subgroups, and let P be a basis of patterns such that A = Av(P). Then P = {(p, {0, …, n} × {0, …, n}) : p ∈ S_n ∖ A for some n}." (Conjecture 2.4.2, page 8.) Here A is Alt, p ∈ S_n is encoded by Equiv.Perm (Fin n), full shading is R = Set.univ, and exclusion from A is sign p ≠ 1.

**Theorem 1.7 (Conjecture 2.4.2 holds).**

$$\forall P \in \operatorname{Set}\left(MeshPattern\right),\; (\operatorname{IsBasis}\left(Alt, P\right)) \Rightarrow (P = \{q : MeshPattern \mid (q.R = Set.univ) \land (Equiv.Perm.sign\left(q.p\right) \ne 1)\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Henning Ulfarsson (2024). *BiSC: An algorithm for discovering generalized permutation patterns*. DOI: [10.48550/arXiv.2411.17778](https://doi.org/10.48550/arXiv.2411.17778). URL: <https://arxiv.org/abs/2411.17778v1>.

*Commentary.*

If a cell is unshaded, insert two points in that cell in either order. Both resulting permutations contain the pattern; exchanging the two points reverses the sign, so one resulting permutation is even. Therefore every forbidden pattern is fully shaded. A fully shaded pattern occurs only in its underlying permutation, which forces the forbidden patterns to be exactly the odd permutations with full shading. The argument uses only Av P = Alt; the minimality clause of IsBasis is unnecessary.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Alt`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Av`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.IsBasis`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.MeshPattern`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.Occurs`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.claim`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.result`
