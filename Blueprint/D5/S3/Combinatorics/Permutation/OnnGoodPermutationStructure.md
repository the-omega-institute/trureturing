# The structure of good permutations

## Abstract

Local extreme positions force a unique split into two chains.

An array is an equivalence (Fin m × Fin n) ≃ Fin (m*n). Coordinates are zero-based; entry adds one to each rank. Natural subtraction is truncated. List.Pairwise uses the strict order on natural numbers.

**Definition 1.1 (One-based entries).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; \forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{entry}\left(s, i, j\right) = if hi:i < m then (if hj:j < n then \operatorname{val}\left(s\left((\langle i,hi\rangle,\langle j,hj\rangle)\right)\right) + 1 else 0) else 0$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.entry` (`✓ std3`).

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Introduction, page 1: “For an m×n matrix σ whose entries form a permutation of 1,2,…,mn, let A^σ be obtained from A by permuting its entries such that σᵢ,ⱼ<σᵣ,ₛ implies A^σᵢ,ⱼ≤A^σᵣ,ₛ.” The equivalence records zero-based ranks; the displayed function adds one and returns zero outside the rectangle.

**Definition 1.2 (Extreme positions in a square).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{GoodSquare}\left(a, b, c, d\right) = (((\operatorname{max}\left(\operatorname{max}\left(a, b\right), \operatorname{max}\left(c, d\right)\right) = a) \lor (\operatorname{max}\left(\operatorname{max}\left(a, b\right), \operatorname{max}\left(c, d\right)\right) = d)) \land ((\operatorname{min}\left(\operatorname{min}\left(a, b\right), \operatorname{min}\left(c, d\right)\right) = b) \lor (\operatorname{min}\left(\operatorname{min}\left(a, b\right), \operatorname{min}\left(c, d\right)\right) = c)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.GoodSquare` (`✓ std3`).

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Section 2, page 4: “We say an m×n matrix σ whose entries are a permutation of 1,2,…,mn is good on i,j with 1≤i<m and 1≤j<n if the maximum among σᵢ,ⱼ,σᵢ,ⱼ₊₁,σᵢ₊₁,ⱼ,σᵢ₊₁,ⱼ₊₁ is either σᵢ,ⱼ or σᵢ₊₁,ⱼ₊₁ and the minimum among these entries is either σᵢ,ⱼ₊₁ or σᵢ₊₁,ⱼ.”

**Definition 1.3 (Goodness at one adjacent square).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; \forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{GoodAt}\left(s, i, j\right) = ((i + 1 < m) \land ((j + 1 < n) \land (\operatorname{GoodSquare}\left(\operatorname{entry}\left(s, i, j\right), \operatorname{entry}\left(s, i, j + 1\right), \operatorname{entry}\left(s, i + 1, j\right), \operatorname{entry}\left(s, i + 1, j + 1\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.GoodAt` (`✓ std3`).

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Section 2, page 4: “We say an m×n matrix σ whose entries are a permutation of 1,2,…,mn is good on i,j with 1≤i<m and 1≤j<n if the maximum among σᵢ,ⱼ,σᵢ,ⱼ₊₁,σᵢ₊₁,ⱼ,σᵢ₊₁,ⱼ₊₁ is either σᵢ,ⱼ or σᵢ₊₁,ⱼ₊₁ and the minimum among these entries is either σᵢ,ⱼ₊₁ or σᵢ₊₁,ⱼ.” The source square (i,j) has coordinates (i−1,j−1) here.

**Definition 1.4 (Goodness at every adjacent square).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; \operatorname{Good}\left(s\right) = (\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; (i + 1 < m) \Rightarrow ((j + 1 < n) \Rightarrow (\operatorname{GoodAt}\left(s, i, j\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.Good` (`✓ std3`).

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Section 2, page 4: “We say an m×n matrix σ whose entries are a permutation of 1,2,…,mn is good on i,j with 1≤i<m and 1≤j<n if the maximum among σᵢ,ⱼ,σᵢ,ⱼ₊₁,σᵢ₊₁,ⱼ,σᵢ₊₁,ⱼ₊₁ is either σᵢ,ⱼ or σᵢ₊₁,ⱼ₊₁ and the minimum among these entries is either σᵢ,ⱼ₊₁ or σᵢ₊₁,ⱼ.” Every in-range adjacent square satisfies this condition.

**Definition 1.5 (The two increasing chains).**

$$\forall n \in \mathbb{N},\; \forall T \in (\mathbb{N}\to\mathbb{N}),\; \forall B \in (\mathbb{N}\to\mathbb{N}),\; \forall k \in \mathbb{N},\; \operatorname{TwoChains}\left(n, T, B, k\right) = ((k \le n) \land ((\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), \operatorname{List.append}\left(\operatorname{List.ofFn}\left(((j:\operatorname{Fin}\left(k\right))\mapsto B\left(\operatorname{val}\left(j\right)\right))\right), \operatorname{List.reverse}\left(\operatorname{List.ofFn}\left(((j:\operatorname{Fin}\left(k\right))\mapsto T\left(\operatorname{val}\left(j\right)\right))\right)\right)\right)\right)) \land (\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), \operatorname{List.append}\left(\operatorname{List.reverse}\left(\operatorname{List.ofFn}\left(((j:\operatorname{Fin}\left(n - k\right))\mapsto T\left(k + \operatorname{val}\left(j\right)\right))\right)\right), \operatorname{List.ofFn}\left(((j:\operatorname{Fin}\left(n - k\right))\mapsto B\left(k + \operatorname{val}\left(j\right)\right))\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TwoChains` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The first chain follows B up to k and returns along T in reverse. The second returns along T from n to k and then follows B. Empty chains are allowed.

**Definition 1.6 (The first three-by-three type).**

$$\forall A \in (\mathbb{N}\to(\mathbb{N}\to\mathbb{N})),\; \operatorname{TypeA}\left(A\right) = ((\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), [A\left(2, 0\right),A\left(1, 0\right),A\left(1, 1\right),A\left(0, 1\right),A\left(0, 0\right)]\right)) \land (\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), [A\left(0, 2\right),A\left(1, 2\right),A\left(1, 1\right),A\left(2, 1\right),A\left(2, 2\right)]\right)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TypeA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The two increasing lists meet at the center and impose g<d<e<b<a and c<f<e<h<i.

**Definition 1.7 (The second three-by-three type).**

$$\forall A \in (\mathbb{N}\to(\mathbb{N}\to\mathbb{N})),\; \operatorname{TypeB}\left(A\right) = ((\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), [A\left(0, 2\right),A\left(0, 1\right),A\left(1, 1\right),A\left(1, 0\right),A\left(0, 0\right)]\right)) \land (\operatorname{List.Pairwise}\left(((x:\mathbb{N})\mapsto ((y:\mathbb{N})\mapsto x < y)), [A\left(2, 0\right),A\left(2, 1\right),A\left(1, 1\right),A\left(1, 2\right),A\left(2, 2\right)]\right)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TypeB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The two increasing lists meet at the center and impose c<b<e<d<a and g<h<e<f<i.

**Definition 1.8 (All rectangular structural cases).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; \operatorname{Structure}\left(s\right) = ((m = 1) \lor ((n = 1) \lor (((m = 2) \land (\exists!k:\mathbb{N},\operatorname{TwoChains}\left(n, \operatorname{entry}\left(s, 0\right), \operatorname{entry}\left(s, 1\right), k\right))) \lor (((n = 2) \land (\exists!k:\mathbb{N},\operatorname{TwoChains}\left(m, ((j:\mathbb{N})\mapsto \operatorname{entry}\left(s, j, 0\right)), ((j:\mathbb{N})\mapsto \operatorname{entry}\left(s, j, 1\right)), k\right))) \lor ((m = 3) \land ((n = 3) \land ((\operatorname{TypeA}\left(\operatorname{entry}\left(s\right)\right)) \lor (\operatorname{TypeB}\left(\operatorname{entry}\left(s\right)\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.Structure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

One-dimensional arrays have no adjacent square. Two-row and two-column arrays have a unique chain split. The only remaining case is three by three, with TypeA or TypeB.

**Definition 1.9 (Transposing a rank array).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; \operatorname{transpose}\left(s\right) = (let h:m \cdot n = n \cdot m := by ring; \operatorname{Equiv.trans}\left(\operatorname{Equiv.trans}\left(\operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right), s\right), \operatorname{finCongr}\left(h\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.transpose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Swap the two coordinates and transport the label through finCongr along m*n=n*m. The local proof h is obtained by natural-number arithmetic.

**Theorem 1.10 (Goodness and transposition).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; (\operatorname{Good}\left(\operatorname{transpose}\left(s\right)\right)) \Leftrightarrow (\operatorname{Good}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Transposition exchanges the two off-diagonal entries and preserves both extreme-position conditions.

**Theorem 1.11 (A unique split in every width).**

$$\forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(2 \cdot n\right)),\; (\operatorname{Good}\left(s\right)) \Leftrightarrow (\exists!k:\mathbb{N},\operatorname{TwoChains}\left(n, \operatorname{entry}\left(s, 0\right), \operatorname{entry}\left(s, 1\right), k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.two_good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

A negative row sign propagates to every later column. Its first occurrence separates the two increasing chains, and their inequalities make the split unique.

**Theorem 1.12 (The four compatible squares).**

$$\forall s \in ((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right))\equiv\operatorname{Fin}\left(3 \cdot 3\right)),\; (\operatorname{Good}\left(s\right)) \Leftrightarrow ((\operatorname{TypeA}\left(\operatorname{entry}\left(s\right)\right)) \lor (\operatorname{TypeB}\left(\operatorname{entry}\left(s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.three_good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The four local extreme-position conditions give exactly the two three-by-three types.

**Theorem 1.13 (No three-by-four subrectangle).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; (3 \le m) \Rightarrow ((4 \le n) \Rightarrow (\neg\operatorname{Good}\left(s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.no_good_large` (`✓ std3`). ∎

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Theorem 1.3, page 2: “For m≤n, a universal σ exists if and only if m=1,2 or m=n=3.” Overlapping three-by-three blocks force a shared column both to decrease and to be nonmonotone.

**Theorem 1.14 (The one-dimensional cases).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; ((m = 1) \lor (n = 1)) \Rightarrow (\operatorname{Good}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_of_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

There is no adjacent square when either dimension is one.

**Theorem 1.15 (The complete characterization).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; (0 < m) \Rightarrow ((0 < n) \Rightarrow ((\operatorname{Good}\left(s\right)) \Leftrightarrow (\operatorname{Structure}\left(s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_iff_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The unique sign split handles both two-dimensional orientations. Local compatibility gives the three-by-three alternatives; overlapping blocks exclude every larger rectangle.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.Good`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.GoodAt`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.GoodSquare`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.Structure`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TwoChains`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TypeA`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.TypeB`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.entry`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_iff_structure`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_of_one`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.good_transpose`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.no_good_large`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.three_good_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.transpose`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure.two_good_iff`
