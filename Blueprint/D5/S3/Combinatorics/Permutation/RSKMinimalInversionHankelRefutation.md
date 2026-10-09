# A four-row refutation of Pahuja's Hankel conjecture

## Abstract

Minimal matrices of RSK shape (8,8,1,1) cannot be Hankel.

A nonnegative integer matrix is a function Fin(n) → Fin(n) → ℕ. Indices and insertion letters start at zero. Adding one to every letter recovers the paper's positive letters without changing comparisons or row lengths. The integer sequence in the Hankel clause shifts its index by two relative to s₂,…,s₂ₙ. It is defined on all natural numbers; values at unused indices impose no condition.

**Definition 1.1 (Insertion into one row).**

$$\forall x \in \mathbb{N},\; \operatorname{insertRow}\left(x, []\right) = ([x],\mathit{none}) \land \left(\forall y \in \mathbb{N},\; \forall ys \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{insertRow}\left(x, y::\mathit{ys}\right) = \operatorname{if}x < y\operatorname{then}(x::\mathit{ys},\operatorname{some}\left(y\right))\operatorname{else}\operatorname{let}z = \operatorname{insertRow}\left(x, \mathit{ys}\right);(y::z.1,z.2)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.insertRow` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 3.1, page 6: ‘If x₁ is greater than or equal to all entries in R₁, append x₁ at the end of R₁. Otherwise, let x₂ be the smaller entry in R₁ that is strictly greater than x₁. Replace x₂ by x₁, and the bumped entry x₂ is then inserted into the second row R₂.’ insertRow returns the modified row and the optional bumped letter. The recursion selects the leftmost entry strictly greater than x; equality passes to the next entry. A weakly increasing row makes this the entry specified by the paper.

**Definition 1.2 (Bumping through successive rows).**

$$\forall x \in \mathbb{N},\; \operatorname{rowInsert}\left(x, []\right) = [[x]] \land \left(\forall r \in \operatorname{List}\left(\mathbb{N}\right),\; \forall rs \in \operatorname{List}\left(\operatorname{List}\left(\mathbb{N}\right)\right),\; \operatorname{let}z = \operatorname{insertRow}\left(x, r\right);\left(z.2 = \mathit{none} \Rightarrow \operatorname{rowInsert}\left(x, r::\mathit{rs}\right) = z.1::\mathit{rs}\right) \land \left(\forall y \in \mathbb{N},\; z.2 = \operatorname{some}\left(y\right) \Rightarrow \operatorname{rowInsert}\left(x, r::\mathit{rs}\right) = z.1::\operatorname{rowInsert}\left(y, \mathit{rs}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.rowInsert` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 3.1, page 6: ‘This bumping process continues row by row until an entry is added at the end of some row Rₛ. The resulting tableau remains semistandard.’ rowInsert passes a bumped letter to the next row and stops when insertRow returns none. Lists contain rows in top-to-bottom order. The equations specify both Option constructors, with z denoting insertRow(x,r).

**Definition 1.3 (The insertion tableau of a matrix word).**

$$\forall w \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{insertionTableau}\left(w\right) = \operatorname{List}.\operatorname{foldl}\left((T:\operatorname{List}\left(\operatorname{List}\left(\mathbb{N}\right)\right))\mapsto (x:\mathbb{N})\mapsto \operatorname{rowInsert}\left(x, T\right), [], w\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.insertionTableau` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 3.1, page 6: ‘The RSK algorithm proceeds inductively through the insertion operation, where at each iteration, we obtain Pₖ by inserting jₖ into Pₖ₋₁, and recording iₖ in Qₖ₋₁ in the cell (s,t) where the new cell is added in Pₖ.’ insertionTableau keeps the insertion component P: List.foldl starts from [] and inserts letters from left to right. Recording Q is unnecessary for the common shape.

**Definition 1.4 (The bottom row of the generalised permutation).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{readingWord}\left(M\right) = \operatorname{List}.\operatorname{flatMap}\left((i:\operatorname{Fin}\left(n\right))\mapsto \operatorname{List}.\operatorname{flatMap}\left((j:\operatorname{Fin}\left(n\right))\mapsto \operatorname{List}.\operatorname{replicate}\left(\operatorname{M}\left(i, j\right), \operatorname{val}\left(j\right)\right), \operatorname{List}.\operatorname{finRange}\left(n\right)\right), \operatorname{List}.\operatorname{finRange}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.readingWord` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 3, page 6: ‘A matrix M=(mᵢ,ⱼ) of size n × n can be written in a two-line notation as a generalised permutation by listing each pair (i,j) exactly mᵢ,ⱼ times. That is, we expand each entry of the matrix into repeated pairs.’ Page 6 also states: ‘In other words, the top row is weakly increasing, and two pairs with the same top entry have bottom entries in weakly increasing order.’ List.finRange enumerates each index ascending. The outer and inner List.flatMap implement this lexicographic order, and List.replicate supplies each multiplicity. readingWord denotes this matrix's bottom row, rather than the tableau row-word of Definition 3.5.

**Definition 1.5 (RSK shape as row lengths).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{shape}\left(M\right) = \operatorname{List}.\operatorname{map}\left(\operatorname{List}.\operatorname{length}, \operatorname{insertionTableau}\left(\operatorname{readingWord}\left(M\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.shape` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 1, page 1: ‘In this setting, the shape of a matrix is defined to be the common shape of the resulting pair of semistandard Young tableaux.’ The insertion component alone determines it: List.map List.length records the top-to-bottom row lengths. The partition condition is expressed separately by IsPartitionN.

**Definition 1.6 (The source inversion count).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{inv}\left(M\right) = \sum_{i:\operatorname{Fin}\left(n\right)}\sum_{k:\operatorname{Fin}\left(n\right)}\sum_{j:\operatorname{Fin}\left(n\right)}\sum_{l:\operatorname{Fin}\left(n\right)}(\operatorname{if}i < k \land l < j\operatorname{then}\operatorname{M}\left(i, j\right) \cdot \operatorname{M}\left(k, l\right)\operatorname{else}0)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.inv` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Definition 3.1, page 6: ‘An inversion of a matrix M ∈ ℳλ is a pair of positions (i,j) and (k,l)} such that mᵢⱼ,mₖₗ > 0, and i < k and j > l.’ The following display gives the total ∑ᵢ<ₖ,ⱼ>ₗ mᵢ,ⱼ mₖ,ₗ. The formula sums over all four finite indices and selects precisely i < k and l < j; zero entries automatically contribute zero. No pairs with equal row indices contribute.

**Definition 1.7 (Minimum over all matrices of the same shape).**

$$\forall n \in \mathbb{N},\; \forall lam \in \operatorname{List}\left(\mathbb{N}\right),\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{IsMinimal}\left(\mathit{lam}, M\right) = \left(\operatorname{shape}\left(M\right) = \mathit{lam} \land \left(\forall Mprime \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{shape}\left(\mathit{Mprime}\right) = \mathit{lam} \Rightarrow \operatorname{inv}\left(M\right) \le \operatorname{inv}\left(\mathit{Mprime}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.IsMinimal` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Section 1, page 2: ‘A matrix M ∈ ℳλ that attains this minimum will be called a minimal matrix of shape λ. This matrix need not be unique.’ The preceding sentence restricts the comparison to matrices of size n × n and shape λ. IsMinimal retains both the shape equation and comparison against every matrix M' on the same Fin(n) carrier.

**Definition 1.8 (Exactly n positive partition parts).**

$$\forall n \in \mathbb{N},\; \forall lam \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{IsPartitionN}\left(n, \mathit{lam}\right) = \left(\operatorname{List}.\operatorname{length}\left(\mathit{lam}\right) = n \land \left(\left(\forall x \in \mathbb{N},\; x \in \mathit{lam} \Rightarrow 0 < x\right) \land \operatorname{List}.\operatorname{Pairwise}\left((x:\mathbb{N})\mapsto (y:\mathbb{N})\mapsto y \le x, \mathit{lam}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.IsPartitionN` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Conjecture 1.1, page 2: ‘Let λ be a partition with n parts’. IsPartitionN requires length n, positivity of every part and nonincreasing order. List.Pairwise uses the relation x ≥ y; zero padding is excluded.

**Definition 1.9 (Pahuja's Conjecture 1.1, both clauses).**

$$\mathit{claim} = \left(\forall n \in \mathbb{N},\; \forall lam \in \operatorname{List}\left(\mathbb{N}\right),\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; \operatorname{IsPartitionN}\left(n, \mathit{lam}\right) \Rightarrow \left(\operatorname{IsMinimal}\left(\mathit{lam}, M\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{M}\left(i, j\right) = \operatorname{M}\left(j, i\right)\right) \land \left(\exists s \in \mathbb{N} \to \mathbb{Z},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (\operatorname{M}\left(i, j\right):\mathbb{Z}) = \operatorname{s}\left(\operatorname{val}\left(i\right) + \operatorname{val}\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.claim` (`✓ std3`).

*Citation.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

Conjecture 1.1, page 2: ‘Let λ be a partition with n parts, and let M=(mᵢ,ⱼ)₁≤ᵢ,ⱼ≤ₙ ∈ ℳλ be a minimal matrix of shape λ. Then M is symmetric, that is, mᵢ,ⱼ = mⱼ,ᵢ for all 1 ≤ i,j ≤ n. Moreover, every minimal matrix of shape λ is Hankel: there exists a sequence of integers s₂, s₃, …, s₂ₙ such that mᵢ,ⱼ = sᵢ₊ⱼ for all 1 ≤ i,j ≤ n.’ The quantified carriers are n : ℕ, lam : List ℕ and M : Fin(n) → Fin(n) → ℕ. The conjunction retains symmetry and Hankel, including the cast of M(i,j) to ℤ. Extending the finite integer sequence to ℕ → ℤ and shifting its indices by two is equivalent to the printed sequence. Every relevant index lies between zero and 2n−2.

**Theorem 1.10 (The Hankel clause fails at shape (8,8,1,1)).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pahuja-2026-hankel-minimal-matrices` (refuted) by `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pahuja-2026-hankel-minimal-matrices","declaration_gid":"D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nimisha Pahuja (2026). *Minimal Inversions in Integer Matrices of Fixed RSK Shape*. URL: <https://arxiv.org/abs/2602.14931v1>.

*Commentary.*

The symmetric matrix [[0,3,0,1],[3,0,2,0],[0,2,0,3],[1,0,3,0]] has shape [8,8,1,1] and inversion count 43. Insertion adds exactly one cell per letter, so a Hankel matrix of this shape has total weight 18. Its seven anti-diagonal parameters satisfy t₀+2t₁+3t₂+4t₃+3t₄+2t₅+t₆=18. All 2,743 nonnegative weighted tuples are enumerated, with the first parameter split into nineteen cases. Every tuple with the required shape has at least 45 inversions. Natural-valued inversion counts attain a minimum whenever the shape class is nonempty. Every minimizer therefore has at most 43 inversions and cannot be Hankel. This refutes the conjunction; it does not decide whether every minimizer is symmetric. The four-row example leaves the paper's two-row Theorem 4.1 outside the counterexample's range.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.IsMinimal`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.IsPartitionN`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.insertRow`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.insertionTableau`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.inv`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.readingWord`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.rowInsert`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.shape`
- Dependency: [D5/S3/Constants/Moments/CoefficientNewtonSums](../../Constants/Moments/CoefficientNewtonSums.md)
