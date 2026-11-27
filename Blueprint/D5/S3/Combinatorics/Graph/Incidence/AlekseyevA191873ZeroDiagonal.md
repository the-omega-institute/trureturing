# Alekseyev's Zero-Diagonal Zarankiewicz Conjecture

## Abstract

Zero-diagonal and unrestricted rectangle-free maxima agree for n at least three.

Binary matrices have entries in Fin 2. Rows and columns range independently over Fin n. A rectangle uses two distinct rows and two distinct columns, with no adjacency requirement. The least forcing count is restricted to counts at most n*n.

**Definition 1.1 (Four corners equal to one).**

$$\forall n: \mathbb{N}, \forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(2\right)\right), \operatorname{HasRectangle}\left(M\right) = (\exists i: \operatorname{Fin}\left(n\right), \exists iPrime: \operatorname{Fin}\left(n\right), \exists j: \operatorname{Fin}\left(n\right), \exists jPrime: \operatorname{Fin}\left(n\right), (i \neq iPrime) \land (j \neq jPrime) \land (M (i, j) = 1) \land (M (i, jPrime) = 1) \land (M (iPrime, j) = 1) \land (M (iPrime, jPrime) = 1))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.HasRectangle` (`✓ std3`).

*Citation.* Max Alekseyev and OEIS contributors (2022). *OEIS A191873: zero-diagonal Zarankiewicz conjecture*. URL: <https://oeis.org/A191873>.

*Commentary.*

OEIS A072567, NAME (unpaginated): "A variant of Zarankiewicz problem: maximal number of 1s in n X n 01-matrix with no four 1s forming a rectangle." The four corners are at i,j; i,j'; i',j; i',j'.

**Definition 1.2 (Attainable zero-diagonal weights).**

$$\forall n: \mathbb{N}, \operatorname{diagonalWeights}\left(n\right) = \{ w: \mathbb{N} \mid \exists M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(2\right)\right), (\neg \operatorname{HasRectangle}\left(M\right)) \land (\forall i: \operatorname{Fin}\left(n\right), M (i, i) = 0) \land (\operatorname{Finset}.\operatorname{card} (\operatorname{Finset}.\operatorname{filter} (\operatorname{fun} ij: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right) \mapsto M (ij.1, ij.2) = 1, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)))) = w) \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.diagonalWeights` (`✓ std3`).

*Citation.* Max Alekseyev and OEIS contributors (2022). *OEIS A191873: zero-diagonal Zarankiewicz conjecture*. URL: <https://oeis.org/A191873>.

*Commentary.*

OEIS A191873, NAME (unpaginated): "A problem of Zarankiewicz: maximal number of 1's in an n X n matrix of 0's and 1's with 0's on the main diagonal and no "rectangle" with 1's at the four corners." The count is Finset.card of the entry positions equal to one; all main-diagonal entries are zero.

**Definition 1.3 (Counts forcing a rectangle).**

$$\forall n: \mathbb{N}, \operatorname{forcingCounts}\left(n\right) = \{ k: \mathbb{N} \mid (k \le n \cdot n) \land (\forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(2\right)\right), (\operatorname{Finset}.\operatorname{card} (\operatorname{Finset}.\operatorname{filter} (\operatorname{fun} ij: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right) \mapsto M (ij.1, ij.2) = 1, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)))) = k) \implies \operatorname{HasRectangle}\left(M\right)) \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.forcingCounts` (`✓ std3`).

*Citation.* Max Alekseyev and OEIS contributors (2022). *OEIS A191873: zero-diagonal Zarankiewicz conjecture*. URL: <https://oeis.org/A191873>.

*Commentary.*

OEIS A001197, COMMENTS (unpaginated): "a(n) is the minimum number k_2(n) such that any n X n matrix having that number of nonzero entries has a 2 X 2 submatrix with only nonzero entries. - _M. F. Hasler_, Sep 28 2021" Fin 2 makes nonzero entries exactly the entries equal to one. The bound k ≤ n*n excludes impossible counts.

**Definition 1.4 (The source conjecture).**

$$claim = (\forall n: \mathbb{N}, 3 \le n \implies \exists d: \mathbb{N}, \exists k: \mathbb{N}, (\operatorname{IsGreatest}\left(\operatorname{diagonalWeights}\left(n\right), d\right)) \land (\operatorname{IsLeast}\left(\operatorname{forcingCounts}\left(n\right), k\right)) \land (d = \operatorname{SimpleGraph}.\operatorname{zarankiewicz} (n, n, 2, 2)) \land (d+1 = k))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.claim` (`✓ std3`).

*Citation.* Max Alekseyev and OEIS contributors (2022). *OEIS A191873: zero-diagonal Zarankiewicz conjecture*. URL: <https://oeis.org/A191873>.

*Commentary.*

OEIS A191873, COMMENTS (unpaginated): "Conjecture: for n >= 3, a(n) = A072567(n) = A001197(n) - 1 (per above comment). - _Max Alekseyev_, Jan 29 2022" The witnesses d and k are respectively the attained greatest zero-diagonal weight and the attained least forcing count. SimpleGraph.zarankiewicz n n 2 2 is the unrestricted maximum. The final equality d+1=k expresses the source's subtraction without truncated subtraction.

**Theorem 1.5 (Equality in every dimension at least three).**

$$\forall n: \mathbb{N}, 3 \le n \implies \exists d: \mathbb{N}, \exists k: \mathbb{N}, (\operatorname{IsGreatest}\left(\operatorname{diagonalWeights}\left(n\right), d\right)) \land (\operatorname{IsLeast}\left(\operatorname{forcingCounts}\left(n\right), k\right)) \land (d = \operatorname{SimpleGraph}.\operatorname{zarankiewicz} (n, n, 2, 2)) \land (d+1 = k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result` (`✓ std3`). ∎

*Resolves.* `Problems/alekseyev-a191873` (proved) by `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alekseyev-a191873","declaration_gid":"D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Max Alekseyev and OEIS contributors (2022). *OEIS A191873: zero-diagonal Zarankiewicz conjecture*. URL: <https://oeis.org/A191873>.

*Commentary.*

The proof uses a cyclic avoiding matrix of weight 2*n. A full row or column in an avoiding matrix has fewer than 2*n ones, so an extremizer has a zero in every row and column. A deficient Hall neighbourhood of zero entries would give four ones forming a rectangle; Hall therefore yields a permutation of zero entries. Permuting columns preserves the weight and places those zeros on the diagonal. Trimming an avoiding matrix to each smaller weight proves minimality of the forcing count. The argument does not require symmetry and makes no assertion about arbitrary prescribed diagonal patterns.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.HasRectangle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.diagonalWeights`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.forcingCounts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result`
- Dependency: [D5/S0/Automata/TwoStateCertificateWidth](../../../../S0/Automata/TwoStateCertificateWidth.md)
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination](../Domination/TrapezohedralMinimalDomination.md)
