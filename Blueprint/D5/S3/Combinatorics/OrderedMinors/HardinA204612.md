# Hardin's recurrence for OEIS A204612

## Abstract

Five-column ordered-minor array counts satisfy Hardin's eleven-term recurrence.

**Definition 1.1 (The adjacent integer determinant).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(5\right), \operatorname{Fin}\left(2\right)\right), \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(4\right), \operatorname{minor}\left(A, i, j\right) = \operatorname{Matrix}.\operatorname{det}\left(\begin{pmatrix}(\operatorname{val}\left(A\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right): \mathbb{Z})&(\operatorname{val}\left(A\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right): \mathbb{Z})\\(\operatorname{val}\left(A\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right): \mathbb{Z})&(\operatorname{val}\left(A\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right): \mathbb{Z})\end{pmatrix}\right)$$

*Formalization.* `D5/S3/Combinatorics/OrderedMinors/HardinA204612.minor` (`✓ std3`).

*Citation.* R. H. Hardin (2012). *OEIS A204612: five-column arrays with ordered adjacent determinants*. URL: <https://oeis.org/A204612>.

*Commentary.*

OEIS A204612, NAME (unpaginated): "Number of (n+1)X5 0..1 arrays with the determinants of 2X2 subblocks nondecreasing rightwards and downwards." For A : Matrix (Fin (n + 1)) (Fin 5) (Fin 2), i : Fin n and j : Fin 4, minor A i j is the determinant over the integers of the adjacent block with top left corner (i,j). Fin.val gives the natural value of a binary entry, which is then cast to the integers. The boundary does not wrap.

**Definition 1.2 (Monotonicity in both directions).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(5\right), \operatorname{Fin}\left(2\right)\right), \operatorname{OrderedMinors}\left(A\right) = \left((\forall i: \operatorname{Fin}\left(n\right), \operatorname{Monotone}\left(\operatorname{minor}\left(A, i\right)\right)) \land (\forall j: \operatorname{Fin}\left(4\right), \operatorname{Monotone}\left((i: \operatorname{Fin}\left(n\right) \mapsto \operatorname{minor}\left(A, i, j\right))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/OrderedMinors/HardinA204612.OrderedMinors` (`✓ std3`).

*Citation.* R. H. Hardin (2012). *OEIS A204612: five-column arrays with ordered adjacent determinants*. URL: <https://oeis.org/A204612>.

*Commentary.*

OEIS A204612, NAME (unpaginated): "Number of (n+1)X5 0..1 arrays with the determinants of 2X2 subblocks nondecreasing rightwards and downwards." Every row of adjacent determinants is Monotone in the column index, and every column of adjacent determinants is Monotone in the row index. Repeated rows and equal determinants are allowed.

**Definition 1.3 (The literal array count).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = (\operatorname{Nat}.\operatorname{card}\left(\{A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(5\right), \operatorname{Fin}\left(2\right)\right) | \operatorname{OrderedMinors}\left(A\right)\}\right): \mathbb{Z})$$

*Formalization.* `D5/S3/Combinatorics/OrderedMinors/HardinA204612.a` (`✓ std3`).

*Citation.* R. H. Hardin (2012). *OEIS A204612: five-column arrays with ordered adjacent determinants*. URL: <https://oeis.org/A204612>.

*Commentary.*

OEIS A204612, NAME (unpaginated): "Number of (n+1)X5 0..1 arrays with the determinants of 2X2 subblocks nondecreasing rightwards and downwards." The integer a(n) is Nat.card of the subtype of the binary matrices satisfying OrderedMinors. Thus the count is defined from the arrays, independently of the recurrence. The source offset is 1,1; n = 0 is defined in Lean but does not occur in the asserted range.

**Definition 1.4 (Hardin's empirical formula).**

$$claim = (\forall n: \mathbb{N}, (15 < n) \Rightarrow \operatorname{a}\left(n\right) = 18 \cdot \operatorname{a}\left(n - 1\right) - 73 \cdot \operatorname{a}\left(n - 2\right) - 256 \cdot \operatorname{a}\left(n - 3\right) + 2060 \cdot \operatorname{a}\left(n - 4\right) - 1216 \cdot \operatorname{a}\left(n - 5\right) - 12612 \cdot \operatorname{a}\left(n - 6\right) + 18224 \cdot \operatorname{a}\left(n - 7\right) + 20992 \cdot \operatorname{a}\left(n - 8\right) - 40064 \cdot \operatorname{a}\left(n - 9\right) - 9984 \cdot \operatorname{a}\left(n - 10\right) + 24576 \cdot \operatorname{a}\left(n - 11\right))$$

*Formalization.* `D5/S3/Combinatorics/OrderedMinors/HardinA204612.claim` (`✓ std3`).

*Citation.* R. H. Hardin (2012). *OEIS A204612: five-column arrays with ordered adjacent determinants*. URL: <https://oeis.org/A204612>.

*Commentary.*

OEIS A204612, FORMULA (unpaginated): "Empirical: a(n) = 18*a(n-1) -73*a(n-2) -256*a(n-3) +2060*a(n-4) -1216*a(n-5) -12612*a(n-6) +18224*a(n-7) +20992*a(n-8) -40064*a(n-9) -9984*a(n-10) +24576*a(n-11) for n>15" The index n is natural, the strict threshold is 15 < n, and all eleven subtractions in the arguments are natural subtraction. The count is cast to the integers before the signed arithmetic on the right hand side.

**Theorem 1.5 (The eleven-term recurrence).**

$$\forall n: \mathbb{N}, (15 < n) \Rightarrow \operatorname{a}\left(n\right) = 18 \cdot \operatorname{a}\left(n - 1\right) - 73 \cdot \operatorname{a}\left(n - 2\right) - 256 \cdot \operatorname{a}\left(n - 3\right) + 2060 \cdot \operatorname{a}\left(n - 4\right) - 1216 \cdot \operatorname{a}\left(n - 5\right) - 12612 \cdot \operatorname{a}\left(n - 6\right) + 18224 \cdot \operatorname{a}\left(n - 7\right) + 20992 \cdot \operatorname{a}\left(n - 8\right) - 40064 \cdot \operatorname{a}\left(n - 9\right) - 9984 \cdot \operatorname{a}\left(n - 10\right) + 24576 \cdot \operatorname{a}\left(n - 11\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedMinors/HardinA204612.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a204612` (proved) by `D5/S3/Combinatorics/OrderedMinors/HardinA204612.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a204612","declaration_gid":"D5/S3/Combinatorics/OrderedMinors/HardinA204612.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2012). *OEIS A204612: five-column arrays with ordered adjacent determinants*. URL: <https://oeis.org/A204612>.

*Commentary.*

Coding the two initial rows and all subsequent rows gives a labeled path on 68 boundary states. The literal array count equals the total of a power of the transition matrix applied to the initial multiplicities. A degree-eleven polynomial residual belongs to an invariant span of eleven paired boundary-bit differences whose total is zero. Every further transition power preserves that span, so taking totals yields the displayed identity at every n > 15. This proves the source formula; minimal order, a smaller threshold and larger widths are separate questions.

## References

- Truth anchor: `D5/S3/Combinatorics/OrderedMinors/HardinA204612.OrderedMinors`
- Truth anchor: `D5/S3/Combinatorics/OrderedMinors/HardinA204612.a`
- Truth anchor: `D5/S3/Combinatorics/OrderedMinors/HardinA204612.claim`
- Truth anchor: `D5/S3/Combinatorics/OrderedMinors/HardinA204612.minor`
- Truth anchor: `D5/S3/Combinatorics/OrderedMinors/HardinA204612.result`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer](../NarayanaStrip/CiglerCycleWalkTransfer.md)
