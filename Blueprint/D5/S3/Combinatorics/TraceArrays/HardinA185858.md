# Hardin–Barker A185858

## Abstract

The number of binary arrays with three columns whose adjacent contiguous three-by-three blocks have different traces, divided by 128, has the generating function and radical expression proposed by Colin Barker for OEIS A185858.

**Definition 1.1 (Trace of a contiguous block).**

$$\forall n \in \mathbb{N},\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 2\right), \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(2\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{blockTrace}\left(n, B, i\right) = \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{Matrix}.\operatorname{submatrix}\left(\operatorname{fun} (r:\operatorname{Fin}\left(n + 2\right)) \mapsto \operatorname{fun} (c:\operatorname{Fin}\left(3\right)) \mapsto \operatorname{val}\left(B\left(r, c\right)\right), \operatorname{fun} (r:\operatorname{Fin}\left(3\right)) \mapsto (\langle\operatorname{val}\left(i\right) + \operatorname{val}\left(r\right), \operatorname{by} \operatorname{omega}\rangle:\operatorname{Fin}\left(n + 2\right)), \operatorname{id}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.blockTrace` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” Entries lie in Fin 2 and are read by val as natural numbers. The contiguous block starts at row i. Its row index val i + val r lies below n + 2; the Fin constructor carries this bound.

**Definition 1.2 (Adjacent traces differ).**

$$\forall n \in \mathbb{N},\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 2\right), \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(2\right)\right),\; \operatorname{Valid}\left(n, B\right) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (\operatorname{val}\left(j\right) = \operatorname{val}\left(i\right) + 1) \Rightarrow \operatorname{blockTrace}\left(n, B, i\right) \ne \operatorname{blockTrace}\left(n, B, j\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.Valid` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” There is one block column. Thus only block origins in successive rows are adjacent. Arrays are actual matrices with no identification by symmetry and no periodic boundary.

**Definition 1.3 (Number of arrays).**

$$\forall n \in \mathbb{N},\; \operatorname{count}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\{B:\operatorname{Matrix}\left(\operatorname{Fin}\left(n + 2\right), \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(2\right)\right) \mid \operatorname{Valid}\left(n, B\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.count` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” Nat.card counts the subtype of matrices satisfying the adjacent-trace inequalities.

**Definition 1.4 (Normalized count).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{count}\left(n\right)\right):\mathbb{Q})}{128}$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.a` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” The division takes place in the rationals. The entry has offset 1 and begins 4, 22, 124, 694, 3892.

**Definition 1.5 (Series with zero constant coefficient).**

$$generatingSeries = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (n:\mathbb{N}) \mapsto \operatorname{if} n = 0 \operatorname{then} 0 \operatorname{else} \operatorname{a}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.generatingSeries` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, FORMULA (unpaginated): “G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).” The offset is 1: the coefficient of degree zero is zero, and the coefficient at every positive index n is a n. No value for the source sequence at index zero is asserted.

**Definition 1.6 (Barker's two formulas).**

$$claim \Leftrightarrow ((generatingSeries = (2 \cdot \operatorname{PowerSeries}.\operatorname{X} \cdot (2 + 3 \cdot \operatorname{PowerSeries}.\operatorname{X})) \cdot (1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X} - 9 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})^{-1}) \land (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{Rat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right):\mathbb{R}) = \frac{(2 - \operatorname{Real}.\operatorname{sqrt}\left(13\right))^{n} \cdot (-4 + \operatorname{Real}.\operatorname{sqrt}\left(13\right)) + (2 + \operatorname{Real}.\operatorname{sqrt}\left(13\right))^{n} \cdot (4 + \operatorname{Real}.\operatorname{sqrt}\left(13\right))}{3 \cdot \operatorname{Real}.\operatorname{sqrt}\left(13\right)}))$$

*Formalization.* `D5/S3/Combinatorics/TraceArrays/HardinA185858.claim` (`✓ std3`).

*Citation.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

OEIS A185858, FORMULA (unpaginated): “Conjectures from _Colin Barker_, Apr 17 2018: (Start)” followed by “G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).” and “a(n) = ((2 - sqrt(13))^n*(-4+sqrt(13)) + (2+sqrt(13))^n*(4+sqrt(13))) / (3*sqrt(13)).” The generating function is an identity in PowerSeries ℚ. The second formula holds for natural n at least 1, with a n cast from ℚ to ℝ and sqrt the nonnegative real square root.

**Theorem 1.7 (Proof of both formulas).**

$$(generatingSeries = (2 \cdot \operatorname{PowerSeries}.\operatorname{X} \cdot (2 + 3 \cdot \operatorname{PowerSeries}.\operatorname{X})) \cdot (1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X} - 9 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})^{-1}) \land (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{Rat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right):\mathbb{R}) = \frac{(2 - \operatorname{Real}.\operatorname{sqrt}\left(13\right))^{n} \cdot (-4 + \operatorname{Real}.\operatorname{sqrt}\left(13\right)) + (2 + \operatorname{Real}.\operatorname{sqrt}\left(13\right))^{n} \cdot (4 + \operatorname{Real}.\operatorname{sqrt}\left(13\right))}{3 \cdot \operatorname{Real}.\operatorname{sqrt}\left(13\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceArrays/HardinA185858.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin185858` (proved) by `D5/S3/Combinatorics/TraceArrays/HardinA185858.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin185858","declaration_gid":"D5/S3/Combinatorics/TraceArrays/HardinA185858.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin and Colin Barker (2018). *OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces*. URL: <https://oeis.org/A185858>.

*Commentary.*

A cyclic shift in each column separates the n diagonal triples from six free binary cells. A prescribed trace word s therefore has 64 times the product of choose(3, val(s i)) arrays. The triple sums 0, 1, 2, 3 have multiplicities 1, 3, 3, 1. Splitting a word at its first triple gives four extension equations. Their weighted total satisfies the recurrence with coefficients 4 and 9, and its normalized first two terms are 4 and 22. Coefficient comparison proves the series identity. The two real numbers 2 − sqrt(13) and 2 + sqrt(13) satisfy r² = 4r + 9, so the radical expression has the same recurrence and initial values. Uniqueness of solutions to a linear recurrence proves the second formula for every positive index.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.a`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.blockTrace`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.count`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.generatingSeries`
- Truth anchor: `D5/S3/Combinatorics/TraceArrays/HardinA185858.result`
