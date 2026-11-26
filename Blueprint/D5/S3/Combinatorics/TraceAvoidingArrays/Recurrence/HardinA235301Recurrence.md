# The A235301 recurrence

## Abstract

Hardin's common order-ten recurrence for stress-three rectangles.

**Theorem 1.1 (The recurrence in both coordinates).**

$$\begin{aligned}&\forall k: \mathbb{N}, \forall n: \mathbb{N}, 1 \le k \implies 11 \le n \implies\\((C\left(3, 3, n, k\right) : \mathbb{Z}) &=3\cdot(C\left(3, 3, n - 1, k\right) : \mathbb{Z})+17\cdot(C\left(3, 3, n - 2, k\right) : \mathbb{Z})-57\cdot(C\left(3, 3, n - 3, k\right) : \mathbb{Z})\\&\quad-86\cdot(C\left(3, 3, n - 4, k\right) : \mathbb{Z})+372\cdot(C\left(3, 3, n - 5, k\right) : \mathbb{Z})+76\cdot(C\left(3, 3, n - 6, k\right) : \mathbb{Z})\\&\quad-972\cdot(C\left(3, 3, n - 7, k\right) : \mathbb{Z})+360\cdot(C\left(3, 3, n - 8, k\right) : \mathbb{Z})+864\cdot(C\left(3, 3, n - 9, k\right) : \mathbb{Z})\\&\quad-576\cdot(C\left(3, 3, n - 10, k\right) : \mathbb{Z}))\\&\land\\((C\left(3, 3, k, n\right) : \mathbb{Z}) &=3\cdot(C\left(3, 3, k, n - 1\right) : \mathbb{Z})+17\cdot(C\left(3, 3, k, n - 2\right) : \mathbb{Z})-57\cdot(C\left(3, 3, k, n - 3\right) : \mathbb{Z})\\&\quad-86\cdot(C\left(3, 3, k, n - 4\right) : \mathbb{Z})+372\cdot(C\left(3, 3, k, n - 5\right) : \mathbb{Z})+76\cdot(C\left(3, 3, k, n - 6\right) : \mathbb{Z})\\&\quad-972\cdot(C\left(3, 3, k, n - 7\right) : \mathbb{Z})+360\cdot(C\left(3, 3, k, n - 8\right) : \mathbb{Z})+864\cdot(C\left(3, 3, k, n - 9\right) : \mathbb{Z})\\&\quad-576\cdot(C\left(3, 3, k, n - 10\right) : \mathbb{Z}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235301-common-recurrence` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235301-common-recurrence","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235301 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235301>.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235292 — Column two of A235301*. URL: <https://oeis.org/A235292>.

*Commentary.*

The integer cast of C(3,3,h,w) counts indexed arrays of shape (h+1) by (w+1) over 0 through 3. Each contiguous 2×2 block has absolute diagonal-minus-antidiagonal sum 3. Both identities use a positive fixed side and a varying index at least eleven. The first full window uses indices 1 through 11.

Subtracting three times the product of the row and column indices in the ring modulo six turns the mixed differences into zero. The resulting grid is reconstructed from two boundary words, with the local crossing conditions ensuring that every reconstructed entry and block is legal.

The weighted row transfer records the current type, parity and intersection of compatible column-edge masks. Its acceptance value at any positive width depends only on the mask. The signed residual vectors R0, R1 and R2 satisfy R2 = −3R1 − 2R0, and the first two residual weights sum to zero at every mask. Linearity propagates these equalities to every subsequent residual. This gives one axis, and transposition gives the other.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate](HardinA235301Certificate.md)
