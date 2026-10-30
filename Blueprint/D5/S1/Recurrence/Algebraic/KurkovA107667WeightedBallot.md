# Kurkov's Weighted-Ballot Formula for A107667

## Abstract

Kurkov's weighted-ballot formula for the A107667 triangle.

All indices and table entries are natural numbers. T is zero-indexed. P has three arguments and is constrained only on r >= k >= 1; it is different from the two-argument conjugating matrix also called P in the OEIS entry. Natural subtraction is truncated at zero. OEIS A107667 revision 25 has no page numbers; the locators below are its NAME and FORMULA fields.

**Definition 1.1 (The source triangle).**

$$\forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)), \operatorname{IsSourceTriangle}\left(T\right) \iff (\forall (a: \mathbb{N}), \forall (b: \mathbb{N}), (a < b) \implies T\left(a, b\right) = 0) \land (\forall (a: \mathbb{N}), T\left(a, a\right) = a + 1) \land (\forall (a: \mathbb{N}), \forall (b: \mathbb{N}), (b < a) \implies T\left(a, b\right) = \sum_{j \in \operatorname{Finset}.\operatorname{Icc}\left(b + 1, a\right)} (T\left(a, j\right) \cdot T\left(j, b + 1\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.IsSourceTriangle` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov (2026). *OEIS A107667: Kurkov's weighted-ballot formula for Hanna's triangular matrix*. URL: <https://oeis.org/history/view?seq=A107667&v=25>.

*Commentary.*

NAME, verbatim: Triangular matrix T, read by rows, that satisfies: T = D + SHIFT_LEFT(T^2) where SHIFT_LEFT shifts each row 1 place to the left and D is the diagonal matrix {1, 2, 3, ...}. The function T has type N -> N -> N. Lower triangularity and ordinary matrix multiplication give the finite interval sum. The diagonal entry in row a is a+1, as in the displayed row zero 1.

**Definition 1.2 (Kurkov's three-argument table).**

$$\forall (P: \mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)\right)), \operatorname{IsPTable}\left(P\right) \iff (\forall (r: \mathbb{N}), \forall (m: \mathbb{N}), (1 \le r) \implies P\left(r, 1, m\right) = 1) \land (\forall (r: \mathbb{N}), \forall (k: \mathbb{N}), \forall (m: \mathbb{N}), (1 < k) \implies (k < r) \implies P\left(r, k, m\right) = P\left(r - 1, k, m\right) + (r + m) \cdot P\left(r, k - 1, m\right)) \land (\forall (r: \mathbb{N}), \forall (m: \mathbb{N}), (2 \le r) \implies P\left(r, r, m\right) = (r + m) \cdot P\left(r, r - 1, m\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.IsPTable` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov (2026). *OEIS A107667: Kurkov's weighted-ballot formula for Hanna's triangular matrix*. URL: <https://oeis.org/history/view?seq=A107667&v=25>.

*Commentary.*

FORMULA, verbatim: Conjecture: T(n+m, m) = (n+m+1) * P(n+1, n+1, m) where P(n, k, m) = P(n-1, k, m) + (n+m) * P(n, k-1, m) for 1 < k < n with P(n, 1, m) = 1, P(n, n, m) = (n+m) * P(n, n-1, m). - _Mikhail Kurkov_, Jun 02 2026 The source's row variable n is called r in IsPTable. The base rule applies for r >= 1; the diagonal rule applies for r >= 2. Thus P(1,1,m)=1 comes from the base rule. Values outside r >= k >= 1 are unrestricted and do not occur in the conclusion.

**Definition 1.3 (The two-parameter conjecture).**

$$\operatorname{claim} \iff \forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)), \forall (P: \mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)\right)), (\operatorname{IsSourceTriangle}\left(T\right)) \implies (\operatorname{IsPTable}\left(P\right)) \implies \forall (n: \mathbb{N}), \forall (m: \mathbb{N}), T\left(n + m, m\right) = (n + m + 1) \cdot P\left(n + 1, n + 1, m\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.claim` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov (2026). *OEIS A107667: Kurkov's weighted-ballot formula for Hanna's triangular matrix*. URL: <https://oeis.org/history/view?seq=A107667&v=25>.

*Commentary.*

FORMULA, verbatim: Conjecture: T(n+m, m) = (n+m+1) * P(n+1, n+1, m) where P(n, k, m) = P(n-1, k, m) + (n+m) * P(n, k-1, m) for 1 < k < n with P(n, 1, m) = 1, P(n, n, m) = (n+m) * P(n, n-1, m). - _Mikhail Kurkov_, Jun 02 2026 The claim quantifies over every natural-valued T and P satisfying the displayed source rules, and over every n,m in N, including zero.

**Theorem 1.4 (The weighted-ballot identity).**

$$\forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)), \forall (P: \mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)\right)), (\operatorname{IsSourceTriangle}\left(T\right)) \implies (\operatorname{IsPTable}\left(P\right)) \implies \forall (n: \mathbb{N}), \forall (m: \mathbb{N}), T\left(n + m, m\right) = (n + m + 1) \cdot P\left(n + 1, n + 1, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result` (`✓ std3`). ∎

*Resolves.* `Problems/kur107667-ballot` (proved) by `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kur107667-ballot","declaration_gid":"D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Mikhail Kurkov (2026). *OEIS A107667: Kurkov's weighted-ballot formula for Hanna's triangular matrix*. URL: <https://oeis.org/history/view?seq=A107667&v=25>.

*Commentary.*

The identity holds for every pair of source tables. A zero extension of P satisfies a first-return convolution with parameter shifts m+1 and m+i+1. Induction proves that convolution directly from the three recurrence rules; strong induction on the row-column difference then identifies the diagonal values with T. The proof does not construct a separate bijection between path sets.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.IsPTable`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.IsSourceTriangle`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.result`
