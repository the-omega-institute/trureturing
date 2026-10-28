# Periodic Boundary Arrays And Schroder Numbers

## Abstract

Two periodic shifts of Kurkov's original array have the large Schroder diagonal.

**Remark 1.1 (The original total array).**

Lean statement: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.P`

*Formalization.* `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.P` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A376317, periodic shifts of a two-index recurrence*. URL: <https://oeis.org/A376317>.

*Commentary.*

For an arbitrary natural-valued shift f, set P_f(0,m)=1 for every natural m, with this clause taking priority. For n positive and m<=n set P_f(n,m)=P_f(n-1,m). For n positive and m>n set P_f(n,m)=P_f(n,m-1)+P_f(n-1,m+f(m-n)). All indices and values are natural numbers. Lexicographic recursion on (n,m) terminates even when the lower-row column increases; no bound on f is assumed.

**Remark 1.2 (The period-two shift).**

Lean statement: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f2`

*Formalization.* `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f2` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A376317, periodic shifts of a two-index recurrence*. URL: <https://oeis.org/A376317>.

*Commentary.*

Set f2(d)=d mod 2.

**Remark 1.3 (The period-three shift).**

Lean statement: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f3`

*Formalization.* `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f3` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A376317, periodic shifts of a two-index recurrence*. URL: <https://oeis.org/A376317>.

*Commentary.*

Set f3(d)=0 when d mod 3 is zero, and f3(d)=1 otherwise.

**Theorem 1.4 (The two exact diagonals).**

$$\forall n \in \mathbb{N}, \left(P_{f2}\right)\left(n+1, n+1\right) = largeSchroder\left(n\right) \land \left(P_{f3}\right)\left(n+1, n+1\right) = largeSchroder\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a376317-kurkov-periodic-boundary-schroder` (proved) by `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a376317-kurkov-periodic-boundary-schroder","declaration_gid":"D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A376317, periodic shifts of a two-index recurrence*. URL: <https://oeis.org/A376317>.

*Commentary.*

The statement includes every natural n, starting at zero, and both source shifts simultaneously. The target is Mathlib's unshifted Nat.largeSchroder, the sequence A006318. In particular P_f(1,1)=1. A376388 repeats the same source conjecture; it does not supply a separate question or a second resolution.

Write C_f(n,d)=P_f(n,n+d). The original equations give C_f(0,d)=1, C_f(n+1,0)=C_f(n,1), and C_f(n+1,d+1)=C_f(n+1,d)+C_f(n,d+2+f(d+1)). Thus P_f(n+1,n+1)=C_f(n,1). The original below-diagonal branch remains in the definition of P; no reconstructed or truncated array replaces it.

Work in rational formal power series. A family H with every constant coefficient one, H(0)=1+xH(1), and H(d+1)=H(d)+xH(d+2+f(d+1)) has coefficient n at column d equal to C_f(n,d). The proof inducts first on n with its hypothesis quantified over all columns. At degree n+1 the zero column uses degree n of column one. Induction on d then uses the previous column at degree n+1 and the shifted column at degree n. This supplies the entire infinite family without convergence or a finite-column cutoff.

Let S be Mathlib's largeSchroderSeries mapped to the rationals. Its existing theorem gives S=1+xS+xS^2 and its constant coefficient is one. For f2 take H(2j)=(1+xS)S^j and H(2j+1)=S^(j+1). The even and odd recurrences follow from this quadratic identity; the odd branch includes d=1.

For f3 put R=(S^2+S)/2 in the rational series ring. The same quadratic gives R-S=xSR and S^2-R=xSR. Set H(0)=1+xS, H(3j+1)=SR^j, H(3j+2)=R^(j+1), and H(3j+3)=S^2R^j. The column-one recurrence is checked separately; the three positive residue branches use the two displayed identities. Every constant coefficient is one and H(1)=S. All exponents are natural; no negative exponent or natural division by two is used. The coefficient-identification argument applies to both families. Extracting coefficient n and using the existing injective natural-to-rational cast proves the two equalities. A separate integrality assumption on R is unnecessary.

The source is Kurkov's conjecture in OEIS A376317 revision 25, introduced in revision 15; the original wording and bounded literature search are recorded in the cited Library note. OEIS attribution and its CC-BY-SA-4.0 license apply to source text. The proof is a repository derivation reusing Mathlib's Apache-2.0 Schroder series theorem. The literature search has a bounded scope and does not establish global priority.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.P`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f2`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.f3`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result`
