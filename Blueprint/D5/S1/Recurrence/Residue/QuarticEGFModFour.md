# A396804 Modulo Four

## Abstract

Every positive-index EGF coefficient in OEIS A396804 is congruent to its index modulo four.

The symbols A and a denote the rational series and natural sequence in QuarticEGFFixedPoint. That module proves the exact zero-constant source equation, existence, uniqueness, and natural integrality. The proof here assumes none of the source's conjectures.

**Remark 1.1 (The comparison series).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFModFour.F`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFModFour.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396804 — E.g.f. satisfies A(x) = x exp(A^4(x))*. URL: <https://oeis.org/A396804>.

*Commentary.*

F=X exp(X). Its factorial-normalized degree-n coefficient is n, including zero.

**Remark 1.2 (Exact square coefficients).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFModFour.square_coeff`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFModFour.square_coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396804 — E.g.f. satisfies A(x) = x exp(A^4(x))*. URL: <https://oeis.org/A396804>.

*Commentary.*

The degree-n EGF coefficient of F composed with F is the sum of binomial(n,k) k k^(n-k) for 0<=k<=n. In characteristic two, k k^(n-k)=k, so the sum is n times 2^(n-1), zero for n>=2.

**Remark 1.3 (The active fourth-iterate escape).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFModFour.linear_fourth_mod_four`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFModFour.linear_fourth_mod_four` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396804 — E.g.f. satisfies A(x) = x exp(A^4(x))*. URL: <https://oeis.org/A396804>.

*Commentary.*

The square has integral EGF coefficients and equals X+2H for an integral half-series H. Substitution preserves coefficient congruences, so H composed with the square equals H modulo two. Composing the square with itself therefore gives X modulo four. This new arithmetic fact is used by the invariant of the natural fixed-point approximations.

**Remark 1.4 (The proposed companion divisibility).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFModFour.fourth_coeff_divisible`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFModFour.fourth_coeff_divisible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396804 — E.g.f. satisfies A(x) = x exp(A^4(x))*. URL: <https://oeis.org/A396804>.

*Commentary.*

For each n>=2 there is a natural k such that n! [X^n](A fourth)=4k. The proof transfers the comparison-series iterate to the constructed A. This is an all-degree statement, not a finite residue table.

**Theorem 1.5 (The OEIS conjecture).**

$$\forall n:\mathbb{N}, 1\leq n\implies \operatorname{a}\left(n\right) \bmod 4=n \bmod 4$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuarticEGFModFour.mod_four` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396804-quartic-egf-mod-four` (proved) by `D5/S1/Recurrence/Residue/QuarticEGFModFour.mod_four`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396804-quartic-egf-mod-four","declaration_gid":"D5/S1/Recurrence/Residue/QuarticEGFModFour.mod_four","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396804 — E.g.f. satisfies A(x) = x exp(A^4(x))*. URL: <https://oeis.org/A396804>.

*Commentary.*

The initial approximation is F in EGF coordinates. The fourth-iterate identity and integral composition show that step preserves coefficient n modulo four. Stabilization gives the claimed congruence for every positive n. The independently computed examples a(2)=2, a(3)=27 and the fourth iterate's second EGF coefficient 8 check nonempty values; they are not used as a bounded proof.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFModFour.F`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFModFour.fourth_coeff_divisible`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFModFour.linear_fourth_mod_four`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFModFour.mod_four`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFModFour.square_coeff`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](QuarticEGFFixedPoint.md)
