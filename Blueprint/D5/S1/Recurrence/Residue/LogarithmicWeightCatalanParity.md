# Logarithmic-Weight Coefficients Modulo Three

## Abstract

OEIS A397349 alternates 1, 2 modulo three at positive indices; its parity conjecture remains open.

The NAME and both conjecture COMMENTS are quoted in hanna2026a397349. Only the modulo-three statement is proved below. The separate statement that a(n) is odd exactly at powers of two is not proved: parity_conjecture is a proposition definition carrying no proof, and is not a theorem.

Write a for the module's function from natural numbers to integers. The displayed mod denotes the remainder operation: integer remainder for a(n) mod 3, natural-number remainder for n mod 2. The words if, then, else denote Lean's conditional, with integer-valued branches 1 and 2. A single well-founded recursion constructs s with s(0)=s(1)=0. Define a(k)=1 if k=1 and (3*k^2-1)*s(k) otherwise; b(m)=1 if m<=1 and 3*m*s(m) otherwise. For n>=2, s_eq_sum gives s(n)=sum over 1<=k<n of a(k)*b(n-k). No uniqueness or formal identification with the logarithmic generating function is proved here.

**Theorem 1.1 (Hanna's modulo-three conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{a}\left(n\right) \operatorname{mod} 3) = \operatorname{if} (n \operatorname{mod} 2) = 1 \operatorname{then} 1 \operatorname{else} 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.hanna_conjecture_a397349_mod_three` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397349-logarithmic-weight-mod-three` (proved) by `D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.hanna_conjecture_a397349_mod_three`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397349-logarithmic-weight-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.hanna_conjecture_a397349_mod_three","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397349, logarithmic-weight coefficients: residue and parity*. URL: <https://oeis.org/A397349>.

*Commentary.*

For m>=2, b_mod_three uses the explicit factor of three in b(m). In s_eq_sum only k=n-1 survives modulo three, since b(1)=1; the lemma s_mod_three proves s(n) mod 3 = a(n-1) mod 3. The factor 3*n^2-1 has remainder 2, so a_mod_three_step gives a(n) mod 3 = (2*(a(n-1) mod 3)) mod 3. Induction from a(1)=1 proves the displayed alternation. This argument does not prove the parity conjecture, which remains open.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.hanna_conjecture_a397349_mod_three`
