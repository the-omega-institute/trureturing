# Golden Prime Classification

## Abstract

Golden prime splitting, inertia, and ramification are classified modulo five.

**Theorem 1.1 (Quadratic-residue criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \land p\neq2 \Rightarrow (\operatorname{IsSquare}(5 : \operatorname{ZMod} p) \Leftrightarrow p\equiv\pm1\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenPrimeClassification.five_is_square_mod_prime_iff_mod_five_eq_one_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd natural prime p other than five, five is a square modulo p exactly when p is congruent to plus or minus one modulo five. The oddness premise is explicit because the equivalence fails at p = 2.

**Theorem 1.2 (Split-prime criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \Rightarrow (\neg\operatorname{Prime}(p : \operatorname{GoldenInt}) \Leftrightarrow p\equiv\pm1\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenPrimeClassification.golden_not_prime_iff_mod_five_eq_one_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime other than five, failure to remain prime in GoldenInt is equivalent to congruence plus or minus one modulo five.

**Theorem 1.3 (Inert-prime criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \Rightarrow (\operatorname{Prime}(p : \operatorname{GoldenInt}) \Leftrightarrow (p\equiv2 \lor p\equiv3)\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenPrimeClassification.golden_prime_iff_mod_five_eq_two_or_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime other than five, remaining prime in GoldenInt is equivalent to congruence two or three modulo five, namely plus or minus two.

**Theorem 1.4 (Five is a ramified square).**

$$5 = (-1+2\varphi)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenPrimeClassification.golden_five_eq_ramified_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In GoldenInt, five is exactly the square of the ramifying element -1 + 2 phi.

## References

- Truth anchor: `D5/S3/PrimeForms/GoldenPrimeClassification.five_is_square_mod_prime_iff_mod_five_eq_one_or_four`
- Truth anchor: `D5/S3/PrimeForms/GoldenPrimeClassification.golden_five_eq_ramified_square`
- Truth anchor: `D5/S3/PrimeForms/GoldenPrimeClassification.golden_not_prime_iff_mod_five_eq_one_or_four`
- Truth anchor: `D5/S3/PrimeForms/GoldenPrimeClassification.golden_prime_iff_mod_five_eq_two_or_three`
