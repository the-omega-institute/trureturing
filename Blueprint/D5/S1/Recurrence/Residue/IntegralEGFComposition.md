# Integral EGF Composition

## Abstract

Factorial-normalized rational coefficients compose by an integral chain-rule recurrence.

For a rational formal power series f, eCoeff(f,n) means n! times its ordinary coefficient. All indices are natural numbers. Composition below uses an inner series with constant coefficient zero; this condition is proved at every use in the A396804 construction.

**Remark 1.1 (Factorial normalization).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient eCoeff(f,n) is defined in Rat, without any integrality assumption.

**Remark 1.2 (Binomial multiplication).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary Cauchy product becomes the sum of binomial(n,i) times eCoeff(f,i) times eCoeff(g,n-i). The factorial identity in Mathlib justifies the conversion.

**Remark 1.3 (Integral composition recurrence).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(f,g)(0)=f(0). At n+1, sum binomial(n,i) C(shift(f),g)(i) g(n-i+1) over 0<=i<=n. This well-founded recurrence makes sense over every commutative semiring and implicitly uses inner constant zero.

**Remark 1.4 (Agreement with rational substitution).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_composition`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_composition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formal chain rule and binomial multiplication prove that the recurrence computes exactly eCoeff(f composed with g). This is an all-degree theorem with the explicit hypothesis constantCoeff(g)=0.

**Remark 1.5 (Coefficient reduction).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_map`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_map` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applying any semiring homomorphism before or after the integral recurrence has the same result. This supplies reduction modulo two and four.

**Remark 1.6 (Dependence on the finite prefix).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_congr`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_congr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-n result depends only on outer and inner coefficients through n. Strong induction proves this locality statement.

**Remark 1.7 (Natural integrality).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.natural_subst`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.natural_subst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural EGF coefficients remain natural under valid substitution. The proof uses the natural-valued recurrence and its rational interpretation.

**Remark 1.8 (Signed integrality).**

Lean statement: `D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst`

*Formalization.* `D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same argument over Int permits subtraction and the integral half-series needed by the modulo-four lifting argument.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_congr`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_map`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_composition`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst`
- Truth anchor: `D5/S1/Recurrence/Residue/IntegralEGFComposition.natural_subst`
