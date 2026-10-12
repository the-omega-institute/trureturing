# Actual Prime Hecke Trace

## Abstract

An actual trace-and-translate prime Hecke endomorphism on level-one cusp forms.

**Theorem 1.1 (Actual prime Hecke endomorphism).**

$$\operatorname{primeHecke} : CuspForm \Rightarrow CuspForm$$

*Proof.* Machine-checked in Lean as `D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and an integer weight k, this is the complex-linear map obtained by translating by the rational diagonal p-isogeny matrix and applying Mathlib's finite-index cusp-form trace. The codomain is the level-one CuspForm space itself; the trace construction supplies holomorphy and vanishing at every cusp.

**Theorem 1.2 (Pointwise trace application).**

$$\operatorname{primeHeckeApply}$$

*Proof.* Machine-checked in Lean as `D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise equality unfolds the endomorphism to the actual translated cusp-form trace. The finite quotient and its inverse representative convention remain explicit in the library definition.

The explicit P^1(F_p) representative expansion, the literal upper-triangular slash formula, and the unconditional convergent q-expansion coefficient law are not asserted by this document; they remain the next unpaid obligations for the complete analytic unit.

## References

- Truth anchor: `D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke`
- Truth anchor: `D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke_apply`
