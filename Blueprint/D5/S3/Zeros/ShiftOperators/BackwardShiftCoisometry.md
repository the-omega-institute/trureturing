# Backward Shift Coisometry

## Abstract

The backward shift is a norm-one coisometry with an isometric right inverse.

**Theorem 1.1 (Forward translation is a right inverse).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall x\in \operatorname{ZetaHilbertSpace},\ \operatorname{backwardShiftCLM}(u)(\operatorname{forwardTranslationCLM}(u)(x)) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_comp_forward_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime-axis address u, applying the backward shift after the zero-extended forward translation returns every Hilbert vector x. At a translated coordinate, Function.extend evaluates to the original coefficient because normalizedTableAdd is injective.

**Theorem 1.2 (The backward shift is surjective).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{Surjective}(\operatorname{backwardShiftCLM}(u))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime-axis address u, backwardShiftCLM is onto. The explicit preimage of x is forwardTranslationCLM u x, so surjectivity follows directly from the right-inverse identity.

**Theorem 1.3 (Forward translation is an isometry).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall x\in \operatorname{ZetaHilbertSpace},\ \Vert \operatorname{forwardTranslationCLM}(u)(x)\Vert = \Vert x\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.forward_translation_norm_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward translation is norm-nonincreasing by its zero-extension construction. Applying the norm-nonincreasing backward shift and then using the right-inverse identity gives the reverse inequality, hence exact preservation of the Hilbert norm.

**Theorem 1.4 (The backward shift has norm one).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \Vert \operatorname{backwardShiftCLM}(u)\Vert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_operator_norm_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen contraction estimate supplies the upper bound one. A unit single-support vector remains unit under forward translation and is sent back to itself, so the backward shift attains that bound and its operator norm is exactly one.

## References

- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_comp_forward_translation`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_operator_norm_eq_one`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.backward_shift_surjective`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry.forward_translation_norm_eq`
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftOperator](BackwardShiftOperator.md)
