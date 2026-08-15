# Backward Shift Adjoint

## Abstract

The backward shift and zero-extended translation are Hilbert adjoints whose star products identify the orthogonal projection onto divisible coefficient families.

**Theorem 1.1 (The backward-shift adjoint is forward translation).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{adjoint}(\operatorname{backwardShiftCLM}(u)) = \operatorname{forwardTranslationCLM}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.adjoint_backwardShiftCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bespoke source-pairing identity upgrades to the standard Hilbert-space adjoint: the adjoint of the backward shift is exactly the zero-extended forward translation. Taking adjoints again gives the reverse identity, so the two continuous linear maps are mutual adjoints.

**Theorem 1.2 (The backward-shift star square is the range projection).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{adjoint}(\operatorname{backwardShiftCLM}(u)) \circ \operatorname{backwardShiftCLM}(u) = \operatorname{shiftRangeProjection}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.adjoint_backward_shift_comp_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product B-star B is exactly the divisibility filter. In the opposite order, B B-star is the identity, while the forward translation satisfies V-star V equal to the identity. Thus forward translation is a star isometry and the backward shift is a star coisometry.

**Theorem 1.3 (The range projection is a star projection).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{IsStarProjection}(\operatorname{shiftRangeProjection}(u))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.shift_range_projection_isStarProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjoint reversal exchanges the two shift factors in the projection, so the divisibility filter is self-adjoint. Together with its established idempotence, this makes shiftRangeProjection a star projection rather than only a source-pairing-symmetric operator.

**Theorem 1.4 (Forward translation ranges over divisible families).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{range}(\operatorname{forwardTranslationCLM}(u)) = \operatorname{divisibleSubspace}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.range_forwardTranslationCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The submodule divisibleSubspace u consists of square-summable coefficient families supported only at addresses whose encodings are divisible by u. Zero-extension lands in this submodule, and every member is recovered by forward-translating its backward shift, so this submodule is exactly the range of forward translation.

**Theorem 1.5 (The divisibility filter is the orthogonal projection).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{shiftRangeProjection}(u) = \operatorname{starProjection}(\operatorname{divisibleSubspace}(u))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.shift_range_projection_eq_starProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The star-projection characterization supplies the closed-range orthogonal projection instance for divisibleSubspace u. Since the filter range is that same submodule, uniqueness identifies shiftRangeProjection with the canonical starProjection onto divisible coefficient families.

**Theorem 1.6 (The backward-shift kernel is the wandering complement).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \ker (\operatorname{backwardShiftCLM}(u)) = \operatorname{divisibleSubspace}(u)^{\perp}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.ker_backwardShiftCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard adjoint theorem identifies the kernel of a continuous linear map with the orthogonal complement of the range of its adjoint. Here that adjoint range is divisibleSubspace u, so the backward-shift kernel is precisely the wandering orthogonal complement.

**Theorem 1.7 (The wandering complement is supported off multiples).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall x\in \operatorname{ZetaHilbertSpace},\ x\in \operatorname{divisibleSubspace}(u)^{\perp} \Leftrightarrow \forall b, \operatorname{primeAxisEncoding}(u) \mid \operatorname{primeAxisEncoding}(b) \Rightarrow x(b) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.mem_orthogonal_divisibleSubspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the wandering complement has a coordinatewise description: the coefficient must vanish at every address divisible by u. The forward direction evaluates the zero backward shift at the exact quotient address; the converse checks every translated coordinate of the backward shift.

## References

- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.adjoint_backwardShiftCLM`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.adjoint_backward_shift_comp_self`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.ker_backwardShiftCLM`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.mem_orthogonal_divisibleSubspace`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.range_forwardTranslationCLM`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.shift_range_projection_eq_starProjection`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint.shift_range_projection_isStarProjection`
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry](BackwardShiftCoisometry.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftOperator](BackwardShiftOperator.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/ShiftRangeProjection](ShiftRangeProjection.md)
