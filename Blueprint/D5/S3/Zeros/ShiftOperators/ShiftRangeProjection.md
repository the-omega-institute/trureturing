# Shift Range Projection

## Abstract

The backward-shift defect projection is the norm-one divisibility filter on zeta coefficients.

**Theorem 1.1 (The projection is the divisibility filter).**

$$\forall u, b\in \operatorname{PrimeAxisTable},\ \forall x\in \operatorname{ZetaHilbertSpace},\ \operatorname{shiftRangeProjection}(u)(x)(b) = \begin{cases}x(b),&\operatorname{primeAxisEncoding}(u) \mid \operatorname{primeAxisEncoding}(b)\\0,&\text{otherwise}\end{cases}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shiftRangeProjection_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime-axis address u, the projection retains exactly those coefficients whose encoded address is divisible by the encoding of u. At a divisible address it returns the original coefficient, and at every other address it returns zero.

**Theorem 1.2 (The projection is idempotent).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \operatorname{shiftRangeProjection}(u) \circ \operatorname{shiftRangeProjection}(u) = \operatorname{shiftRangeProjection}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the divisibility filter twice has the same effect as applying it once. The proof is coordinatewise: on divisible addresses both passes retain the coefficient, while on all other addresses the first pass has already produced zero.

**Theorem 1.3 (The backward shift and projection have the same kernel).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall x\in \operatorname{ZetaHilbertSpace},\ \operatorname{backwardShiftCLM}(u)(x) = 0 \Leftrightarrow \operatorname{shiftRangeProjection}(u)(x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.backward_shift_apply_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hilbert vector is annihilated by the backward shift exactly when it is annihilated by the defect projection. One direction follows by applying forward translation to zero; the reverse follows by applying the backward shift and using its right-inverse identity.

**Theorem 1.4 (The projection has norm one).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \Vert \operatorname{shiftRangeProjection}(u)\Vert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_norm_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection is a contraction because forward translation preserves the norm and the backward shift is norm-nonincreasing. The unit single-support vector at u is fixed by the projection, so the contraction bound is attained and the operator norm is exactly one.

**Theorem 1.5 (The projected zeta pairing reproduces the Euler-factor kernel).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall s, w\in \mathbb{C},\ (\operatorname{criticalAbscissa} < \Re{s} \land \operatorname{criticalAbscissa} < \Re{w}) \Rightarrow \operatorname{sourcePairing}(\operatorname{shiftRangeProjection}(u)(\operatorname{labeledZetaVector}(s)), \operatorname{labeledZetaVector}(w)) = \operatorname{labeledZetaCoefficient}(s + \overline{w}, u) \cdot \operatorname{classicalZeta}(s + \overline{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_zeta_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For square-summable labeled zeta vectors at s and w, projecting the first vector before taking the source pairing multiplies the zeta reproducing kernel by the u-th labeled coefficient at s plus conjugate w. The proof uses the backward-shift eigenrelation, pairing adjointness, and the multiplicativity of the labeled coefficient.

## References

- Truth anchor: `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.backward_shift_apply_eq_zero_iff`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shiftRangeProjection_apply`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_idempotent`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_norm_eq_one`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/ShiftRangeProjection.shift_range_projection_zeta_kernel`
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry](BackwardShiftCoisometry.md)
