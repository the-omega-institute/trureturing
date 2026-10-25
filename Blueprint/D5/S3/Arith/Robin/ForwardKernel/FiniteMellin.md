# Finite Mellin corrections

## Abstract

Bounded intervals of the original adjoint contribute entire Mellin corrections.

**Theorem 1.1 (An integrable density on positive compact centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.compact_mellin_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.compact_mellin_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a>0 and f is complex-valued and integrable on [a,b], then the integral of f(x)*x^(-s-1) over that interval is entire in s. Extend f by zero outside [a,b]. This integrable extension vanishes near zero and at infinity, so Mathlib's mellin_differentiableAt_of_isBigO_rpow applies at every complex parameter. Composing with negation gives the stated exponent.

**Theorem 1.2 (Entire dependence at a fixed adjoint point).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=4 and every real t, the actual adjoint q_s(t) is entire in s. Its center integral has compact support in [x0,max(x0,t)], so the compact Mellin theorem applies to the original price kernel.

**Theorem 1.3 (A bounded interval of adjoint points).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_finite_integral_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_finite_integral_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 4<=x0<=b, the integral of q_s(t) over [1,b] is entire. All its center integrals lie in [x0,b]. The original kernel lies between zero and one, and the Mellin powers are uniformly bounded on compact parameter sets. These bounds allow integration of the entire parameter family.

**Theorem 1.4 (The bounded signed correction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.finiteCorrection_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.finiteCorrection_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract n^(-s-1/2)/2 from q_s(n) in the finite complete Mangoldt sum up to floor(b), and subtract the corresponding Lebesgue integral on [1,b]. The resulting correction is entire. The zero index has zero Mangoldt weight; every positive base in the finite sum and integral has an entire complex power.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_entire`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_finite_integral_entire`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.compact_mellin_entire`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.finiteCorrection_entire`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Adjoint](Adjoint.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Analytic](Analytic.md)
