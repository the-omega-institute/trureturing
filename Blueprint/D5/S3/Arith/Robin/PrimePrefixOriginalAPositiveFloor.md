# A Strict Positive Reserve for the Original Complete A

## Abstract

The exact positive curvature remainder proves the original complete A is strictly between one sixteenth and one half.

Keep the literal Phi curvature B(v), the original complete two-piece constant A, gamma=Euler's constant and k=exp(gamma)-1. Define R(v)=B(v)-exp(-v)/2, r=k-1/2 and g(v)=(2*r*v-1-log(2*r*v))*R(v).

**Theorem 1.1 (Complete remainder moments, the exact strict gap and a positive reserve).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass r is strictly positive. The functions R(v), v*R(v) and log(v)*R(v) are absolutely integrable on the entire positive axis, with complete mass integral R=r and first moment integral v*R=1/2. The original complete constant satisfies A=gamma/2-integral log(v)*R(v).

The full g kernel is absolutely integrable. Its complete integral equals A-gamma/2-r*log(2*r) and is strictly positive. Thus gamma/2+r*log(2*r)<A and 1/16<A<1/2.

PrimePrefixCurvatureExponentialFloor supplies the exact whole-axis positive remainder. PrimePrefixCurvatureMoments supplies the complete original mass k, first moment 1 and logarithmic binding. The classical half-exponential density contributes mass 1/2, first moment 1/2 and logarithmic moment -gamma/2; all integrals retain their full tails.

The logarithmic tangent makes g nonnegative everywhere on the positive axis and strictly positive for v>1/r, where the exact remainder is strictly positive. The positive-integral support criterion pays strictness. The scalar bound x*log(x)>=-1/exp(1), the existing gamma>1/2 and exp(1)>8/3 then give A>1/16.

The original A and Euler amplitude remain the public PrimePrefixOriginalShoulder definitions; A<1/2 is reused from PrimePrefixOriginalA. The complete exponential log integrability proof and Gamma identity retain Mertens.Gamma and Mathlib provenance. The result does not assume A is positive and does not pay the remaining Robin signed tail.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixCurvatureExponentialFloor](PrimePrefixCurvatureExponentialFloor.md)
- Dependency: [D5/S3/Arith/Robin/PrimePrefixCurvatureMoments](PrimePrefixCurvatureMoments.md)
- Dependency: [D5/S3/Arith/Robin/PrimePrefixOriginalShoulder](PrimePrefixOriginalShoulder.md)
