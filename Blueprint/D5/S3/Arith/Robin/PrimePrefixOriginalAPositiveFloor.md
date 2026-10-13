# A Strict Positive Reserve for the Original Complete A

## Abstract

The exact positive curvature remainder and a compiled scalar application put the original complete A strictly between 21/200 and one half.

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

An exact scalar application improves the lower reserve to A>21/200 while retaining this same original A, full remainder and all three complete moments. Mathlib's strict lower Euler sequence gives H_32-log(33)<gamma. The exact harmonic value satisfies H_32>2029/500, log(2)<1733/2500 and the logarithmic tangent gives log(33)<=5*log(2)+1/32, so gamma>14/25. The first five nonnegative terms of the exponential series give exp(14/25)>7/4; hence r=exp(gamma)-3/2>1/4. The tangent 1-1/(4*r)<=log(4*r), together with log(2)<1, gives r*log(2*r)>=-log(2)/4. Applying the already proved strict gap gamma/2+r*log(2*r)<A and log(2)<7/10 yields A>21/200. This same-source application passed actual Lean compilation with the standard axiom closure. Its saved proof is a transient reuse check, with no new canonical wrapper or additional theorem Describe.

The original A and Euler amplitude remain the public PrimePrefixOriginalShoulder definitions; A<1/2 is reused from PrimePrefixOriginalA. The complete exponential log integrability proof and Gamma identity retain Mertens.Gamma and Mathlib provenance. The result does not assume A is positive and does not pay the remaining Robin signed tail. The stronger scalar reserve also does not supply a lower bound for the original frozen-window baseline plus its signed Mobius endpoint integral, cofinal actual positive-mass windows, RH or all-integer strict Robin beyond 5040; the required source transmission remains a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixCurvatureExponentialFloor](PrimePrefixCurvatureExponentialFloor.md)
- Dependency: [D5/S3/Arith/Robin/PrimePrefixCurvatureMoments](PrimePrefixCurvatureMoments.md)
- Dependency: [D5/S3/Arith/Robin/PrimePrefixOriginalShoulder](PrimePrefixOriginalShoulder.md)
