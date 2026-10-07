# The Original Two-Piece Phi Constant

## Abstract

The original two-piece Phi constant has complete integrability and is strictly below one half.

Use the original actualPhi(v)=exp(integral from 0 to 1 of (1-exp(-v*b))/b db) and C=exp(Euler's constant). The near kernel is (actualPhi(v)*(1-exp(-v))-v)/v^2; the far kernel is actualPhi(v)*(1-exp(-v))/v^2-C/v.

**Theorem 1.1 (Complete integrability and the strict half-unit bound).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixOriginalA.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixOriginalA.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original near kernel is interval integrable from 0 to 1. The original far kernel is integrable on the entire interval (1,infinity). The sum of those two literal integrals is strictly less than 1/2.

The finite average of the genuine Phi curvature represents the near kernel at every positive input. The existing literal curvature theorem bounds this continuous average by 1/2, strictly at every positive input, which pays near integrability and the strict near integral bound.

The exact normalization actualPhi(v)=C*v*exp(E1(v)) retains E1(v)=integral over all w>v of exp(-w)/w. The zero endpoint of (1-exp(-w))*log(w) is paid by continuity of w*log(w). Finite and infinite FTC, the original Gamma integral and its Euler constant identity pay the same literal normalization.

For v>=1, E1(v)<=exp(-v)/v<=exp(-v). The strict exponential tangent inequality therefore gives exp(E1(v))*(1-exp(-v))<1. The full far kernel is strictly negative and its absolute value is bounded by 2*C*exp(1)*exp(-v). This pays the complete infinite tail's absolute integrability and strict negative integral.

The literal Phi, rate and finite Ein binding retain the attribution to PrimorialGlobalLaplaceEnvelope; rate differentiation and curvature retain the attribution to PrimePrefixPhiCurvature and its original supplier PrimorialFirstOrderConcentrationCounterexample. The log-exponential integrability and Gamma integral retain the attribution to Mertens.Gamma. The original A estimate is the repository derivation in actual-prefix theory section 444.1. The full Robin pairing and RH remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixOriginalA.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixPhiCurvature](PrimePrefixPhiCurvature.md)
