# Complete Curvature Moments of the Literal Prime-Prefix Phi

## Abstract

The literal Phi curvature has complete mass, first and logarithmic moments, and an exact full excess tail.

Use the original actualPhi(v)=exp(integral from 0 to 1 of (1-exp(-v*b))/b db), C=exp(Euler's constant), and B(v)=actualPhi''(v). Retain the original two-piece constant A=integral from 0 to 1 of (actualPhi(v)*(1-exp(-v))-v)/v^2 plus the integral over every v>1 of actualPhi(v)*(1-exp(-v))/v^2-C/v.

**Theorem 1.1 (Complete moments and the full excess-tail identity).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixCurvatureMoments.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixCurvatureMoments.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The functions B(v), v*B(v), and log(v)*B(v) are absolutely integrable on the entire interval (0,infinity). Their complete mass and first moment satisfy integral B=C-1 and integral v*B=1. The same original two-piece constant satisfies A=-integral over all v>0 of log(v)*B(v).

For every real t>=0, (v-t)*B(v) is absolutely integrable over the entire interval v>t, and its full integral equals actualPhi(t)-C*t. This includes the zero endpoint and retains all of the infinite tail.

The same original derivative has actualPhi'(0)=1 and actualPhi'(v) tending to C. Its derivative is B, giving the full curvature mass. The primitive v*actualPhi'(v) -actualPhi(v) has value -1 at zero, tends to zero at infinity, and has derivative v*B(v). The shifted primitive (v-t)*actualPhi'(v)-actualPhi(v) has derivative (v-t)*B(v), value -actualPhi(t) at t, and limit -t*C.

Near zero, B(v)<=1/2 dominates the logarithmic moment by an integrable multiple of absolute log(v); on v>=1, log(v)<=v is dominated by the complete first moment. The original near and far kernels equal (actualPhi'(v)-1)/v and (actualPhi'(v)-C)/v. Integration by parts with their logarithmic primitives pays both endpoints and gives the original A identity.

The exact normalization actualPhi(v)=C*v*exp(E1(v)) uses E1(v)=integral over every w>v of exp(-w)/w. Its full exponential tail bound supplies the slope limit and all primitive limits at infinity. The near logarithmic primitive is continuous at zero through a finite curvature average times v*log(v).

The literal Phi, rate and finite Ein binding retain PrimorialGlobalLaplaceEnvelope provenance. The all-real rate derivative and curvature retain PrimePrefixPhiCurvature provenance and its original supplier PrimorialFirstOrderConcentrationCounterexample. The consumed Ein/E1/Euler normalization and the original two-piece A integrability retain PrimePrefixOriginalA provenance; its log-exponential and Gamma integral suppliers retain Mertens.Gamma provenance. The curvature moment and complete excess-tail identities are the actual-prefix theory section 450 derivation.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixCurvatureMoments.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixOriginalA](PrimePrefixOriginalA.md)
