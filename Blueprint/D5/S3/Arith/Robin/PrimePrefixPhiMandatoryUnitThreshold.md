# The Exact Three-Point Error with a Mandatory Unit Atom

## Abstract

A fixed genuine unit atom strictly increases the exact three-point positive Laplace error of the literal Phi curvature, with a genuine two-atom measure attaining the new threshold.

Retain the original actualPhi(v)=exp(integral from 0 to 1 of (1-exp(-v*b))/b db), B=deriv(deriv actualPhi), and c>0. For every compact unit budget 0<=aMax<c/2, the theorem fixes one eta>0 before the endpoints, unit mass, or measure are selected.

**Theorem 1.1 (A stronger exact threshold and an actual attaining measure).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixPhiMandatoryUnitThreshold.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixPhiMandatoryUnitThreshold.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any 0<p<q<eta and 0<=a<=aMax, set m=(p+q)/2, x=c*B(p), y=c*B(m), z=c*B(q), S=2*y+x+z, K=(y*y-x*z)/S, and Ka=((y-a)*(y-a)-(x-a)*(z-a))/(S-4*a). Both thresholds are positive. Their exact difference is Ka-K=a*(x-z)*(x-z)/(S*(S-4*a)), and K<Ka whenever a>0.

Every positive measure mu on the real line with genuine unit mass mu({0})=ENNReal.ofReal(a) and integrable exp(-p*t), exp(-q*t), and exp(-m*t) has at least one absolute error between its three actual exponential integrals and x,y,z at least Ka. The comparison class has no total-mass or support restriction.

The same result constructs tau>0 and w>0. The actual measure ENNReal.ofReal(a) times Dirac(0) plus ENNReal.ofReal(w) times Dirac(tau) has precisely the fixed unit mass. Its exponential kernel is genuinely integrable at every real parameter v, and its integral is a+w*exp(-v*tau). All three actual integral errors at p,m,q equal Ka. The original p=h,q=2*h triple is included, and a=0 recovers the unrestricted threshold.

Continuity of the literal curvature and its zero value give c*B(v)>aMax on one common interval. The actual negative fourth derivative and derivative criteria supply strict concavity and decrease there. Restricting mu to the complement of {0} leaves a genuine positive measure whose exponential integrals are exactly those of mu minus a. Three true integrability hypotheses pay the integrated-square discriminant inequality; the residual sharp data give the stronger lower bound.

The original Phi and first derivative retain PrimorialGlobalLaplaceEnvelope attribution. Private moment, derivative, integrated-square and atom bodies reuse the staged PrimePrefixPhiFourthDerivativeObstruction supplier, preserving PrimePrefixPhiCurvature and its original PrimorialFirstOrderConcentrationCounterexample provenance. Mathlib supplies measure restriction, true Dirac integrals and derivative criteria. The fixed-unit threshold is the zero-negative-Jordan-cost branch of actual-prefix theory section 461. The complete signed n_a optimum, actual arithmetic unit and node suppliers, and complete critical signed tail remain obligations.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixPhiMandatoryUnitThreshold.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction](PrimePrefixPhiFourthDerivativeObstruction.md)
