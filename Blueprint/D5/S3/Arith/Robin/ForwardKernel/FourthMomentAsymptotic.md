# Cumulative fourth-moment asymptotics

## Abstract

Uniform cumulative fourth-moment asymptotics give band and local energy estimates.

**Definition 1.1 (The uniform cumulative formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.FourthMomentAsymptoticFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.FourthMomentAsymptoticFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every eta>0, one threshold in Y works for every Y^alpha<=v<=Y^beta: the absolute difference between the integral of |E(x+v)-E(x)|^4 over [1,Y] and 3*v^2 times the integral of (log(y/v)+B)^2 over [1,Y] is at most eta*Y*v^2*log(Y/v)^2. The threshold is independent of v.

**Theorem 1.2 (The fourth-moment band bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_band`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose E is locally bounded and measurable and 0<alpha<beta<1. The uniform cumulative formula implies the existence of a nonnegative C such that the fourth moment is at most C*Y*v^2*log(Y/v)^2 for all sufficiently large Y and all lengths in the exponent band. On [1,Y], the bounds 1<=v<=Y give |log(y/v)|<=log(Y), while log(Y/v)>=(1-beta)*log(Y). One may take C=3*((1+|B|)/(1-beta))^2+1.

**Theorem 1.3 (Local fourth energy with constant thirteen).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_local`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions, there is a nonnegative epsilon(X) tending to zero such that, for all sufficiently large X, simultaneously for X/2<=A<=B<=4X and (4X)^alpha<=v<=(X/2)^beta, the integral of |E(y+v)-E(y)|^4 over [A,B] is at most 13*v^2*log(X)^2*(B-A+epsilon(X)*X).

The length v lies in the exponent band at both cumulative endpoints. Subtract the formulas at B and A. Their main terms differ by the integral over [A,B], where 0<=log(y/v)<=2*log(X). Once log(X)>=20*|B|, three times (2*log(X)+|B|)^2 is at most 13*log(X)^2. Each cumulative error is at most 16*delta*X*v^2*log(X)^2; delta=13*eta/32 gives the window bound with any prescribed eta>0. Taking an infimum of admissible nonnegative window errors and adding 1/max(1,X) produces a single nonnegative error function tending to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.FourthMomentAsymptoticFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_band`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentAsymptotic.asymptotic_implies_local`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs](FourthMomentBandDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentTransferDefs](FourthMomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
