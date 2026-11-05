# The strict omitted tail and original finite time

## Abstract

The strict omitted tail and original finite time.

**Theorem 1.1 (The strict omitted tail and original finite time).**

Lean statement: `D5/S3/Weil/ZeroData/ActualGaussianDirectTail.full_E_original_time`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualGaussianDirectTail.full_E_original_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>=1, gamma>10, t nonzero and abs(t-gamma)>=6, the scalar majorant exp(-m*(t-gamma)^2)<=(gamma+10)^2*exp(-36*m)/t^2 is proved directly. The strip contributes exp(17*m). Summing only occurrences with STRICT distance greater than six therefore gives norm(sum omitted)<=2*(gamma+10)^2*exp(-19*m).

This stronger constant-two bound immediately implies the old constant-four bound because (gamma+10)^2*exp(-19*m)>=0. The unused omitted_tail_original weakening is omitted from Lean source. full_E_original_time actually consumes the stronger bound. The split E=closed-local-sum+strict-omitted-sum is made only after absolute convergence.

For an actual rho with Re(rho)>1/2 and Im(rho)>0, let delta=Re(rho)-1/2, D=Im(rho)+10, m0=100*D^2/delta^2, m1=500*D^4/delta^2 and a=Re(rho)^2+16*Re(rho). The local window includes an actual occurrence of rho and all its other analytic repetitions. Existing ZeroPowerSum.exists_pow_sum_re_ge_one chooses an integer nu between one and 2*card(window)+1, giving m=nu*m0 in [m0,m1] and a local real sum at least exp(a*m).

The actual height and strip give m>=1 and allow the entire omitted tail to be absorbed below 1/2. Therefore there exists m in the original interval, with m>=1 and Re(E(m,Im(rho)))>=exp(a*m)/2. OriginalPositiveUPeak consumes exactly this lower bound; no height, tail or full-E lower bound is a premise.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualGaussianDirectTail.full_E_original_time`
- Dependency: [D5/S3/Arith/Robin/ZeroPowerSum](../../Arith/Robin/ZeroPowerSum.md)
- Dependency: [D5/S3/Weil/ZeroData/ActualGaussianLocalWindow](ActualGaussianLocalWindow.md)
