# Actual Relative Clock Covariance for the Finite Robin Log Kernel

## Abstract

For the literal finite clipped kernel W(A,x)=sum over 2<=k<=floor A of
log(k)*max(g(k*x)-g(A),0), the common ambient floor is proved equal to the
literal definition, including noninteger clocks. Increasing the clock
increases each W(A,x), while the relative activation W(A,x)-W(A',x) decreases
in x. Consequently the unnormalized covariance across an actual finite clock
sample is nonnegative on positive shifts and decreases when both arguments
advance.

**Theorem 1.1 (actual covariance signs and support).**

Lean statement:
D5/S3/Arith/Robin/ActualRobinClockCovariance.actual_clock_covariance.

*Proof.* Machine-checked in Lean as the exact finite clipped-kernel theorem.

*Source.* Repository-derived.

The theorem includes the empty sample case. If every clock is at most b and
b <= 2*y, the later covariance is exactly zero. No covariance envelope,
relative-clock K or C bound, Corr estimate, CA optimizer realization, or
Robin/RH conclusion is assumed or asserted here.

The exact finite Abel coefficient-mass estimate and its conditional Corr
consumer remain open follow-on obligations. The complete Robin state retains
m*Rbar^2, V_a, 2*sum mu(d)*beta(d), D_sf, the unit index, all lower rows,
untreated shifts, reserve, and defect.

## References

- Truth anchor: D5/S3/Arith/Robin/ActualRobinClockCovariance.actual_clock_covariance
- Existing finite Abel consumers: ActualOddMobiusFinitePairing and
  PrimePrefixMobiusDirectedAbel
