# Mechanical Readout Uniform Limit

## Abstract

Geometric mechanical readouts approach their slope uniformly as the weights flatten.

**Theorem 1.1 (One-sided slope approximation and a joint error budget).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every slope in [0,1), every real phase, and every geometric ratio in [0,1), the completed readout differs from the slope by an amount between (1-r)*(fract(x)-1) and (1-r)*fract(x). The cumulative floor discrepancy is exactly fract(x)-fract(x+k*alpha). Finite Abel summation weights these discrepancies by nonnegative successive weight drops whose total is 1-r, and the geometric tail passes the one-sided bounds to the infinite readout. In particular, its absolute error is at most 1-r. For any target slope and finite horizon n, the truncated readout differs from the target by at most r^n plus 1-r plus the parameter distance. These estimates hold uniformly in phase, including phases where the fixed-ratio readout jumps as a function of slope.

**Theorem 1.2 (The two orders of the horizon and weight limits).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a fixed geometric ratio below one, the finite mechanical readout converges to its completed value as the horizon grows. As the ratio approaches one from below, the completed readout converges to the slope, while every fixed finite prefix converges to zero. The two iterated limits therefore differ whenever the slope is positive.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound`
- Dependency: [D5/S1/Words/Mechanical/MechanicalDensity](MechanicalDensity.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutOrder](MechanicalReadoutOrder.md)
