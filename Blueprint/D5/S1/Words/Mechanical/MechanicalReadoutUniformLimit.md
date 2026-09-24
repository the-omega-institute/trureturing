# Mechanical Readout Uniform Limit

## Abstract

Geometric mechanical readouts approach their slope uniformly as the weights flatten.

**Theorem 1.1 (Uniform slope approximation and a joint error budget).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every slope in [0,1), every real phase, and every geometric ratio in [0,1), the completed readout differs from the slope by at most 1-r. The cumulative count of actual mechanical letters differs from its slope prediction by less than one. Finite Abel summation weights these discrepancies by nonnegative successive weight drops whose total is 1-r, and the geometric tail passes the bound to the infinite readout. For any target slope and finite horizon n, the truncated readout differs from the target by at most r^n plus 1-r plus the parameter distance. Both estimates hold uniformly in phase, including phases where the fixed-ratio readout jumps as a function of slope.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound`
- Dependency: [D5/S1/Words/Mechanical/MechanicalDensity](MechanicalDensity.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutOrder](MechanicalReadoutOrder.md)
