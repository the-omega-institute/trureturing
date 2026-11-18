# Directed closed walks and the pressure curvature dichotomy

## Abstract

Directed closed walks and the pressure curvature dichotomy

**Theorem 1.1 (The exact directed cycle obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.coboundary_iff_closedWalkMean`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.coboundary_iff_closedWalkMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty state type and every irreducible nonnegative matrix P, the arbitrary edge reward g is a constant c plus f(source)-f(target) on the positive support exactly when every supported directed closed walk of positive length has reward sum equal to c times its length. Repeated vertices, repeated edges and loops are included. In one direction the potential telescopes. In the other, the finite-edge MaxPlus theorem supplies potentials for g-c and its negative. Their sum is nondecreasing on every supported edge. A return path from irreducibility forces equality, so both one-sided inequalities become the required edge identity. Empty walks impose no extra condition; their centered weight is zero.

**Theorem 1.2 (Global scalar pressure dichotomy).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.pressure_cycle_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.pressure_cycle_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty irreducible row-stochastic real P, every positive normalized stationary row pi and arbitrary directed reward g, pressure satisfies p(0)=0 and is globally C2. Its Poisson-corrected variance rate vanishes exactly when the supported directed closed walks have a common mean. In that case the common mean equals the stationary mean m, p(t)=tm and the actual global Doob kernel Q_t=P for every real t. Otherwise p second(t)>0 for every real t. No reversibility, aperiodicity, symmetric support or Green-Kubo summability is assumed. Deterministic cycles, singleton states and zero-variance rewards remain included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.coboundary_iff_closedWalkMean`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles.pressure_cycle_dichotomy`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/CyclePressure](CyclePressure.md)
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal](MarkovAdditiveGlobal.md)
