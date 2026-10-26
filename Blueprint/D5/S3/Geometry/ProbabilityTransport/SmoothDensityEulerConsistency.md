# The actual density is the characteristic pushforward

## Abstract

The actual density is the characteristic pushforward

**Theorem 1.1 (The actual density is the characteristic pushforward).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency.actual_density_characteristic_pushforward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency.actual_density_characteristic_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive horizon and every observation time r in the closed interval from zero to that horizon, the original density measure at r is exactly the pushforward of the original initial density measure by x mapped to quotient of characteristicOperator at times zero and r applied to representative x. Every finite spatial dimension, including zero, is allowed. The potential and density assumptions are exactly those of the SmoothFP structure in the PeriodicDensityModel module.

All constants are derived from the actual smooth slab before the mesh size N varies. The public actual_density_euler_grid_error theorem gives the finite-N difference between the original density pairing and the same-velocity Euler pairing, bounded by C exp(L r)(K+L B)r squared divided by N. Backward tests are constructed from the terminal C1 test and the actual Euler steps. Their derivative growth is controlled by C exp(L r). The PDE material-derivative formula gives the error on each closed cell, and the cells telescope.

The actual ODE gives a matching inverse-N bound between the actual characteristicOperator and those Euler trajectories. Uniform Euler approximation derives continuity of its forward slices. The public actual_density_characteristic_moment theorem then gives exact equality of all C1 periodic test integrals by the Archimedean inverse-N argument. No Euler invertibility, second derivative of the test, ambient density time extension, or differentiability of the flow is an extra premise.

To pass from moments to measures, the pinned Fourier characters have C1 Euclidean lifts. Their complex linear span is uniformly dense in C(Torus, complex), using span_mFourier_closure_eq_top. Continuous integral functionals therefore agree on every continuous test, which determines the actual finite Borel measures. This is a uniform determining-class argument; L2 density is not used.

The constants theorem covers the zero-length slab in SmoothDensityCharacteristics. The positive-horizon characteristic theorem here covers both closed observation endpoints, including r equal to zero. It does not assert the original C1-in-initial-point flow clause, the endpoint quadratic action estimate, the inverse-horizon Wasserstein bound, or completion of all original section 17.3 obligations. Those remain separate until their exact proofs are supplied.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency.actual_density_characteristic_pushforward`
- Dependency: [D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics](SmoothDensityCharacteristics.md)
- Dependency: [D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport](SmoothDensityWeakTransport.md)
