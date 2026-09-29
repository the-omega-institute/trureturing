# Fast Hidden Gradient Energy

## Abstract

The actual coupled gradient flow has exact dissipation and uniform energy bounds.

For positive dimensions p and r, a positive-definite symmetric block matrix L, epsilon > 0, and any initial state u0, the trajectory is the exponential solution of the full epsilon-scaled block generator. The least eigenvalue ell is the exact minimum of the eigenvalues of L. All estimates hold for every nonnegative time.

**Theorem 1.1 (Energy, state, and visible velocity of the coupled flow).**

Lean statement: `D5/S3/Observer/HiddenFlow/FastSchurGradientEnergy.coupled_energy_state_velocity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/FastSchurGradientEnergy.coupled_energy_state_velocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem gives the actual initial value and both coordinate ODEs, the exact visible and hidden squared-force dissipation identity, energy antitonicity, the ell-coercive state radius, and the visible derivative bound using the Euclidean operator norm of [A B]. It does not establish the fast residual estimate or the uniform slow-trajectory error of Theorem 20.4.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/FastSchurGradientEnergy.coupled_energy_state_velocity`
