# Smooth bounds for a periodic planar sublevel

## Abstract

Smooth tests from the regular zeros bound the entire periodic sublevel.

**Theorem 1.1 (Periodized tests for the strict sublevel).**

Lean statement: `D5/S3/Fourier/Asymptotics/PeriodicSublevelSandwich.periodic_test_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/PeriodicSublevelSandwich.periodic_test_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a continuous map from the Euclidean plane to itself, periodic under integer translations. List all zeros of F in a closed unit square without repetition. Require the listed zeros to lie in the interior and let Aᵢ be the invertible Fréchet derivative at zero zᵢ. The list may be empty.

Choose 0 < η < 1, 0 < ρ < (1+η)⁻¹ and (1−η)⁻¹ < σ. There are fixed smooth compactly supported real lower and upper tests for each center. For every sufficiently small positive ε and every plane representative x, sum each family of tests at (a+x−zᵢ)/ε over all centers and integer shifts a. The resulting sums bound the indicator of ‖F(x)‖ < ε pointwise.

The sum of lower plane integrals is at least πρ² times the sum of |det Aᵢ|⁻¹. The sum of upper plane integrals is at most πσ² times that same sum.

Take disjoint open neighborhoods within the local chart balls and inside the unit square. The norm of F has a positive lower bound on the compact complement. For small ε the scaled test supports lie inside their respective neighborhoods. Each lattice sum then reduces to evaluation at the unique representative in the half-open square. At most one lower test contributes there, and every point in the sublevel has an upper test that dominates the indicator.

Applications supply the zero enumeration and derivatives for the chosen map, and use a separate sampling estimate to count points in the sublevel.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/PeriodicSublevelSandwich.periodic_test_sandwich`
