# Noncommutative null-cone clock-area bounds

## Abstract

Noncommutative operator Cauchy-Schwarz rigidity and shear-focusing clock-area bounds on any complex Hilbert space.

**Theorem 1.1 (Exact noncommutative weighted operator Cauchy-Schwarz identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For any finite index set, real weights w_i, and arbitrary (not necessarily commuting) bounded linear operators A_i on a complex Hilbert space H, the weighted second-moment defect (∑ w_i)(∑ w_i ‖A_i η‖²) − ‖(∑ w_i A_i) η‖² equals half the double sum ∑_i ∑_j w_i w_j ‖(A_i − A_j) η‖².

Expanding the squared norm of the weighted sum via the complex inner product and comparing against pairwise norm-difference squares yields the identity with no commutativity assumption.

**Theorem 1.2 (Noncommutative weighted operator Cauchy-Schwarz inequality).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

When all weights w_i are nonnegative, the exact pairwise-difference sum is nonnegative, giving ‖(∑ w_i A_i) η‖² ≤ (∑ w_i)(∑ w_i ‖A_i η‖²).

**Theorem 1.3 (Uniform-cap rigidity for operator Cauchy-Schwarz).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

When all weights w_i are strictly positive, equality holds on η if and only if A_i η = A_j η for every pair i, j in the index set.

**Theorem 1.4 (Noncommutative shear-focusing clock lower bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_shear_clock_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_shear_clock_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Extends the null-cone gravitational clock bound (Chandrasekaran, arXiv:2611.34924v1, Eqs. 4.26–4.27 and 5.21a–c) to arbitrary noncommuting bounded operators A_i with fixed total area ∑ w_i ‖A_i η‖² = area · ‖η‖², self-adjoint square root B with B² = ∑ w_i A_i, and focusing operators E_i satisfying Re ⟪v, E_i v⟫ ≥ ‖v‖².

Combining focusing monotonicity with the noncommutative operator Cauchy-Schwarz bound on a = ∑ w_i A_i and Hilbert-space Cauchy-Schwarz on ‖B η‖² = Re ⟪η, a η⟫ yields (1 − ε) √(area / M) ‖B η‖² ≤ (1 − ε) ∑ w_i Re ⟪A_i η, E_i(A_i η)⟫ without classical Wigner heuristics.

**Theorem 1.5 (Corner-area ceiling from a bounded noncommutative clock reading).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_clock_area_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_clock_area_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Whenever B η ≠ 0 and the noncommutative clock quadratic form is at most ℓ ‖B η‖² (ℓ ≥ 0, ε < 1), the fixed corner area obeys area ≤ M ℓ² / (1 − ε)² (generalizing Eq. 5.21d).

**Definition 1.6 (Shear-delayed corner clock reading).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shearDelayedClock`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shearDelayedClock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Area-weighted average of per-generator clock readings (1 − ε) ρ_i + δ_i over a finite corner partition.

**Theorem 1.7 (Two-channel clock deficit decomposition and uniform shear-free rigidity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shear_clock_deficit_and_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shear_clock_deficit_and_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Decomposes the excess of the shear-delayed clock over the round shear-free floor (1 − ε) √(A / M) into two nonnegative channels—corner-density inhomogeneity and radiative shear delay—and proves that equality holds if and only if every shear delay vanishes and the corner density is constant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_clock_area_upper_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_shear_clock_lower_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_eq_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_identity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.operator_weighted_cauchy_schwarz_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shearDelayedClock`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.shear_clock_deficit_and_rigidity`
