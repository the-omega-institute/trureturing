# Noncommuting clock sublevels

## Abstract

Bounded spectral sublevel projections and strict trial-energy bounds for noncommuting positive operator sums.

**Definition 1.1 (Closed sublevel projection).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a bounded self-adjoint operator T on a complex Hilbert space, the closed sublevel projection at ℓ is the orthogonal projection onto the kernel of the positive part of T − ℓ1, formed by continuous functional calculus.

**Theorem 1.2 (Strict complementary energy and reduction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection_energy_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For T ≥ 0 and ℓ > 0, the kernel of the shifted positive part and its orthogonal complement are both invariant under T. Writing P for the kernel projection gives ℓ‖(1 − P)x‖² ≤ Re ⟪x, Tx⟫, strict whenever the complementary component is nonzero. On the complement this becomes ℓ‖x‖² < Re ⟪x, Tx⟫ for x ≠ 0. The proof uses orthogonality of the positive and negative parts and strict positivity of the square-root norm away from the kernel.

**Theorem 1.3 (Trial-energy sublevel mass and strict rank bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_rank_of_trial_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_rank_of_trial_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For k orthonormal trial vectors u_j and total energy S = ∑_j Re ⟪u_j, Tu_j⟫, the projection mass satisfies k − S/ℓ ≤ ∑_j ‖Pu_j‖². When the range of P is finite-dimensional with rank r < k, Bessel's inequality bounds this mass by r. At least one trial vector has a nonzero complementary component, so summing the strict energy inequality yields ℓ(k − r) < S.

**Theorem 1.4 (Nonzero sublevel and Rayleigh rank).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_nonempty_and_rayleigh_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_nonempty_and_rayleigh_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

If k > 0 and S ≤ kℓ, the closed spectral sublevel is nonzero. For any trial subspace W satisfying Re ⟪v, Tv⟫ ≤ ℓ‖v‖² for every v in W, the sublevel projection is injective on W. A finite-dimensional sublevel therefore bounds the dimension of W from above.

**Theorem 1.5 (Sublevel bounds for positive operator sums).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.noncommuting_sum_sublevel_rank_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.noncommuting_sum_sublevel_rank_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For any finite operator sum T = ∑_i A_i† E_i A_i with E_i ≥ 0, positivity holds without commutation hypotheses. The trial energy is exactly S = ∑_j∑_i Re ⟪A_i u_j, E_i A_i u_j⟫. The projection mass and deficient-rank energy bounds apply to this sum, giving a bounded-operator result for the clock-domain question of Footnote 18.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.noncommuting_sum_sublevel_rank_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevelProjection_energy_lower_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_nonempty_and_rayleigh_rank`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel.sublevel_rank_of_trial_energy`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](../TraceClass/Basic.md)
