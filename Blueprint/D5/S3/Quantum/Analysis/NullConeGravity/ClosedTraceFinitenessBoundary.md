# Closed-trace finiteness boundaries

## Abstract

Positive trace-class dimension bounds, cycle-union variance bounds, and exact rearrangement boundaries for closed traces.

**Theorem 1.1 (Finite dimensionality and dimension bound from a trace-class lower bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

If W ≥ 0 is trace-class on a complex Hilbert space H and satisfies c ‖x‖² ≤ Re ⟪x, W x⟫ for all x with c > 0, then H is finite-dimensional and finrank ℂ H ≤ (trace W).re / c.

**Theorem 1.2 (Spectral-sublevel dimension bound from a trace-class cylinder).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

If C ≥ 0 is trace-class on H and satisfies c ‖x‖² ≤ Re ⟪x, C x⟫ on the range of a star projection p (c > 0), then range p is finite-dimensional with finrank ℂ (range p) ≤ (trace C).re / c, matching the positive content of Chandrasekaran (arXiv:2611.34924v1, Appendix E, Eq. E.12).

**Theorem 1.3 (Positive cycle-union area-variance bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_union_area_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_union_area_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Proves the weighted variance bound Δs² + sMax² / (r c) on any finite union of cycles with at most a 1/r fraction of states outside a band of half-width Δs and weights in [c, 1] (Chandrasekaran, arXiv:2611.34924v1, Appendix D.2, Eq. D.25).

**Definition 1.4 (Bounded two-level area function on ℕ).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.toyArea`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.toyArea` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Assigns area 0 to even indices and 1 to odd indices on the orthonormal basis ℕ of ℓ²(ℕ).

**Definition 1.5 (Two-sided pair-flip boost difference kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.pairFlipBoostKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.pairFlipBoostKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Off-diagonal kernel of Δ_η(-σ_x ⊗ σ_x) at boost phase (-1)^{toyArea}, equal to 2 on matched pairs {2m, 2m+1}.

**Definition 1.6 (Subtracted boost observable kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.subtractedKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.subtractedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Kernel of X = Δ_η O − (δ_η/2) I with δ_η = 2.

**Definition 1.7 (Finite-rank closed-cut amplitude).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cutAmplitudeX`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cutAmplitudeX` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Unnormalized closed-cut expectation Z_F[X] = ∑_{i,j ∈ F} subtractedKernel i j on a finite basis subset F.

**Definition 1.8 (Symmetric pair cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.symCut`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.symCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

First N matched pairs {0, ..., 2N − 1}.

**Definition 1.9 (Order-r cycle element).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleElement`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleElement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Places one odd index 2n + 1 with r − 1 even indices in the n-th r-cycle.

**Definition 1.10 (Cycle decomposition bijection).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleBlockEquiv`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleBlockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Explicit bijection ℕ × Fin r ≃ ℕ partitioning ℕ into disjoint r-cycles.

**Definition 1.11 (Order-r cycle permutation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleShiftPerm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleShiftPerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Permutation V_r on ℕ of exact order r whose orbits are the r-cycles of cycleBlockEquiv.

**Definition 1.12 (Finite union of complete r-cycles).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycCut`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Union of the first N complete r-cycles of cycleShiftPerm.

**Theorem 1.13 (Closed-trace rearrangement sign-flip counterexample).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_rearrangement_sign_flip`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_rearrangement_sign_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Isolates the exact analytical gap in Chandrasekaran (arXiv:2611.34924v1, Section 5.2, Eq. 5.38). On the infinite basis ℕ with C_b = 1 and bounded area in [0, 1], both symCut N and cycCut r N (r ≥ 5) exhaust ℕ (so their projections converge strongly to 1), and cycCut r N is invariant under the order-r cycle permutation V_r. Yet cutAmplitudeX (symCut N) = 2N → +∞ while cutAmplitudeX (cycCut r N) = (4 − r)N ≤ −N → −∞.

Hence strong convergence of cycle-union projections plus Z_P[X] ≤ 0 < Z_sym[X] does not contradict infinite dimensionality without an independent trace-class or rearrangement-invariance hypothesis on closed traces.

**Definition 1.14 (Disjoint joint-cut summand).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.jointCutTerm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.jointCutTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Product summand f(i, a) = w_i v_a (1_I(a) − p) on ℕ × α.

**Theorem 1.15 (Exact summability equivalence for disjoint joint cuts).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.disjoint_joint_cut_summable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.disjoint_joint_cut_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Settles the exact logical content of Chandrasekaran (arXiv:2611.34924v1, Eqs. 5.44–5.45): for any nonnegative sequence w and non-degenerate finite distribution v with p = ∑_{a ∈ I} v_a ∈ (0, 1), every fiber sum vanishes identically (∑_a f(i, a) = 0 even when w is non-summable), the fiber L¹ norm equals 2 p (1 − p) w_i, and unconditional summability of f over ℕ × α holds if and only if Summable w already holds.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cutAmplitudeX`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycCut`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleBlockEquiv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleElement`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycleShiftPerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_rearrangement_sign_flip`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.cycle_union_area_variance_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.disjoint_joint_cut_summable_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.jointCutTerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.pairFlipBoostKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.subtractedKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.symCut`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.toyArea`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](../TraceClass/Basic.md)
