# Nonperturbative phase resummation

## Abstract

Finite-coupling absolute convergence versus perturbative cubic harmonic divergence in phase-oscillating mode sums.

**Definition 1.1 (Radial mode term).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.modeTerm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.modeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The k-th mode term (g² / 2) exp(-2 i (k + 1) g) / (k + 1)² at coupling parameter g = 1/s.

**Definition 1.2 (N-mode partial phase sum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.partialPhaseSum`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.partialPhaseSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Finite cutoff sum F_N(g) = ∑_{k < N} modeTerm g k.

**Theorem 1.3 (Finite-coupling absolute convergence and uniform quadratic bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.summable_and_norm_le_modeTerm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.summable_and_norm_le_modeTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Formalizes the finite-coupling convergence of Chandrasekaran (arXiv:2611.34924v1, Section 4.4, Eq. 4.33): for every real coupling g, the infinite mode series converges absolutely and its sum has norm at most g².

**Theorem 1.4 (Exact cubic perturbative coefficient at zero coupling).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.iteratedDeriv_three_partialPhaseSum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.iteratedDeriv_three_partialPhaseSum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Formalizes Eq. 4.34: for every finite mode cutoff N, (1/6) iteratedDeriv 3 (partialPhaseSum N) 0 equals -i times the N-th harmonic number H_N.

**Theorem 1.5 (Harmonic divergence of the cubic perturbative coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.tendsto_neg_im_cubic_coeff_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.tendsto_neg_im_cubic_coeff_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

As N → ∞, the negative imaginary part of the cubic coefficient at g = 0 diverges to +∞, witnessing the failure of the UV limit and zero-coupling expansion to commute.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.iteratedDeriv_three_partialPhaseSum_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.modeTerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.partialPhaseSum`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.summable_and_norm_le_modeTerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.tendsto_neg_im_cubic_coeff_atTop`
