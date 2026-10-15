# Actual Five-Mode Waits Span the Real Symmetric Effects

## Abstract

Actual Five-Mode Waits Span the Real Symmetric Effects

**Lemma 1.1 (The fixed generator is skew symmetric).**

$$\operatorname{transpose}(generator)=-generator$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.generator_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This coordinate identity is consumed by the waiting-span theorem and by the complex unitary realization of the same menu.

**Theorem 1.2 (Actual Five-Mode Waits Span the Real Symmetric Effects).**

$$waitSpan=\operatorname{Sym}(5,\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.five_mode_nonnegative_wait_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed real skew generator has rows (0,1,1,1,0), (-1,0,0,0,-1), (-1,0,0,0,0), (-1,0,0,0,-1), and (0,1,0,1,0). Its coordinate order is N, 2, 3, 5, 25. Only nonnegative real waiting times followed by a complete mode read enter the observation span.

The fifteen selected commutator jets have orders and modes (0,0) through (0,4), (1,0) through (1,3), (2,0) through (2,2), (3,0), (3,1), and (4,0). The fulfilled numerical premise symmetric_decomposition expresses every real symmetric matrix as a linear combination of these same-generator jets with exact coefficients. The theorem reduces the continuous span to this finite premise; waits_separate_real and actual_effect_span_eq in FiveModeRealResponse consume the resulting full nonnegative-time span on the proof path to the public five_mode_real_response_fiber theorem.

The analytic supplier NonnegativeConjugationSpan puts each jet in the closed span of actual nonnegative-time effects. The reverse inclusion uses skew symmetry and the transpose identity for matrix exponentials. Consequently the commutator spanning calculation determines the actual waiting-effect span; the menu only requires waiting and reading.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.five_mode_nonnegative_wait_span`
- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.generator_skew`
- Dependency: [D5/S3/Quantum/Fibers/NonnegativeConjugationSpan](NonnegativeConjugationSpan.md)
