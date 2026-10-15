# Scalar square-sum Cauchy-Schwarz

## Abstract

Attributed analytic trace infrastructure, used by the original-operator quantum bridge.

**Theorem 1.1 (Scalar square-sum Cauchy-Schwarz).**

$$\forall H \in Type, w \in \operatorname{Set}\left(H\right), f \in w \to \mathbb{R}, g \in w \to \mathbb{R},\; \left(\operatorname{Summable}\left(\left(\operatorname{square}\left(f\left(i\right)\right)\right)_{i \in w}\right) \land \left(\operatorname{Summable}\left(\left(\operatorname{square}\left(g\left(i\right)\right)\right)_{i \in w}\right) \land \left(\operatorname{NonnegativeFamily}\left(f\right) \land \operatorname{NonnegativeFamily}\left(g\right)\right)\right)\right) \Rightarrow \operatorname{tsum}\left(\left(f\left(i\right) \cdot g\left(i\right)\right)_{i \in w}\right) \le \operatorname{sqrt}\left(\operatorname{tsum}\left(\left(\operatorname{square}\left(f\left(i\right)\right)\right)_{i \in w}\right)\right) \cdot \operatorname{sqrt}\left(\operatorname{tsum}\left(\left(\operatorname{square}\left(g\left(i\right)\right)\right)_{i \in w}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt.tsum_mul_le_sqrt_mul_sqrt` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For nonnegative real families f and g on any set-indexed basis carrier, summability of their squares bounds the sum of their products by the product of the square roots of their square sums. The same supplied module gives product summability, basis-independent Hilbert-Schmidt square sums, and bounded multiplication closure. The consumer applies these supplied estimates directly rather than reproving them.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The minimal five-module closure is consumed by the concrete quadratic-reference Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. An equivalent consumed result at the repository-pinned Mathlib replaces the transplant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt.tsum_mul_le_sqrt_mul_sqrt`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](Basic.md)
