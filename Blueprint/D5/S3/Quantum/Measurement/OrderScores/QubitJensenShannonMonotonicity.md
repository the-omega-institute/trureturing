# Monotonicity of the qubit Jensen–Shannon order score

## Abstract

Strict increase of Wu’s optimized qubit Lüders order score.

**Theorem 1.1 (Quantitative increase).**

$$\forall t \in \mathbb{R},\; \forall u \in \mathbb{R},\; \left(0 \le t \land \left(t < u \land u \le \frac{1}{2}\right)\right) \Rightarrow \frac{u^{2} - t^{2}}{2 \operatorname{ln} 2} \le \operatorname{psi}\left(u\right) - \operatorname{psi}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.quantitative_increase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shengjun Wu (2026). *Measurement-order dependence bounds uncertainty, contextuality, steering, and Bell nonlocality*. DOI: [10.48550/arXiv.2611.24604](https://doi.org/10.48550/arXiv.2611.24604). URL: <https://arxiv.org/abs/2611.24604v1>.

*Commentary.*

Starting from a lower-angle maximizer, one state at the larger angle weakly increases all even series coefficients. The quadratic coefficient gives the displayed gain in bits.

**Theorem 1.2 (Strict monotonicity on the closed interval).**

$$\operatorname{StrictMonoOn}\left(psi, [0, \frac{1}{2}]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-2026-qubit-order-score-monotonicity` (proved) by `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-2026-qubit-order-score-monotonicity","declaration_gid":"D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shengjun Wu (2026). *Measurement-order dependence bounds uncertainty, contextuality, steering, and Bell nonlocality*. DOI: [10.48550/arXiv.2611.24604](https://doi.org/10.48550/arXiv.2611.24604). URL: <https://arxiv.org/abs/2611.24604v1>.

*Commentary.*

The optimized score from Section II.C increases strictly on the full closed interval. The quantitative gain is positive for every strictly ordered pair, including the endpoints.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.quantitative_increase`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result`
- Dependency: [D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon](QubitJensenShannon.md)
