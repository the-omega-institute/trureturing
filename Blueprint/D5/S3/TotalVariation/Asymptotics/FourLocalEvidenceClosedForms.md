# Four Local Evidence Closed Forms

## Abstract

Four symmetric Bernoulli local evidence quantities have closed forms on the interior bias domain.

**Theorem 1.1 (Symmetric Bernoulli total variation closed form).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| < \frac{1}{2} \Rightarrow \operatorname{totalVariation}(P_{\delta}, Q_{\delta})= 2 \left|\delta\right|.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.total_variation_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository defines total variation as one half of the finite L1 distance. For the two Bool coordinates, the absolute gaps are twice the absolute bias, so the result is 2|delta|. The algebraic statement is stronger than the probability-domain interpretation and needs no sign hypothesis.

**Theorem 1.2 (Symmetric Bernoulli Bhattacharyya affinity closed form).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| < \frac{1}{2} \Rightarrow \operatorname{bhattacharyya}(P_{\delta}, Q_{\delta})= \sqrt{1 - 4 \delta^{2}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.bhattacharyya_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here rho is read as Bhattacharyya affinity, not a correlation coefficient. The two equal square-root products reduce to twice the square root of (one half plus delta)(one half minus delta), which is the displayed square root. The strict interior hypothesis keeps both masses nonnegative.

**Theorem 1.3 (Symmetric Bernoulli squared Hellinger closed form).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| < \frac{1}{2} \Rightarrow \operatorname{hellingerSq}(P_{\delta}, Q_{\delta})= 2 (1 - \sqrt{1 - 4 \delta^{2}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.hellinger_sq_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen hellingerSq normalization is the unhalved squared Hellinger distance. Its normalized bridge is H^2 = 2(1 - rho), and the preceding affinity calculation supplies rho. Nonnegativity and normalization of both Bool laws are discharged from |delta| < 1/2.

**Theorem 1.4 (Symmetric Bernoulli KL divergence closed form).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| < \frac{1}{2} \Rightarrow \operatorname{klDivergence}(P_{\delta}, Q_{\delta})= 2 \delta \log \frac{1 + 2 \delta}{1 - 2 \delta}.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.kl_divergence_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's finite real-valued klDivergence uses Real.log, so this is the natural-log, or nats, convention. Expanding the two Bool summands, using log of an inverse, and collecting coefficients gives the stated symmetric logarithmic ratio. Strict positivity follows from the interior bias hypothesis.

**Theorem 1.5 (Zero bias gives identical-law evidence values).**

$$\operatorname{totalVariation}(P_{0}, Q_{0})= 0 \land \operatorname{bhattacharyya}(P_{0}, Q_{0})= 1 \land \operatorname{hellingerSq}(P_{0}, Q_{0})= 0 \land \operatorname{klDivergence}(P_{0}, Q_{0})= 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.zero_bias_degenerate_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At delta = 0 the positive and negative laws coincide. The four quantities therefore evaluate to TV = 0, affinity = 1, squared Hellinger distance = 0, and KL = 0 under the repository's fixed normalizations.

**Theorem 1.6 (Negative bias satisfies all four closed forms).**

$$\left|- \frac{1}{4}\right| < \frac{1}{2} \land \operatorname{totalVariation}(P_{- \frac{1}{4}}, Q_{- \frac{1}{4}})= 2 \left|- \frac{1}{4}\right| \land \operatorname{bhattacharyya}(P_{- \frac{1}{4}}, Q_{- \frac{1}{4}})= \sqrt{1 - 4 - \frac{1}{4}^{2}} \land \operatorname{hellingerSq}(P_{- \frac{1}{4}}, Q_{- \frac{1}{4}})= 2 (1 - \sqrt{1 - 4 - \frac{1}{4}^{2}}) \land \operatorname{klDivergence}(P_{- \frac{1}{4}}, Q_{- \frac{1}{4}})= 2 - \frac{1}{4} \log \frac{1 + 2 - \frac{1}{4}}{1 - 2 - \frac{1}{4}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.negative_bias_degenerate_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete interior point delta = -1/4 checks the sign audit. The TV absolute value changes sign correctly, while affinity, squared Hellinger distance, and the symmetric KL expression remain valid.

**Theorem 1.7 (The strict bias bound excludes a zero reference mass).**

$$Q_{\frac{1}{2}}(true)= 0 \land \neg \forall b: Bool, 0< Q_{\frac{1}{2}}(b) \land \operatorname{klDivergence}(P_{\frac{1}{2}}, Q_{\frac{1}{2}})= 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.strict_bias_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At delta = 1/2 the negative-bias law assigns zero mass to true, so strict positivity needed for the ordinary finite-KL reading fails. The frozen real-valued klDivergence totalizes the zero-denominator expression to 0; this is recorded explicitly and is not claimed to be an extended-real infinite divergence.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.bhattacharyya_closed_form`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.hellinger_sq_closed_form`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.kl_divergence_closed_form`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.negative_bias_degenerate_case`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.strict_bias_bound_is_necessary`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.total_variation_closed_form`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms.zero_bias_degenerate_case`
- Dependency: [D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder](SymmetricBernoulliSecondOrder.md)
