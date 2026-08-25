# Symmetric Bernoulli Evidence Closed Forms

## Abstract

Four local evidence measures have exact closed forms on the symmetric two-point law pair.

**Theorem 1.1 (Exact evidence of a symmetric two-point bias).**

$$\forall b \in \operatorname{Bool},\\{}P_{\delta}(b) := \operatorname{ite}(b, \frac{1}{2} + \delta, \frac{1}{2} - \delta), Q_{\delta}(b) := \operatorname{ite}(b, \frac{1}{2} - \delta, \frac{1}{2} + \delta);\\{}\forall \delta \in \mathbb{R}, \lvert\delta\rvert < \frac{1}{2} \Rightarrow\\{}(\operatorname{TV}(P_{\delta}, Q_{\delta}) = 2 \lvert\delta\rvert) \land\\{}(\rho(P_{\delta}, Q_{\delta}) = \sqrt{1 - 4 \delta^{2}}) \land\\{}(\operatorname{H}(P_{\delta}, Q_{\delta})^{2} = 2(1 - \sqrt{1 - 4 \delta^{2}})) \land\\{}(D_{KL}(P_{\delta}\Vert\Vert Q_{\delta}) = 2 \delta \log(\frac{1 + 2 \delta}{1 - 2 \delta})).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliClosedForms.symmetric_bernoulli_evidence_closed_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-bias law assigns one half plus delta to true and one half minus delta to false; the negative-bias law swaps these masses.

Inside the open probability domain, direct two-coordinate evaluation gives total variation, affinity, squared Hellinger distance, and finite KL divergence simultaneously.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliClosedForms.symmetric_bernoulli_evidence_closed_forms`
- Dependency: [D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder](SymmetricBernoulliSecondOrder.md)
