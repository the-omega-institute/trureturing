# Externalized Certification Meaning

## Abstract

One realized decision transcript can carry collapsed or independently sampled certification value.

**Theorem 1.1 (Certification meaning is external to the decision transcript).**

$$\begin{gathered}\forall epsilon: \mathbb{R}, m: \mathbb{N},\\{}0 < epsilon < 1 \land 0 < m \Rightarrow\\{}\exists \mu: \operatorname{PMF}(Bool), W_{c}, W_{i}: \operatorname{World}(m),\\{}\operatorname{suite}(W_{c}) = \operatorname{suite}(W_{i}) \land\\{}\forall j, \operatorname{suite}(W_{c})(j) = false \land\\{}\operatorname{Transcript}(W_{c}) = \operatorname{Transcript}(W_{i}) \land\\{}\forall j, \operatorname{law}(W_{c}, j) = \operatorname{pure}(\operatorname{suite}(W_{c})(j)) \land\\{}\forall j, \operatorname{law}(W_{i}, j) = \mu \land\\{}\operatorname{Loss}(constantFalse, id, \mu) = \frac{1+epsilon}{2} \land\\{}epsilon < \operatorname{Loss}(constantFalse, id, \mu) \land\\{}\operatorname{BadGreenMass}(W_{c}) = 1 \land\\{}\operatorname{BadGreenMass}(W_{i}) = \frac{1-epsilon}{2}^{m} \land\\{}\operatorname{BadGreenMass}(W_{i}) \leq \operatorname{exp}(-epsilon \times m) \land\\{}\operatorname{exp}(-epsilon \times m) < \operatorname{BadGreenMass}(W_{c}) \land\\{}\operatorname{laws}(W_{c}) \neq \operatorname{laws}(W_{i}) \land\\{}\neg \operatorname{FactorsThrough}(\operatorname{BadGreenMass}, \operatorname{Transcript}) \land\\{}\neg \operatorname{FactorsThrough}(\operatorname{IndependentOf}(\mu), \operatorname{Transcript}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning.externalized_certification_meaning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The implementation is the constant-false Boolean program and the expected behavior is the identity. The constructed deployment law gives the single failing input mass (1 + epsilon)/2, strictly above epsilon.

Both worlds realize the same all-false suite and therefore the same all-green bit transcript. In the co-selected world every coordinate law is concentrated on that realized input. In the independent world every coordinate law equals the deployment law.

The bad-green mass is the product of the coordinate pass masses. It is one under co-selection and ((1 - epsilon)/2)^m under independent sampling. The repository exponential bound gives the displayed certification envelope, while positivity of epsilon and m makes the co-selected mass strictly exceed that envelope.

The final two clauses state the information-theoretic corollary directly: neither bad-green mass nor the independent-sampling precondition factors through the transcript. The source explicitly leaves signature semantics out of scope, so no separate universal semantics of signing is invented.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning.externalized_certification_meaning`
- Dependency: [D5/S3/TotalVariation/IndependentSamplingExponentialBound](../../TotalVariation/IndependentSamplingExponentialBound.md)
