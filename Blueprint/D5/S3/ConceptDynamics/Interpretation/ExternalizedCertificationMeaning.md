# Externalized Certification Meaning

## Abstract

One realized decision transcript can carry collapsed or independently sampled certification value.

**Theorem 1.1 (Certification meaning is external to the decision transcript).**

$$\begin{gathered}\forall epsilon: \mathbb{R}, m: \mathbb{N},\\{}0 < epsilon < 1 \land 0 < m \Rightarrow\\{}\operatorname{let}(implementation: Bool \to Bool = (_ \mapsto false),\\{}expected: Bool \to Bool = id,\\{}World = (\operatorname{Fin}(m) \to \operatorname{PMF}(Bool)) \times (\operatorname{Fin}(m) \to Bool),\\{}transcript: World \to \operatorname{Fin}(m) \to Bool = (world \mapsto j \mapsto \operatorname{decide}(implementation(world.2(j)) = expected(world.2(j)))),\\{}badGreenMass: World \to \mathbb{R} = (world \mapsto \prod_{j} (world.1(j)(false)).toReal));\\{}\exists \mu: \operatorname{PMF}(Bool), W_{c}, W_{i}: World,\\{}W_{c}.2 = W_{i}.2 \land\\{}(\forall j, W_{c}.2(j) = false) \land\\{}transcript(W_{c}) = transcript(W_{i}) \land\\{}(\forall j, W_{c}.1(j) = \operatorname{pure}(W_{c}.2(j))) \land\\{}(\forall j, W_{i}.1(j) = \mu) \land\\{}\sum_{input: Bool} \text{if }implementation(input) = expected(input)\text{ then }0\text{ else }(\mu(input)).toReal = \frac{1+epsilon}{2} \land\\{}epsilon < \sum_{input: Bool} \text{if }implementation(input) = expected(input)\text{ then }0\text{ else }(\mu(input)).toReal \land\\{}badGreenMass(W_{c}) = 1 \land\\{}badGreenMass(W_{i}) = \frac{1-epsilon}{2}^{m} \land\\{}badGreenMass(W_{i}) \leq \operatorname{exp}(-(epsilon \times (m: \mathbb{R}))) \land\\{}\operatorname{exp}(-(epsilon \times (m: \mathbb{R}))) < badGreenMass(W_{c}) \land\\{}W_{c}.1 \neq W_{i}.1 \land\\{}\neg \operatorname{FactorsThrough}(badGreenMass, transcript) \land\\{}\neg \operatorname{FactorsThrough}((world \mapsto \forall j, world.1(j) = \mu), transcript).\end{gathered}$$

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
