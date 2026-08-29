# Joint-Law Certification Value Separation

## Abstract

The same complete decision transcript can carry separated certification values under co-selected and independently sampled joint laws.

**Theorem 1.1 (Certification value is not a function of the decision transcript).**

$$\begin{gathered}\forall epsilon: \mathbb{R}, m: \mathbb{N},\\{}0 < epsilon \land epsilon < 1 \land 0 < m \Rightarrow\\{}\operatorname{let}(implementation: Bool \to Bool = (_ \mapsto false),\\{}expected: Bool \to Bool = id,\\{}World = (\operatorname{Measure}(\operatorname{Fin}(m) \to Bool)) \times (\operatorname{Fin}(m) \to Bool),\\{}transcript: World \to (\operatorname{Fin}(m) \to Bool) \times (\operatorname{Fin}(m) \to Bool) = (world \mapsto (world.2, (j \mapsto \operatorname{decide}(implementation(world.2(j)) = expected(world.2(j)))))),\\{}certificationValue: World \to \mathbb{R} = (world \mapsto \operatorname{badGreenMass}(implementation, expected, world.1)));\\{}\exists \mu: \operatorname{PMF}(Bool), W_{c}, W_{i}: World,\\{}W_{c}.2 = W_{i}.2 \land\\{}(\forall j, W_{c}.2(j) = false) \land\\{}transcript(W_{c}) = transcript(W_{i}) \land\\{}W_{c}.1 = \operatorname{dirac}(W_{c}.2) \land\\{}W_{i}.1 = \operatorname{pi}(j \mapsto \operatorname{toMeasure}(\mu)) \land\\{}\sum_{input: Bool} \text{if }implementation(input) = expected(input)\text{ then }0\text{ else }(\mu(input)).toReal = \frac{1+epsilon}{2} \land\\{}epsilon < \sum_{input: Bool} \text{if }implementation(input) = expected(input)\text{ then }0\text{ else }(\mu(input)).toReal \land\\{}certificationValue(W_{c}) = 1 \land\\{}certificationValue(W_{i}) = \frac{1-epsilon}{2}^{m} \land\\{}certificationValue(W_{i}) \leq \operatorname{exp}(-(epsilon \times (m: \mathbb{R}))) \land\\{}\operatorname{exp}(-(epsilon \times (m: \mathbb{R}))) < certificationValue(W_{c}) \land\\{}W_{c}.1 \neq W_{i}.1 \land\\{}\neg \operatorname{FactorsThrough}(certificationValue, transcript) \land\\{}\neg \operatorname{FactorsThrough}((world \mapsto world.1 = \operatorname{pi}(j \mapsto \operatorname{toMeasure}(\mu))), transcript).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/JointLawCertificationValueSeparation.joint_law_certification_value_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a threshold strictly between zero and one and a positive suite budget, the implementation is the constant-false Boolean program and the expected behavior is the identity.

The two worlds realize the same suite and the same complete suite-and-verdict transcript. The co-selected world has the Dirac law at that suite, while the independent world has the finite product of the deployment law.

Deployment loss is strictly above epsilon. The co-selected bad-green mass is one, while the independent mass is the displayed product and lies below the exponential envelope; positive budget makes the separation strict.

The final clauses state directly that neither certification value nor the independent-product-law status factors through the transcript.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/JointLawCertificationValueSeparation.joint_law_certification_value_separation`
- Dependency: [D5/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning](JointLawExternalizedCertificationMeaning.md)
