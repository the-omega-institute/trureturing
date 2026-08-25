# Joint-Law Externalized Certification Meaning

## Abstract

A realized suite does not determine whether its certification law was co-selected or independently sampled.

**Theorem 1.1 (Certification meaning is carried by a joint sampling law).**

$$\begin{gathered}\forall epsilon: \mathbb{R}, m: \mathbb{N},\\{}0 < epsilon \land epsilon < 1 \Rightarrow\\{}\operatorname{let}(implementation: Bool \to Bool = (_ \mapsto false),\\{}expected: Bool \to Bool = id,\\{}World = (\operatorname{Measure}(\operatorname{Fin}(m) \to Bool)) \times (\operatorname{Fin}(m) \to Bool));\\{}\exists \mu: \operatorname{PMF}(Bool), Wc, Wi: World,\\{}Wc.2 = Wi.2 \land\\{}(\forall j, Wc.2(j) = false) \land\\{}Wc.1 = \operatorname{dirac}(Wc.2) \land\\{}Wi.1 = \operatorname{pi}(j \mapsto \operatorname{toMeasure}(\mu)) \land\\{}\sum_{input: Bool} \text{if }implementation(input) = expected(input)\text{ then }0\text{ else }\operatorname{toReal}(\mu(input)) = \frac{1+epsilon}{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning.joint_law_externalized_certification_meaning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The implementation is the constant-false Boolean program and the expected behavior is the identity. A Boolean deployment PMF assigns the failing input mass (1 + epsilon)/2.

Both worlds realize the same all-false suite. The co-selected world uses the Dirac law at that suite, while the independently sampled world uses the finite product measure of copies of the deployment law.

These five independently falsifiable world clauses are the public statement. The Lean module derives the co-selected mass, the product bad-green mass, and its repository exponential envelope from those clauses, so the consequences are not repeated as public conjuncts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning.joint_law_externalized_certification_meaning`
- Dependency: [D5/S3/TotalVariation/IndependentSamplingExponentialBound](../../TotalVariation/IndependentSamplingExponentialBound.md)
