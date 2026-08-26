# Stable and Flip Observational Law

## Abstract

The stable and flip Boolean structural models have the same observational law.

**Theorem 1.1 (Both observational laws are uniform and independent).**

$$\begin{gathered}Lobs(M, x, y) := \operatorname{sum}(x0, \operatorname{sum}(u, \operatorname{if}((x0, \operatorname{outcome}(M, u, x0)) = (x, y), \frac{1}{4}, 0))),\\{}\forall M: \operatorname{DeterministicBoolSCM}(),\\{}(M = MStable \lor M = MFlip) \Rightarrow\\{}(\forall x: Bool, \operatorname{sum}(yPrime, Lobs(M, x, yPrime)) = \frac{1}{2})\\{}\land\\{}(\forall y: Bool, \operatorname{sum}(xPrime, Lobs(M, xPrime, y)) = \frac{1}{2})\\{}\land\\{}(\forall x, y: Bool, Lobs(M, x, y) = \operatorname{sum}(yPrime, Lobs(M, x, yPrime)) \cdot \operatorname{sum}(xPrime, Lobs(M, xPrime, y)))\\{}\land\\{}(\forall x, y: Bool, Lobs(M, x, y) = \frac{1}{4}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/StableFlipObservationalLaw.stable_and_flip_observational_laws_are_uniform_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stable and flip models are the canonical Boolean structural models from the intervention family. A natural treatment and exogenous unit are sampled independently from the uniform four-point Boolean population.

The displayed observational mass is constructed by evaluating the model outcome on each source pair. Separate public clauses state the two uniform marginals, pointwise factorization into those marginals, and the exact mass of every observed pair.

Thus both structural equations induce independent uniform Bernoulli X and Y coordinates and the same one-quarter joint law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/StableFlipObservationalLaw.stable_and_flip_observational_laws_are_uniform_independent`
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](../Interventions/InterventionCounterfactualSeparation.md)
