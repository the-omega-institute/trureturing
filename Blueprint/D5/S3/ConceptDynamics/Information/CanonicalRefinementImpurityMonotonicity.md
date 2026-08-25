# Canonical Refinement Lowers Conditional Impurity

## Abstract

Canonical joint-fiber masses witness impurity monotonicity under refinement.

**Theorem 1.1 (Refinement cannot increase conditional impurity).**

$$\begin{gathered}\forall X, C, D, A: \operatorname{Type},\\{}mu: \operatorname{PMF}(X),\\{}coarse: X \to C, refined: X \to D,\\{}target: X \to A,\\{}\operatorname{Refines}(coarse, refined) \Rightarrow\\{}\operatorname{conditionalLogicalImpurity}(mu, refined, target) \leq \operatorname{conditionalLogicalImpurity}(mu, coarse, target).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/CanonicalRefinementImpurityMonotonicity.canonical_refinement_impurity_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each target-conditioned mass is the canonical fiber mass of the joint concept-target readout.

The countable Cauchy inequality compares coarse and refined collision terms; the complementary disagreement identity gives the displayed impurity inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/CanonicalRefinementImpurityMonotonicity.canonical_refinement_impurity_monotone`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity](ConditionalLogicalImpurity.md)
