# Adaptive Depth of Independent Role Profiles

## Abstract

Independent binary role profiles require and admit exactly one experiment per role.

**Theorem 1.1 (The role-profile depth bound is attained by coordinate experiments).**

$$\begin{aligned}\forall r \in \mathbb{N},\\(\forall d \in \mathbb{N}, pi: \operatorname{BinaryProtocol}(\operatorname{Fin}(r) \to Bool, d), \operatorname{IdentifiesGiven}({p \mapsto unit}, id, pi) \implies r \leq d) \land\\\operatorname{Injective}(\operatorname{jointReadout}({i \mapsto {p \mapsto p(i)}})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/RoleProfileAdaptiveDepthOptimality.independent_role_profile_adaptive_depth_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier contains every Boolean profile on r role coordinates. A deterministic adaptive binary protocol identifies a profile only when equal transcripts force the underlying profiles to agree.

The general binary-protocol bound therefore forces at least r rounds. Jointly reading the r coordinate projections is injective, giving a nonadaptive role-basis experiment at the same depth.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/RoleProfileAdaptiveDepthOptimality.independent_role_profile_adaptive_depth_optimality`
- Dependency: [D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound](../Coding/BinaryProtocolDepthLowerBound.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
