# Countable common-stage clopen reflection

## Abstract

A countable family of final clopens in an omega-one profinite inverse limit has exact traces at one proper common stage.

CountableStage consists of the ordinals strictly below the first uncountable ordinal. F is an actual functor from its opposite preorder category to Profinite at universe one. Every component is nonempty and every actual bonding map is surjective. C is any actual cone and hC proves that this cone is a limit. The index type I is any countable type in an independent universe, including the empty type. W is any I-indexed family of clopen subsets of C.pt. Empty clopens are included; disjointness and nonemptiness are conclusions, not extra hypotheses. In the displayed formula TypeU means Type u, Profinite1 means Profinite at universe one, and CountableStageOpp is the opposite stage category. Fobj and Fmap are the actual functor object and map operations; Cpt and Cprojection are the actual cone point and projection. Family(I,X) means the function type I to X, Le is the ordinal stage order, and inverseImage is literal set preimage. IsLimit(C) asserts that the cone has an IsLimit witness. Nonempty applied to a component means carrier nonemptiness; applied to a subset it means set nonemptiness.

**Theorem 1.1 (Simultaneous exact traces below omega-one).**

$$\forall I \in TypeU,\; \forall F \in Functor\left(CountableStageOpp, Profinite1\right),\; \left(Countable\left(I\right) \land \left(\forall j \in CountableStageOpp,\; Nonempty\left(Fobj\left(j\right)\right)\right)\right) \Rightarrow \left(\forall C \in Cone\left(F\right),\; \left(IsLimit\left(C\right) \land \left(\forall i \in CountableStageOpp,\; \forall j \in CountableStageOpp,\; \forall f \in Hom\left(i, j\right),\; Surjective\left(Fmap\left(f\right)\right)\right)\right) \Rightarrow \left(\forall base \in CountableStage,\; \forall W \in Family\left(I, Set\left(Cpt\left(\right)\right)\right),\; \left(\forall n \in I,\; IsClopen\left(W\left(n\right)\right)\right) \Rightarrow \left(\exists beta \in CountableStage,\; Le\left(base, beta\right) \land \left(\exists V \in Family\left(I, Set\left(Fobj\left(op\left(beta\right)\right)\right)\right),\; \left(\forall n \in I,\; IsClopen\left(V\left(n\right)\right)\right) \land \left(\left(\forall n \in I,\; W\left(n\right) = inverseImage\left(Cprojection\left(op\left(beta\right)\right), V\left(n\right)\right)\right) \land \left(\left(\forall n \in I,\; Nonempty\left(V\left(n\right)\right) \Leftrightarrow Nonempty\left(W\left(n\right)\right)\right) \land \left(\forall m \in I,\; \forall n \in I,\; Disjoint\left(V\left(m\right), V\left(n\right)\right) \Leftrightarrow Disjoint\left(W\left(m\right), W\left(n\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CountableClopenReflection.exists_common_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

For every requested base stage, the theorem returns one beta at or above that base and an I-indexed family V of clopen subsets of F(beta). For every index n the actual final clopen W(n) equals the full inverse image of V(n) under the cone projection at beta. V(n) is nonempty exactly when W(n) is nonempty. For every m and n, V(m) and V(n) are disjoint exactly when W(m) and W(n) are disjoint.

Mathlib's Profinite.exists_isClopen_of_cofiltered first reflects each individual W(n) to a stage j(n). Take the supremum over Option(I), assigning base to none and j(n) to some(n). This includes the base even when I is empty. Ordinal.iSup_lt_omega_one certifies that this countable supremum is still a proper stage beta. Pull each reflected clopen back along the actual bonding map from beta to j(n). Cone naturality gives each exact final inverse-image equality.

The existing compact_projection_image theorem from D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit supplies full compatible-thread lifts. Since all bonding maps are surjective, every component point is in the eventual range. The limit-cone isomorphism transfers these lifts to the given cone C, so the actual beta projection is surjective. Lifting one trace point proves the nonemptiness equivalence; lifting a hypothetical intersection point proves the reverse disjointness implication. The public projection_surjective helper is a consumed application of that existing theorem. It is also reused by CountableContinuousReflection for continuous quotient descent; publicization preserves its statement and proof.

This is attributed known inverse-limit infrastructure. In the Talagrand CH candidate, one may include a separating clopen among the countable family and reflect all final clopen supports into one actual launch row. The theorem supplies that common-stage reflection only. It does not realize the transfinite compactum, prove signed-measure clauses (A)-(G), perform retrospective paired-Dirac capture, or settle Kania and Kakol's arXiv:2607.06808v2 Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/CountableClopenReflection.exists_common_stage`
- Dependency: [D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit](../../../S1/Dynamics/Shadowing/MittagLefflerInverseLimit.md)
