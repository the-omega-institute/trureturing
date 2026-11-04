# Continuous real tests reflect below omega-one

## Abstract

Every continuous real test on an omega-one profinite inverse limit factors exactly through one proper stage above any prescribed base.

CountableStage is the subtype of ordinals strictly below omega-one. F is an actual functor from its opposite preorder category to Profinite at universe one. Every stage is nonempty and every actual bonding map is surjective. C is an actual cone with an IsLimit witness. For each prescribed base and each continuous real-valued f on C.pt, the theorem constructs a proper beta at least base and a continuous real-valued g on F(op beta), with exact equality at every point. In the display Fobj, Fmap, Cpt and Cprojection denote the actual functor objects, bonding maps, cone point and projection evaluation. ContinuousMap denotes bundled continuous maps, Real is the usual topological real field, and Le is the ordinal stage order.

**Theorem 1.1 (Exact continuous factorization at a proper stage).**

$$\forall F \in Functor\left(CountableStageOpp, Profinite1\right),\; \left(\forall j \in CountableStageOpp,\; Nonempty\left(Fobj\left(j\right)\right)\right) \Rightarrow \left(\forall C \in Cone\left(F\right),\; \left(IsLimit\left(C\right) \land \left(\forall i \in CountableStageOpp,\; \forall j \in CountableStageOpp,\; \forall a \in Hom\left(i, j\right),\; Surjective\left(Fmap\left(a\right)\right)\right)\right) \Rightarrow \left(\forall base \in CountableStage,\; \forall f \in ContinuousMap\left(Cpt\left(\right), Real\right),\; \exists beta \in CountableStage,\; Le\left(base, beta\right) \land \left(\exists g \in ContinuousMap\left(Fobj\left(op\left(beta\right)\right), Real\right),\; \forall x \in Cpt\left(\right),\; f\left(x\right) = g\left(Cprojection\left(op\left(beta\right), x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CountableContinuousReflection.exists_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

The range of LocallyConstant.toContinuousMapAlgHom over the reals separates points of the profinite cone point. Mathlib's real Stone-Weierstrass theorem supplies locally constant l(n) whose pointwise errors are strictly below 1/(n+1). Profinite.exists_locallyConstant reflects each l(n) through an actual component j(n). The supremum over Option(Nat), assigning base to none and j(n) to some(n), remains below omega-one by Ordinal.iSup_lt_omega_one and lies above every chosen stage.

Cone naturality makes each l(n) equal at any two points with equal beta projections. For arbitrary positive epsilon choose n with 1/(n+1) below epsilon/2. The triangle inequality bounds the distance between the original two f values by epsilon. Thus f is constant on every actual beta fiber. Function.factorsThrough_iff produces a total real-valued factor. CountableClopenReflection.projection_surjective supplies actual surjectivity of this projection; it reuses the existing compatible-thread lifting proof. A continuous surjection from compact C.pt to the Hausdorff stage is a quotient map, and its continuous_iff criterion proves continuity of the factor.

This is ordinary compact inverse-limit mathematics, assembled from the cited project and pinned Mathlib APIs; no mathematical novelty is claimed. The supplemental four-slot source-selection audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21901; no validated registration is claimed. In the CH signed Talagrand construction, an actual final Prefix diagram and its limit cone may instantiate F and C. For each fixed continuous real test, this supplier gives an actual proper stage above the required launch base. Applying any stage-level integral or convergence theorem still requires its own signed-measure hypotheses and projection identities. The chosen stage depends on f. This theorem does not assert one proper stage for all continuous functions, nor does it construct the CH recursion, prove all signed clauses (A)-(G), or settle Kania and Kakol's arXiv:2607.06808v2 Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/CountableContinuousReflection.exists_stage`
- Dependency: [D5/S3/Topology/InverseLimit/CountableClopenReflection](CountableClopenReflection.md)
