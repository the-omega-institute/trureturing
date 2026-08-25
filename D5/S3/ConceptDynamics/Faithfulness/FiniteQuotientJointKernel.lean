/- GID: D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint finite-quotient observations have the finite residual as kernel. -/

import Mathlib.GroupTheory.ResiduallyFinite

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for residual finiteness, finite quotients, joint
     kernels, and joint faithfulness found no D5 declaration stating the full
     kernel identity and three-way equivalence below.
   * Exact pinned-Mathlib hit `Group.residuallyFinite_def` supplies residual
     finiteness iff the infimum of finite-index normal subgroups is bottom.
     Exact hits `QuotientGroup.mk'`, `MonoidHom.pi`, and
     `MonoidHom.ker_eq_bot_iff` supply the canonical quotient observations,
     their joint homomorphism, and the injectivity criterion. No library theorem
     packages all three public clauses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel

universe u

/-- The finite residual, constructed as the intersection of all finite-index
normal subgroups. -/
def finiteResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup

/-- The canonical joint observation into all finite quotients. -/
def finiteQuotientObserver (G : Type u) [Group G] :
    G →* ((H : FiniteIndexNormalSubgroup G) → (G ⧸ H.toSubgroup)) :=
  MonoidHom.pi fun H => QuotientGroup.mk' H.toSubgroup

/-- The kernel read jointly by all finite quotients is exactly the finite
residual. Consequently residual finiteness, triviality of the finite residual,
and joint faithfulness of all finite-quotient observations are equivalent. -/
theorem finite_quotient_joint_kernel {G : Type u} [Group G] :
    (finiteQuotientObserver G).ker = finiteResidual G ∧
      (Group.ResiduallyFinite G ↔ finiteResidual G = ⊥) ∧
      (finiteResidual G = ⊥ ↔ Function.Injective (finiteQuotientObserver G)) := by
  have kernelIdentity :
      (finiteQuotientObserver G).ker = finiteResidual G := by
    ext g
    constructor
    · intro inKernel
      change g ∈ (⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup)
      rw [Subgroup.mem_iInf]
      intro H
      apply (QuotientGroup.eq_one_iff g).mp
      simpa [finiteQuotientObserver] using congrFun inKernel H
    · intro inResidual
      change (fun H : FiniteIndexNormalSubgroup G =>
        (QuotientGroup.mk' H.toSubgroup) g) = 1
      funext H
      have inH : g ∈ H.toSubgroup :=
        (Subgroup.mem_iInf.mp (show
          g ∈ (⨅ K : FiniteIndexNormalSubgroup G, K.toSubgroup) from inResidual)) H
      exact (QuotientGroup.eq_one_iff g).mpr inH
  refine ⟨kernelIdentity, ?_, ?_⟩
  · simpa [finiteResidual] using
      (Group.residuallyFinite_def (G := G))
  · rw [← kernelIdentity]
    exact MonoidHom.ker_eq_bot_iff (finiteQuotientObserver G)

#print axioms finite_quotient_joint_kernel

end D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
