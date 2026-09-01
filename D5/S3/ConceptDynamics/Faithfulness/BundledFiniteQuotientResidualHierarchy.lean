/- GID: D5/S3/ConceptDynamics/Faithfulness/BundledFiniteQuotientResidualHierarchy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/BundledFiniteQuotientResidualHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bundled finite quotient languages induce the reverse residual hierarchy. -/

import D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
import Mathlib.GroupTheory.Nilpotent

/- Library-search audit trail (2026-08-25):
   * `FiniteQuotientJointKernel.finiteResidual` is the canonical D5 finite
     residual and is imported rather than redeclared.
   * Repository name and body-shape searches found no solvable or nilpotent
     quotient predicate on `FiniteIndexNormalSubgroup`, nor their residuals.
   * Pinned Mathlib's `IsNilpotent.to_isSolvable` is the exact substantive
     language inclusion. No library theorem packages the residual hierarchy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.BundledFiniteQuotientResidualHierarchy

open D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel

universe u

/-- Finite-index normal subgroups whose canonical quotient is solvable. -/
def solvableFiniteQuotientLanguage (G : Type u) [Group G] :
    Set (FiniteIndexNormalSubgroup G) :=
  { H | IsSolvable (G ⧸ H.toSubgroup) }

/-- Finite-index normal subgroups whose canonical quotient is nilpotent. -/
def nilpotentFiniteQuotientLanguage (G : Type u) [Group G] :
    Set (FiniteIndexNormalSubgroup G) :=
  { H | Group.IsNilpotent (G ⧸ H.toSubgroup) }

/-- The intersection of kernels of the bundled finite solvable quotients. -/
def solvableFiniteResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ H : solvableFiniteQuotientLanguage G, H.1.toSubgroup

/-- The intersection of kernels of the bundled finite nilpotent quotients. -/
def nilpotentFiniteResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ H : nilpotentFiniteQuotientLanguage G, H.1.toSubgroup

/--
Finite nilpotent quotient observations are finite solvable quotient
observations. Restricting the quotient language reverses the inclusions of the
corresponding residual intersections.
-/
theorem bundled_finite_quotient_residual_hierarchy {G : Type u} [Group G] :
    nilpotentFiniteQuotientLanguage G ⊆ solvableFiniteQuotientLanguage G ∧
      finiteResidual G ≤ solvableFiniteResidual G ∧
      solvableFiniteResidual G ≤ nilpotentFiniteResidual G := by
  have nilpotent_to_solvable :
      nilpotentFiniteQuotientLanguage G ⊆
        solvableFiniteQuotientLanguage G := by
    intro H nilpotentQuotient
    change Group.IsNilpotent (G ⧸ H.toSubgroup) at nilpotentQuotient
    change IsSolvable (G ⧸ H.toSubgroup)
    letI : Group.IsNilpotent (G ⧸ H.toSubgroup) := nilpotentQuotient
    exact IsNilpotent.to_isSolvable
  have finite_to_solvable_residual :
      finiteResidual G ≤ solvableFiniteResidual G := by
    refine le_iInf fun H => ?_
    exact iInf_le_of_le H.1 le_rfl
  have solvable_to_nilpotent_residual :
      solvableFiniteResidual G ≤ nilpotentFiniteResidual G := by
    refine le_iInf fun H => ?_
    let solvableQuotient : solvableFiniteQuotientLanguage G :=
      ⟨H.1, nilpotent_to_solvable H.2⟩
    exact iInf_le_of_le solvableQuotient le_rfl
  exact ⟨nilpotent_to_solvable, finite_to_solvable_residual,
    solvable_to_nilpotent_residual⟩

#print axioms bundled_finite_quotient_residual_hierarchy

end D5.S3.ConceptDynamics.Faithfulness.BundledFiniteQuotientResidualHierarchy
