/- GID: D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientResidualHierarchy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/FiniteQuotientResidualHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite quotient language inclusion reverses the associated residual subgroup order. -/

import D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
import Mathlib.GroupTheory.Nilpotent

/- Library-search audit trail (2026-08-25):
   * The frozen finite-quotient faithfulness family owns `finiteResidual`; it
     is imported and reused rather than redeclared.
   * Repository body-shape searches found no solvable- or nilpotent-quotient
     language or residual intersection.
   * Pinned Mathlib's `IsNilpotent.to_isSolvable` is the exact target-class
     inclusion. `le_iInf` and `iInf_le_of_le` supply the reverse inclusions of
     the corresponding kernel intersections. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientResidualHierarchy

open D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel

universe u

/-- Finite quotient channels, represented canonically by normal subgroups
whose quotient maps are the observations and whose quotient targets are finite. -/
def finiteQuotientLanguage (G : Type u) [Group G] :
    Set { subgroup : Subgroup G // subgroup.Normal } :=
  { quotient |
    letI : quotient.1.Normal := quotient.2
    Finite (G ⧸ quotient.1) }

/-- The finite quotient channels whose quotient target is solvable. -/
def solvableQuotientLanguage (G : Type u) [Group G] :
    Set { subgroup : Subgroup G // subgroup.Normal } :=
  { quotient |
    letI : quotient.1.Normal := quotient.2
    Finite (G ⧸ quotient.1) ∧ IsSolvable (G ⧸ quotient.1) }

/-- The finite quotient channels whose quotient target is nilpotent. -/
def nilpotentQuotientLanguage (G : Type u) [Group G] :
    Set { subgroup : Subgroup G // subgroup.Normal } :=
  { quotient |
    letI : quotient.1.Normal := quotient.2
    Finite (G ⧸ quotient.1) ∧ Group.IsNilpotent (G ⧸ quotient.1) }

/-- The intersection of the kernels of all finite solvable quotient channels. -/
def solvableResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ quotient : solvableQuotientLanguage G, quotient.1.1

/-- The intersection of the kernels of all finite nilpotent quotient channels. -/
def nilpotentResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ quotient : nilpotentQuotientLanguage G, quotient.1.1

/--
Finite nilpotent quotient observations form a sublanguage of the finite
solvable quotient observations, which form a sublanguage of all finite
quotient observations. Intersecting the kernels reverses both inclusions.
-/
theorem finite_quotient_residual_hierarchy {G : Type u} [Group G] :
    nilpotentQuotientLanguage G ⊆ solvableQuotientLanguage G ∧
      solvableQuotientLanguage G ⊆ finiteQuotientLanguage G ∧
      finiteResidual G ≤ solvableResidual G ∧
      solvableResidual G ≤ nilpotentResidual G := by
  have nilpotent_to_solvable :
      nilpotentQuotientLanguage G ⊆ solvableQuotientLanguage G := by
    intro quotient nilpotentTarget
    letI : quotient.1.Normal := quotient.2
    change Finite (G ⧸ quotient.1) ∧
      Group.IsNilpotent (G ⧸ quotient.1) at nilpotentTarget
    change Finite (G ⧸ quotient.1) ∧ IsSolvable (G ⧸ quotient.1)
    refine ⟨nilpotentTarget.1, ?_⟩
    letI : Group.IsNilpotent (G ⧸ quotient.1) := nilpotentTarget.2
    exact IsNilpotent.to_isSolvable
  have solvable_to_finite :
      solvableQuotientLanguage G ⊆ finiteQuotientLanguage G := by
    intro quotient _solvableTarget
    letI : quotient.1.Normal := quotient.2
    change Finite (G ⧸ quotient.1) ∧
      IsSolvable (G ⧸ quotient.1) at _solvableTarget
    change Finite (G ⧸ quotient.1)
    exact _solvableTarget.1
  have finite_to_solvable_residual :
      finiteResidual G ≤ solvableResidual G := by
    refine le_iInf fun quotient => ?_
    letI : quotient.1.1.Normal := quotient.1.2
    have quotientProperty := quotient.2
    have finiteTarget : Finite (G ⧸ quotient.1.1) := by
      change Finite (G ⧸ quotient.1.1) ∧
        IsSolvable (G ⧸ quotient.1.1) at quotientProperty
      exact quotientProperty.1
    letI : Finite (G ⧸ quotient.1.1) := finiteTarget
    letI : quotient.1.1.FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    let finiteIndex := FiniteIndexNormalSubgroup.ofSubgroup quotient.1.1
    exact iInf_le_of_le finiteIndex le_rfl
  have solvable_to_nilpotent_residual :
      solvableResidual G ≤ nilpotentResidual G := by
    refine le_iInf fun quotient => ?_
    let solvableQuotient : solvableQuotientLanguage G :=
      ⟨quotient.1, nilpotent_to_solvable quotient.2⟩
    exact iInf_le_of_le solvableQuotient le_rfl
  exact ⟨nilpotent_to_solvable, solvable_to_finite,
    finite_to_solvable_residual, solvable_to_nilpotent_residual⟩

end D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientResidualHierarchy
