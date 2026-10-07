/- GID: D5/S3/FiniteGroups/NikolovSegal/OwnerAdapters
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/OwnerAdapters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.ExtractionResidual
import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueLinks

set_option autoImplicit false

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

/-- Exact adapter to the original owner's signed Letter projection. -/
theorem signedVariables_eq_owner (W : List (Letter V S)) :
    signedVariables W = Equation47ValueNormalization.signedVariables W := rfl

/-- The owner's final signed count theorem supplies literal signed balance.
This premise records both sign counts, rather than assumed coverage/freshness. -/
theorem balanced_of_owner_counts (W : List (Letter V S)) (Y : Finset V)
    (h : ∀ x s, (Equation47ValueNormalization.signedVariables W).count (x,s) =
      if x ∈ Y then 1 else 0) : Balanced (signedVariables W) := by
  constructor
  · apply List.nodup_iff_count_le_one.mpr
    rintro ⟨x,s⟩
    rw [signedVariables_eq_owner,h]
    split_ifs <;> omega
  · intro x
    rw [signedVariables_eq_owner,h x false,h x true]

theorem support_eq_of_owner_counts (W : List (Letter V S)) (Y : Finset V)
    (h : ∀ x s, (Equation47ValueNormalization.signedVariables W).count (x,s) =
      if x ∈ Y then 1 else 0) : support (signedVariables W) = Y := by
  ext x
  simp only [support,List.mem_toFinset,List.mem_map,Prod.exists]
  constructor
  · rintro ⟨y,s,hm,he⟩
    change y = x at he; subst y
    have hc := List.count_pos_iff.mpr hm
    rw [signedVariables_eq_owner,h] at hc
    split_ifs at hc <;> first | assumption | omega
  · intro hx
    refine ⟨x,false,?_,rfl⟩
    apply List.count_pos_iff.mp
    rw [signedVariables_eq_owner,h,if_pos hx]
    omega

end NikolovSegal.CrossingKernel
