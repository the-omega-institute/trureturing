/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnStandardTorusStability
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnStandardTorusStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareUClassification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnFullGroup
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIUnitriangularActions NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F

/-- The actual prescribed DFG action preserves the actual diagonal carrier. -/
theorem diagonalFieldGraph_mem_torus (a : Fin n → Fˣ) (phi : RingAut F) (eps : Bool)
    (d : G) (hd : d ∈ T) : diagonalFieldGraph a phi eps d ∈ T := by
  have hf : ∀ d ∈ T, fieldAut phi d ∈ T := by
    intro d hd r c hrc
    change phi (d.val r c)=0
    rw [hd r c hrc,map_zero]
  have hg : ∀ d ∈ T, positiveGraph d ∈ T := by
    intro d hd r c hrc
    change (heightTorus (-1:Fˣ) ((unitAction% rawGraph) d)).val r c=0
    rw [(unitAction% torus_entry),(unitAction% rawGraph_entry)]
    have hi := (T).inv_mem hd
    have he : d⁻¹.val c.rev r.rev=0 := hi c.rev r.rev (fun h => hrc (Fin.rev_inj.mp h).symm)
    rw [he,mul_zero,zero_mul]
  have ha : ∀ d ∈ T, (unitOdd% diagonalAut) a d ∈ T := by
    intro d hd r c hrc
    rw [(unitOdd% diagonal_entry),hd r c hrc,mul_zero,zero_mul]
  cases eps
  · exact ha _ (hf d hd)
  · exact ha _ (hf _ (hg d hd))

/-- Finite injectivity upgrades the derived diagonal inclusion to literal subgroup equality. -/
theorem diagonalFieldGraph_map_torus [Fintype F]
    (a : Fin n → Fˣ) (phi : RingAut F) (eps : Bool) :
    (T).map (diagonalFieldGraph a phi eps).toMonoidHom=T := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨d,hd,rfl⟩
    exact diagonalFieldGraph_mem_torus a phi eps d hd
  · have he := Nat.card_congr ((T).equivMapOfInjective
      (diagonalFieldGraph a phi eps).toMonoidHom (diagonalFieldGraph a phi eps).injective).toEquiv
    exact le_of_eq he

/-- The actual composition convention: delta⁻¹*beta, preserving T when both do. -/
theorem relative_map_subgroup {K : Type*} [Group K] (H : Subgroup K)
    (beta delta : MulAut K) (hb : H.map beta.toMonoidHom=H)
    (hd : H.map delta.toMonoidHom=H) :
    H.map (delta⁻¹*beta).toMonoidHom=H := by
  change H.map (delta.symm.toMonoidHom.comp beta.toMonoidHom)=H
  rw [← Subgroup.map_map,hb]
  exact (Subgroup.map_symm_eq_iff_map_eq H).mpr hd
end NikolovSegal.SLnFullGroup
