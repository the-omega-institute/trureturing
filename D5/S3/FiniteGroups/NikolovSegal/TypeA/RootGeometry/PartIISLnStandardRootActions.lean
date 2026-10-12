/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnStandardRootActions
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnStandardRootActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIPropositionSixFive
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootGraph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace NikolovSegal.SLnRootAction
open Matrix NikolovSegal.PartIIUnitriangularActions NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem fieldAut_root (phi : RingAut F) (r : PositiveIndex n) (t : F) :
    fieldAut phi (root r t)=root r (phi t) := by
  apply SpecialLinearGroup.ext
  intro i j
  change phi ((1+Matrix.single r.val.1 r.val.2 t) i j) =
    (1+Matrix.single r.val.1 r.val.2 (phi t)) i j
  simp only [Matrix.add_apply,map_add,Matrix.one_apply,Matrix.single_apply]
  split_ifs <;> simp

theorem diagonalAut_root (a : Fin n → Fˣ) (r : PositiveIndex n) (t : F) :
    (unitOdd% diagonalAut) a (root r t)=root r ((a r.val.1:F)*t*(((a r.val.2)⁻¹:Fˣ):F)) := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [(unitOdd% diagonal_entry)]
  change (a i:F)*(1+Matrix.single r.val.1 r.val.2 t) i j*(((a j)⁻¹:Fˣ):F)=
    (1+Matrix.single r.val.1 r.val.2 ((a r.val.1:F)*t*(((a r.val.2)⁻¹:Fˣ):F)) : Matrix (Fin n) (Fin n) F) i j
  by_cases h : r.val.1=i ∧ r.val.2=j
  · rcases h with ⟨rfl,rfl⟩
    simp [Matrix.one_apply,Matrix.single_apply,ne_of_lt r.property]
  · by_cases he : i=j
    · subst j; simp [Matrix.single_apply,h]
    · simp [Matrix.one_apply,Matrix.single_apply,h,he]

/-- The already accepted positiveGraph convention has coefficient +1 on
actual simple roots, including characteristic two. -/
theorem positiveGraph_simple_root (r : Fin (n-1)) (t : F) :
    positiveGraph (root (simpleRoot r) t)=root (reflectRoot (simpleRoot r)) t := by
  apply SpecialLinearGroup.ext
  intro i j
  change (heightTorus (-1:Fˣ) ((unitAction% rawGraph) (root (simpleRoot r) t))) i j = _
  rw [(unitAction% torus_entry),(unitAction% rawGraph_entry)]
  simp only [root,SpecialLinearGroup.transvection_inv]
  change ((((-1:Fˣ)⁻¹:Fˣ):F)^i.val)*(1+Matrix.single (simpleRoot r).val.1 (simpleRoot r).val.2 (-t)) j.rev i.rev*(-1:F)^j.val =
    (1+Matrix.single (reflectRoot (simpleRoot r)).val.1 (reflectRoot (simpleRoot r)).val.2 t) i j
  have hi : (((-1:Fˣ)⁻¹:Fˣ):F)=(-1:F) := by simp
  rw [hi]
  by_cases he : i=j
  · subst j
    have hh : ¬((simpleRoot r).val.1=i.rev ∧ (simpleRoot r).val.2=i.rev) := by
      rintro ⟨h1,h2⟩; exact (ne_of_lt (simpleRoot r).property) (h1.trans h2.symm)
    have hh' : ¬((reflectRoot (simpleRoot r)).val.1=i ∧ (reflectRoot (simpleRoot r)).val.2=i) := by
      rintro ⟨h1,h2⟩; exact (ne_of_lt (reflectRoot (simpleRoot r)).property) (h1.trans h2.symm)
    simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.single_apply,if_neg hh,if_neg hh',add_zero,mul_one]
    rw [← mul_pow]
    simp
  · have hrev : j.rev ≠ i.rev := fun h => he (Fin.rev_inj.mp h).symm
    have hp : ((simpleRoot r).val.1=j.rev ∧ (simpleRoot r).val.2=i.rev) ↔
        ((reflectRoot (simpleRoot r)).val.1=i ∧ (reflectRoot (simpleRoot r)).val.2=j) := by
      constructor
      · rintro ⟨h1,h2⟩; exact ⟨by simpa [reflectRoot] using congrArg Fin.rev h2,by simpa [reflectRoot] using congrArg Fin.rev h1⟩
      · rintro ⟨h1,h2⟩; exact ⟨by simpa [reflectRoot] using congrArg Fin.rev h2,by simpa [reflectRoot] using congrArg Fin.rev h1⟩
    by_cases hpair : (simpleRoot r).val.1=j.rev ∧ (simpleRoot r).val.2=i.rev
    · have hv : j.val=i.val+1 := by
        have h1:=congrArg Fin.val hpair.1
        have h2:=congrArg Fin.val hpair.2
        simp only [simpleRoot,Fin.val_rev] at h1 h2
        have hb:=r.isLt; omega
      simp only [Matrix.add_apply,Matrix.one_apply,if_neg he,if_neg hrev,Matrix.single_apply,if_pos hpair,if_pos (hp.mp hpair),zero_add]
      rw [hv,pow_succ]
      calc
        _ = ((-1:F)^i.val*(-1:F)^i.val)*t := by ring
        _ = t := by rw [← mul_pow]; simp
    · have hpneg := mt hp.mpr hpair
      simp [Matrix.one_apply,he,hrev,Matrix.single_apply,hpair,hpneg]

theorem diagonalFieldGraph_simple_root (a : Fin n → Fˣ) (phi : RingAut F) (eps : Bool)
    (r : Fin (n-1)) (t : F) :
    diagonalFieldGraph a phi eps (root (simpleRoot r) t)=
      let s := if eps then reflectRoot (simpleRoot r) else simpleRoot r
      root s ((a s.val.1:F)*phi t*(((a s.val.2)⁻¹:Fˣ):F)) := by
  cases eps
  · change (unitOdd% diagonalAut) a (fieldAut phi (root (simpleRoot r) t)) = _
    rw [fieldAut_root,diagonalAut_root]
    rfl
  · change (unitOdd% diagonalAut) a (fieldAut phi (positiveGraph (root (simpleRoot r) t))) = _
    rw [positiveGraph_simple_root,fieldAut_root,diagonalAut_root]
    rfl
end NikolovSegal.SLnRootAction
