/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthPivot
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthPivot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRootOperations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-! Three genuine SU row operations supply a literal unit last pivot,
with a count independent of rank, field size, or characteristic.
This is the first whole-group Hermitian reduction boundary. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow SLnNormalizer PartIIUnitaryUpperTorus PartIIUnitriangularLayers
open UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ} {ι : RingAut F}

abbrev first : Fin (k+4) := 0
abbrev last : Fin (k+4) := Fin.last (k+3)
def interior : Fin (k+4) := ⟨1,by omega⟩

@[simp] theorem rev_first : (first : Fin (k+4)).rev=last := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
@[simp] theorem rev_last : (last : Fin (k+4)).rev=first := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
theorem first_ne_last : (first : Fin (k+4))≠last := by
  intro h; have hh := congrArg Fin.val h; simp [first,last] at hh

theorem interior_ne_first : (interior : Fin (k+4))≠first := by
  intro h; have hh := congrArg Fin.val h; simp [interior,first] at hh
theorem interior_ne_last : (interior : Fin (k+4))≠last := by
  intro h; have hh := congrArg Fin.val h; simp [interior,last] at hh
theorem interior_ne_rev : (interior : Fin (k+4))≠interior.rev := by
  intro h; have hh := congrArg Fin.val h
  simp only [interior,Fin.val_rev] at hh; omega

private theorem mul_short_entry {a b c : Fin (k+4)}
    (hab : a≠b) (hbc : b≠c) (hac : a≠c) (x z y : F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (r s : Fin (k+4)) :
    (g * shortRoot hab hbc hac x z y) r s =
      g r s + (if s=b then g r a*x else 0) +
        (if s=c then g r b*z else 0) + (if s=c then g r a*y else 0) := by
  rw [SpecialLinearGroup.coe_mul,shortRoot_matrix,
    Matrix.mul_add,Matrix.mul_add,Matrix.mul_add,Matrix.mul_one]
  simp only [Matrix.add_apply]
  by_cases hb : s=b <;> by_cases hc : s=c <;> simp [hb,hc,hbc,hbc.symm]

/-- Actual arbitrary SU, not an isotropic-vector or generation premise.
One upper and one lower operation create a noncentral interior pivot.
A short root handles the odd central-coordinate case using true trace surjectivity. -/
theorem prepare_interior_pivot (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary (k+4) ι) :
    ∃ u l : specialUnitary (k+4) ι, Positive u ∧ Negative l ∧
      ∃ j : Fin (k+4), j≠first ∧ j≠last ∧ j≠j.rev ∧
        (g*u*l).val.val last j≠0 := by
  classical
  by_cases h : ∃ j : Fin (k+4), j≠first ∧ j≠last ∧ j≠j.rev ∧ g.val.val last j≠0
  · obtain ⟨j,hj0,hjl,hjr,hj⟩ := h
    exact ⟨1,1,positive_one,negative_one,j,hj0,hjl,hjr,by simpa using hj⟩
  have hw : ∀ j : Fin (k+4), j≠first → j≠last → j≠j.rev → g.val.val last j=0 := by
    intro j hj0 hjl hjr
    by_contra hj
    exact h ⟨j,hj0,hjl,hjr,hj⟩
  have hi0 := interior_ne_first (k:=k)
  have hil := interior_ne_last (k:=k)
  have hir := interior_ne_rev (k:=k)
  have hwi := hw interior hi0 hil hir
  have h0r : (first : Fin (k+4))≠first.rev := by simpa using first_ne_last (k:=k)
  have hlr : (last : Fin (k+4))≠last.rev := by simpa using (first_ne_last (k:=k)).symm
  by_cases hb : g.val.val last last≠0
  · let l := pairRoot ι hinv hil.symm hlr hir (1:F)
    refine ⟨1,l,positive_one,pairRoot_negative hinv _ _ _ (by simp [interior,last]) 1,
      interior,hi0,hil,hir,?_⟩
    simp only [mul_one]
    rw [mul_pairRoot_entry]
    simpa [hwi,rev_last,hi0] using hb
  by_cases ha : g.val.val last first≠0
  · let u := pairRoot ι hinv hi0.symm h0r hir (1:F)
    refine ⟨u,1,pairRoot_positive hinv _ _ _ (by simp [interior,first]) 1,
      negative_one,interior,hi0,hil,hir,?_⟩
    simp only [mul_one]
    rw [mul_pairRoot_entry]
    simpa [hwi,rev_first,hil] using ha
  have hrow : ∃ j : Fin (k+4), g.val.val last j≠0 := by
    by_contra hh
    apply g.val.row_ne_zero last
    funext j
    exact not_ne_iff.mp (not_exists.mp hh j)
  obtain ⟨j,hj⟩ := hrow
  have hj0 : j≠first := by intro he; subst j; exact ha hj
  have hjl : j≠last := by intro he; subst j; exact hb hj
  have hjr : j.rev=j := by
    by_contra he
    exact hj (hw j hj0 hjl (Ne.symm he))
  have hj1 : j≠interior := by intro he; subst j; exact hir hjr.symm
  have h0j : (first : Fin (k+4)).val<j.val := by
    have : j.val≠0 := fun he => hj0 (Fin.ext he)
    simp only [first,Fin.val_zero]; omega
  have hjL : j.val<(last : Fin (k+4)).val := by
    have : j.val≠k+3 := fun he => hjl (Fin.ext he)
    simp only [last,Fin.val_last]; omega
  let T : fixedField ι := ⟨-1,by simp [mem_fixedField]⟩
  obtain ⟨y,hy⟩ := trace_surjective ι hinv hne T
  have hy' : y+ι y= -((1:F)*ι 1) := by simpa [T] using hy
  let u : specialUnitary (k+4) ι :=
    ⟨shortRoot hj0.symm hjl first_ne_last 1 (-ι 1) y,
      shortRoot_fixed ι hinv _ _ _ rev_first hjr 1 y hy'⟩
  have hu : Positive u := by
    apply (mem_positiveU_iff _).mp
    exact shortRoot_mem_Uplus h0j hjL _ _ _
  have huL : (g*u).val.val last last≠0 := by
    change (g.val * shortRoot hj0.symm hjl (first_ne_last (k:=k)) (1:F) (-ι 1) y).val last last≠0
    rw [mul_short_entry]
    simpa [not_ne_iff.mp ha,not_ne_iff.mp hb,hjl.symm] using neg_ne_zero.mpr hj
  have hui : (g*u).val.val last interior=0 := by
    change (g.val * shortRoot hj0.symm hjl (first_ne_last (k:=k)) (1:F) (-ι 1) y).val last interior=0
    rw [mul_short_entry]
    simp [hwi,hj1.symm,hil]
  let l := pairRoot ι hinv hil.symm hlr hir (1:F)
  refine ⟨u,l,hu,pairRoot_negative hinv _ _ _ (by simp [interior,last]) 1,
    interior,hi0,hil,hir,?_⟩
  rw [mul_pairRoot_entry]
  rw [hui]
  simpa [rev_last,hi0] using huL

/-- A literal unit last pivot is obtained in three alternating actual SU slots.
This count is absolute. No fixed flag, orbit transitivity, or decomposition is assumed. -/
theorem unit_last_pivot (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary (k+4) ι) :
    ∃ u l v : specialUnitary (k+4) ι,
      Positive u ∧ Negative l ∧ Positive v ∧ (g*u*l*v).val.val last last=1 := by
  classical
  obtain ⟨u,l,hu,hl,j,hj0,hjl,hjr,hj⟩ := prepare_interior_pivot hinv hne g
  let b := g*u*l
  have hjr0 : j.rev≠first := by
    intro he; apply hjl
    have he' := congrArg Fin.rev he; simpa using he'
  have hjrL : j.rev≠last := by
    intro he; apply hj0
    have he' := congrArg Fin.rev he; simpa using he'
  have h0r : (first : Fin (k+4))≠first.rev := by simpa using first_ne_last (k:=k)
  have hrr : j.rev≠j.rev.rev := by simpa using hjr.symm
  let t := ι ((b.val.val last last-1)/b.val.val last j)
  let v := pairRoot ι hinv hjr0.symm h0r hrr t
  refine ⟨u,l,v,hu,hl,pairRoot_positive hinv _ _ _ ?_ t,?_⟩
  · have hh : j.rev.val≠0 := fun he => hjr0 (Fin.ext he)
    simp only [first,Fin.val_zero]; omega
  · change (b*v).val.val last last=1
    rw [mul_pairRoot_entry]
    simp only [rev_first,Fin.rev_rev,ite_true,if_neg hjrL.symm,add_zero,t]
    rw [hinv]
    have hj' : b.val.val last j≠0 := hj
    field_simp [hj']
    ring

end NikolovSegal.UnitaryWholeGroupWidth
