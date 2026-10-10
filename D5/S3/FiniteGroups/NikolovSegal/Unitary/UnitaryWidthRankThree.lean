/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThree
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRankThreeRoots
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRankTwo

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {ι : RingAut F}

/-- One actual lower root creates a nonzero first coordinate when necessary.
Isotropy excludes a row supported on the middle coordinate. -/
theorem rankThree_prepare_first (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary 3 ι) :
    ∃ l : specialUnitary 3 ι, Negative l ∧ (g*l).val.val 2 0≠0 := by
  by_cases ha : g.val.val 2 0≠0
  · exact ⟨1,negative_one,by simpa using ha⟩
  have ha0 := not_ne_iff.mp ha
  have hwN : g.val.val 2 1*ι (g.val.val 2 1)=0 := by
    simpa [ha0] using rankThree_row_isotropic hinv g
  have hw0 : g.val.val 2 1=0 := by
    rcases mul_eq_zero.mp hwN with h | h
    · exact h
    · exact (map_eq_zero ι).mp h
  have hb : g.val.val 2 2≠0 := by
    intro hb0
    apply g.val.row_ne_zero (2:Fin 3)
    funext j
    fin_cases j <;> simp [ha0,hw0,hb0]
  obtain ⟨y,hy⟩ := trace_surjective ι hinv hne (⟨-1,by simp [mem_fixedField]⟩ : fixedField ι)
  have hy0 : y≠0 := by intro h; simp [h] at hy
  have ht : y+ι y= -((1:F)*ι 1) := by simpa using hy
  let v := shortUpper hinv 1 y ht
  let l := transpose v
  have hl : Negative l := (positive_transpose_iff l).mp (by
    simpa [l] using shortUpper_positive hinv 1 y ht)
  refine ⟨l,hl,?_⟩
  have hh := (row_shortLower hinv 1 y ht g 2).1
  change (g*transpose (shortUpper hinv 1 y ht)).val.val 2 0≠0
  rw [hh,ha0,hw0,zero_mul,zero_add,zero_add]
  exact mul_ne_zero hb hy0

/-- A unit last pivot is cleared by one genuine lower short root, retaining
its central quadratic term in every characteristic. -/
theorem rankThree_clear_last (hinv : Function.Involutive ι)
    (g : specialUnitary 3 ι) (hb : g.val.val 2 2=1) :
    ∃ l : specialUnitary 3 ι, Negative l ∧
      ∀ j : Fin 3, (g*l).val.val 2 j=(1:Matrix (Fin 3) (Fin 3) F) 2 j := by
  let a := g.val.val 2 0
  let w := g.val.val 2 1
  have hI : a+w*ι w+ι a=0 := by
    simpa only [hb,map_one,mul_one,one_mul] using rankThree_row_isotropic hinv g
  have ht : ι a+ι (ι a)= -(ι w*ι (ι w)) := by
    rw [hinv,hinv]
    linear_combination hI
  let v := shortUpper hinv (ι w) (ι a) ht
  let l := transpose v
  have hl : Negative l := (positive_transpose_iff l).mp (by
    simpa [l] using shortUpper_positive hinv (ι w) (ι a) ht)
  refine ⟨l,hl,?_⟩
  have hh := row_shortLower hinv (ι w) (ι a) ht g 2
  intro j
  fin_cases j
  · change (g*transpose (shortUpper hinv (ι w) (ι a) ht)).val.val 2 0=_
    rw [hh.1,hb,one_mul]
    simpa [Matrix.one_apply] using hI
  · change (g*transpose (shortUpper hinv (ι w) (ι a) ht)).val.val 2 1=_
    rw [hh.2.1,hb,hinv]
    simp [w,Matrix.one_apply]
  · change (g*transpose (shortUpper hinv (ι w) (ι a) ht)).val.val 2 2=_
    rw [hh.2.2,hb]
    simp [Matrix.one_apply]

/-- Actual SU3 has four alternating unitriangular factors over EVERY finite
quadratic field, including F4/F9. Relative norm and trace are used in the
constructed roots; no low-field exception or decomposition input occurs. -/
theorem rankThree_four_factor (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary 3 ι) :
    ∃ a b c d : specialUnitary 3 ι,
      Positive a ∧ Negative b ∧ Positive c ∧ Negative d ∧ a*b*c*d=g := by
  obtain ⟨l,hl,ha⟩ := rankThree_prepare_first hinv hne g
  obtain ⟨v,hv,hb⟩ := rankThree_normalize_last hinv hne (g*l) ha
  obtain ⟨m,hm,hrow⟩ := rankThree_clear_last hinv (g*l*v) hb
  have hcol : ∀ i : Fin 3, (g*l*v*m).val.val i 0=(1:Matrix (Fin 3) (Fin 3) F) i 0 := by
    intro i
    have hh := reflected_coordinate_column (g*l*v*m) (2:Fin 3) hrow i
    rw [show (2:Fin 3).rev=0 from by decide] at hh
    exact hh
  have hE : Endpoints (g*l*v*m).val := ⟨hcol,hrow⟩
  obtain ⟨b,w,hw,heq⟩ := endpoint_levi_radical (n:=1) (g*l*v*m) hE
  have hbone : b=1 := Subsingleton.elim _ _
  have hback : w=g*l*v*m := by simpa [hbone] using heq
  refine ⟨w,m⁻¹,v⁻¹,l⁻¹,upRadical_positive hw,negative_inv hm,positive_inv hv,negative_inv hl,?_⟩
  rw [hback]
  group

end NikolovSegal.UnitaryWholeGroupWidth
