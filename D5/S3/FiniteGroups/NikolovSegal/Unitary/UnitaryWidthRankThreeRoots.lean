/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThreeRoots
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThreeRoots
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthLeviExtraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Genuine short-root coordinates for SU3, using relative trace and norm over
every finite quadratic field. No odd-characteristic or field-size premise. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {ι : RingAut F}

/-- Extend the genuine unit norm surjection to the zero scalar as well. -/
theorem scalar_norm_surjective (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (t : fixedField ι) :
    ∃ x : F, x*ι x=(t:F) := by
  by_cases ht : t=0
  · exact ⟨0,by simp [ht]⟩
  obtain ⟨x,hx⟩ := norm_units_surjective ι hinv hne (Units.mk0 t ht)
  exact ⟨x,hx⟩

def shortUpper (hinv : Function.Involutive ι) (x y : F)
    (hy : y+ι y= -(x*ι x)) : specialUnitary 3 ι :=
  ⟨shortRoot (a:=0) (b:=1) (c:=2) (by decide) (by decide) (by decide) x (-ι x) y,
    shortRoot_fixed ι hinv _ _ _ (by decide) (by decide) x y hy⟩

theorem shortUpper_matrix (hinv : Function.Involutive ι) (x y : F)
    (hy : y+ι y= -(x*ι x)) :
    (shortUpper hinv x y hy).val.val= !![1,x,y;0,1,-ι x;0,0,1] := by
  rw [show (shortUpper hinv x y hy).val=shortRoot (a:=0) (b:=1) (c:=2)
    (by decide) (by decide) (by decide) x (-ι x) y from rfl,shortRoot_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem shortUpper_positive (hinv : Function.Involutive ι) (x y : F)
    (hy : y+ι y= -(x*ι x)) : Positive (shortUpper hinv x y hy) := by
  apply (mem_positiveU_iff _).mp
  exact shortRoot_mem_Uplus (by decide) (by decide) x (-ι x) y

/-- Exact ordered right multiplication, in all three coordinates. -/
theorem row_shortUpper (hinv : Function.Involutive ι) (x y : F)
    (hy : y+ι y= -(x*ι x)) (g : specialUnitary 3 ι) (r : Fin 3) :
    (g*shortUpper hinv x y hy).val.val r 0=g.val.val r 0 ∧
    (g*shortUpper hinv x y hy).val.val r 1=g.val.val r 1+g.val.val r 0*x ∧
    (g*shortUpper hinv x y hy).val.val r 2=g.val.val r 2-g.val.val r 1*ι x+g.val.val r 0*y := by
  change (g.val.val*(shortUpper hinv x y hy).val.val) r 0=_ ∧
    (g.val.val*(shortUpper hinv x y hy).val.val) r 1=_ ∧
    (g.val.val*(shortUpper hinv x y hy).val.val) r 2=_
  rw [shortUpper_matrix]
  simp [Matrix.mul_apply,Fin.sum_univ_succ]
  constructor <;> ring

theorem row_shortLower (hinv : Function.Involutive ι) (x y : F)
    (hy : y+ι y= -(x*ι x)) (g : specialUnitary 3 ι) (r : Fin 3) :
    (g*transpose (shortUpper hinv x y hy)).val.val r 0=
      g.val.val r 0+g.val.val r 1*x+g.val.val r 2*y ∧
    (g*transpose (shortUpper hinv x y hy)).val.val r 1=
      g.val.val r 1-g.val.val r 2*ι x ∧
    (g*transpose (shortUpper hinv x y hy)).val.val r 2=g.val.val r 2 := by
  change (g.val.val*(shortUpper hinv x y hy).val.val.transpose) r 0=_ ∧
    (g.val.val*(shortUpper hinv x y hy).val.val.transpose) r 1=_ ∧
    (g.val.val*(shortUpper hinv x y hy).val.val.transpose) r 2=_
  rw [shortUpper_matrix]
  simp [Matrix.mul_apply,Fin.sum_univ_succ]
  constructor <;> ring

theorem rankThree_row_isotropic (hinv : Function.Involutive ι)
    (g : specialUnitary 3 ι) :
    g.val.val 2 0*ι (g.val.val 2 2)+g.val.val 2 1*ι (g.val.val 2 1)+
      g.val.val 2 2*ι (g.val.val 2 0)=0 := by
  simpa [Fin.sum_univ_succ,Fin.rev,add_assoc] using row_isotropic hinv g (2:Fin 3) (by decide)

/-- For a nonzero first row coordinate, a single genuine upper short root
makes the last coordinate exactly one. Its trace equation is DERIVED from
isotropy and the actual scalar norm surjection, including characteristic two. -/
theorem rankThree_normalize_last (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary 3 ι)
    (ha : g.val.val 2 0≠0) :
    ∃ v : specialUnitary 3 ι, Positive v ∧ (g*v).val.val 2 2=1 := by
  let a := g.val.val 2 0
  let w := g.val.val 2 1
  let b := g.val.val 2 2
  let t : fixedField ι := ⟨-(a+ι a),by
    rw [mem_fixedField]
    rw [map_neg,map_add,hinv,add_comm]⟩
  obtain ⟨v,hv⟩ := scalar_norm_surjective hinv hne t
  change v*ι v= -(a+ι a) at hv
  let x := (v-w)/a
  let y := (1-b+w*ι x)/a
  have ha' : a≠0 := ha
  have hx : w+a*x=v := by dsimp only [x]; field_simp [ha']; ring
  have hyB : b-w*ι x+a*y=1 := by dsimp only [y]; field_simp [ha']; ring
  have hyBar : ι b-ι w*x+ι a*ι y=1 := by
    have hh := congrArg ι hyB
    simp only [map_add,map_sub,map_mul,map_one] at hh
    rw [hinv] at hh
    exact hh
  have hN : (w+a*x)*(ι w+ι a*ι x)= -(a+ι a) := by
    rw [←map_mul,←map_add, hx]; exact hv
  have hI : a*ι b+w*ι w+b*ι a=0 := rankThree_row_isotropic hinv g
  have hc : a*ι a*(y+ι y+x*ι x)=0 := by
    linear_combination (ι a)*hyB+a*hyBar-hI+hN
  have hai : ι a≠0 := (map_ne_zero ι).mpr ha
  have htrace : y+ι y= -(x*ι x) := by
    have hz := (mul_eq_zero.mp hc).resolve_left (mul_ne_zero ha hai)
    linear_combination hz
  refine ⟨shortUpper hinv x y htrace,shortUpper_positive hinv x y htrace,?_⟩
  exact (row_shortUpper hinv x y htrace g 2).2.2.trans hyB

end NikolovSegal.UnitaryWholeGroupWidth
