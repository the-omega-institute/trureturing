/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalDiagonalNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalDiagonalNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryCentralEvenProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Actual PartII p263 unitary middle diagonal normalization.
Norm removes the given similitude multiplier; quadratic Hilbert90
absorbs its determinant at the second reflected pair. Middle entries
are1 and the first entry is ANY prescribed nonzero u before all targets. -/
namespace NikolovSegal.PartIIUnitaryRadicalDiagonalNormalization
open Matrix PartIIUnitriangularActions PartIIUnitaryUpperTorus UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ}
private def innerWeights (ι : RingAut F) (u v : Fˣ) : Fin (k+4) → Fˣ :=
  (unitaryCentral% extendWeights) ι ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) v) u
private theorem innerWeights_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (u v : Fˣ) (i : Fin (k+4)) :
    ι (innerWeights ι u v i:F)*(innerWeights ι u v i.rev:F)=1 :=
  (unitaryCentral% extend_unitary) ι hinv _
    ((unitaryCentral% extend_unitary) ι hinv _ (fun _ => by simp) v) u i
private theorem innerWeights_product (ι : RingAut F) (u v : Fˣ) :
    ∏ i, innerWeights (k:=k) ι u v i=(u/involutionUnit ι u)*(v/involutionUnit ι v) := by
  change (∏ i, Fin.cons u (Fin.snoc (Fin.cons v (Fin.snoc (fun _ : Fin k => (1:Fˣ))
    (involutionUnit ι v)⁻¹)) (involutionUnit ι u)⁻¹) i)=_
  simp only [Fin.prod_cons,Fin.prod_snoc,Finset.prod_const_one,mul_one,one_mul,div_eq_mul_inv]
  simp [mul_assoc,mul_comm,mul_left_comm]

/-- Actual pre-target unitary diagonal normalization for the V middle
quotient. The determinant-one h is CONSTRUCTED and the action identity
holds on ALL group elements; it assumes no quotient or VALUE coverage. -/
theorem actual_unitary_radical_middle_diagonal_inner (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin (k+4) → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F)) (u : Fˣ) :
    ∃ h : SpecialLinearGroup (Fin (k+4)) F, ∃ v : Fˣ,
      (∀ i j, i≠j → h i j=0) ∧ steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin (k+4)) F,
        (MulAut.conj h) ((unitOdd% diagonalAut) a g)=
          (unitOdd% diagonalAut) (innerWeights ι u v) g := by
  classical
  obtain ⟨lambda,hlambda⟩ := norm_units_surjective ι hinv hne c⁻¹
  let a' := fun i => lambda*a i
  have ha' : ∀ i, ι (a' i:F)*(a' i.rev:F)=1 := by
    intro i
    simp only [a',Units.val_mul,map_mul]
    calc
      _ = ((lambda:F)*ι (lambda:F))*(ι (a i:F)*(a i.rev:F)) := by ring
      _ = 1 := by rw [hlambda,ha i]; simp
  let P : Fˣ := ∏ i, a' i
  have hP : involutionUnit ι P*P=1 := by
    apply Units.ext
    simp only [involutionUnit_val,Units.val_mul,Units.val_one,Units.coe_prod,map_prod]
    have hr : ∏ i : Fin (k+4), (a' i.rev:F)=∏ i : Fin (k+4), (a' i:F) :=
      Equiv.prod_comp (Fin.revPerm : Fin (k+4)≃Fin (k+4)) (fun i => (a' i:F))
    dsimp only [P]
    rw [Units.coe_prod,map_prod,← hr,← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => ha' i)
  have hinu : involutionUnit ι (involutionUnit ι u)=u := by
    apply Units.ext; exact hinv (u:F)
  let T : Fˣ := P/(u/involutionUnit ι u)
  have hT : (T:F)*ι (T:F)=1 := by
    have htu : T*involutionUnit ι T=1 := by
      simp only [T,map_div,hinu]
      calc
        _ = P*involutionUnit ι P := by
          apply Units.ext
          simp only [Units.val_mul,Units.val_div_eq_div_val]
          field_simp
          <;> ring
        _ = 1 := by simpa only [mul_comm] using hP
    exact congrArg (fun z : Fˣ => (z:F)) htu
  obtain ⟨v,hv⟩ := (unitaryCentral% norm_one_divisor) ι hinv hne T hT
  let B := innerWeights (k:=k) ι u v
  have hBprod : ∏ i, B i=P := by
    rw [innerWeights_product,hv]
    dsimp only [T]
    rw [mul_comm]
    exact div_mul_cancel _ _
  let w := fun i => B i/a' i
  have hw : ∏ i, w i=1 := by
    simp only [w,Finset.prod_div_distrib,hBprod]
    change P/P=1
    simp
  have hwu : ∀ i, ι (w i:F)*(w i.rev:F)=1 := by
    intro i
    simp only [w,Units.val_div_eq_div_val,map_div₀]
    calc
      _ = (ι (B i:F)*(B i.rev:F))/(ι (a' i:F)*(a' i.rev:F)) := by ring
      _ = 1 := by rw [innerWeights_unitary ι hinv,ha' i]; simp
  let h := (radicalTorus% diagonalSL) w hw
  refine ⟨h,v,?_,(unitaryTorus% diagonal_fixed) ι w hw hwu,?_⟩
  · intro i j hij
    change Matrix.diagonal (fun t => (w t:F)) i j=0
    simp [Matrix.diagonal_apply,hij]
  · intro g
    rw [radicalTorus% diagonalSL_action]
    apply SpecialLinearGroup.ext
    intro i j
    rw [unitOdd% diagonal_entry,unitOdd% diagonal_entry,unitOdd% diagonal_entry]
    simp only [w,a',Units.val_div_eq_div_val,Units.val_mul,Units.val_inv_eq_inv_val]
    dsimp only [B]
    field_simp
    <;> ring
end NikolovSegal.PartIIUnitaryRadicalDiagonalNormalization
