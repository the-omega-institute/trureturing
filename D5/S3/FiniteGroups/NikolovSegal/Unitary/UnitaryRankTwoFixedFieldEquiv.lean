/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryRankTwoCoordinates

/-! Explicit rank-two unitary recognition, including characteristic two.
The chosen scalar comes from a nontrivial involution and has actual relative trace zero. -/
namespace NikolovSegal.UnitaryRankTwo

open Matrix NikolovSegal.UnitaryField
variable {F : Type*} [Field F] [Finite F]

theorem exists_nonzero_trace_zero (ι : F ≃+* F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) :
    ∃ τ : F, τ ≠ 0 ∧ Algebra.trace (fixedField ι) F τ = 0 ∧ ι τ = -τ := by
  obtain ⟨τ, hτ, hanti⟩ := exists_antifixed ι hinv hne
  refine ⟨τ, hτ, ?_, hanti⟩
  apply (fixedField ι).subtype.injective
  change (Algebra.trace (fixedField ι) F τ : F) = 0
  rw [trace_formula ι hinv hne, hanti, add_neg_cancel]

/-- An explicit actual group equivalence for any nonzero anti-fixed scaling element. -/
def coordinateEquiv (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0) (hanti : ι τ = -τ) :
    specialUnitary ι ≃* SpecialLinearGroup (Fin 2) (fixedField ι) where
  toFun := toFixedSL ι τ hτ hanti
  invFun := fromFixedSL ι τ hτ hanti
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    change coordinateMatrix τ⁻¹
      ((fixedCoordinateMatrix ι τ hτ hanti A).map (fixedField ι).subtype) = A.val.val
    rw [fixedCoordinateMatrix_coe, coordinateMatrix_inverse τ hτ]
  right_inv B := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change coordinateMatrix τ
      (coordinateMatrix τ⁻¹ (B.val.map (fixedField ι).subtype)) i j = (B.val i j : F)
    have hh := coordinateMatrix_inverse τ⁻¹ (inv_ne_zero hτ)
      (B.val.map (fixedField ι).subtype)
    simpa only [inv_inv, Matrix.map_apply, Subfield.subtype_apply] using congrArg (fun M => M i j) hh
  map_mul' := (toFixedSL ι τ hτ hanti).map_mul

theorem coordinateEquiv_forward (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (A : specialUnitary ι) :
    ((coordinateEquiv ι τ hτ hanti A).val.map (fixedField ι).subtype) =
      !![A.val.val 0 0, A.val.val 0 1 / τ; τ * A.val.val 1 0, A.val.val 1 1] := rfl

theorem coordinateEquiv_backward (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (B : SpecialLinearGroup (Fin 2) (fixedField ι)) :
    ((coordinateEquiv ι τ hτ hanti).symm B).val.val =
      !![(B.val 0 0 : F), τ * (B.val 0 1 : F);
         (B.val 1 0 : F) / τ, (B.val 1 1 : F)] := by
  change coordinateMatrix τ⁻¹ (B.val.map (fixedField ι).subtype) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, div_eq_mul_inv, mul_comm]

/-- One actual equivalence is selected before every group target. -/
noncomputable def specialUnitaryEquivFixedSL (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    specialUnitary ι ≃* SpecialLinearGroup (Fin 2) (fixedField ι) :=
  let h := exists_nonzero_trace_zero ι hinv hne
  coordinateEquiv ι (Classical.choose h) (Classical.choose_spec h).1
    (Classical.choose_spec h).2.2

/-- Literal constructive endpoint, recording both the actual conjugation and inverse coordinates. -/
theorem exists_explicit_fixedField_equiv (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    ∃ τ : F, τ ≠ 0 ∧ Algebra.trace (fixedField ι) F τ = 0 ∧ ι τ = -τ ∧
      ∃ e : specialUnitary ι ≃* SpecialLinearGroup (Fin 2) (fixedField ι),
        (∀ A : specialUnitary ι,
          (e A).val.map (fixedField ι).subtype =
            diagonal ![τ⁻¹, 1] * A.val.val * diagonal ![τ, 1]) ∧
        (∀ B : SpecialLinearGroup (Fin 2) (fixedField ι),
          (e.symm B).val.val = !![(B.val 0 0 : F), τ * (B.val 0 1 : F);
            (B.val 1 0 : F) / τ, (B.val 1 1 : F)]) := by
  obtain ⟨τ, hτ, htrace, hanti⟩ := exists_nonzero_trace_zero ι hinv hne
  refine ⟨τ, hτ, htrace, hanti, coordinateEquiv ι τ hτ hanti, ?_, ?_⟩
  · intro A
    exact coordinateMatrix_conjugation τ hτ A.val.val
  · exact coordinateEquiv_backward ι τ hτ hanti

end NikolovSegal.UnitaryRankTwo
