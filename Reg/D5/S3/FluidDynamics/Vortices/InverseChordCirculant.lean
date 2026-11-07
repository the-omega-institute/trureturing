import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.InverseChordCirculant
import Reg.Support.SingleDependentReadout

/-! Source registrations for the charge diagonal, alternating sum and product spectrum. -/

namespace Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant
open _root_.D5.S3.FluidDynamics.Vortices.InverseChordCirculant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

namespace ChargeDiagonal
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin (2 * m)) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ j => (-1 : ℝ) ^ (j.val + 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => (-1 : ℝ) ^ (j.val + 2) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, chargeMatrix m = Matrix.diagonal (fun j => R.readout () m j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun M => M 0 0) (h 1)
  change chargeMatrix 1 0 0 = (-1 : ℝ) ^ ((0 : Fin 2).val + 2) + 1 at he
  rw [chargeMatrix_diagonal] at he
  norm_num [Matrix.diagonal_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (-1 : ℝ) ^ ((0 : Fin 2).val + 2) ≠ (-1 : ℝ) ^ ((1 : Fin 2).val + 2)
  norm_num

def source : Registration arena (type_of% @chargeMatrix_diagonal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chargeMatrix_diagonal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chargeMatrix_diagonal) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.ChargeDiagonal.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.ChargeDiagonal.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => (-1 : ℝ) ^ (j.val + 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.InverseChordCirculant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end ChargeDiagonal

namespace AlternatingWeightSum
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin (2 * m)) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m j =>
    ∑ k : Fin (2 * m), (-1 : ℝ) ^ (k.val + 2) * weights m j k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ m j =>
    (∑ k : Fin (2 * m), (-1 : ℝ) ^ (k.val + 2) * weights m j k) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 3 ≤ m → ∀ j : Fin (2 * m),
    R.readout () m j = (-1 : ℝ) ^ (j.val + 2) * diagonalWeight m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 3 (by omega) 0
  change (∑ k : Fin (2 * 3), (-1 : ℝ) ^ (k.val + 2) * weights 3 0 k) + 1 = _ at hb
  rw [alternating_weight_sum 3 (by omega) 0] at hb
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  change (∑ k : Fin (2 * 3), (-1 : ℝ) ^ (k.val + 2) * weights 3 0 k) ≠
    ∑ k : Fin (2 * 3), (-1 : ℝ) ^ (k.val + 2) * weights 3 1 k
  rw [alternating_weight_sum 3 (by omega) 0, alternating_weight_sum 3 (by omega) 1]
  norm_num [diagonalWeight]

def source : Registration arena (type_of% @alternating_weight_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@alternating_weight_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@alternating_weight_sum) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.AlternatingWeightSum.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.AlternatingWeightSum "source"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m j =>
    ∑ k : Fin (2 * m), (-1 : ℝ) ^ (k.val + 2) * weights m j k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.InverseChordCirculant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end AlternatingWeightSum

namespace ProductSpectrum
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m y => (y • 1 - blockC m * blockB m).det) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ m y => (y • 1 - blockC m * blockB m).det + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) [NeZero (2 * m)], 3 ≤ m → ∀ y : ℝ,
    R.readout () m y = ∏ k : ZMod (2 * m), (y - gamma m k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 3 (by omega) 0
  change ((0 : ℝ) • 1 - blockC 3 * blockB 3).det + 1 = _ at hb
  rw [product_spectrum 3 (by omega) 0] at hb
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  dsimp only [actual, realize]
  rw [product_spectrum 3 (by omega) 0, product_spectrum 3 (by omega) 1]
  have hz : (∏ k : ZMod (2 * 3), (0 - gamma 3 k)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (3 : ZMod (2 * 3)))
    have hv : (3 : ZMod (2 * 3)).val = 3 := rfl
    norm_num [gamma, hv]
  rw [hz]
  apply Ne.symm
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  fin_cases k <;> norm_num [gamma, ZMod.val]

def source : Registration arena (type_of% @product_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_spectrum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@product_spectrum) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.ProductSpectrum.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant.ProductSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m y => (y • 1 - blockC m * blockB m).det)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.InverseChordCirculant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end ProductSpectrum
end
end Reg.D5.S3.FluidDynamics.Vortices.InverseChordCirculant
