import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QPECircularTail
import Reg.Support.SingleDependentReadout

/-! Source-bound circular-tail audit on the original probability family. -/
namespace Reg.D5.S3.Quantum.QPECircularTail
open QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℝ)
    (fun p => Fin (2 ^ p.1)) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p j => probability (2 ^ p.1) p.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ) (φ ρ : ℝ), 0 < ρ →
    (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ t) =>
        ρ ≤ ‖((φ - (j.val : ℝ) / (2 : ℝ) ^ t : ℝ) : UnitAddCircle)‖),
      R.readout () ⟨t, φ⟩ j) ≤
      1 / (2 * (2 : ℝ) ^ t * ρ) + 1 / (2 * ((2 : ℝ) ^ t * ρ) ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 (1 / 2) (1 / 2) (by norm_num)
  norm_num [rejected, realize, UnitAddCircle.norm_eq, round_eq] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change probability 2 0 0 ≠ probability 2 0 1
  have hzero : probability 2 0 0 = 1 := by
    rw [probability, amplitude_of_integral 2 (by norm_num) 0 0]
    · norm_num
    · norm_num
  have hn := qpe_probability_normalized (N := 2) (by norm_num) (0 : ℝ)
  rw [Fin.sum_univ_two] at hn
  linarith

def source_registration : Registration arena (type_of% @qpe_circular_tail_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qpe_circular_tail_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@qpe_circular_tail_le) (Realization signature) Unit Unit := {
  unitName := `QuantumPhaseEstimationGeneral.qpe_circular_tail_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QPECircularTail.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p j => probability (2 ^ p.1) p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QPECircularTail
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.QPECircularTail


namespace Reg.D5.S3.Quantum.QPECircularTail.ShiftedReciprocalTail
open QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a k => 1 / (a + (k : ℝ)) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) (n : ℕ), 0 < a →
    (∑ k ∈ Finset.range n, R.readout () a k) ≤ 1 / a ^ 2 + 1 / a

private theorem source_reconstruction :
    (type_of% @reciprocal_square_shifted_finite_tail_le) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num)
  norm_num [rejected, realize] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration :
    Registration arena (type_of% @reciprocal_square_shifted_finite_tail_le) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@reciprocal_square_shifted_finite_tail_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@reciprocal_square_shifted_finite_tail_le) (Realization signature) Unit Unit := {
  unitName := `QuantumPhaseEstimationGeneral.reciprocal_square_shifted_finite_tail_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QPECircularTail.ShiftedReciprocalTail.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ a k => 1 / (a + (k : ℝ)) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QPECircularTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.QPECircularTail.ShiftedReciprocalTail
