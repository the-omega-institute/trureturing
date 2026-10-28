import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CommutatorGap
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the unitary first-column existence theorem. -/

namespace Reg.D5.S3.Quantum.Matrix.CommutatorGap
open _root_.D5.S3.Quantum.Matrix.CommutatorGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => EuclideanSpace ℂ (Fin (n + 1))) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => ‖v‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (v : EuclideanSpace ℂ (Fin (n + 1))),
    R.readout () n v = 1 →
      ∃ U : Matrix.unitaryGroup (Fin (n + 1)) ℂ,
        ∀ i, (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i 0 = v.ofLp i

abbrev sourceScope := type_of% (@exists_unitary_first_column)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, hU⟩ := h (n := 0) (0 : EuclideanSpace ℂ (Fin 1))
    (by norm_num [rejected, realize])
  have hu : (U : _root_.Matrix (Fin 1) (Fin 1) ℂ)ᴴ * (U : _root_.Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have hentry := congrArg (fun M : _root_.Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hu
  have hzero := hU 0
  have hz : (0 : ℂ) = 1 := by
    simpa [Matrix.mul_apply, hzero] using hentry
  exact zero_ne_one hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (0 : EuclideanSpace ℂ (Fin 1)), EuclideanSpace.single 0 1, ?_⟩
  simp [actual, realize, EuclideanSpace.single]

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitary_first_column, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CommutatorGap.exists_unitary_first_column)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CommutatorGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CommutatorGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => ‖v‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CommutatorGap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.CommutatorGap
