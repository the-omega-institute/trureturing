import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.LogarithmicMellinReserve
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the lower logarithmic Mellin envelope. -/

namespace Reg.D5.S3.Arith.Robin.LogarithmicMellinReserve

open _root_.D5.S3.Arith.Robin.LogarithmicMellinReserve
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set Filter

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ b y => -Real.log y * y ^ (b - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => y ^ (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {b : ℝ}, 0 < b →
    IntegrableOn (fun y => R.readout () b y) (Ioc 0 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h (b := 1) (by norm_num)).mono_set Ioo_subset_Ioc_self
  have hf := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (by norm_num : (0 : ℝ) < 1)).mp hi
  norm_num at hf

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change -Real.log 1 * (1 : ℝ) ^ (1 - 1 : ℝ) ≠
    -Real.log 2 * (2 : ℝ) ^ (1 - 1 : ℝ)
  norm_num

def source_registration : Registration arena
    (type_of% @low_log_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨low_log_integrable,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@low_log_integrable)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.LogarithmicMellinReserve.unit
  realizationName := `Reg.D5.S3.Arith.Robin.LogarithmicMellinReserve.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b y => -Real.log y * y ^ (b - 1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.LogarithmicMellinReserve
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Arith.Robin.LogarithmicMellinReserve
