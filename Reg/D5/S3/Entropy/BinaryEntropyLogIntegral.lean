import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.BinaryEntropyLogIntegral

namespace Reg.D5.S3.Entropy.BinaryEntropyLogIntegral
open _root_.D5.S3.Entropy.BinaryEntropyLogIntegral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set MeasureTheory LeanInformationAudit
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
    IntegrableOn (fun s : ℝ => Real.log (1 + x / s) / Real.sqrt (1 + s)) (Ioi 0) ∧
      R.readout () () x =
        (1 / 4 : ℝ) * ∫ s in Ioi (0 : ℝ), Real.log (1 + x / s) / Real.sqrt (1 + s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (x := 0) (by norm_num)).2
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  norm_num [actual, realize]
  exact hp.ne

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.BinaryEntropyLogIntegral.binEntropy_sqrt_log_integral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.BinaryEntropyLogIntegral.binEntropy_sqrt_log_integral,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Entropy.BinaryEntropyLogIntegral.binEntropy_sqrt_log_integral)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.BinaryEntropyLogIntegral.binEntropy_sqrt_log_integral.__information_unit
  realizationName := `Reg.D5.S3.Entropy.BinaryEntropyLogIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.BinaryEntropyLogIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.BinaryEntropyLogIntegral
