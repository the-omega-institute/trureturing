import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.ProductAbsorptionScalar

namespace Reg.D5.S3.Entropy.ProductAbsorptionScalar
open _root_.D5.S3.Entropy.ProductAbsorptionScalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set MeasureTheory LeanInformationAudit
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ b t => phaseNoiseEntropy b t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z w b : ℝ}, z ∈ Icc (-1 : ℝ) 1 → w ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
    let l := z * w
    let T := Real.sqrt ((1 - z ^ 2) * (1 - w ^ 2))
    0 ≤ R.readout () b z + R.readout () b w - 2 * R.readout () b l +
      (R.readout () b (l + T) + R.readout () b (l - T)) / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 0) (w := 0) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  change phaseNoiseEntropy 0 0 ≠ phaseNoiseEntropy 0 1
  norm_num [phaseNoiseEntropy]
  exact hp.ne

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.ProductAbsorptionScalar.product_binary_entropy_absorption)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.ProductAbsorptionScalar.product_binary_entropy_absorption,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Entropy.ProductAbsorptionScalar.product_binary_entropy_absorption)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.ProductAbsorptionScalar.product_binary_entropy_absorption.__information_unit
  realizationName := `Reg.D5.S3.Entropy.ProductAbsorptionScalar.family
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
    (fun _ b t => phaseNoiseEntropy b t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.ProductAbsorptionScalar
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.ProductAbsorptionScalar
