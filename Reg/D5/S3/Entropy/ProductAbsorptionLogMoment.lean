import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.ProductAbsorptionLogMoment

namespace Reg.D5.S3.Entropy.ProductAbsorptionLogMoment
open _root_.D5.S3.Entropy.ProductAbsorptionLogMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.ProductAbsorptionLogIntegral
open Set MeasureTheory LeanInformationAudit
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ u v => productLogMoment u v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → 0 ≤ R.readout () u v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 0) (v := 0) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  change productLogMoment 1 0 ≠ productLogMoment 1 (1 / 2)
  norm_num [productLogMoment, Real.log_div]
  intro he
  linarith

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.ProductAbsorptionLogMoment.product_log_moment_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.ProductAbsorptionLogMoment.product_log_moment_nonneg,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Entropy.ProductAbsorptionLogMoment.product_log_moment_nonneg)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.ProductAbsorptionLogMoment.product_log_moment_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Entropy.ProductAbsorptionLogMoment.family
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
    (fun _ u v => productLogMoment u v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.ProductAbsorptionLogMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.ProductAbsorptionLogMoment
