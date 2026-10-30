import Reg.D5.S3.Entropy.ProductAbsorptionLogKernel
import D5.S3.Entropy.ProductAbsorptionLogIntegral

namespace Reg.D5.S3.Entropy.ProductAbsorptionLogIntegral
open _root_.D5.S3.Entropy.ProductAbsorptionLogIntegral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set MeasureTheory LeanInformationAudit
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.D5.S3.Entropy.ProductAbsorptionLogKernel.signature
abbrev actual := Reg.D5.S3.Entropy.ProductAbsorptionLogKernel.actual

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
    IntegrableOn (R.readout () ⟨u, v⟩) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), R.readout () ⟨u, v⟩ s) = productLogMoment u v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (u := 1) (v := 1 / 2) (by norm_num) (by norm_num)).2
  have hg : productLogMoment 1 (1 / 2) = Real.log 2 := by
    norm_num [productLogMoment, Real.log_div]
    <;> ring
  rw [hg] at he
  have hz : (0 : ℝ) = Real.log 2 := by simpa [rejected, realize] using he
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' hz.symm

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.ProductAbsorptionLogIntegral.product_log_kernel_integrable_integral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.ProductAbsorptionLogIntegral.product_log_kernel_integrable_integral,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Reg.D5.S3.Entropy.ProductAbsorptionLogKernel.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Entropy.ProductAbsorptionLogIntegral.product_log_kernel_integrable_integral)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.ProductAbsorptionLogIntegral.product_log_kernel_integrable_integral.__information_unit
  realizationName := `Reg.D5.S3.Entropy.ProductAbsorptionLogIntegral.family
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
    (fun _ p s => _root_.D5.S3.Entropy.ProductAbsorptionLogKernel.productLogKernel p.1 p.2 s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.ProductAbsorptionLogIntegral
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.ProductAbsorptionLogIntegral
