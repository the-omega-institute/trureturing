import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.ProductAbsorptionLogKernel

namespace Reg.D5.S3.Entropy.ProductAbsorptionLogKernel
open _root_.D5.S3.Entropy.ProductAbsorptionLogKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set LeanInformationAudit
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p s => productLogKernel p.1 p.2 s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => if s ≤ 1 then (-1 : ℝ) else 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
    (∀ s ∈ Ioi (0 : ℝ), 0 ≤ R.readout () ⟨u, v⟩ s) ∨
      ∃ r ∈ Ioi (0 : ℝ), R.readout () ⟨u, v⟩ r = 0 ∧
        (∀ s ∈ Ioo (0 : ℝ) r, 0 < R.readout () ⟨u, v⟩ s) ∧
        (∀ s ∈ Ioi r, R.readout () ⟨u, v⟩ s < 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h (u := 1 / 2) (v := 1 / 2) (by norm_num) (by norm_num) with h | ⟨r, _, he, _⟩
  · have hh := h (1 / 2) (by norm_num)
    norm_num [rejected, realize] at hh
  · change (if r ≤ 1 then (-1 : ℝ) else 1) = 0 at he
    split_ifs at he <;> norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1 / 2, 1 / 2⟩, 1 / 4, 1, ?_⟩
  have hlog1 : Real.log ((405 : ℝ) / 256) =
      4 * Real.log 3 + Real.log 5 - 4 * Real.log 4 := by
    rw [show (405 : ℝ) / 256 = 3 ^ 4 * 5 / 4 ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hlog2 : Real.log ((2592 : ℝ) / 2401) =
      4 * Real.log (3 / 2) + Real.log 2 - 4 * Real.log (7 / 4) := by
    rw [show (2592 : ℝ) / 2401 = (3 / 2) ^ 4 * 2 / (7 / 4) ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hlt : Real.log ((2592 : ℝ) / 2401) < Real.log ((405 : ℝ) / 256) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  change productLogKernel (1 / 2) (1 / 2) (1 / 4) ≠ productLogKernel (1 / 2) (1 / 2) 1
  norm_num [productLogKernel]
  intro he
  linarith

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.ProductAbsorptionLogKernel.product_log_kernel_single_crossing)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.ProductAbsorptionLogKernel.product_log_kernel_single_crossing,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Entropy.ProductAbsorptionLogKernel.product_log_kernel_single_crossing)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.ProductAbsorptionLogKernel.product_log_kernel_single_crossing.__information_unit
  realizationName := `Reg.D5.S3.Entropy.ProductAbsorptionLogKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => productLogKernel p.1 p.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.ProductAbsorptionLogKernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Entropy.ProductAbsorptionLogKernel
