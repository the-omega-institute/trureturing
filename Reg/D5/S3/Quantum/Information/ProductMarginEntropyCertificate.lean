import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ProductMarginEntropyCertificate

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Information.ProductMarginEntropyCertificate

noncomputable section
namespace Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, s ∈ Set.Icc (2 / 3 : ℝ) 1 →
    (1 - s) / (2 * s) * Real.log (4096 / 3125) ≤
      Real.log 2 - R.readout () () ((1 - s) / (1 + s)) -
        (3 - 2 / s) * (Real.log 2 - Real.binEntropy ((1 + s) / 2))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := @h 1 (by norm_num)
  norm_num [bad, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 5, ?_⟩
  simp only [actual, realize, Real.binEntropy_zero]
  exact ne_of_lt (Real.binEntropy_pos (by norm_num) (by norm_num))
def family : Registration arena (type_of% (@binary_entropy_certificate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binary_entropy_certificate, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binary_entropy_certificate) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginEntropyCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
namespace Budget

def bad : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b k j c d : ℝ},
    a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ k → 0 ≤ c → 0 ≤ d → 0 ≤ j →
    k ≤ (1 - Real.sqrt (a * b)) / (1 + Real.sqrt (a * b)) →
    j ≤ b * c → j ≤ a * d →
    j ≤ Real.log 2 - Real.binEntropy ((1 + Real.sqrt (a * b)) / 2) →
    0 ≤ Real.log 2 - R.readout () () k + c + d - 3 * j
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := @h 0 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact sub_nonneg.mpr Real.binEntropy_le_log_two)
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num [bad, realize] at hh
  linarith

def family : Registration arena (type_of% (@information_budget_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@information_budget_nonneg, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@information_budget_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate.Budget.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate.Budget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginEntropyCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Budget
end Reg.D5.S3.Quantum.Information.ProductMarginEntropyCertificate
