import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedMangoldtRate
import Reg.Support.SingleDependentReadout

/-!
The source realization retains the entire arithmetic rate telescope, with a
constant normalized error as the rejected realization.
-/

namespace Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate
open LeanInformationAudit Real Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => _root_.Mertens.E₁Λ x) (fun e => nomatch e)

/-- A constant normalized error of one cannot have any positive exponential rate. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 - Real.eulerMascheroniConstant) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ c > 0, ∃ C > 0, ∃ X ≥ (2 : ℝ), ∀ x ≥ X,
    |R.readout () () x + Real.eulerMascheroniConstant| ≤
      C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨c, hc, C, _hC, X, _hX, hbound⟩
  have hexp : Tendsto
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -c < 0)
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
          Real.tendsto_log_atTop))
  have hzero : Tendsto
      (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul C
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  have hb := hbound (max X A) (le_max_left _ _)
  change |(1 - Real.eulerMascheroniConstant) + Real.eulerMascheroniConstant| ≤
    C * Real.exp (-c * (Real.log (max X A)) ^ ((1 : ℝ) / 10)) at hb
  simp only [sub_add_cancel, abs_one] at hb
  exact (not_lt_of_ge hb) (hA (max X A) (le_max_right _ _))

def rateEvidence : Registration arena (type_of% E1Lambda_stretched_exponential) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨E1Lambda_stretched_exponential, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change _root_.Mertens.E₁Λ 1 ≠ _root_.Mertens.E₁Λ 2
    norm_num [_root_.Mertens.E₁Λ,
      show Finset.Ioc 0 1 = {1} by decide,
      show Finset.Ioc 0 2 = {1, 2} by decide,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

def rateRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E1Lambda_stretched_exponential) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate.rateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨rateEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => _root_.Mertens.E₁Λ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedMangoldtRate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg", "arg", "body", "arg",
        "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rateEvidence
#print axioms rateRegistration

end
end Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate
