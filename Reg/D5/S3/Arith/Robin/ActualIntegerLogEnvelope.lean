import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualIntegerLogEnvelope
import Reg.Support.DependentFamily

/-! Source-bound whole-family registration for the actual integer envelope. -/

namespace Reg.D5.S3.Arith.Robin.ActualIntegerLogEnvelope

open _root_.D5.S3.Arith.Robin.ActualIntegerLogEnvelope
open _root_.D5.S3.Arith.Robin.OriginalFirstClockTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => originalObjective n) (fun e => nomatch e)

theorem objective_three_pos : 0 < originalObjective 3 := by
  have hl : 1 < Real.log (3 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hl0 : 0 < Real.log (3 : ℝ) := by linarith
  have hl2 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hexp : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hll : 0 < Real.log (Real.log (3 : ℝ)) := Real.log_pos hl
  have hll1 : Real.log (Real.log (3 : ℝ)) < 1 := by
    have := Real.log_lt_log hl0 (hl2.trans_lt hexp)
    simpa only [Real.log_exp] using this
  have hneg := Real.log_neg hll hll1
  have hs : (ArithmeticFunction.sigma 1 3 : ℝ) = 4 := by norm_num [ArithmeticFunction.sigma]
  unfold originalObjective
  rw [hs]
  have hpos : 0 < Real.log ((4 : ℝ) / 3) := Real.log_pos (by norm_num)
  norm_num only [Nat.cast_ofNat]
  linarith

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  change originalObjective 0 ≠ originalObjective 3
  have hz : originalObjective 0 = 0 := by simp [originalObjective]
  rw [hz]
  exact objective_three_pos.ne

abbrev envelopeArena : Arena where
  signature := signature
  Law R := ∃ A : ℝ, 286 ≤ A ∧ ∀ n : ℕ, 0 < n → A ≤ Real.log (n : ℝ) →
    R.readout () () n - Real.eulerMascheroniConstant ≤
      2 / Real.log (Real.log (n : ℝ))

def rejected : Realization signature :=
  realize signature (fun _ _ n => Real.log (n : ℝ) + Real.eulerMascheroniConstant)
    (fun e => nomatch e)

theorem rejected_law : ¬ envelopeArena.Law rejected := by
  rintro ⟨A, hA, h⟩
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hnA⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (ht.eventually_ge_atTop (max A (max 3 (Real.exp 1))))).exists
  have hAn : A ≤ Real.log (n : ℝ) := (le_max_left A _).trans hnA
  have h3 : 3 ≤ Real.log (n : ℝ) :=
    (le_max_left 3 _).trans ((le_max_right A _).trans hnA)
  have he : Real.exp 1 ≤ Real.log (n : ℝ) :=
    (le_max_right 3 _).trans ((le_max_right A _).trans hnA)
  have hl : 1 ≤ Real.log (Real.log (n : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hb := h n hn hAn
  change Real.log (n : ℝ) + Real.eulerMascheroniConstant -
    Real.eulerMascheroniConstant ≤ _ at hb
  have hc : 2 / Real.log (Real.log (n : ℝ)) ≤ 2 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

def envelopeFamily : Registration envelopeArena (type_of% @eventual_actual_integer_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventual_actual_integer_envelope, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def envelopeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_actual_integer_envelope) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualIntegerLogEnvelope.eventual_actual_integer_envelope.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualIntegerLogEnvelope.envelopeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨envelopeArena⟩
  objectArena := .source ⟨envelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source envelopeArena ⟨envelopeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualIntegerLogEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms envelopeFamily
#print axioms envelopeAudit

namespace SupportedSigmaBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (ArithmeticFunction.sigma 1 n : ℝ) / n)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {U : ℕ}, 0 < U → ∀ {x : ℝ},
    (∀ p ∈ U.primeFactors, (p : ℝ) ≤ x) →
    R.readout () () U ≤
      ∏ p ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (U := 1) (by norm_num) (x := 0) (by simp)
  change (2 : ℝ) ≤ ∏ p ∈ Finset.Ioc (0 : ℕ) ⌊(0 : ℝ)⌋₊ with p.Prime,
    (1 - 1 / (p : ℝ))⁻¹ at hb
  norm_num at hb

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @supported_sigma_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supported_sigma_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@supported_sigma_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualIntegerLogEnvelope.supported_sigma_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualIntegerLogEnvelope.SupportedSigmaBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualIntegerLogEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end SupportedSigmaBound

end
end Reg.D5.S3.Arith.Robin.ActualIntegerLogEnvelope
