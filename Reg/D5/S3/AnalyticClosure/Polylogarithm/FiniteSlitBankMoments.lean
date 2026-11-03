import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter MeasureTheory Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments
open _root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ h x ↦ h x) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (h : ℝ → ℝ) (R : ℝ), 1 < R → ContinuousOn h (Icc 1 R) →
    (∀ x ∈ Icc 1 R, 0 ≤ h x) → (∀ x ∈ Ioo 1 R, 0 < h x) →
    ∀ B : ℝ, ∀ᶠ n : ℕ in atTop,
      B / R ^ n < (1 / Real.pi) *
        ∫ x in (1 : ℝ)..R, r.readout () h x / x ^ (n + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (fun _ ↦ 1) 2 (by norm_num) continuousOn_const
    (by intros; norm_num) (by intros; norm_num) 1
  simp only [rejected, realize, zero_div, intervalIntegral.integral_zero, mul_zero] at he
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)) hn

def source : Registration arena (type_of% @bank_dominance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bank_dominance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨id, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bank_dominance) (Realization signature) Type Unit where
  unitName := `D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments.bank_dominance.__information_unit
  realizationName := `Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h x ↦ h x) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg", "arg", "fn", "fn", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 8
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments
