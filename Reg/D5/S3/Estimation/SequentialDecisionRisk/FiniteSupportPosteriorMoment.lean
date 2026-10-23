import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open scoped BigOperators
open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment

noncomputable section
namespace Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha1 : compensation M q r < 1)
    (e : Experiment) (o : Obs M s e) (I : Finset (Fin M)) (t : ℝ) (ht : 0 ≤ t),
    (∑ S : Support M q, posterior r e o S *
      Real.exp (t * ((I ∩ S.val).card : ℝ))) ≤
      ∏ i ∈ I, (1 + (Real.exp t - 1) * inclusion q r e o i) ∧
    (∏ i ∈ I, (1 + (Real.exp t - 1) * inclusion q r e o i)) ≤
      R.readout () () ((Real.exp t - 1) * ∑ i ∈ I, inclusion q r e o i)

def family : Registration arena (type_of% (@finite_support_posterior_moment)) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hcase := h (M := 2) (q := 1) (s := 0) (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [compensation]) Experiment.pair (fun i => Fin.elim0 i) ∅ 0 le_rfl
    have hb := hcase.2
    norm_num [rejected, realize] at hb
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@finite_support_posterior_moment, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      arena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
      change Real.exp 0 ≠ Real.exp 1
      exact Real.exp_injective.ne zero_ne_one }

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_support_posterior_moment)
    (type_of% (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.finite_support_posterior_moment.__information_unit
  realizationName := `Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment
end

#print axioms Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.family
#print axioms Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.registration
