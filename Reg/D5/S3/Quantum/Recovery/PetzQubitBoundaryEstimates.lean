import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the close-pair logistic endpoint bound. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates (close_pair_weighted_evaluation)
open PetzExponentialBoundaryEvaluation (petzWeight)
open PetzLogisticEvaluation (correlation exact_gram_factorization)
open ExponentialGramWeightedEvaluation (exponentialSum)

namespace Reg.D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ω : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (j : Fin 3) (_ : j ≠ 0) (_ : (1 / 5 : ℝ) ≤ ‖correlation ω 0 j‖ ^ 2),
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    R.readout () () (‖exponentialSum ω a 0‖ ^ 2) ((8 / 3) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ω : Fin 3 → ℝ := fun _ => 0
  have hunit : correlation ω 0 1 = 1 :=
    (show correlation ω 0 1 = correlation ω 0 0 from rfl).trans
      ((exact_gram_factorization ω).2.1 0)
  exact (h ω (fun _ => 0) 1 (by decide) (by rw [hunit, norm_one]; norm_num)).2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @close_pair_weighted_evaluation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@close_pair_weighted_evaluation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@close_pair_weighted_evaluation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates.close_pair_weighted_evaluation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates
