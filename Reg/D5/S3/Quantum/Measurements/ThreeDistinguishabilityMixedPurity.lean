import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation (InRegion)
open scoped BigOperators Classical

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4 → ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ p => decide (InRegion p)) (fun e => nomatch e)

/-- Replace mixed-region membership by the row cap on the same law. -/
def capOnly : Realization signature :=
  realize signature (fun _ _ p => decide (∀ i, p i ≤ 1 / 3)) (fun e => nomatch e)

/-- Observe membership while retaining the simplex premises and the entire scalar test. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 4 → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
    (R.readout () () p = true ↔
      (∀ i, p i ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        (∀ i, q p i ^ 2 * t ≥ d p i ^ 2) ∧ phaseCubic p t = 0)

private theorem capOnly_fails : ¬ arena.Law capOnly := by
  intro h
  have hn (i : Fin 4) : 0 ≤ infeasibleWeights i := by
    fin_cases i <;> norm_num [infeasibleWeights]
  have hs : ∑ i, infeasibleWeights i = 1 := by
    norm_num [infeasibleWeights, Fin.sum_univ_four]
  have hc (i : Fin 4) : infeasibleWeights i ≤ 1 / 3 :=
    (infeasible_weighted_phase_columns.1 i).le
  have hread : capOnly.readout () () infeasibleWeights = true := by
    simpa only [capOnly, realize, decide_eq_true_eq] using hc
  exact infeasible_not_inRegion ((inRegion_iff_cubic _ hn hs).2 ((h _ hn hs).1 hread))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ![0, 1 / 3, 1 / 3, 1 / 3], infeasibleWeights, ?_⟩
  change decide (InRegion (![0, 1 / 3, 1 / 3, 1 / 3] : Fin 4 → ℝ)) ≠
    decide (InRegion infeasibleWeights)
  intro heq
  have hgood := decide_eq_true one_zero_feasible
  exact infeasible_not_inRegion (of_decide_eq_true (heq.symm.trans hgood))

def source_registration : Registration arena (type_of% @inRegion_iff_cubic) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using inRegion_iff_cubic,
    capOnly, capOnly_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual capOnly
    capOnly_fails
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity.unit
  realizationName := `Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => decide (InRegion p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
