import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.PeriodicOrbits.CountableRealization

/-! Faithful whole-family source reconstruction for the all-index fixed-card formula. -/

namespace Reg.D5.S1.Dynamics.PeriodicOrbits.CountableRealization
open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.PeriodicOrbits.CountableRealization
noncomputable section

abbrev signature : Signature where
  Params := ℕ → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : ℕ → ℕ) {n : ℕ}, 0 < n →
    R.readout () c n = ∑ d ∈ n.divisors, d * c d

def actual : Realization signature :=
  realize signature (fun _ c n => fixedCard (rotation c) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceScope := type_of% (@fixed_card)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := @h (fun _ => 1) 1 (by omega)
  norm_num [rejected,realize] at hc

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@fixed_card), rejected, rejected_law⟩
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
    refine ⟨(fun _ => 1), 1, 2, ?_⟩
    change fixedCard (rotation (fun _ => 1)) 1 ≠ fixedCard (rotation (fun _ => 1)) 2
    rw [fixed_card _ (by omega), fixed_card _ (by omega)]
    decide

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixed_card) (Realization signature) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.CountableRealization.fixed_card.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.CountableRealization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ c n => fixedCard (rotation c) n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.CountableRealization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S1.Dynamics.PeriodicOrbits.CountableRealization
