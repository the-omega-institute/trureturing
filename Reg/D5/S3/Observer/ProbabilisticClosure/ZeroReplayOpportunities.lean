import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities
import Reg.Support.DependentFamily

/-! The complete seed, policy and root family is retained in the opportunity readout. -/

namespace Reg.D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities

open _root_.D5.S3.Observer.ProbabilisticClosure
open AdaptiveMarkerStoppingTails ZeroReplayOpportunities
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

structure Context where
  Seed : Type u
  space : MeasurableSpace Seed
  policy : @Policy Seed space
  seed : Seed
  root : Bool

abbrev signature : Signature where
  Params := Context.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ c => @opportunityCount c.Seed c.space c.policy c.seed c.root)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Seed : Type u} [space : MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (r : ℕ),
    ∃ (n : ℕ) (source : Source),
      opportunityQuery policy seed root r = n + 1 ∧ n + 1 ≤ 2 * r + 3 ∧
      R.readout () ⟨Seed, space, policy, seed, root⟩ n = r ∧
      opportunity policy seed root n ∧ source.1 = root ∧ noAdjacentOnes source ∧
      (actualRun policy seed source n).stopped = false ∧
      actualRun policy seed source (n + 1) = (archive policy seed root r).2 ∧
      (archive policy seed root r).1 = seed ∧
      (archive policy seed root r).2.actions.length = n + 1

private def leftPolicy : @Policy (ULift.{u} Unit) ⊤ where
  choose := fun _ _ _ => false
  measurable_section := fun _ _ => measurable_const

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, hc, _⟩ := @h (ULift.{u} Unit) ⊤ leftPolicy ⟨()⟩ false 1
  exact Nat.zero_ne_one hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Unit, ⊤, leftPolicy, ⟨()⟩, false⟩, 0, 1, ?_⟩
  change opportunityCount leftPolicy ⟨()⟩ false 0 ≠
    opportunityCount leftPolicy ⟨()⟩ false 1
  simp [opportunityCount, opportunity, zeroReplay, sideCount, alternatingBit]

def source_registration : Registration arena.{u} (type_of% @finite_replay_first_failure.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_replay_first_failure.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration
      (@finite_replay_first_failure.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities.finite_replay_first_failure.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ c => @opportunityCount c.Seed c.space c.policy c.seed c.root)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities
