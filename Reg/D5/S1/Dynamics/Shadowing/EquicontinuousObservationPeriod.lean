import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open TopologicalSpace Set Function Filter UniformSpace

namespace Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod

noncomputable section
universe u v

/-- Observe the period used in the iterate, retaining the full source telescope. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ M => M) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {D : Type u} {A : Type v} [UniformSpace D] [CompactSpace D]
    [TopologicalSpace A] [DiscreteTopology A]
    (T : D → D) (q : D → A) (_hT : Surjective T) (_hq : Continuous q)
    (_heq : Equicontinuous (fun n : ℕ => T^[n])),
    ∃ M : ℕ, 0 < M ∧ ∀ x : D, q (T^[R.readout () () M] x) = q x

/-- Forcing the observed period to one fails for the two-cycle. -/
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let D := ULift.{u} Bool
  let A := ULift.{v} Bool
  let T : D → D := fun x => ⟨!x.down⟩
  let q : D → A := fun x => ⟨x.down⟩
  have hT : Surjective T := by
    intro x
    refine ⟨⟨!x.down⟩, ?_⟩
    apply ULift.ext
    simp [T]
  have heq : Equicontinuous (fun n : ℕ => T^[n]) := by
    intro x E hE
    rw [nhds_discrete]
    exact mem_pure.mpr (fun n => refl_mem_uniformity hE)
  obtain ⟨M, hM, hp⟩ := h T q hT continuous_of_discreteTopology heq
  have hh := congrArg ULift.down (hp (⟨false⟩ : D))
  change (!false) = false at hh
  exact Bool.noConfusion hh

def sourceRegistration : Registration arena.{u,v}
    (type_of% (@finite_observation_period_of_equicontinuous_surjective.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_observation_period_of_equicontinuous_surjective.{u,v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

/-- The natural-number readout is the period inside the iterated dynamics. -/
def attempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_period_of_equicontinuous_surjective.{u,v})
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod.period
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨sourceRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceRegistration
#print axioms attempt

end
end Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObservationPeriod
