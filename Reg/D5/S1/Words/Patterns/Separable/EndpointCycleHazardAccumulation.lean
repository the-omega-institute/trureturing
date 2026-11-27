import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
import Reg.Support.DependentFamily
import Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard

/-! Read out the actual future-hit family at its selected initial offset. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation

open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard (nextHazard)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Set Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => hitAt e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ e : ℤ, ∀ᵐ ω ∂streamMeasure,
    (∑' j, nextHazard (e + streamDiscrepancy j ω)) = ∞ ∧
      ∀ N : ℕ, ∃ k ≥ N, ω ∈ R.readout () () e k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible : ∀ᵐ _ : Stream ∂streamMeasure, False := (h 0).mono fun ω hω => by
    obtain ⟨k, _, hk⟩ := hω.2 0
    exact (show ω ∈ (∅ : Set Stream) from hk).elim
  exact (neBot_iff.mp (inferInstance : (ae streamMeasure).NeBot))
    (eventually_false_iff_eq_bot.mp impossible)

def family : Registration arena (type_of% @actual_hazard_accumulation_and_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_hazard_accumulation_and_recurrence, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence :=
    Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_hazard_accumulation_and_recurrence) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => hitAt e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg",
        "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
