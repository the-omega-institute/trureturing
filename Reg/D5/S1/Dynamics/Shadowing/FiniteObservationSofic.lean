import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open _root_.D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open TopologicalSpace Set

namespace Reg.D5.S1.Dynamics.Shadowing.FiniteObservationSofic

noncomputable section
universe u v

/-- Observe the chosen finite graph's vertex count. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete source telescope and the exact entire graph-language
equality. Vary only the count used for the graph's finite vertex carrier. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [TopologicalSpace X]
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (f : X → X) (a : X → A) (_ha : Continuous a) (_hs : HasShadowing f),
    ∃ (n : ℕ) (edge : Fin (R.readout () () n) → Fin (R.readout () () n) → Prop)
      (label : Fin (R.readout () () n) → A),
      Set.range (completeItinerary f a) = graphLanguage edge label

/-- A one-point source has a nonempty complete-history language. No graph
on Fin 0 can present it. This also checks the included time-zero coordinate. -/
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let X := ULift.{u} Unit
  let A := ULift.{v} Unit
  let f : X → X := id
  let a : X → A := fun _ => ⟨()⟩
  have hs : HasShadowing f := by
    intro C hC
    refine ⟨C, hC, fun seq _ => ⟨seq 0, fun n => ?_⟩⟩
    obtain ⟨U, hx⟩ := hC.exists_mem (seq n)
    exact ⟨U.1, U.2, (Subsingleton.elim (f^[n] (seq 0)) (seq n)) ▸ hx, hx⟩
  obtain ⟨n, edge, label, heq⟩ := h f a continuous_const hs
  have hm : completeItinerary f a (⟨()⟩ : X) ∈ graphLanguage edge label := by
    rw [← heq]
    exact ⟨⟨()⟩, rfl⟩
  obtain ⟨path, _, _⟩ := hm
  exact Fin.elim0 (path 0)

def registration : Registration arena.{u,v}
    (type_of% (@_root_.D5.S1.Dynamics.Shadowing.finite_observation_isSofic.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Dynamics.Shadowing.finite_observation_isSofic.{u,v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

/-- The mathematical realization, variation, sensitivity, and dependence are
supplied. Source-selection admission remains explicitly unfilled: its readout
lives under the IsSofic existential carrier rather than a literal theorem term.
No validated source binding is claimed by this source alone. -/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Shadowing.finite_observation_isSofic.{u,v})
    (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S1.Dynamics.Shadowing.finite_observation_isSofic
      "Reg.D5.S1.Dynamics.Shadowing.FiniteObservationSofic/arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.FiniteObservationSofic.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v}⟩, objectArena := .source ⟨arena.{u,v}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v} ⟨registration.{u,v}⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{name := `Elab.async, value := .bool true},
    {name := `internal.cmdlineSnapshots, value := .bool true},
    {name := `linter.mathlibStandardSet, value := .bool true},
    {name := `maxSynthPendingDepth, value := .nat 3},
    {name := `pp.unicode.fun, value := .bool true},
    {name := `relaxedAutoImplicit, value := .bool false}] }

#print axioms registration
#print axioms registration_1

end
end Reg.D5.S1.Dynamics.Shadowing.FiniteObservationSofic
