import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.FiniteObservationShadowing
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open TopologicalSpace Set Function

namespace Reg.D5.S1.Dynamics.Shadowing.FiniteObservationShadowing

noncomputable section
universe u

/-- The observed object is the actual finite open control cover, on its full
possibly infinite topological carrier. -/
abbrev signature : Signature where
  Params := TopCat.{u}
  State X := Finset (Opens X)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := Finset (Opens X)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ D => D) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (f : X → X) (_hf : Continuous f)
    (_hfinite : ∀ (m : ℕ) (q : X → Fin m), Continuous q →
      (Set.range (fun x n => q (f^[n] x))).Finite)
    (C : Finset (Opens X)) (_hC : IsOpenCover (fun U : C => U.1)),
    ∃ D : Finset (Opens X),
      IsOpenCover (fun U : R.readout () (TopCat.of X) D => U.1) ∧
      ∀ a : ℕ → X, PseudoOrbit f (R.readout () (TopCat.of X) D) a →
        Shadows f C a (a 0)

/-- Replacing every control cover by the empty family fails on a nonempty
compact discrete carrier, even for its identity dynamics. -/
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let X := ULift.{u} Unit
  let f : X → X := id
  let C : Finset (Opens X) := {⊤}
  have hC : IsOpenCover (fun U : C => U.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    exact Opens.mem_iSup.mpr ⟨⟨⊤, Finset.mem_singleton_self _⟩, Set.mem_univ x⟩
  obtain ⟨D, hD, _⟩ := h f continuous_id
    (fun m q _ => Set.finite_range (fun x n => q (f^[n] x))) C hC
  obtain ⟨U, _⟩ := hD.exists_mem (⟨()⟩ : X)
  exact Finset.notMem_empty U.val U.property

def sourceRegistration : Registration arena.{u}
    (type_of% (@initial_point_tracing_of_finite_observation_names.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@initial_point_tracing_of_finite_observation_names.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let X := TopCat.of (ULift.{u} Unit)
    refine ⟨X, (∅ : Finset (Opens X)), ({⊤} : Finset (Opens X)), ?_⟩
    change (∅ : Finset (Opens X)) ≠ {⊤}
    simp

/-- The typed source-family proof is complete; raw reconstruction of the
existential cover's dependent subtype and PseudoOrbit operand is unfinished.
No source coordinate or escape-origin identity is asserted by this attempt. -/
def attempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@initial_point_tracing_of_finite_observation_names.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.FiniteObservationShadowing.controlCover
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.FiniteObservationShadowing.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ D => D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceRegistration
#print axioms attempt

end
end Reg.D5.S1.Dynamics.Shadowing.FiniteObservationShadowing
