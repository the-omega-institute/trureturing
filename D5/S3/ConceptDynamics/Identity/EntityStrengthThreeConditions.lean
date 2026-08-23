/- GID: D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Process stability, target fidelity, and nontrivial resolution are independent. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'three_conditions_are_independent' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested search for `Refines|invariant.*process|stable.*under` found the
     canonical factorization relation `ConceptJoinUniversal.Refines`, but no theorem
     combining process invariance, target factorization, and nontrivial resolution.
   * The three existing `Identity` modules concern concept kernels, branching memory,
     and noninjective layers; their digests and declarations do not cover this claim.
   * Pinned Mathlib searches found `Function.FactorsThrough` and Boolean discrimination,
     but no declaration packaging the three countermodels. The proof below reuses
     `Refines` and otherwise uses products, functions, sets, and `Bool.false_ne_true`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.EntityStrengthThreeConditions

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A concept is process-stable when every designated process preserves its readout. -/
def ProcessStable {X C : Type*} (processes : Set (X -> X))
    (concept : Concept X C) : Prop :=
  ∀ p ∈ processes, ∀ x, concept (p x) = concept x

/-- A concept is faithful to a target when the target can be decoded from the concept. -/
def TargetFaithful {X C T : Type*} (target : Concept X T)
    (concept : Concept X C) : Prop :=
  Refines target concept

/-- A concept has nontrivial resolution when it distinguishes at least two states. -/
def NontrivialResolution {X C : Type*} (concept : Concept X C) : Prop :=
  exists x y, concept x ≠ concept y

/-- Processes on a product that may change the second coordinate but preserve the first. -/
def secondCoordinateProcesses : Set ((Bool × Bool) -> Bool × Bool) :=
  {process | forall x, (process x).1 = x.1}

/-- Each entity-strength condition is independent of the other two: there are explicit
stable faithful trivial, stable nontrivial unfaithful, and faithful nontrivial unstable
concepts. -/
theorem three_conditions_are_independent :
    (exists (concept : Concept Bool Unit) (target : Concept Bool Unit)
        (processes : Set (Bool -> Bool)),
      ProcessStable processes concept ∧ TargetFaithful target concept ∧
        Not (NontrivialResolution concept)) ∧
    (exists (concept : Concept (Bool × Bool) Bool)
        (target : Concept (Bool × Bool) Bool)
        (processes : Set ((Bool × Bool) -> Bool × Bool)),
      ProcessStable processes concept ∧ NontrivialResolution concept ∧
        Not (TargetFaithful target concept)) ∧
    (exists (concept : Concept Bool Bool) (target : Concept Bool Bool)
        (processes : Set (Bool -> Bool)),
      TargetFaithful target concept ∧ NontrivialResolution concept ∧
        Not (ProcessStable processes concept)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => (), fun _ => (), Set.univ, ?_, ?_, ?_⟩
    · intro process processAllowed x
      rfl
    · exact ⟨id, rfl⟩
    · rintro ⟨x, y, distinguishes⟩
      exact distinguishes rfl
  · refine ⟨Prod.fst, Prod.snd, secondCoordinateProcesses, ?_, ?_, ?_⟩
    · intro process preservesFirst x
      exact preservesFirst x
    · exact ⟨(false, false), (true, false), Bool.false_ne_true⟩
    · rintro ⟨factor, factorization⟩
      have atFalse := congrFun factorization (false, false)
      have atTrue := congrFun factorization (false, true)
      change false = factor false at atFalse
      change true = factor false at atTrue
      exact Bool.false_ne_true (atFalse.trans atTrue.symm)
  · refine ⟨id, id, {fun b : Bool => !b}, ?_, ?_, ?_⟩
    · exact ⟨id, rfl⟩
    · exact ⟨false, true, Bool.false_ne_true⟩
    · intro stable
      have changed := stable (fun b : Bool => !b) (by rfl) false
      change true = false at changed
      exact Bool.false_ne_true changed.symm

/-- The three conditions are jointly satisfiable by reading the first coordinate while
admitting exactly processes that preserve it. -/
theorem three_conditions_jointly_realizable :
    exists (concept : Concept (Bool × Bool) Bool)
      (target : Concept (Bool × Bool) Bool)
      (processes : Set ((Bool × Bool) -> Bool × Bool)),
      ProcessStable processes concept ∧ TargetFaithful target concept ∧
        NontrivialResolution concept := by
  refine ⟨Prod.fst, Prod.fst, secondCoordinateProcesses, ?_, ?_, ?_⟩
  · intro process preservesFirst x
    exact preservesFirst x
  · exact ⟨id, rfl⟩
  · exact ⟨(false, false), (true, false), Bool.false_ne_true⟩

example :
    ProcessStable secondCoordinateProcesses
        (Prod.fst : Concept (Bool × Bool) Bool) ∧
      TargetFaithful (Prod.fst : Concept (Bool × Bool) Bool) Prod.fst ∧
      NontrivialResolution (Prod.fst : Concept (Bool × Bool) Bool) := by
  refine ⟨?_, ⟨id, rfl⟩, (false, false), (true, false), Bool.false_ne_true⟩
  intro process preservesFirst x
  exact preservesFirst x

#print axioms three_conditions_are_independent

end D5.S3.ConceptDynamics.Identity.EntityStrengthThreeConditions
