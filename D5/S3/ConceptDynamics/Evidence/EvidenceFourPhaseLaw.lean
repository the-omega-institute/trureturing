/- GID: D5/S3/ConceptDynamics/Evidence/EvidenceFourPhaseLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Evidence/EvidenceFourPhaseLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite evidence fiber with a decidable predicate lies in exactly one of the impossible, stably true, stably false, and undecided phases. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Finset.Basic

/- Library-search audit trail (2026-08-21):
   * `rg -n 'KnowTrue|KnowFalse|Insufficient|Impossible|Evidence|epistemic|phase|四分' D5/S3/ConceptDynamics D5 -g '*.lean'`
     found evidence-related declarations but no exact four-phase classifier.
   * `rg -n 'Decidable.*ExactlyOne|ExactlyOne|Pairwise.*Disjoint|one.*of.*four|Fin 4' .lake/packages/mathlib/Mathlib -g '*.lean'`
     found generic uniqueness and finite-enumeration infrastructure, but no theorem
     stating this partition of a finite fiber by a decidable predicate.
   * Exact pinned-Mathlib hits `Finset.mem_filter` and
     `Finset.nonempty_iff_ne_empty` supply the finite decision and nonemptiness
     bridges used below; no source-shaped result is reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Evidence.EvidenceFourPhaseLaw

/-- The four epistemic phases of a finite evidence fiber. -/
inductive EvidencePhase where
  | impossible
  | stableTrue
  | stableFalse
  | undecided
  deriving DecidableEq

/-- The source semantics of each phase for a finite fiber and proposition. -/
def PhaseHolds {X : Type*} (fiber : Finset X) (P : X -> Prop) :
    EvidencePhase -> Prop
  | .impossible => fiber = ∅
  | .stableTrue => fiber.Nonempty ∧ ∀ x ∈ fiber, P x
  | .stableFalse => fiber.Nonempty ∧ ∀ x ∈ fiber, ¬ P x
  | .undecided =>
      ∃ x ∈ fiber, ∃ y ∈ fiber, P x ∧ ¬ P y

/-- A finite fiber with decidable membership and a decidable proposition lies
in exactly one of the four source phases. -/
theorem finite_classical_four_phase_law
    {X : Type*} [DecidableEq X] (fiber : Finset X)
    (P : X -> Prop) [DecidablePred P] :
    ∃! phase, PhaseHolds fiber P phase := by
  by_cases hEmpty : fiber = ∅
  · refine ⟨.impossible, hEmpty, ?_⟩
    intro phase hPhase
    cases phase with
    | impossible => rfl
    | stableTrue =>
        exact (hPhase.1.ne_empty hEmpty).elim
    | stableFalse =>
        exact (hPhase.1.ne_empty hEmpty).elim
    | undecided =>
        rcases hPhase with ⟨x, hx, _⟩
        rw [hEmpty] at hx
        exact (Finset.notMem_empty x hx).elim
  have hNonempty : fiber.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  let trueFiber := fiber.filter P
  let falseFiber := fiber.filter fun x => ¬ P x
  by_cases hTrue : trueFiber.Nonempty
  · rcases hTrue with ⟨x, hxTrue⟩
    have hx : x ∈ fiber := (Finset.mem_filter.mp hxTrue).1
    have hPx : P x := (Finset.mem_filter.mp hxTrue).2
    by_cases hFalse : falseFiber.Nonempty
    · rcases hFalse with ⟨y, hyFalse⟩
      have hy : y ∈ fiber := (Finset.mem_filter.mp hyFalse).1
      have hPy : ¬ P y := (Finset.mem_filter.mp hyFalse).2
      refine ⟨.undecided, ⟨x, hx, y, hy, hPx, hPy⟩, ?_⟩
      intro phase hPhase
      cases phase with
      | impossible =>
          rw [hPhase] at hx
          exact (Finset.notMem_empty x hx).elim
      | stableTrue =>
          exact (hPy (hPhase.2 y hy)).elim
      | stableFalse =>
          exact (hPhase.2 x hx hPx).elim
      | undecided => rfl
    · have hAll : ∀ y ∈ fiber, P y := by
        intro y hy
        by_contra hPy
        apply hFalse
        exact ⟨y, Finset.mem_filter.mpr ⟨hy, hPy⟩⟩
      refine ⟨.stableTrue, ⟨hNonempty, hAll⟩, ?_⟩
      intro phase hPhase
      cases phase with
      | impossible =>
          exact (hEmpty hPhase).elim
      | stableTrue => rfl
      | stableFalse =>
          exact (hPhase.2 x hx hPx).elim
      | undecided =>
          rcases hPhase with ⟨_, _, y, hy, _, hPy⟩
          exact (hPy (hAll y hy)).elim
  · have hNone : ∀ x ∈ fiber, ¬ P x := by
      intro x hx hPx
      apply hTrue
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hPx⟩⟩
    refine ⟨.stableFalse, ⟨hNonempty, hNone⟩, ?_⟩
    intro phase hPhase
    cases phase with
    | impossible =>
        exact (hEmpty hPhase).elim
    | stableTrue =>
        rcases hNonempty with ⟨x, hx⟩
        exact (hNone x hx (hPhase.2 x hx)).elim
    | stableFalse => rfl
    | undecided =>
        rcases hPhase with ⟨x, hx, _, _, hPx, _⟩
        exact (hNone x hx hPx).elim

/-- An empty Boolean fiber realizes the impossible phase. -/
example : PhaseHolds (∅ : Finset Bool) (fun value => value = true)
    .impossible := by
  simp [PhaseHolds]

/-- A singleton true fiber realizes the stably-true phase. -/
example : PhaseHolds ({true} : Finset Bool) (fun value => value = true)
    .stableTrue := by
  simp [PhaseHolds]

/-- A singleton false fiber realizes the stably-false phase. -/
example : PhaseHolds ({false} : Finset Bool) (fun value => value = true)
    .stableFalse := by
  simp [PhaseHolds]

/-- A two-valued fiber realizes the undecided phase. -/
example : PhaseHolds ({false, true} : Finset Bool) (fun value => value = true)
    .undecided := by
  simp [PhaseHolds]

#print axioms finite_classical_four_phase_law

end D5.S3.ConceptDynamics.Evidence.EvidenceFourPhaseLaw
