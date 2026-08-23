/- GID: D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An interior projective probability fiber has canonical relative-phase coordinates. -/

import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.Fin.Tuple.Reflection

/- Library-search audit trail (2026-08-23):
   * Repository searches found no projective basis-probability fiber equivalence or equivalent
     family primitive.
   * Pinned Mathlib provides the exact unit phase group `Circle`, including `Circle.coe_mul`,
     `Circle.coe_div`, and `Circle.normSq_coe`.
   * Pinned Mathlib's exact `Quotient.lift` and `Quotient.sound` construct projective states from
     polar representatives modulo common phase. No exact fiber-torus theorem was found. -/

noncomputable section

namespace D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A strictly interior probability vector on `n + 1` basis outcomes. -/
structure InteriorProbability (n : Nat) where
  weight : Fin (n + 1) → ℝ
  positive : ∀ i, 0 < weight i
  total : ∑ i, weight i = 1

/-- One unit phase for every nonzero polar coordinate. -/
abbrev PhaseConfiguration (n : Nat) := Fin (n + 1) → Circle

/-- Two polar representatives describe the same projective state exactly when their probability
coordinates agree and all phases differ by one common unit phase. -/
def commonPhaseRelation (n : Nat)
    (first second : InteriorProbability n × PhaseConfiguration n) : Prop :=
  first.1 = second.1 ∧ ∃ global : Circle, ∀ i, second.2 i = global * first.2 i

private theorem commonPhaseRelation_equivalence (n : Nat) :
    Equivalence (commonPhaseRelation n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro representative
    exact ⟨rfl, 1, by simp⟩
  · intro first second h
    rcases h with ⟨h_probability, global, h_phase⟩
    refine ⟨h_probability.symm, global⁻¹, ?_⟩
    intro i
    rw [h_phase i]
    simp
  · intro first second third h_first h_second
    rcases h_first with ⟨h_probability_first, global_first, h_phase_first⟩
    rcases h_second with ⟨h_probability_second, global_second, h_phase_second⟩
    refine ⟨h_probability_first.trans h_probability_second,
      global_second * global_first, ?_⟩
    intro i
    rw [h_phase_second i, h_phase_first i, mul_assoc]

/-- The interior projective pure-state chart constructed from probabilities and phases modulo the
global phase action. -/
def interiorProjectiveSetoid (n : Nat) :
    Setoid (InteriorProbability n × PhaseConfiguration n) :=
  ⟨commonPhaseRelation n, commonPhaseRelation_equivalence n⟩

/-- Interior projective pure states in a fixed orthonormal basis. -/
def InteriorProjectiveState (n : Nat) :=
  Quotient (interiorProjectiveSetoid n)

/-- The basis-probability map; it forgets all relative phases. -/
def basisProbabilityMap (n : Nat) : InteriorProjectiveState n → InteriorProbability n :=
  Quotient.lift Prod.fst (by
    intro first second h
    exact h.1)

/-- The fiber over one strictly positive basis-probability vector. -/
def BasisProbabilityFiber (n : Nat) (probability : InteriorProbability n) :=
  {state : InteriorProjectiveState n // basisProbabilityMap n state = probability}

/-- The `n` relative phases obtained by dividing each non-reference phase by phase zero. -/
def relativePhaseCoordinates (n : Nat) : InteriorProjectiveState n → (Fin n → Circle) :=
  Quotient.lift
    (fun representative i => representative.2 i.succ / representative.2 0)
    (by
      intro first second h
      rcases h with ⟨_, global, h_phase⟩
      funext i
      rw [h_phase i.succ, h_phase 0]
      exact (mul_div_mul_left_eq_div (first.2 i.succ) (first.2 0) global).symm)

/-- The canonical relative-phase map restricted to a single probability fiber. -/
def relativePhaseCoordinatesOnFiber (n : Nat) (probability : InteriorProbability n) :
    BasisProbabilityFiber n probability → (Fin n → Circle) :=
  fun state => relativePhaseCoordinates n state.1

/-- Gauge-fixed phases with reference phase equal to one. -/
def gaugeFixedPhases (n : Nat) (relative : Fin n → Circle) : PhaseConfiguration n :=
  Fin.cases 1 relative

/-- The projective state reconstructed from one probability vector and all relative phases. -/
def stateFromProbabilityAndRelativePhases (n : Nat) (probability : InteriorProbability n)
    (relative : Fin n → Circle) : InteriorProjectiveState n :=
  Quotient.mk (interiorProjectiveSetoid n) (probability, gaugeFixedPhases n relative)

@[simp]
theorem basisProbabilityMap_stateFromProbabilityAndRelativePhases
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n → Circle) :
    basisProbabilityMap n (stateFromProbabilityAndRelativePhases n probability relative) =
      probability := by
  rfl

@[simp]
theorem relativePhaseCoordinates_stateFromProbabilityAndRelativePhases
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n → Circle) :
    relativePhaseCoordinates n
        (stateFromProbabilityAndRelativePhases n probability relative) = relative := by
  funext i
  simp [relativePhaseCoordinates, stateFromProbabilityAndRelativePhases, gaugeFixedPhases]

private theorem reconstruct_from_probability_and_relative_phases
    (n : Nat) (state : InteriorProjectiveState n) :
    stateFromProbabilityAndRelativePhases n (basisProbabilityMap n state)
        (relativePhaseCoordinates n state) = state := by
  induction state using Quotient.inductionOn with
  | _ representative =>
      apply Quotient.sound
      refine ⟨rfl, representative.2 0, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [gaugeFixedPhases]
      · simp [relativePhaseCoordinates, gaugeFixedPhases]

/-- For every strictly positive probability vector, the named canonical relative-phase map from
its projective basis-probability fiber to the `n`-torus is bijective. -/
theorem interior_probability_fiber_relative_phase_coordinates_bijective
    (n : Nat) (probability : InteriorProbability n) :
    Function.Bijective (relativePhaseCoordinatesOnFiber n probability) := by
  constructor
  · intro first second h_relative
    apply Subtype.ext
    calc
      first.1 = stateFromProbabilityAndRelativePhases n
          (basisProbabilityMap n first.1) (relativePhaseCoordinates n first.1) :=
        (reconstruct_from_probability_and_relative_phases n first.1).symm
      _ = stateFromProbabilityAndRelativePhases n probability
          (relativePhaseCoordinates n first.1) := by rw [first.2]
      _ = stateFromProbabilityAndRelativePhases n probability
          (relativePhaseCoordinates n second.1) := by
        rw [show relativePhaseCoordinates n first.1 = relativePhaseCoordinates n second.1 from
          h_relative]
      _ = stateFromProbabilityAndRelativePhases n
          (basisProbabilityMap n second.1) (relativePhaseCoordinates n second.1) := by
        rw [second.2]
      _ = second.1 := reconstruct_from_probability_and_relative_phases n second.1
  · intro relative
    refine ⟨⟨stateFromProbabilityAndRelativePhases n probability relative, rfl⟩, ?_⟩
    exact relativePhaseCoordinates_stateFromProbabilityAndRelativePhases n probability relative

example : InteriorProbability 0 where
  weight := fun _ => 1
  positive := by simp
  total := by simp

#print axioms interior_probability_fiber_relative_phase_coordinates_bijective

end D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber
