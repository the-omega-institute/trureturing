/- GID: D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCoherenceRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite future separation asserted as a necessary condition for actual SCC coherence. -/

import D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
import D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation (singletonRival separates)
open D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open Quiver

/-- The full product of the original graphs, retaining every jointly permitted color
and every original all-containment edge, including parallel source-label pairs. -/
@[instance_reducible] noncomputable def pairedGraph (b : ℝ) (q : ℕ) (R : ℝ) :
    Quiver (Vertex q R × Vertex q R) where
  Hom a z := {lm : Label × Label // edge a.1 lm.1 z.1 ∧ edge a.2 lm.2 z.2 ∧
    ∃ c : Fin 6, permits b a.1 c ∧ permits b a.2 c}

/-- Reachability after an initial equal-label history and its first unequal-label edge. -/
def divergenceReachable (b : ℝ) (q : ℕ) (R : ℝ) (r : Vertex q R × Vertex q R) : Prop :=
  letI := pairedGraph b q R
  ∃ a u v : Vertex q R × Vertex q R,
    a.1.val.1 = false ∧ a.2.val.1 = false ∧
    ∃ stem : Path a u, (∀ lm ∈ output (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val) stem, lm.1 = lm.2) ∧
    ∃ e : u ⟶ v, e.val.1 ≠ e.val.2 ∧ Nonempty (Path v r)

/-- An actual rival belongs to a cyclic, divergence-reachable SCC whose two source
projections and ordered source-pair returns all satisfy the original synchronization law. -/
def actualCoherentRival (b : ℝ) (q : ℕ) (R : ℝ) (eta : LegalDigits) : Prop :=
  letI := pairedGraph b q R
  ∃ r : Vertex q R × Vertex q R,
    r.2.val.1 = actualGuard false eta 1 ∧
    piece r.2 = {kappa (bitShift eta 3)} ∧ divergenceReachable b q R r ∧
    Cyclic (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val.1) (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val.2) (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val) (StronglyConnectedComponent.mk r)

/-- The claimed necessity of unconditional finite future separation for actual return coherence. -/
def claim : Prop :=
  ∀ (b : ℝ) (q : ℕ) (R : ℝ), 0 < b → b < lambda → endpointParameters b q R →
    ∀ eta : LegalDigits, singletonRival q R eta → actualCoherentRival b q R eta →
      separates b eta

end D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation
