/- GID: D5/S0/Certificates/SkeletonChannelRetraction
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonChannelRetraction
   mirror-E: none(waiver:sample-preserving-output-retraction)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   digest: Channelwise output retractions preserve fixed observations, partial run failure, and canonical state-cost upper bounds without deleting transitions or identifying states. -/

import D5.S0.Automata.BinaryZeckendorfBlockSkeleton
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/- The existing Skeleton, BlockCode, SignatureFiber and CanonicalState own the
   semantics and cost. This is a completeness reduction for finite observation
   problems, not a claim that every original candidate already has the reduced
   output range. All return targets and all undefined transitions are retained.
   Logical review and separate finite checks were performed; Lean was not run. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonChannelRetraction

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton

variable {Output State : Type*}

/-- Postcompose the two terminal channels; retain the complete transition data. -/
def mapChannels (K : Skeleton Output State) (f g : Output → Output) :
    Skeleton Output State where
  start := K.start
  zeroStep := K.zeroStep
  oneSignature := fun q => (K.oneSignature q).map (fun p => (g p.1, p.2))
  zeroOutput := fun q => f (K.zeroOutput q)

/-- Select the postcomposition associated with the original terminal channel. -/
def channelMap (f g : Output → Output) : TerminalChannel → Output → Output
  | .recurrent => f
  | .transient => g

/-- Exact evaluation commutes with channelwise postcomposition, including none. -/
theorem evalFrom_mapChannels (K : Skeleton Output State) (f g : Output → Output)
    (q : State) (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    (mapChannels K f g).evalFrom q blocks terminal =
      (K.evalFrom q blocks terminal).map (channelMap f g terminal) := by
  induction blocks generalizing q with
  | nil =>
      cases terminal with
      | recurrent => rfl
      | transient =>
          cases hs : K.oneSignature q <;>
            simp [Skeleton.evalFrom, mapChannels, channelMap, hs]
  | cons block blocks ih =>
      cases block with
      | zero =>
          cases hs : K.zeroStep q <;>
            simp [Skeleton.evalFrom, mapChannels, hs, ih]
      | oneZero =>
          cases hs : K.oneSignature q with
          | none => simp [Skeleton.evalFrom, mapChannels, hs]
          | some p =>
              rcases p with ⟨d, next⟩
              cases hn : next <;>
                simp [Skeleton.evalFrom, mapChannels, hs, hn, ih]

/-- Start-state version for the existing block-code input representation. -/
theorem eval_mapChannels (K : Skeleton Output State) (f g : Output → Output)
    (code : BlockCode) :
    (mapChannels K f g).eval code =
      (K.eval code).map (channelMap f g code.terminal) :=
  evalFrom_mapChannels K f g K.start code.blocks code.terminal

/-- Every old used signature maps to a used signature with the same return. -/
def signatureMap (K : Skeleton Output State) (f g : Output → Output)
    (p : SignatureFiber K) : SignatureFiber (mapChannels K f g) :=
  ⟨(g p.1.1, p.1.2), by
    obtain ⟨q, hq⟩ := p.2
    refine ⟨q, ?_⟩
    change (K.oneSignature q).map (fun x => (g x.1, x.2)) = _
    rw [hq]
    rfl⟩

/-- Output retraction creates no signature outside the image of old ones. -/
theorem signatureMap_surjective (K : Skeleton Output State) (f g : Output → Output) :
    Function.Surjective (signatureMap K f g) := by
  intro p
  obtain ⟨q, hq⟩ := p.2
  change (K.oneSignature q).map (fun x => (g x.1, x.2)) = some p.1 at hq
  obtain ⟨old, ho, hp⟩ := Option.map_eq_some_iff.mp hq
  refine ⟨⟨old, ⟨q, ho⟩⟩, ?_⟩
  apply Subtype.ext
  exact hp

/-- Canonical state cost cannot increase under either terminal retraction. -/
theorem canonical_state_card_mapChannels_le [Fintype Output] [Fintype State]
    (K : Skeleton Output State) (f g : Output → Output) :
    Fintype.card (CanonicalState (mapChannels K f g)) ≤
      Fintype.card (CanonicalState K) := by
  rw [canonical_state_card_eq, canonical_state_card_eq]
  apply Nat.add_le_add_left
  exact Fintype.card_le_of_surjective (signatureMap K f g)
    (signatureMap_surjective K f g)

/-- Fixed observed labels survive even when unobserved outputs change. -/
theorem fixed_observation_preserved (K : Skeleton Output State) (f g : Output → Output)
    (code : BlockCode) (d : Output)
    (fits : K.eval code = some d) (fixed : channelMap f g code.terminal d = d) :
    (mapChannels K f g).eval code = some d := by
  rw [eval_mapChannels, fits]
  simpa only [Option.map_some, fixed]

/-- In radix four, recurrent output two may be retracted to zero. -/
def recurrentRetract (d : Fin 4) : Fin 4 := if d = 2 then 0 else d

/-- In radix four, transient output zero may be retracted to one. -/
def transientRetract (d : Fin 4) : Fin 4 := if d = 0 then 1 else d

/-- The recurrent retraction has precisely the intended forbidden-value exclusion. -/
theorem recurrentRetract_ne_two (d : Fin 4) : recurrentRetract d ≠ 2 := by
  fin_cases d <;> decide

/-- The transient retraction excludes zero without altering any other label. -/
theorem transientRetract_ne_zero (d : Fin 4) : transientRetract d ≠ 0 := by
  fin_cases d <;> decide

/-- Finite-state candidates with the reduced terminal alphabets. -/
def NormalRange (K : Skeleton (Fin 4) State) : Prop :=
  (∀ q, K.zeroOutput q ≠ 2) ∧
  ∀ q d next, K.oneSignature q = some (d, next) → d ≠ 0

/-- The explicit retraction constructs that range for every partial skeleton. -/
theorem retracted_normalRange (K : Skeleton (Fin 4) State) :
    NormalRange (mapChannels K recurrentRetract transientRetract) := by
  constructor
  · intro q
    exact recurrentRetract_ne_two _
  · intro q d next h
    change (K.oneSignature q).map (fun p => (transientRetract p.1, p.2)) =
      some (d, next) at h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp h
    have hd : transientRetract p.1 = d := congrArg Prod.fst hp
    rw [← hd]
    exact transientRetract_ne_zero _

/-- Reduced-output search is equisatisfiable at the same canonical budget.
Only the given observations are assumed to avoid the two forbidden labels;
the unknown original machine's unobserved outputs are unrestricted. -/
theorem normalized_sample_feasibility_iff [Fintype State] {Index : Type*}
    (codes : Index → BlockCode) (labels : Index → Fin 4) (budget : Nat)
    (allowedR : ∀ i, (codes i).terminal = .recurrent → labels i ≠ 2)
    (allowedT : ∀ i, (codes i).terminal = .transient → labels i ≠ 0) :
    (∃ K : Skeleton (Fin 4) State,
      (∀ i, K.eval (codes i) = some (labels i)) ∧
      K.zeroStep K.start = some K.start ∧ K.zeroOutput K.start = 0 ∧
      Fintype.card (CanonicalState K) ≤ budget) ↔
    (∃ K : Skeleton (Fin 4) State,
      (∀ i, K.eval (codes i) = some (labels i)) ∧
      K.zeroStep K.start = some K.start ∧ K.zeroOutput K.start = 0 ∧
      Fintype.card (CanonicalState K) ≤ budget ∧ NormalRange K) := by
  constructor
  · rintro ⟨K, fits, loop, zero, cost⟩
    refine ⟨mapChannels K recurrentRetract transientRetract, ?_, loop, ?_,
      (canonical_state_card_mapChannels_le K _ _).trans cost, retracted_normalRange K⟩
    · intro i
      apply fixed_observation_preserved K _ _ (codes i) (labels i) (fits i)
      cases ht : (codes i).terminal with
      | recurrent => simp [channelMap, ht, recurrentRetract, allowedR i ht]
      | transient => simp [channelMap, ht, transientRetract, allowedT i ht]
    · change recurrentRetract (K.zeroOutput K.start) = 0
      rw [zero]
      rfl
  · rintro ⟨K, fits, loop, zero, cost, _⟩
    exact ⟨K, fits, loop, zero, cost⟩

#print axioms evalFrom_mapChannels
#print axioms canonical_state_card_mapChannels_le
#print axioms normalized_sample_feasibility_iff

end D5.S0.Certificates.SkeletonChannelRetraction
