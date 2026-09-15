/- GID: D5/S3/Factorization/Automata/PrimeCapacityHorizon
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeCapacityHorizon
   mirror-E: none(waiver:all-capacities-all-horizons)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Continuation words determine exactly the clipped remaining-capacity quotient at every finite horizon. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Factorization.Automata.PrimeCapacityHorizon

variable {I : Type*} [DecidableEq I]

/-- The remaining prime-exponent capacities, not an encoding of their names. -/
abbrev Capacity (a : I → Nat) := ∀ i, Fin (a i + 1)

/-- A realizable finite-horizon signature: remaining amounts larger than H
cannot be exhausted by a word of total length at most H. -/
abbrev Profile (a : I → Nat) (H : Nat) := ∀ i, Fin (min (a i) H + 1)

/-- The actual input is a list of register indices. Each occurrence consumes
one unit of that register's remaining multiplicative capacity. -/
def fits (r : I → Nat) (w : List I) : Prop := ∀ i, w.count i ≤ r i

/-- Rejection remains distinguishable, including on the empty continuation. -/
def allowed (a : I → Nat) : Option (Capacity a) → List I → Prop
  | none, _ => False
  | some r, w => fits (fun i => (r i).val) w

/-- This is the observation to be proved complete, not an assumed quotient. -/
def clipState (a : I → Nat) (H : Nat) :
    Option (Capacity a) → Option (Profile a H)
  | none => none
  | some r => some (fun i =>
      ⟨min (r i).val H, by
        have hr := (r i).isLt
        have hx := min_le_left (r i).val H
        have hy := min_le_right (r i).val H
        have he : min (r i).val H ≤ min (a i) H := le_min (by omega) hy
        omega⟩)

/-- Complete observation quotient for every capacity vector and every horizon.
It gives the exact kernel on actual list continuations, surjectivity onto the
stated profile carrier, and its cardinality. A fixed-H quotient need not be
stable under a further input; the theorem does not assert that it is. -/
theorem finite_horizon_state_classification [Fintype I] (a : I → Nat) (H : Nat) :
    Function.Surjective (clipState a H) ∧
    (∀ s t : Option (Capacity a),
      (∀ w : List I, w.length ≤ H → (allowed a s w ↔ allowed a t w)) ↔
        clipState a H s = clipState a H t) ∧
    Fintype.card (Option (Profile a H)) = 1 + ∏ i, (min (a i) H + 1) := by
  have repeated_fits (r : I → Nat) (i : I) (k : Nat) (hk : k ≤ r i) :
      fits r (List.replicate k i) := by
    intro j
    by_cases hij : i = j
    · subst j
      simpa using hk
    · simp [List.count_replicate, hij]
  have finite_word_kernel (r s : I → Nat) :
      (∀ w : List I, w.length ≤ H → (fits r w ↔ fits s w)) ↔
        ∀ i, min (r i) H = min (s i) H := by
    constructor
    · intro he i
      have hleft : min (r i) H ≤ s i := by
        have h := (he (List.replicate (min (r i) H) i)
          (by simp [min_le_right])).mp
            (repeated_fits r i _ (min_le_left _ _))
        simpa using h i
      have hright : min (s i) H ≤ r i := by
        have h := (he (List.replicate (min (s i) H) i)
          (by simp [min_le_right])).mpr
            (repeated_fits s i _ (min_le_left _ _))
        simpa using h i
      exact le_antisymm
        (le_min hleft (min_le_right _ _))
        (le_min hright (min_le_right _ _))
    · intro he w hw
      constructor
      · intro hr i
        have hc : w.count i ≤ H := List.count_le_length.trans hw
        have hm : w.count i ≤ min (r i) H := le_min (hr i) hc
        rw [he i] at hm
        exact hm.trans (min_le_left _ _)
      · intro hs i
        have hc : w.count i ≤ H := List.count_le_length.trans hw
        have hm : w.count i ≤ min (s i) H := le_min (hs i) hc
        rw [← he i] at hm
        exact hm.trans (min_le_left _ _)
  have profile_surjective : Function.Surjective (clipState a H) := by
    intro q
    cases q with
    | none => exact ⟨none, rfl⟩
    | some q =>
        let r : Capacity a := fun i =>
          ⟨(q i).val, lt_of_lt_of_le (q i).isLt
            (Nat.add_le_add_right (min_le_left (a i) H) 1)⟩
        refine ⟨some r, ?_⟩
        apply congrArg some
        funext i
        apply Fin.ext
        change min (q i).val H = (q i).val
        have hq := (q i).isLt
        have hm := min_le_right (a i) H
        exact min_eq_left (by omega)
  refine ⟨profile_surjective, ?_, ?_⟩
  · intro s t
    cases s with
    | none =>
        cases t with
        | none => simp [clipState, allowed]
        | some t =>
            constructor
            · intro h
              have hf := (h [] (by simp)).mpr (by simp [allowed, fits])
              exact hf.elim
            · simp [clipState]
    | some s =>
        cases t with
        | none =>
            constructor
            · intro h
              have hf := (h [] (by simp)).mp (by simp [allowed, fits])
              exact hf.elim
            · simp [clipState]
        | some t =>
            change (∀ w : List I, w.length ≤ H →
                (fits (fun i => (s i).val) w ↔ fits (fun i => (t i).val) w)) ↔ _
            rw [finite_word_kernel]
            constructor
            · intro h
              apply congrArg some
              funext i
              exact Fin.ext (h i)
            · intro h i
              have hv := congrArg (fun q => (q i).val) (Option.some.inj h)
              exact hv
  · simp [Profile, Fintype.card_pi, Nat.add_comm]

#print axioms finite_horizon_state_classification

end D5.S3.Factorization.Automata.PrimeCapacityHorizon
