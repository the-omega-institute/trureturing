/- GID: D5/S3/Observer/ProbabilisticClosure/ZeroReplayOpportunities
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ZeroReplayOpportunities
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every zero replay reaches each opportunity within a uniform finite query bound. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import Mathlib.Data.Bool.Count

/-! Chronological opportunity counts and native finite first-failure records. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities

open AdaptiveMarkerStoppingTails

/-- The side queried at zero-based time n in the original policy's zero replay. -/
def replaySide {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (n : ℕ) : Side :=
  policy.choose seed (zeroReplay policy seed n) (List.replicate n false)

/-- An opportunity has a zero inner endpoint before the query, on that very arm. -/
def opportunity {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (root : Bool) (n : ℕ) : Prop :=
  alternatingBit root (sideCount (zeroReplay policy seed n) (replaySide policy seed n)) = false

instance {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (root : Bool) (n : ℕ) : Decidable (opportunity policy seed root n) :=
  inferInstanceAs (Decidable (_ = false))

/-- Counts opportunities chronologically among the first n actual replay queries. -/
def opportunityCount {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (root : Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => opportunityCount policy seed root n +
      if opportunity policy seed root n then 1 else 0

private theorem opportunity_count_balance {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (n : ℕ) :
    opportunityCount policy seed root n =
      if root then
        sideCount (zeroReplay policy seed n) false / 2 +
          sideCount (zeroReplay policy seed n) true / 2
      else
        (sideCount (zeroReplay policy seed n) false + 1) / 2 +
          (sideCount (zeroReplay policy seed n) true + 1) / 2 := by
  induction n with
  | zero => cases root <;> simp [opportunityCount, zeroReplay, sideCount]
  | succ n ih =>
      rw [opportunityCount, ih]
      have hf := Nat.mod_two_eq_zero_or_one (sideCount (zeroReplay policy seed n) false)
      have ht := Nat.mod_two_eq_zero_or_one (sideCount (zeroReplay policy seed n) true)
      have hstep : zeroReplay policy seed (n + 1) =
          replaySide policy seed n :: zeroReplay policy seed n := rfl
      rw [hstep]
      dsimp [sideCount] at hf ht
      cases hs : replaySide policy seed n <;> cases root <;>
        rcases hf with hf | hf <;> rcases ht with ht | ht <;>
        simp [opportunity, alternatingBit, hs,
          sideCount, hf, ht] <;> omega

private theorem opportunity_count_bound {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (r : ℕ) :
    r < opportunityCount policy seed root (2 * r + 3) := by
  have hc := List.count_false_add_count_true (zeroReplay policy seed (2 * r + 3))
  rw [zero_replay_length] at hc
  rw [opportunity_count_balance]
  change sideCount _ false + sideCount _ true = 2 * r + 3 at hc
  cases root <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem enough_opportunities {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (r : ℕ) :
    ∃ n, r < opportunityCount policy seed root n :=
  ⟨2 * r + 3, opportunity_count_bound policy seed root r⟩

/-- One-based query number of the (r+1)-st opportunity. -/
def opportunityQuery {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (root : Bool) (r : ℕ) : ℕ :=
  Nat.find (enough_opportunities policy seed root r)

private theorem opportunity_query_spec {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (r : ℕ) :
    ∃ n, opportunityQuery policy seed root r = n + 1 ∧
      n + 1 ≤ 2 * r + 3 ∧ opportunityCount policy seed root n = r ∧
      opportunity policy seed root n := by
  let h := enough_opportunities policy seed root r
  have hs := Nat.find_spec h
  have hn : Nat.find h ≠ 0 := by
    intro he
    simp [he, opportunityCount] at hs
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hp := Nat.find_min h (show n < Nat.find h by omega)
  have hb := opportunity_count_bound policy seed root r
  have hle := Nat.find_min' h hb
  rw [he, opportunityCount] at hs
  refine ⟨n, he, by omega, ?_, ?_⟩
  · split_ifs at hs <;> omega
  · by_contra ho
    simp [ho] at hs
    omega

/-- A source alternating on both arms until a specified zero endpoint fails. -/
def failureSource (root : Bool) (marked : Side) (before : ℕ) : Source :=
  (root, (fun i => if marked = false ∧ before ≤ i then false else alternatingBit root (i + 1)),
    (fun i => if marked = true ∧ before ≤ i then false else alternatingBit root (i + 1)))

private theorem failure_source_arm (root : Bool) (marked side : Side) (before i : ℕ) :
    arm (failureSource root marked before) side i =
      if marked = side ∧ before ≤ i then false else alternatingBit root (i + 1) := by
  cases side <;> rfl

private theorem failure_source_support (root : Bool) (marked : Side) (before : ℕ) :
    noAdjacentOnes (failureSource root marked before) := by
  intro side i
  cases i with
  | zero =>
      change ¬(root = true ∧ arm (failureSource root marked before) side 0 = true)
      rw [failure_source_arm]
      split_ifs <;> simp [alternatingBit]
  | succ i =>
      simp only [endpoint, failure_source_arm]
      split_ifs <;> simp_all [alternating_bit_succ]

private theorem failure_source_prefix (root : Bool) (actions : List Side) (marked : Side) :
    prefixNoMarker (failureSource root marked (sideCount actions marked)) actions := by
  let source := failureSource root marked (sideCount actions marked)
  intro side i hi
  have halt : ∀ j ≤ sideCount actions side,
      endpoint source side j = alternatingBit root j := by
    intro j hj
    cases j with
    | zero => simp [endpoint, source, failureSource, alternatingBit]
    | succ j =>
        rw [endpoint, failure_source_arm]
        split_ifs with h
        · obtain ⟨rfl, h⟩ := h
          omega
        · rfl
  have hx : ∀ j, ¬(endpoint source side j = true ∧
      endpoint source side (j + 1) = true) :=
    failure_source_support root marked (sideCount actions marked) side
  have hz := (no_marker_iff_alternating_prefix root (endpoint source side) rfl hx
    (sideCount actions side)).mpr halt i hi
  apply decide_eq_false
  exact hz

/-- The finite record retains the original seed and the acquired native state. -/
def archive {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (root : Bool) (r : ℕ) : Seed × State :=
  let n := opportunityQuery policy seed root r - 1
  (seed, ⟨replaySide policy seed n :: zeroReplay policy seed n,
    true :: List.replicate n false, true⟩)

/-- Every seed and both roots have a finite, policy-compatible first-failure record. -/
theorem finite_replay_first_failure {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (root : Bool) (r : ℕ) :
    ∃ (n : ℕ) (source : Source),
      opportunityQuery policy seed root r = n + 1 ∧ n + 1 ≤ 2 * r + 3 ∧
      opportunityCount policy seed root n = r ∧ opportunity policy seed root n ∧
      source.1 = root ∧
      noAdjacentOnes source ∧
      (actualRun policy seed source n).stopped = false ∧
      actualRun policy seed source (n + 1) = (archive policy seed root r).2 ∧
      (archive policy seed root r).1 = seed ∧
      (archive policy seed root r).2.actions.length = n + 1 := by
  obtain ⟨n, hn, hb, hc, ho⟩ := opportunity_query_spec policy seed root r
  let actions := zeroReplay policy seed n
  let side := replaySide policy seed n
  let source := failureSource root side (sideCount actions side)
  have hp : prefixNoMarker source actions := failure_source_prefix root actions side
  have ha := (stopped_execution_replay_bridge policy seed source n).2.1.mpr hp
  obtain ⟨hact, hrep, _⟩ := (stopped_execution_replay_bridge policy seed source n).2.2.1 ha
  have hin : endpoint source side (sideCount actions side) = false := by
    have he : endpoint source side (sideCount actions side) =
        alternatingBit root (sideCount actions side) := by
      cases hi : sideCount actions side with
      | zero => simp [endpoint, source, failureSource, alternatingBit]
      | succ i =>
          simp only [endpoint, source, failure_source_arm]
          simp [hi]
    exact he.trans ho
  have hm : markerResponse source side (sideCount actions side) = true := by
    simp [markerResponse, hin, source, failure_source_arm]
  refine ⟨n, source, hn, hb, hc, ho, rfl, failure_source_support root side _, ha, ?_, rfl, ?_⟩
  · simp only [actualRun, ha, Bool.false_eq_true, ↓reduceIte, hact, hrep]
    change State.mk (side :: actions) (markerResponse source side (sideCount actions side) ::
      List.replicate n false) (markerResponse source side (sideCount actions side)) = _
    simp [hm, archive, hn, actions, side]
  · simp [archive, hn, zero_replay_length]

end D5.S3.Observer.ProbabilisticClosure.ZeroReplayOpportunities
