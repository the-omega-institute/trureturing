/- GID: D5/S3/Observer/Separation/RootPulseSharpness
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/RootPulseSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The root-pulse chain attains the finite observation refinement bound exactly. -/

import D5.S3.Observer.Separation.FiniteObservationRefinementBound
import Mathlib.Data.Nat.Find

/- Library-search audit trail (2026-08-20):
   * Repository search found the exact general bound
     `finite_observation_refinement_and_stability_bound`; it is imported and
     applied below. The repository also supplies the exact source notions
     `separationTime`, `stabilizationIndex`, `observationSetoid`, and
     `observationStabilityDepth` used in the public statement.
   * Pinned Mathlib search found exact hits `Nat.find_eq_iff`, `Finset.sup_le`,
     `Finset.le_sup`, `Fintype.card_fin`, and `Fintype.card_bool`; each is
     applied below.
   * Repository and pinned-Mathlib shape searches found no root-pulse-chain
     sharpness theorem or theorem packaging all seven public clauses. -/

noncomputable section

namespace D5.S3.Observer.Separation.RootPulseSharpness

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-- The source chain update, truncated at its root. -/
def rootPulseUpdate {n : Nat} (i : Fin n) : Fin n :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The source readout is true exactly at the root. -/
def rootPulseReadout {n : Nat} (i : Fin n) : Bool :=
  decide (i.val = 0)

/-- The penultimate state of a chain with at least two states. -/
def penultimateState {n : Nat} (hn : 2 ≤ n) : Fin n :=
  ⟨n - 2, by omega⟩

/-- The last state of a nonempty finite chain. -/
def lastState {n : Nat} (hn : 2 ≤ n) : Fin n :=
  ⟨n - 1, by omega⟩

private theorem root_pulse_iterate_val {n : Nat} (k : Nat) (i : Fin n) :
    ((rootPulseUpdate^[k]) i).val = i.val - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change ((rootPulseUpdate^[k]) i).val - 1 = i.val - (k + 1)
      rw [ih]
      omega

private theorem root_pulse_observed_at {n : Nat} (k : Nat) (i : Fin n) :
    observedAt rootPulseUpdate rootPulseReadout k i = decide (i.val ≤ k) := by
  simp [observedAt, rootPulseReadout, root_pulse_iterate_val,
    Nat.sub_eq_zero_iff_le]

private theorem root_pulse_future_word_apply {n : Nat} (m : Nat)
    (i : Fin n) (k : Fin (m + 1)) :
    futureReadoutWord rootPulseUpdate rootPulseReadout m i k =
      decide (i.val ≤ k.val) := by
  simpa [futureReadoutWord, observedAt] using
    root_pulse_observed_at k.val i

private theorem root_pulse_setoid_iff {n : Nat} (m : Nat) (i j : Fin n) :
    observationSetoid rootPulseUpdate rootPulseReadout m i j ↔
      i = j ∨ (m < i.val ∧ m < j.val) := by
  constructor
  · intro hword
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hi : m < i.val := by
          by_contra hnot
          have him : i.val ≤ m := Nat.le_of_not_gt hnot
          have hcoord := congrFun hword
            (show Fin (m + 1) from ⟨i.val, Nat.lt_succ_of_le him⟩)
          simp [root_pulse_future_word_apply] at hcoord
          exact (Nat.not_le_of_lt hlt) hcoord
        exact ⟨hi, by omega⟩
      · have hj : m < j.val := by
          by_contra hnot
          have hjm : j.val ≤ m := Nat.le_of_not_gt hnot
          have hcoord := congrFun hword
            (show Fin (m + 1) from ⟨j.val, Nat.lt_succ_of_le hjm⟩)
          simp [root_pulse_future_word_apply] at hcoord
          exact (Nat.not_le_of_lt hgt) hcoord
        exact ⟨by omega, hj⟩
  · rintro (rfl | ⟨hi, hj⟩)
    · rfl
    · funext k
      have hki : ¬ i.val ≤ k.val := by omega
      have hkj : ¬ j.val ≤ k.val := by omega
      simp [root_pulse_future_word_apply, hki, hkj]

private theorem root_pulse_separation_time_of_lt {n : Nat} (i j : Fin n)
    (hij : i.val < j.val) :
    separationTime rootPulseUpdate rootPulseReadout (i, j) = i.val := by
  classical
  letI : DecidablePred (fun k =>
      observedAt rootPulseUpdate rootPulseReadout k i =
        observedAt rootPulseUpdate rootPulseReadout k j) :=
    fun _ => Classical.propDecidable _
  have hexists : ∃ k,
      observedAt rootPulseUpdate rootPulseReadout k i ≠
        observedAt rootPulseUpdate rootPulseReadout k j := by
    refine ⟨i.val, ?_⟩
    have hnot : ¬ j.val ≤ i.val := Nat.not_le_of_lt hij
    rw [root_pulse_observed_at, root_pulse_observed_at]
    simp [hnot]
  rw [separationTime, dif_pos hexists, Nat.find_eq_iff]
  constructor
  · have hnot : ¬ j.val ≤ i.val := Nat.not_le_of_lt hij
    rw [root_pulse_observed_at, root_pulse_observed_at]
    simp [hnot]
  · intro k hk
    have hki : ¬ i.val ≤ k := by omega
    have hkj : ¬ j.val ≤ k := by omega
    simp [root_pulse_observed_at, hki, hkj]

private theorem root_pulse_separation_time_of_gt {n : Nat} (i j : Fin n)
    (hji : j.val < i.val) :
    separationTime rootPulseUpdate rootPulseReadout (i, j) = j.val := by
  classical
  letI : DecidablePred (fun k =>
      observedAt rootPulseUpdate rootPulseReadout k i =
        observedAt rootPulseUpdate rootPulseReadout k j) :=
    fun _ => Classical.propDecidable _
  have hexists : ∃ k,
      observedAt rootPulseUpdate rootPulseReadout k i ≠
        observedAt rootPulseUpdate rootPulseReadout k j := by
    refine ⟨j.val, ?_⟩
    have hnot : ¬ i.val ≤ j.val := Nat.not_le_of_lt hji
    rw [root_pulse_observed_at, root_pulse_observed_at]
    simp [hnot]
  rw [separationTime, dif_pos hexists, Nat.find_eq_iff]
  constructor
  · have hnot : ¬ i.val ≤ j.val := Nat.not_le_of_lt hji
    rw [root_pulse_observed_at, root_pulse_observed_at]
    simp [hnot]
  · intro k hk
    have hki : ¬ i.val ≤ k := by omega
    have hkj : ¬ j.val ≤ k := by omega
    simp [root_pulse_observed_at, hki, hkj]

private theorem root_pulse_readout_surjective {n : Nat} (hn : 2 ≤ n) :
    Function.Surjective (@rootPulseReadout n) := by
  intro value
  cases value with
  | false =>
      exact ⟨⟨1, by omega⟩, by simp [rootPulseReadout]⟩
  | true =>
      exact ⟨⟨0, by omega⟩, by simp [rootPulseReadout]⟩

private theorem root_pulse_strict_refinement_iff {n : Nat} (hn : 2 ≤ n)
    (m : Nat) :
    observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n) (m + 1) <
        observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n) m ↔
      m < n - 2 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hgeneral := finite_observation_refinement_and_stability_bound
    (@rootPulseUpdate n) (@rootPulseReadout n)
    (root_pulse_readout_surjective hn)
  constructor
  · intro hstrict
    by_contra hnot
    have hm : n - 2 ≤ m := Nat.le_of_not_gt hnot
    have heq : observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n)
        (m + 1) = observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n) m := by
      apply Setoid.ext
      intro i j
      rw [root_pulse_setoid_iff, root_pulse_setoid_iff]
      constructor
      · rintro (hij | ⟨hi, hj⟩)
        · exact Or.inl hij
        · right
          exact ⟨Nat.lt_of_succ_lt hi, Nat.lt_of_succ_lt hj⟩
      · rintro (hij | ⟨hi, hj⟩)
        · exact Or.inl hij
        · left
          apply Fin.ext
          omega
    exact (ne_of_lt hstrict) heq
  · intro hm
    apply lt_of_le_of_ne (hgeneral.1 m)
    intro heq
    let i : Fin n := ⟨m + 1, by omega⟩
    let j : Fin n := ⟨m + 2, by omega⟩
    have hrelated : observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n)
        m i j :=
      (root_pulse_setoid_iff m i j).2 (Or.inr (by simp [i, j]))
    have hrefined :
        observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n)
          (m + 1) i j := by
      rw [heq]
      exact hrelated
    rcases (root_pulse_setoid_iff (m + 1) i j).1 hrefined with hij | hlarge
    · have : i.val ≠ j.val := by simp [i, j]
      exact this (congrArg Fin.val hij)
    · have himpossible := hlarge.1
      simp [i] at himpossible

private theorem root_pulse_stability_depth {n : Nat} (hn : 2 ≤ n) :
    observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) =
      n - 2 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hgeneral := finite_observation_refinement_and_stability_bound
    (@rootPulseUpdate n) (@rootPulseReadout n)
    (root_pulse_readout_surjective hn)
  have hupper : observationStabilityDepth (@rootPulseUpdate n)
      (@rootPulseReadout n) ≤ n - 2 := by
    have hbound := le_trans hgeneral.2.2.2.1 hgeneral.2.2.2.2
    simpa using hbound
  have hnotLower : ¬ observationStabilityDepth (@rootPulseUpdate n)
      (@rootPulseReadout n) < n - 2 := by
    intro hlower
    have hstrict := (root_pulse_strict_refinement_iff hn _).2 hlower
    exact (ne_of_lt hstrict) hgeneral.2.2.1.1.symm
  omega

private theorem root_pulse_stabilization_index {n : Nat} (hn : 2 ≤ n) :
    stabilizationIndex (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 := by
  classical
  apply le_antisymm
  · rw [stabilizationIndex]
    apply Finset.sup_le
    intro pair _
    rcases pair with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      simp [separationTime]
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · rw [root_pulse_separation_time_of_lt i j hlt]
        omega
      · rw [root_pulse_separation_time_of_gt i j hgt]
        omega
  · have hwitness := Finset.le_sup
      (f := separationTime (@rootPulseUpdate n) (@rootPulseReadout n))
      (Finset.mem_univ (penultimateState hn, lastState hn))
    rw [root_pulse_separation_time_of_lt (penultimateState hn) (lastState hn)
      (by simp [penultimateState, lastState]; omega)] at hwitness
    simpa [stabilizationIndex, penultimateState] using hwitness

/-- Every clause of the root-pulse sharpness certificate, including saturation
of the general finite observation bound. -/
theorem root_pulse_sharpness (n : Nat) (hn : 2 ≤ n) :
    (∀ i j : Fin n, i < j →
      separationTime (@rootPulseUpdate n) (@rootPulseReadout n) (i, j) = i.val) ∧
    separationTime (@rootPulseUpdate n) (@rootPulseReadout n)
        (penultimateState hn, lastState hn) = n - 2 ∧
    (∀ m, observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n)
        (m + 1) < observationSetoid (@rootPulseUpdate n) (@rootPulseReadout n) m ↔
          m < n - 2) ∧
    observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 ∧
    stabilizationIndex (@rootPulseUpdate n) (@rootPulseReadout n) = n - 2 ∧
    observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) ≤
      Fintype.card (Fin n) - Fintype.card Bool ∧
    observationStabilityDepth (@rootPulseUpdate n) (@rootPulseReadout n) =
      Fintype.card (Fin n) - Fintype.card Bool := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hgeneral := finite_observation_refinement_and_stability_bound
    (@rootPulseUpdate n) (@rootPulseReadout n)
    (root_pulse_readout_surjective hn)
  have hdepth := root_pulse_stability_depth hn
  refine ⟨?_, ?_, root_pulse_strict_refinement_iff hn, hdepth,
    root_pulse_stabilization_index hn, ?_, ?_⟩
  · intro i j hij
    exact root_pulse_separation_time_of_lt i j hij
  · exact root_pulse_separation_time_of_lt (penultimateState hn) (lastState hn)
      (by simp [penultimateState, lastState]; omega)
  · exact le_trans hgeneral.2.2.2.1 hgeneral.2.2.2.2
  · simpa [Fintype.card_fin, Fintype.card_bool] using hdepth

/-- The chain-size hypothesis is satisfiable in the pinned environment. -/
example : 2 ≤ 2 := by omega

/-- The theorem's state domain has a concrete inhabitant. -/
example : Fin 2 := ⟨0, by omega⟩

/-- The constructed root readout realizes both Boolean observations. -/
example : Function.Surjective (@rootPulseReadout 2) :=
  root_pulse_readout_surjective (by omega)

#print axioms root_pulse_sharpness

end D5.S3.Observer.Separation.RootPulseSharpness
