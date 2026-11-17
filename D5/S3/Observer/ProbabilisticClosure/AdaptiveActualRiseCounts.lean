/- GID: D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chronological acquired rises equal alternating arm counts before the first marker. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod

/-! Actual original-source rise accounting for absorbing adaptive executions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts

open AdaptiveMarkerStoppingTails

/-- Counts chronological queries of original-source 01 edges on one side.
Stopped states contribute nothing, even when the policy would choose that side. -/
def actualRiseCount {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (source : Source) (side : Side) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (fun k =>
    let h := actualRun policy seed source k
    h.stopped = false ∧ policy.choose seed h.actions h.replies = side ∧
      endpoint source side (sideCount h.actions side) = false ∧
      arm source side (sideCount h.actions side) = true) n

/-- Time counts and acquired arm-prefix counts agree, including after absorption. -/
private theorem time_count_eq_prefix_count
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed)
    (source : Source) (side : Side) (n : ℕ) :
    actualRiseCount policy seed source side n =
      Nat.count (fun i => endpoint source side i = false ∧ arm source side i = true)
        (sideCount (actualRun policy seed source n).actions side) := by
  classical
  induction n with
  | zero => simp [actualRiseCount, actualRun, sideCount, Nat.count]
  | succ n ih =>
    change Nat.count _ (n + 1) = _
    rw [Nat.count_succ]
    change actualRiseCount policy seed source side n + _ = _
    rw [ih]
    by_cases hs : (actualRun policy seed source n).stopped = true
    · simp [actualRun, hs]
    · have hf : (actualRun policy seed source n).stopped = false := Bool.eq_false_iff.mpr hs
      by_cases ha : policy.choose seed (actualRun policy seed source n).actions
          (actualRun policy seed source n).replies = side
      · simp [actualRun, hf, ha, sideCount, Nat.count_succ]
      · simp [actualRun, hf, ha, sideCount]

/-- Every active prefix alternates from the original shared root on both arms,
and its chronological 01 counts have the root-dependent half-lengths.
No later finite stopping time is required. -/
theorem actual_rise_count_before_stop
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed)
    (source : Source) (n : ℕ) (hsupport : noAdjacentOnes source)
    (hn : (n : WithTop ℕ) < stoppingTime policy seed source) :
    (∀ side i, i ≤ sideCount (actualRun policy seed source n).actions side →
      endpoint source side i = alternatingBit source.1 i) ∧
    ∀ side, actualRiseCount policy seed source side n =
      (if source.1 then sideCount (actualRun policy seed source n).actions side / 2
        else (sideCount (actualRun policy seed source n).actions side + 1) / 2) := by
  classical
  have hbridge := stopped_execution_replay_bridge policy seed source n
  have hprefix := hbridge.1.mp hn
  have hactions := (hbridge.2.2.1 (hbridge.2.1.mpr hprefix)).1
  have halt : ∀ side i, i ≤ sideCount (actualRun policy seed source n).actions side →
      endpoint source side i = alternatingBit source.1 i := by
    intro side
    apply (no_marker_iff_alternating_prefix source.1 (endpoint source side) rfl ?_
      (sideCount (actualRun policy seed source n).actions side)).mp
    · intro i hi
      have hm0 := hprefix side i (by simpa only [hactions] using hi)
      change ¬(endpoint source side i = false ∧ arm source side i = false)
      exact of_decide_eq_false hm0
    · intro i
      simpa [endpoint] using hsupport side i
  refine ⟨halt, fun side => ?_⟩
  rw [time_count_eq_prefix_count]
  let c := sideCount (actualRun policy seed source n).actions side
  have heq : ∀ i < c,
      (endpoint source side i = false ∧ arm source side i = true) ↔
        (if source.1 then i % 2 = 1 else i % 2 = 0) := by
    intro i hi
    have h0 := halt side i (by omega)
    have h1 := halt side (i + 1) (by omega)
    simp only [endpoint] at h1
    rw [h0, h1, alternating_bit_succ]
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
      cases source.1 <;> simp [alternatingBit, hp]
  have hcount : Nat.count
      (fun i => endpoint source side i = false ∧ arm source side i = true) c =
      Nat.count (fun i => if source.1 then i % 2 = 1 else i % 2 = 0) c := by
    apply Nat.le_antisymm
    · exact Nat.count_mono_left (fun i hi => (heq i hi).mp)
    · exact Nat.count_mono_left (fun i hi => (heq i hi).mpr)
  rw [hcount]
  cases hb : source.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have hc := Nat.count_modEq_card (b := c) (r := 2) (by decide) 0
    simp only [Nat.ModEq, Nat.zero_mod] at hc
    convert hc using 1
    · congr 1 <;> exact Subsingleton.elim _ _
    · split_ifs <;> dsimp [c] at * <;> omega
  · have hc := Nat.count_modEq_card (b := c) (r := 2) (by decide) 1
    norm_num only [Nat.ModEq, Nat.reduceMod] at hc
    convert hc using 1 <;> split_ifs <;> dsimp [c] at * <;> omega


/-- At the finite first marker, the last query adds no rise. The actual rise count
on each arm is the root-dependent half-length of its preterminal zero replay. -/
theorem actual_rise_count_at_first_stop
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed)
    (source : Source) (T : ℕ) (hsupport : noAdjacentOnes source)
    (hT : stoppingTime policy seed source = (T : WithTop ℕ)) :
    0 < T ∧ ∀ side,
      actualRiseCount policy seed source side T =
        actualRiseCount policy seed source side (T - 1) ∧
      actualRiseCount policy seed source side T =
        (if source.1 then sideCount (zeroReplay policy seed (T - 1)) side / 2
          else (sideCount (zeroReplay policy seed (T - 1)) side + 1) / 2) := by
  classical
  have hex : ∃ n, (actualRun policy seed source n).stopped = true := by
    by_contra hn
    simp [stoppingTime, hn] at hT
  have hfind : Nat.find hex = T := by
    exact_mod_cast (show (Nat.find hex : WithTop ℕ) = (T : WithTop ℕ) by
      simpa [stoppingTime, hex] using hT)
  have hstop : (actualRun policy seed source T).stopped = true := by
    simpa [hfind] using Nat.find_spec hex
  have hpos : 0 < T := by
    by_contra hn
    have ht : T = 0 := by omega
    simp [ht, actualRun] at hstop
  have hprev : (actualRun policy seed source (T - 1)).stopped = false := by
    have hn := Nat.find_min hex (show T - 1 < Nat.find hex by omega)
    cases hb : (actualRun policy seed source (T - 1)).stopped <;> simp_all
  have hsucc : T - 1 + 1 = T := by omega
  let h := actualRun policy seed source (T - 1)
  let a := policy.choose seed h.actions h.replies
  have hm : markerResponse source a (sideCount h.actions a) = true := by
    have ht := hstop
    rw [← hsucc] at ht
    simpa only [actualRun, hprev, Bool.false_eq_true, ↓reduceIte] using ht
  have h00 : endpoint source a (sideCount h.actions a) = false ∧
      arm source a (sideCount h.actions a) = false := by
    simpa [markerResponse] using hm
  have hbridge := stopped_execution_replay_bridge policy seed source (T - 1)
  have hactions := (hbridge.2.2.1 hprev).1
  refine ⟨hpos, fun side => ?_⟩
  have hterminal : actualRiseCount policy seed source side T =
      actualRiseCount policy seed source side (T - 1) := by
    rw [← hsucc]
    change Nat.count _ (T - 1 + 1) = _
    rw [Nat.count_succ]
    change actualRiseCount policy seed source side (T - 1) + _ = _
    by_cases ha : a = side
    · subst side
      simp [h, a, h00.2]
    · have ha' : policy.choose seed
          (actualRun policy seed source (T - 1)).actions
          (actualRun policy seed source (T - 1)).replies ≠ side := ha
      simp only [ha', and_false, false_and, ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel]
  refine ⟨hterminal, hterminal.trans ?_⟩
  have hn : ((T - 1 : ℕ) : WithTop ℕ) < stoppingTime policy seed source := by
    rw [hT]
    exact_mod_cast (show T - 1 < T by omega)
  have hactive := actual_rise_count_before_stop policy seed source (T - 1) hsupport hn
  simpa only [hactions] using hactive.2 side

end D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts
