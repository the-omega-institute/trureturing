/- GID: D5/S1/Words/AdmissibleWords/FIBThresholdPairExtrema
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBThresholdPairExtrema
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One legal threshold coupling attains the parity-dependent pair bounds at fixed real path marginals. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MeasureTheory
open D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema

private def event (side : Bool) (p : ℝ) : Set ℝ :=
  if side then Ioo 0 p else Ioo (1 - p) 1

private theorem opposite_events {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) :
    event true a ∩ event false b = Ioo (1 - b) a := by
  simp [event, Ioo_inter_Ioo, max_eq_right (sub_nonneg.mpr hb), min_eq_left ha]

private theorem event_volume (side : Bool) (p : ℝ) :
    volume (event side p) = ENNReal.ofReal p := by
  cases side <;> simp [event, Real.volume_Ioo]

private theorem event_pair_volume (si sj : Bool) {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) :
    volume (event si a ∩ event sj b) =
      ENNReal.ofReal (if si = sj then min a b else max 0 (a + b - 1)) := by
  cases si <;> cases sj
  · simp only [event, Bool.false_eq_true, ite_false, Ioo_inter_Ioo, inf_idem,
      Real.volume_Ioo, ite_true]
    change ENNReal.ofReal (1 - max (1 - a) (1 - b)) = ENNReal.ofReal (min a b)
    by_cases h : a ≤ b
    · rw [min_eq_left h, max_eq_left (by linarith : 1 - b ≤ 1 - a)]
      congr 1
      ring
    · have h' := le_of_not_ge h
      rw [min_eq_right h', max_eq_right (by linarith : 1 - a ≤ 1 - b)]
      congr 1
      ring
  · rw [inter_comm, opposite_events hb ha, Real.volume_Ioo]
    simp [show b - (1 - a) = a + b - 1 by ring]
  · rw [opposite_events ha hb, Real.volume_Ioo]
    simp [show a - (1 - b) = a + b - 1 by ring]
  · simp only [event, ite_true, Ioo_inter_Ioo, sup_idem, Real.volume_Ioo]
    change ENNReal.ofReal (min a b - 0) = ENNReal.ofReal (min a b)
    rw [sub_zero]

/-- One uniform threshold realizes a bounded occupancy profile and all its
parity-dependent pair extremes at once. -/
theorem threshold_pair_extrema {n : ℕ} {p : Fin n → ℝ}
    (bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (adjacent : ∀ i j, i.val + 1 = j.val → p i + p j ≤ 1) :
    ∃ w : ℝ → Fin n → Bool, (∀ u, Adm n (w u)) ∧
      (∀ u ∉ Ioo (0 : ℝ) 1, ∀ i, w u i = false) ∧
      (∀ i, MeasurableSet {u | w u i = true} ∧
        volume {u | w u i = true} = ENNReal.ofReal (p i)) ∧
      ∀ i j, volume {u | w u i = true ∧ w u j = true} =
        ENNReal.ofReal (if i.val % 2 = j.val % 2 then min (p i) (p j)
          else max 0 (p i + p j - 1)) := by
  classical
  let side (i : Fin n) : Bool := decide (i.val % 2 = 0)
  let w (u : ℝ) (i : Fin n) : Bool := decide (u ∈ event (side i) (p i))
  have event_eq (i : Fin n) : {u | w u i = true} = event (side i) (p i) := by
    ext u
    simp [w]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [adm_iff_no_adjacent_true]
    intro i j hij
    by_contra! h
    have hi : u ∈ event (side i) (p i) := by simpa [w] using h.1
    have hj : u ∈ event (side j) (p j) := by simpa [w] using h.2
    have opp : side i ≠ side j := by
      simp only [side, ne_eq, decide_eq_decide]
      omega
    have bound := adjacent i j hij
    cases a : side i <;> cases b : side j <;> simp [a, b] at opp
    · simp only [a, b, event, ite_false, ite_true, Bool.false_eq_true, mem_Ioo] at hi hj
      linarith [hi.1, hj.2]
    · simp only [a, b, event, ite_false, ite_true, Bool.false_eq_true, mem_Ioo] at hi hj
      linarith [hi.2, hj.1]
  · intro u hu i
    have upper := (bounds i).2
    simp only [w, decide_eq_false_iff_not]
    intro h
    apply hu
    cases hs : side i <;> simp [hs, event] at h
    · exact ⟨lt_of_le_of_lt (sub_nonneg.mpr upper) h.1, h.2⟩
    · exact ⟨h.1, h.2.trans_le upper⟩
  · intro i
    rw [event_eq]
    exact ⟨by cases side i <;> simp [event, measurableSet_Ioo], event_volume _ _⟩
  · intro i j
    change volume ({u | w u i = true} ∩ {u | w u j = true}) = _
    rw [event_eq, event_eq, event_pair_volume _ _ (bounds i).2 (bounds j).2]
    congr 1
    have parity : side i = side j ↔ i.val % 2 = j.val % 2 := by
      simp only [side, decide_eq_decide]
      omega
    simp only [parity]

end D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema
