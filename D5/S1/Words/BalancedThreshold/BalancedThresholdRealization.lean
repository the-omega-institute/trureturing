/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdRealization
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdRealization
   mirror-E: none(waiver:irrational-mechanical-return-variation)
   anchors: []
   utility: none
   digest: Successive-return induction rules out a single return block at every factor. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Repeated identical returns would give an unbounded multiple of a nonzero
irrational discrepancy. Consequently every occurring factor has another return. -/
theorem mechanical_return_variation {alpha rho : ℝ}
    (h0 : 0 < alpha) (h1 : alpha < 1) (hirr : Irrational alpha) :
    let u := lowerMechanicalWord alpha rho
    ∀ (n : ℕ) (w : Fin n → Bool), (∃ i, wordFactor u n i = w) →
      ∀ r : List Bool, ∃ i j, AdjacentOccurrences u w i j ∧
        List.ofFn (wordFactor u (j - i) i) ≠ r := by
  classical
  let u := lowerMechanicalWord alpha rho
  let x := colouredMechanicalWord alpha rho 1 (by omega)
  let count := fun i m => lowerMechanicalWindowTrueCount alpha rho i m
  have project : ∀ i, u i = true ↔ (x i).val < 2 := by
    intro i
    have hm := Nat.mod_lt (count 0 i) (by omega : 0 < 2)
    by_cases hu : lowerMechanicalWord alpha rho i = true
    · simpa [u, x, colouredMechanicalWord, hu, count] using hm
    · simp [u, x, colouredMechanicalWord, hu]
      split_ifs <;> simp <;> omega
  have recurrence : UniformlyRecurrentWord u := by
    intro n i
    obtain ⟨R, hR⟩ := coloured_word_uniformly_recurrent (rho := rho) h0.le h1 hirr
      1 (by omega) n i
    refine ⟨R, ?_⟩
    intro s
    obtain ⟨j, hsj, hjR, he⟩ := hR s
    refine ⟨j, hsj, hjR, ?_⟩
    funext k
    apply Bool.eq_iff_iff.mpr
    change u (j + k) = true ↔ u (i + k) = true
    rw [project, project]
    exact iff_of_eq (congrArg (fun a : Fin 5 => a.val < 2) (congrFun he k))
  have split : ∀ a b i, count i (a + b) = count i a + count (i + a) b := by
    intro a b i
    simpa only [Nat.count_eq_card_filter_range, count, lowerMechanicalWindowTrueCount,
      u, Nat.add_assoc] using Nat.count_add (fun k => u (i + k) = true) a b
  have window : ∀ d i, (List.ofFn (wordFactor u d i)).count true = count i d := by
    intro d
    induction d with
    | zero => simp [count, lowerMechanicalWindowTrueCount]
    | succ d hd =>
      intro i
      rw [List.ofFn_succ']
      have he : (fun k : Fin d => wordFactor u (d + 1) i k.castSucc) =
          wordFactor u d i := rfl
      rw [he]
      simp only [List.concat_eq_append, List.count_append, List.count_singleton,
        wordFactor, Fin.val_last]
      rw [hd]
      simp only [count, lowerMechanicalWindowTrueCount, Finset.range_add_one,
        Finset.filter_insert]
      by_cases hu : u (i + d) = true
      · simp [hu, u, Finset.mem_filter, Finset.mem_range]
      · simp [hu, u]
  change ∀ (n : ℕ) (w : Fin n → Bool), (∃ i, wordFactor u n i = w) →
    ∀ r : List Bool, ∃ i j, AdjacentOccurrences u w i j ∧
      List.ofFn (wordFactor u (j - i) i) ≠ r
  intro n w hw r
  obtain ⟨start, hstart⟩ := hw
  by_contra hnone
  have same : ∀ i j, AdjacentOccurrences u w i j →
      List.ofFn (wordFactor u (j - i) i) = r := by
    intro i j hij
    by_contra he
    exact hnone ⟨i, j, hij, he⟩
  have next : ∀ i, wordFactor u n i = w → ∃ j, AdjacentOccurrences u w i j := by
    intro i hi
    obtain ⟨R, hR⟩ := recurrence n start
    obtain ⟨j, hj, _, hwj⟩ := hR (i + 1)
    have hex : ∃ j, i < j ∧ wordFactor u n j = w := ⟨j, by omega, hwj.trans hstart⟩
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, hi, (Nat.find_spec hex).2, ?_⟩
    intro k hik hkj hk
    exact Nat.find_min hex hkj ⟨hik, hk⟩
  obtain ⟨j, hj⟩ := next start hstart
  have hlen := congrArg List.length (same start j hj)
  simp only [List.length_ofFn] at hlen
  have hL : 0 < r.length := by have := hj.1; omega
  have iterate : ∀ k, wordFactor u n (start + k * r.length) = w ∧
      count start (k * r.length) = k * r.count true := by
    intro k
    induction k with
    | zero => simpa [count, lowerMechanicalWindowTrueCount] using hstart
    | succ k ih =>
      obtain ⟨j, hj⟩ := next (start + k * r.length) ih.1
      have he := same _ j hj
      have hl := congrArg List.length he
      simp only [List.length_ofFn] at hl
      have hj' : j = start + (k + 1) * r.length := by
        have := hj.1
        rw [Nat.add_mul, one_mul]
        omega
      have hc := congrArg (List.count true) he
      rw [window, hl] at hc
      constructor
      · simpa only [hj'] using hj.2.2.1
      · rw [Nat.succ_mul, split, ih.2, hc]
        ring
  have he : (r.count true : ℝ) - (r.length : ℝ) * alpha ≠ 0 := by
    intro hz
    have hi := hirr.natCast_mul (by omega : r.length ≠ 0)
    exact hi.ne_int (r.count true : ℤ) (by push_cast; linarith)
  have habs : 0 < |(r.count true : ℝ) - (r.length : ℝ) * alpha| :=
    abs_pos.mpr he
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / |(r.count true : ℝ) - (r.length : ℝ) * alpha|)
  have herr := lower_mechanical_window_true_discrepancy
    (rho := rho) h0.le h1 start (k * r.length)
  change |(count start (k * r.length) : ℝ) - (k * r.length : ℕ) * alpha| < 1 at herr
  rw [(iterate k).2] at herr
  push_cast at herr
  have hid : (k : ℝ) * r.count true - (k : ℝ) * r.length * alpha =
      (k : ℝ) * ((r.count true : ℝ) - (r.length : ℝ) * alpha) := by ring
  rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at herr
  have hbig := (div_lt_iff₀ habs).mp hk
  linarith

end D5.S1.Words.BalancedThreshold
