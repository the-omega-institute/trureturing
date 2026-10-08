/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdBracketing
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdBracketing
   mirror-E: none(waiver:irrational-return-discrepancy-bracketing)
   anchors: []
   utility: none
   digest: Successive-return accumulation forces the two actual errors to have opposite signs. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdReturns
import D5.S1.Words.Mechanical.MechanicalUniformRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- The two distinct physical returns bracket the irrational frequency strictly.
If their errors had the same sign, successive returns would accumulate an
unbounded discrepancy, contradicting the mechanical window bound. -/
theorem mechanical_return_bracketing {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha < 1)
    (hirr : Irrational alpha) {n : ℕ} (w : Fin n → Bool)
    (hw : BispecialFactor (lowerMechanicalWord alpha alpha) w) :
    let u := lowerMechanicalWord alpha alpha
    ∀ i j a b : ℕ, AdjacentOccurrences u w i j → AdjacentOccurrences u w a b →
      List.ofFn (wordFactor u (j - i) i) ≠ List.ofFn (wordFactor u (b - a) a) →
      ((lowerMechanicalWindowTrueCount alpha alpha i (j - i) : ℝ) -
        alpha * (j - i : ℕ)) *
      ((lowerMechanicalWindowTrueCount alpha alpha a (b - a) : ℝ) -
        alpha * (b - a : ℕ)) < 0 := by
  classical
  let u := lowerMechanicalWord alpha alpha
  let count := fun i d => lowerMechanicalWindowTrueCount alpha alpha i d
  let error := fun r : List Bool => (r.count true : ℝ) - alpha * r.length
  obtain ⟨r, s, hr, hs, _, _, hadj⟩ := mechanical_bispecial_returns h0 h1 hirr w hw
  obtain ⟨start, _, _, _, hstart, _, _⟩ := hw.1
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
  have split : ∀ a b i, count i (a + b) = count i a + count (i + a) b := by
    intro a b i
    simpa only [Nat.count_eq_card_filter_range, count, lowerMechanicalWindowTrueCount,
      u, Nat.add_assoc] using Nat.count_add (fun k => u (i + k) = true) a b
  have next : ∀ i, wordFactor u n i = w → ∃ j, AdjacentOccurrences u w i j := by
    intro i hi
    have hmem : List.ofFn w ∈ lowerMechanicalFactorSet alpha alpha n := by
      apply mem_lowerMechanicalFactorSet.mpr
      exact ⟨i, congrArg List.ofFn hi.symm⟩
    obtain ⟨R, hR⟩ := MechanicalUniformRecurrence.lower_mechanical_factor_uniformly_recurrent
      h0.le h1 hirr hmem
    obtain ⟨j, hij, _, hj⟩ := hR (i + 1)
    have hjw : wordFactor u n j = w := List.ofFn_inj.mp hj.symm
    have hex : ∃ j, i < j ∧ wordFactor u n j = w := ⟨j, by omega, hjw⟩
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, hi, (Nat.find_spec hex).2, ?_⟩
    intro k hik hkj hk
    exact Nat.find_min hex hkj ⟨hik, hk⟩
  have nonzero : ∀ v : List Bool, 0 < v.length → error v ≠ 0 := by
    intro v hv he
    have hi := hirr.natCast_mul (by omega : v.length ≠ 0)
    exact hi.ne_int (v.count true : ℤ) (by dsimp [error] at he; push_cast; nlinarith)
  have accumulate : ∀ sigma : ℝ, sigma = 1 ∨ sigma = -1 →
      0 < sigma * error r → 0 < sigma * error s → False := by
    intro sigma hsig hpr hps
    let e := min (sigma * error r) (sigma * error s)
    have he : 0 < e := lt_min hpr hps
    have iterate : ∀ k : ℕ, ∃ d : ℕ, wordFactor u n (start + d) = w ∧
        (k : ℝ) * e ≤ sigma * ((count start d : ℝ) - alpha * d) := by
      intro k
      induction k with
      | zero =>
        exact ⟨0, by simpa using hstart, by simp [count, lowerMechanicalWindowTrueCount]⟩
      | succ k ih =>
        obtain ⟨d, hd, hearlier⟩ := ih
        obtain ⟨j, hj⟩ := next (start + d) hd
        let q := j - (start + d)
        have hjq : start + (d + q) = j := by have := hj.1; dsimp [q]; omega
        have hblock : List.ofFn (wordFactor u q (start + d)) = r ∨
            List.ofFn (wordFactor u q (start + d)) = s := hadj _ _ hj
        have hincrement : e ≤ sigma * ((count (start + d) q : ℝ) - alpha * q) := by
          rcases hblock with hb | hb
          · have hc := congrArg (List.count true) hb
            have hl := congrArg List.length hb
            rw [window] at hc
            simp only [List.length_ofFn] at hl
            rw [hc, hl]
            exact min_le_left _ _
          · have hc := congrArg (List.count true) hb
            have hl := congrArg List.length hb
            rw [window] at hc
            simp only [List.length_ofFn] at hl
            rw [hc, hl]
            exact min_le_right _ _
        refine ⟨d + q, by rw [hjq]; exact hj.2.2.1, ?_⟩
        rw [split]
        push_cast
        have hsum := add_le_add hearlier hincrement
        nlinarith only [hsum]
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / e)
    obtain ⟨d, _, hd⟩ := iterate k
    have herr := lower_mechanical_window_true_discrepancy (rho := alpha) h0.le h1 start d
    change |(count start d : ℝ) - (d : ℝ) * alpha| < 1 at herr
    have hupper : sigma * ((count start d : ℝ) - alpha * d) < 1 := by
      rcases hsig with rfl | rfl <;> rw [abs_lt] at herr <;> nlinarith only [herr.1, herr.2]
    have hbig := (div_lt_iff₀ he).mp hk
    nlinarith only [hd, hupper, hbig]
  have hopposite : error r * error s < 0 := by
    have hnr := nonzero r hr
    have hns := nonzero s hs
    rcases lt_or_gt_of_ne hnr with hneg | hpos
    · have hspos : 0 < error s := by
        rcases lt_or_gt_of_ne hns with hsneg | hspos
        · exact (accumulate (-1) (Or.inr rfl) (by linarith) (by linarith)).elim
        · exact hspos
      exact mul_neg_of_neg_of_pos hneg hspos
    · have hsneg : error s < 0 := by
        rcases lt_or_gt_of_ne hns with hsneg | hspos
        · exact hsneg
        · exact (accumulate 1 (Or.inl rfl) (by simpa) (by simpa)).elim
      exact mul_neg_of_pos_of_neg hpos hsneg
  dsimp only
  intro i j a b hij hab hne
  have hijc := hadj i j hij
  have habc := hadj a b hab
  have identify : ∀ v k l,
      List.ofFn (wordFactor u (l - k) k) = v →
      (count k (l - k) : ℝ) - alpha * (l - k : ℕ) = error v := by
    intro v k l hv
    have hc := congrArg (List.count true) hv
    have hl := congrArg List.length hv
    rw [window] at hc
    simp only [List.length_ofFn] at hl
    dsimp only [error]
    rw [hc, hl]
  change ((count i (j - i) : ℝ) - alpha * (j - i : ℕ)) *
    ((count a (b - a) : ℝ) - alpha * (b - a : ℕ)) < 0
  rcases hijc with hi | hi <;> rcases habc with ha | ha
  · exact (hne (hi.trans ha.symm)).elim
  · rw [identify _ _ _ hi, identify _ _ _ ha]
    exact hopposite
  · rw [identify _ _ _ hi, identify _ _ _ ha, mul_comm]
    exact hopposite
  · exact (hne (hi.trans ha.symm)).elim

end D5.S1.Words.BalancedThreshold
