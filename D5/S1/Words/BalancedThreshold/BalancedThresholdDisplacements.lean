/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDisplacements
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDisplacements
   mirror-E: none(waiver:unbounded-occurrence-displacement-decomposition)
   anchors: []
   utility: none
   digest: Successive occurrence splitting constructs return multiplicities at every distance. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Arbitrary occurrence intervals split into the two unimodular return candidates.
The multiplicities satisfy the physical mechanical discrepancy bound; no bound on
the number of intervening occurrences or realization of both candidates is assumed. -/
theorem mechanical_return_displacements {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha < 1)
    (hirr : Irrational alpha) {n : ℕ} (w : Fin n → Bool)
    (hw : BispecialFactor (lowerMechanicalWord alpha alpha) w) :
    ∃ r s : List Bool,
      0 < r.length ∧ 0 < s.length ∧
      (r.count true * s.count false + 1 = s.count true * r.count false ∨
        s.count true * r.count false + 1 = r.count true * s.count false) ∧
      (∀ b, r.count b + s.count b = (List.ofFn w).count b + 1) ∧
      ∀ i j, i < j → wordFactor (lowerMechanicalWord alpha alpha) n i = w →
        wordFactor (lowerMechanicalWord alpha alpha) n j = w →
        ∃ k l : ℕ, 0 < k + l ∧
          (∀ b, (List.ofFn (wordFactor (lowerMechanicalWord alpha alpha)
            (j - i) i)).count b = k * r.count b + l * s.count b) ∧
          |(k : ℝ) * ((r.count true : ℝ) - alpha * r.length) +
            (l : ℝ) * ((s.count true : ℝ) - alpha * s.length)| < 1 := by
  classical
  let u := lowerMechanicalWord alpha alpha
  obtain ⟨r, s, hr, hs, hdet, hcounts, hadj⟩ :=
    mechanical_bispecial_returns h0 h1 hirr w hw
  have split : ∀ a b i,
      List.ofFn (wordFactor u (a + b) i) =
        List.ofFn (wordFactor u a i) ++ List.ofFn (wordFactor u b (i + a)) := by
    intro a b i
    rw [List.ofFn_add]
    congr 1
    apply congrArg List.ofFn
    funext k
    simp [wordFactor, Nat.add_assoc]
  have decompose : ∀ d i, wordFactor u n i = w → wordFactor u n (i + d) = w →
      ∃ k l : ℕ, (0 < d → 0 < k + l) ∧
        ∀ b, (List.ofFn (wordFactor u d i)).count b = k * r.count b + l * s.count b := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hi hj
      by_cases hd : d = 0
      · subst d
        exact ⟨0, 0, by omega, by simp⟩
      have hnext : ∃ q, 0 < q ∧ wordFactor u n (i + q) = w :=
        ⟨d, by omega, hj⟩
      let q := Nat.find hnext
      have hq : 0 < q ∧ wordFactor u n (i + q) = w := Nat.find_spec hnext
      have hqd : q ≤ d := Nat.find_min' hnext ⟨by omega, hj⟩
      have hqa : AdjacentOccurrences u w i (i + q) := by
        refine ⟨by omega, hi, hq.2, ?_⟩
        intro a hia haq ha
        have hae : wordFactor u n (i + (a - i)) = w := by
          simpa only [Nat.add_sub_of_le hia.le] using ha
        exact Nat.find_min hnext (by omega : a - i < q) ⟨by omega, hae⟩
      obtain ⟨k, l, _, hkl⟩ := ih (d - q) (by omega) (i + q) hq.2
        (by simpa only [Nat.add_assoc, Nat.add_sub_of_le hqd] using hj)
      have he : List.ofFn (wordFactor u d i) =
          List.ofFn (wordFactor u q i) ++
            List.ofFn (wordFactor u (d - q) (i + q)) := by
        have hcast : List.ofFn (wordFactor u d i) =
            List.ofFn (wordFactor u (q + (d - q)) i) := by
          apply List.ext_getElem
          · simp only [List.length_ofFn]
            omega
          · intro a ha hb
            simp [wordFactor]
        exact hcast.trans (split q (d - q) i)
      have hc := hadj i (i + q) hqa
      rw [Nat.add_sub_cancel_left] at hc
      rcases hc with hqr | hqs
      · refine ⟨k + 1, l, by omega, ?_⟩
        intro b
        rw [he, List.count_append, hqr, hkl]
        ring
      · refine ⟨k, l + 1, by omega, ?_⟩
        intro b
        rw [he, List.count_append, hqs, hkl]
        ring
  have total : ∀ v : List Bool, v.count true + v.count false = v.length := by
    intro v
    induction v with
    | nil => simp
    | cons b v hv => cases b <;> simp_all <;> omega
  have window : ∀ d i, (List.ofFn (wordFactor u d i)).count true =
      lowerMechanicalWindowTrueCount alpha alpha i d := by
    intro d
    induction d with
    | zero => simp [lowerMechanicalWindowTrueCount]
    | succ d hd =>
      intro i
      rw [List.ofFn_succ']
      have he : (fun k : Fin d => wordFactor u (d + 1) i k.castSucc) =
          wordFactor u d i := rfl
      rw [he]
      simp only [List.concat_eq_append, List.count_append, List.count_singleton,
        wordFactor, Fin.val_last]
      rw [hd]
      simp only [lowerMechanicalWindowTrueCount, Finset.range_add_one,
        Finset.filter_insert]
      by_cases hu : u (i + d) = true
      · simp [hu, u, Finset.mem_filter, Finset.mem_range]
      · simp [hu, u]
  refine ⟨r, s, hr, hs, hdet, hcounts, ?_⟩
  intro i j hij hi hj
  obtain ⟨k, l, hpos, hc⟩ := decompose (j - i) i hi
    (by simpa only [Nat.add_sub_of_le hij.le] using hj)
  refine ⟨k, l, hpos (by omega), hc, ?_⟩
  have hlength : j - i = k * r.length + l * s.length := by
    have he := total (List.ofFn (wordFactor u (j - i) i))
    rw [hc true, hc false, List.length_ofFn] at he
    rw [← total r, ← total s]
    nlinarith only [he]
  have htrue : lowerMechanicalWindowTrueCount alpha alpha i (j - i) =
      k * r.count true + l * s.count true := by
    rw [← window]
    exact hc true
  have herror : (k : ℝ) * ((r.count true : ℝ) - alpha * r.length) +
      (l : ℝ) * ((s.count true : ℝ) - alpha * s.length) =
      (lowerMechanicalWindowTrueCount alpha alpha i (j - i) : ℝ) -
        (j - i : ℕ) * alpha := by
    rw [htrue, hlength]
    push_cast
    ring
  rw [herror]
  exact lower_mechanical_window_true_discrepancy h0.le h1 i (j - i)

end D5.S1.Words.BalancedThreshold
