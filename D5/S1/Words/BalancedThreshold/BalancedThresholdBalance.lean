/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdBalance
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdBalance
   mirror-E: none(waiver:infinite-word-balance)
   anchors: []
   utility: none
   digest: Physical-window induction and residue rounding prove balance of the palette word. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdPalettes
import D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical BalancedThresholdDefs

/-- Each physical window counts a residue interval in one source-letter rank sequence. -/
theorem palette_colouring_balanced {alpha rho : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha < 1)
    (t : ℕ) (ht : 0 < t) : Balanced (colouredMechanicalWord alpha rho t ht) := by
  classical
  let c := lowerMechanicalWindowTrueCount alpha rho 0
  let f : Bool → ℕ → ℕ := fun b n => if b then c n else n - c n
  let x := colouredMechanicalWord alpha rho t ht
  have cle : ∀ n, c n ≤ n := by
    intro n
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
  have cs : ∀ n, c (n + 1) = c n +
      if lowerMechanicalWord alpha rho n = true then 1 else 0 := by
    intro n
    simp only [c, lowerMechanicalWindowTrueCount, Nat.zero_add,
      Finset.range_add_one, Finset.filter_insert]
    split_ifs <;> simp_all
  have fs : ∀ b n, f b (n + 1) = f b n +
      if lowerMechanicalWord alpha rho n = b then 1 else 0 := by
    intro b n
    have hc := cs n
    have hn := cle n
    cases b <;> cases hw : lowerMechanicalWord alpha rho n <;>
      simp [f, hw] at hc ⊢ <;> omega
  have window : ∀ b i n, ∃ L,
      f b (i + n) = f b i + L ∧
      L = if b then lowerMechanicalWindowTrueCount alpha rho i n
        else n - lowerMechanicalWindowTrueCount alpha rho i n := by
    intro b i n
    let w := lowerMechanicalWindowTrueCount alpha rho i n
    have hw : w ≤ n := (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
    have hi := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) h0 h1 0 i
    have he := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) h0 h1 0 (i + n)
    have hn := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) h0 h1 i n
    simp only [Nat.zero_add, Nat.cast_zero, zero_mul, add_zero] at hi he
    have hc : c (i + n) = c i + w := by dsimp [c, w]; omega
    cases b
    · refine ⟨n - w, ?_, rfl⟩
      have hci := cle i
      simp only [f, Bool.false_eq_true, if_false]
      omega
    · exact ⟨w, by simpa [f] using hc, rfl⟩
  intro a n i j
  have colour : ∃ (b : Bool) (g r : ℕ), 0 < g ∧ r < g ∧
      ∀ k, x k = a ↔ lowerMechanicalWord alpha rho k = b ∧ f b k % g = r := by
    by_cases ha : a.val < 2
    · refine ⟨true, 2, a.val, by omega, ha, ?_⟩
      intro k
      have hm := Nat.mod_lt (c k) (by omega : 0 < 2)
      cases hu : lowerMechanicalWord alpha rho k
      · have hb := Nat.mod_lt ((k - c k) / 2) ht
        have hd := Nat.mod_lt ((k - c k) / 2) (by omega : 0 < t + 1)
        simp only [x, colouredMechanicalWord, hu, Bool.false_eq_true,
          dite_false, Fin.ext_iff, f, if_true, false_and]
        split_ifs <;> dsimp only [c] at * <;> simp only [iff_false]
        · intro he
          have hge : 2 ≤ a.val := by rw [← he]; exact Nat.le_add_right 2 _
          omega
        · intro he
          have hge : 2 ≤ a.val := by
            rw [← he]
            exact (Nat.le_add_right 2 t).trans (Nat.le_add_right (2 + t) _)
          omega
      · simp [x, colouredMechanicalWord, hu, f, c, Fin.ext_iff]
    · by_cases hb : a.val < 2 + t
      · refine ⟨false, 2 * t, 2 * (a.val - 2), by omega, by omega, ?_⟩
        intro k
        have hm : (k - c k) % (2 * t) =
            (k - c k) % 2 + 2 * (((k - c k) / 2) % t) := Nat.mod_mul
        have hp := Nat.mod_lt (k - c k) (by omega : 0 < 2)
        have hd := Nat.mod_lt ((k - c k) / 2) (by omega : 0 < t + 1)
        cases hu : lowerMechanicalWord alpha rho k
        · simp only [x, colouredMechanicalWord, hu, Bool.false_eq_true, if_false,
            dite_false, Fin.ext_iff, f, true_and]
          split_ifs <;> dsimp only [c] at * <;> omega
        · have hp := Nat.mod_lt (c k) (by omega : 0 < 2)
          simp [x, colouredMechanicalWord, hu, f, c, Fin.ext_iff]
          omega
      · refine ⟨false, 2 * (t + 1), 2 * (a.val - (2 + t)) + 1,
          by omega, by have := a.isLt; omega, ?_⟩
        intro k
        have hm : (k - c k) % (2 * (t + 1)) =
            (k - c k) % 2 + 2 * (((k - c k) / 2) % (t + 1)) := Nat.mod_mul
        have hp := Nat.mod_lt (k - c k) (by omega : 0 < 2)
        have hd := Nat.mod_lt ((k - c k) / 2) ht
        cases hu : lowerMechanicalWord alpha rho k
        · simp only [x, colouredMechanicalWord, hu, Bool.false_eq_true, if_false,
            dite_false, Fin.ext_iff, f, true_and]
          split_ifs <;> dsimp only [c] at * <;> omega
        · have hp := Nat.mod_lt (c k) (by omega : 0 < 2)
          simp [x, colouredMechanicalWord, hu, f, c, Fin.ext_iff]
          omega
  obtain ⟨b, g, r, hg, hr, hcolour⟩ := colour
  let shift := g - 1 - r
  let Q : ℕ → ℕ := fun s => (s + shift) / g
  have hs : shift + 1 + r = g := by dsimp [shift]; omega
  have qs : ∀ s, Q (s + 1) = Q s + if s % g = r then 1 else 0 := by
    intro s
    have hdiv : g ∣ s + shift + 1 ↔ s % g = r := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hmod : (s + shift + 1) % g = (s % g + (shift + 1)) % g := by
        simp [Nat.add_mod, Nat.add_assoc]
      rw [hmod]
      have hm := Nat.mod_lt s hg
      by_cases hlt : s % g < r
      · have he : s % g + (shift + 1) < g := by omega
        rw [Nat.mod_eq_of_lt he]
        omega
      · have hge : g ≤ s % g + (shift + 1) := by omega
        have he : s % g + (shift + 1) - g < g := by omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt he]
        omega
    dsimp [Q]
    rw [show s + 1 + shift = s + shift + 1 by omega, Nat.succ_div]
    simp only [hdiv]
  have count : ∀ m k, letterCount x a m k + Q (f b k) = Q (f b (k + m)) := by
    have sum : ∀ m k, letterCount x a m k =
        ∑ h ∈ Finset.range m, if x (k + h) = a then 1 else 0 := by
      intro m k
      unfold letterCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Fin.sum_univ_eq_sum_range (fun h => if x (k + h) = a then 1 else 0) m
    intro m k
    induction m with
    | zero => simp [sum]
    | succ m ih =>
      rw [sum, Finset.sum_range_succ, ← sum]
      have hf := fs b (k + m)
      have hcol := hcolour (k + m)
      by_cases hu : lowerMechanicalWord alpha rho (k + m) = b
      · rw [if_pos hu] at hf
        have he : x (k + m) = a ↔ f b (k + m) % g = r := by simp [hu] at hcol; exact hcol
        have hq := qs (f b (k + m))
        rw [show k + (m + 1) = k + m + 1 by omega, hf, hq]
        simp only [he]
        omega
      · have hx : x (k + m) ≠ a := fun h => hu ((hcol.mp h).1)
        rw [if_neg hu, add_zero] at hf
        rw [show k + (m + 1) = k + m + 1 by omega, hf, if_neg hx]
        omega
  have rounding : ∀ s L K, K + Q s = Q (s + L) →
      L / g ≤ K ∧ K ≤ (L + g - 1) / g := by
    intro s L K hK
    have he : s + L + shift = s + shift + L := by omega
    have hadd := @Nat.add_div (s + shift) L g hg
    change K + (s + shift) / g = (s + L + shift) / g at hK
    rw [he, hadd] at hK
    have hm := Nat.mod_lt (s + shift) hg
    by_cases hcarry : g ≤ (s + shift) % g + L % g
    · rw [if_pos hcarry] at hK
      have hrem : 0 < L % g := by omega
      have hgm : (g - 1) % g = g - 1 := Nat.mod_eq_of_lt (by omega)
      have hgd : (g - 1) / g = 0 := Nat.div_eq_of_lt (by omega)
      have hup := @Nat.add_div L (g - 1) g hg
      rw [hgm, hgd, add_zero, if_pos (by omega)] at hup
      rw [show L + g - 1 = L + (g - 1) by omega, hup]
      omega
    · rw [if_neg hcarry] at hK
      have hle : L / g ≤ (L + g - 1) / g := Nat.div_le_div_right (by omega)
      omega
  obtain ⟨Li, hLi, hi⟩ := window b i n
  obtain ⟨Lj, hLj, hj⟩ := window b j n
  have hsource : Li ≤ Lj + 1 := by
    have hb := lowerMechanicalWord_balanced_one (rho := rho) h0 h1 i j n
    rw [abs_le] at hb
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at hi hj <;> omega
  have hci := count n i
  have hcj := count n j
  rw [hLi] at hci
  rw [hLj] at hcj
  have hri := rounding (f b i) Li (letterCount x a n i) hci
  have hrj := rounding (f b j) Lj (letterCount x a n j) hcj
  have hround : (Li + g - 1) / g ≤ Lj / g + 1 := by
    have hle := @Nat.div_le_div_right (Li + g - 1) (Lj + g) g (by omega)
    rwa [Nat.add_div_right Lj hg] at hle
  exact hri.2.trans (hround.trans (Nat.add_le_add_right hrj.1 1))

end D5.S1.Words.BalancedThreshold
