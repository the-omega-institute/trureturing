/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeConfinement
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeConfinement
   mirror-E: none(waiver:necessary-rotation-class-span)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Round]
   utility: none
   digest: Boundary recovery confines every actual power to one finite-cut interval. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBoundary
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePowerSpan
import D5.S1.Words.Mechanical.FloorFractShift
import Mathlib.Algebra.Order.Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.FloorFractShift

/-- Recover the cut tests at all block starts, select adjacent finite endpoints,
and bound the ordinary-coordinate span inside their common half-open interval. -/
theorem kabelian_power_cut_confinement {alpha : ℝ}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) {k m e start : ℕ}
    (hk : 1 ≤ k) (hmk : k - 1 ≤ m) (he : 0 < e)
    (hp : IsKAbelianPower alpha k m e start) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (a = 0 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
        (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ a = 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (b = 1 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
        (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ b = 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (∀ r : ℕ, 0 < r → r ≤ m → (r ≤ k - 1 ∨ m - (k - 1) ≤ r) →
        1 - Int.fract ((r : ℝ) * alpha) ≤ a ∨
          b ≤ 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (∀ i < e, a ≤ Int.fract (((start + i * m : ℕ) : ℝ) * alpha) ∧
        Int.fract (((start + i * m : ℕ) : ℝ) * alpha) < b) ∧
      ((e - 1 : ℕ) : ℝ) *
        |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)| < b - a := by
  classical
  let s (i : ℕ) := start + i * m
  let x (i : ℕ) := Int.fract ((s i : ℝ) * alpha)
  let cut (r : ℕ) := 1 - Int.fract ((r : ℝ) * alpha)
  obtain ⟨c, hc, _⟩ := kabelian_power_phase_span h0 h1 hk he hp
  have hfull (i : ℕ) (hi : i < e) :
      ⌊((s i + m : ℕ) : ℝ) * alpha⌋ - ⌊(s i : ℝ) * alpha⌋ = c := by
    have ha := hc i hi.le
    have hb := hc (i + 1) (by omega)
    rw [show start + (i + 1) * m = s i + m by dsimp [s]; ring] at hb
    dsimp [s] at hb
    simp only [Int.fract, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at ha hb
    have hh : ((⌊((s i + m : ℕ) : ℝ) * alpha⌋ -
        ⌊(s i : ℝ) * alpha⌋ : ℤ) : ℝ) = (c : ℝ) := by
      simp only [Int.cast_sub, Nat.cast_add]
      dsimp [s]
      push_cast
      nlinarith only [ha, hb]
    exact_mod_cast hh
  have hprefix (i : ℕ) (hi : i < e) :
      lowerMechanicalFactor alpha 0 (k - 1) (s i) =
        lowerMechanicalFactor alpha 0 (k - 1) (s 0) := by
    have hb := (kabelian_boundary_recovery (by omega : k - 1 < k)
      (by simpa [lowerMechanicalFactor] using hmk) (hp i 0 hi he)).1
    have ht (j : ℕ) : (lowerMechanicalFactor alpha 0 m (s j)).take (k - 1) =
        lowerMechanicalFactor alpha 0 (k - 1) (s j) := by
      apply List.ext_getElem
      · simp [lowerMechanicalFactor, Nat.min_eq_left hmk]
      · intro r hr hs
        simp [lowerMechanicalFactor]
    change (lowerMechanicalFactor alpha 0 m (s i)).take (k - 1) =
      (lowerMechanicalFactor alpha 0 m (s 0)).take (k - 1) at hb
    simpa only [ht] using hb
  have hsuffix (i : ℕ) (hi : i < e) :
      lowerMechanicalFactor alpha 0 (k - 1) (s i + (m - (k - 1))) =
        lowerMechanicalFactor alpha 0 (k - 1) (s 0 + (m - (k - 1))) := by
    have hb := (kabelian_boundary_recovery (by omega : k - 1 < k)
      (by simpa [lowerMechanicalFactor] using hmk) (hp i 0 hi he)).2
    have ht (j : ℕ) : (lowerMechanicalFactor alpha 0 m (s j)).drop (m - (k - 1)) =
        lowerMechanicalFactor alpha 0 (k - 1) (s j + (m - (k - 1))) := by
      apply List.ext_getElem
      · simp [lowerMechanicalFactor]; omega
      · intro r hr hs
        simp [lowerMechanicalFactor, Nat.add_assoc]
    simp only [lowerMechanicalFactor, List.length_ofFn] at hb
    change (lowerMechanicalFactor alpha 0 m (s i)).drop (m - (k - 1)) =
      (lowerMechanicalFactor alpha 0 m (s 0)).drop (m - (k - 1)) at hb
    simpa only [ht] using hb
  have hinc (i r : ℕ) (hi : i < e) (hrm : r ≤ m)
      (hr : r ≤ k - 1 ∨ m - (k - 1) ≤ r) :
      ⌊((s i + r : ℕ) : ℝ) * alpha⌋ - ⌊(s i : ℝ) * alpha⌋ =
        ⌊((s 0 + r : ℕ) : ℝ) * alpha⌋ - ⌊(s 0 : ℝ) * alpha⌋ := by
    rcases hr with hr | hr
    · have hh := window_counts_eq_of_factor_eq hr (hprefix i hi)
      have hh' := congrArg (fun n : ℕ => (n : ℤ)) hh
      simpa only [lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1, zero_add]
        using hh'
    · let l := m - r
      have htail := hsuffix i hi
      have hd := congrArg (fun w : List Bool => w.drop (r - (m - (k - 1)))) htail
      have ht (j : ℕ) :
          (lowerMechanicalFactor alpha 0 (k - 1) (s j + (m - (k - 1)))).drop
            (r - (m - (k - 1))) = lowerMechanicalFactor alpha 0 l (s j + r) := by
        apply List.ext_getElem
        · simp [lowerMechanicalFactor, l]; omega
        · intro t ht hu
          simp only [List.getElem_drop, lowerMechanicalFactor, List.getElem_ofFn]
          congr 1
          omega
      rw [ht, ht] at hd
      have hh := window_counts_eq_of_factor_eq (le_refl l) hd
      have hh' := congrArg (fun n : ℕ => (n : ℤ)) hh
      rw [lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1,
        lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1] at hh'
      simp only [zero_add, show s i + r + l = s i + m by dsimp [l]; omega,
        show s 0 + r + l = s 0 + m by dsimp [l]; omega] at hh'
      have ha := hfull i hi
      have hb := hfull 0 he
      omega
  have htests (i r : ℕ) (hi : i < e) (hrm : r ≤ m)
      (hr : r ≤ k - 1 ∨ m - (k - 1) ≤ r) : cut r ≤ x i ↔ cut r ≤ x 0 := by
    have hh := hinc i r hi hrm hr
    have hadd (j : ℕ) : ((s j + r : ℕ) : ℝ) * alpha =
        (s j : ℝ) * alpha + (r : ℝ) * alpha := by push_cast; ring
    rw [hadd, hadd, floor_add_sub_floor, floor_add_sub_floor,
      floor_fract_add_indicator, floor_fract_add_indicator] at hh
    change (⌊(r : ℝ) * alpha⌋ + if cut r ≤ x i then (1 : ℤ) else 0) =
      (⌊(r : ℝ) * alpha⌋ + if cut r ≤ x 0 then (1 : ℤ) else 0) at hh
    by_cases ha : cut r ≤ x i <;> by_cases hb : cut r ≤ x 0
    · exact iff_of_true ha hb
    · simp only [if_pos ha, if_neg hb] at hh; omega
    · simp only [if_neg ha, if_pos hb] at hh; omega
    · exact iff_of_false ha hb
  let R := (Finset.range (m + 1)).filter fun r =>
    0 < r ∧ (r ≤ k - 1 ∨ m - (k - 1) ≤ r)
  let T := insert 0 (insert 1 (R.image cut))
  let L := T.filter fun t => t ≤ x 0
  let U := T.filter fun t => x 0 < t
  have hzero : 0 ∈ L := by
    simp only [L, Finset.mem_filter]
    exact ⟨by simp [T], Int.fract_nonneg _⟩
  have hone : 1 ∈ U := by
    simp only [U, Finset.mem_filter]
    exact ⟨by simp [T], Int.fract_lt_one _⟩
  let a := L.max' ⟨0, hzero⟩
  let b := U.min' ⟨1, hone⟩
  have haL : a ∈ L := Finset.max'_mem _ _
  have hbU : b ∈ U := Finset.min'_mem _ _
  have hax : a ≤ x 0 := (Finset.mem_filter.mp haL).2
  have hxb : x 0 < b := (Finset.mem_filter.mp hbU).2
  have ha0 : 0 ≤ a := Finset.le_max' _ _ hzero
  have hb1 : b ≤ 1 := Finset.min'_le _ _ hone
  have hR (r : ℕ) (hr : r ∈ R) :
      0 < r ∧ r ≤ m ∧ (r ≤ k - 1 ∨ m - (k - 1) ≤ r) := by
    have hh := Finset.mem_filter.mp hr
    exact ⟨hh.2.1, by have := Finset.mem_range.mp hh.1; omega, hh.2.2⟩
  have hendsa : a = 0 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
      (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ a = cut r := by
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp haL).1 with ha | ha
    · exact Or.inl ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · exfalso; linarith [Int.fract_lt_one ((s 0 : ℝ) * alpha)]
    obtain ⟨r, hr, hrc⟩ := Finset.mem_image.mp ha
    exact Or.inr ⟨r, (hR r hr).1, (hR r hr).2.1, (hR r hr).2.2, hrc.symm⟩
  have hendsb : b = 1 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
      (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ b = cut r := by
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hbU).1 with hb | hb
    · exfalso; linarith [Int.fract_nonneg ((s 0 : ℝ) * alpha)]
    rcases Finset.mem_insert.mp hb with hb | hb
    · exact Or.inl hb
    obtain ⟨r, hr, hrc⟩ := Finset.mem_image.mp hb
    exact Or.inr ⟨r, (hR r hr).1, (hR r hr).2.1, (hR r hr).2.2, hrc.symm⟩
  have hcuts (r : ℕ) (hr0 : 0 < r) (hrm : r ≤ m)
      (hr : r ≤ k - 1 ∨ m - (k - 1) ≤ r) : cut r ≤ a ∨ b ≤ cut r := by
    have hrR : r ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr0, hr⟩
    have hcT : cut r ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨r, hrR, rfl⟩))
    by_cases hx : cut r ≤ x 0
    · exact Or.inl (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hcT, hx⟩))
    · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hcT, lt_of_not_ge hx⟩))
  have hstay (i : ℕ) (hi : i < e) : a ≤ x i ∧ x i < b := by
    constructor
    · rcases hendsa with ha | ⟨r, _, hrm, hr, ha⟩
      · rw [ha]; exact Int.fract_nonneg _
      · rw [ha] at hax ⊢
        exact (htests i r hi hrm hr).mpr hax
    · rcases hendsb with hb | ⟨r, _, hrm, hr, hb⟩
      · rw [hb]; exact Int.fract_lt_one _
      · rw [hb] at hxb ⊢
        exact lt_of_not_ge (fun hh => (not_le.mpr hxb) ((htests i r hi hrm hr).mp hh))
  refine ⟨a, b, ha0, hax.trans_lt hxb, hb1, hendsa, hendsb, hcuts, hstay, ?_⟩
  let E := e - 1
  have hE : E < e := by dsimp [E]; omega
  have hphase : x E - x 0 = (E : ℝ) * ((m : ℝ) * alpha - c) := by
    have hh := hc E hE.le
    simpa only [x, s, Nat.zero_mul, Nat.add_zero, add_sub_cancel_left] using
      congrArg (fun z => z - Int.fract ((start : ℝ) * alpha)) hh
  have hdist : |x E - x 0| < b - a := by
    rw [abs_lt]
    constructor <;> linarith [(hstay E hE).1, (hstay E hE).2,
      (hstay 0 he).1, (hstay 0 he).2]
  rw [hphase, abs_mul, abs_of_nonneg (Nat.cast_nonneg E)] at hdist
  exact (mul_le_mul_of_nonneg_left (round_le ((m : ℝ) * alpha) c)
    (Nat.cast_nonneg E)).trans_lt hdist

end D5.S1.Words.KAbelianLagrange
