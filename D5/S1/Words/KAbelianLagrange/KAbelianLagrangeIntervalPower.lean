/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeIntervalPower
   generality: I
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeIntervalPower
   mirror-E: none(waiver:rotation-interval-attainment)
   anchors: []
   utility: none
   digest: An interior orbit segment avoiding boundary cuts realizes an actual k-abelian power. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeClassification
import D5.S1.Words.Mechanical.FloorFractShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.FloorFractShift

/-- Interior phases with constant prefix and suffix floor tests give actual powers.
The starting phase is constructed, and every modular iterate is checked in ordinary coordinates. -/
theorem kabelian_power_in_cut_interval {alpha a b : ℝ}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (hirr : Irrational alpha)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {k m e : ℕ} (hmk : k - 1 ≤ m) (he : 0 < e) (c : ℤ)
    (hcuts : ∀ r : ℕ, 0 < r → r ≤ m →
      (r ≤ k - 1 ∨ m - (k - 1) ≤ r) →
      1 - Int.fract ((r : ℝ) * alpha) ≤ a ∨
        b ≤ 1 - Int.fract ((r : ℝ) * alpha))
    (hspan : ((e - 1 : ℕ) : ℝ) * |(m : ℝ) * alpha - c| < b - a) :
    ∃ start : ℕ, IsKAbelianPower alpha k m e start := by
  classical
  let E := e - 1
  let d := (m : ℝ) * alpha - (c : ℝ)
  let lo := max a (a - (E : ℝ) * d)
  let hi := min b (b - (E : ℝ) * d)
  have hwidth : |(E : ℝ) * d| < b - a := by
    simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (E : ℝ) by positivity),
      E, d] using hspan
  have hlo : 0 ≤ lo := ha.trans (le_max_left _ _)
  have hhi : hi ≤ 1 := (min_le_left _ _).trans hb
  have hlh : lo < hi := by
    rw [abs_lt] at hwidth
    dsimp [lo, hi]
    apply max_lt
    · exact lt_min hab (by linarith)
    · exact lt_min (by linarith) (by linarith)
  obtain ⟨start, hx⟩ := exists_phase_mem_Ioo (rho := 0) hirr hlo hlh hhi
  let x := Int.fract ((start : ℝ) * alpha)
  have hx' : lo < x ∧ x < hi := by simpa only [phase, zero_add, Set.mem_Ioo] using hx
  have hstay (i : ℕ) (hi : i < e) : a < x + (i : ℝ) * d ∧
      x + (i : ℝ) * d < b := by
    have hiE : (i : ℝ) ≤ E := by exact_mod_cast (show i ≤ E by dsimp [E]; omega)
    have hxa : a < x := (le_max_left _ _).trans_lt hx'.1
    have hxb : x < b := hx'.2.trans_le (min_le_left _ _)
    have hxa' : a - (E : ℝ) * d < x := (le_max_right _ _).trans_lt hx'.1
    have hxb' : x < b - (E : ℝ) * d := hx'.2.trans_le (min_le_right _ _)
    rcases le_total 0 d with hd | hd
    · have hil := mul_nonneg (Nat.cast_nonneg i) hd
      have hiu := mul_le_mul_of_nonneg_right hiE hd
      constructor <;> linarith
    · have hiu := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg i) hd
      have hil := mul_le_mul_of_nonpos_right hiE hd
      constructor <;> linarith
  have hphase (i : ℕ) (hi : i < e) :
      Int.fract (((start + i * m : ℕ) : ℝ) * alpha) = x + (i : ℝ) * d := by
    have hdecomp : (((start + i * m : ℕ) : ℝ) * alpha) =
        ((⌊(start : ℝ) * alpha⌋ + (i : ℤ) * c : ℤ) : ℝ) +
          (x + (i : ℝ) * d) := by
      change _ = ((⌊(start : ℝ) * alpha⌋ + (i : ℤ) * c : ℤ) : ℝ) +
        (((start : ℝ) * alpha - (⌊(start : ℝ) * alpha⌋ : ℝ)) +
          (i : ℝ) * ((m : ℝ) * alpha - (c : ℝ)))
      simp only [Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hdecomp, Int.fract_intCast_add, Int.fract_eq_self.mpr]
    exact ⟨(ha.trans_lt (hstay i hi).1).le, (hstay i hi).2.trans_le hb⟩
  have hinc (r i j : ℕ) (hrm : r ≤ m)
      (hr : r ≤ k - 1 ∨ m - (k - 1) ≤ r) (hi : i < e) (hj : j < e) :
      ⌊((start + i * m + r : ℕ) : ℝ) * alpha⌋ -
          ⌊((start + i * m : ℕ) : ℝ) * alpha⌋ =
        ⌊((start + j * m + r : ℕ) : ℝ) * alpha⌋ -
          ⌊((start + j * m : ℕ) : ℝ) * alpha⌋ := by
    by_cases hr0 : r = 0
    · simp [hr0]
    have htest : (1 - Int.fract ((r : ℝ) * alpha) ≤ x + (i : ℝ) * d) ↔
        (1 - Int.fract ((r : ℝ) * alpha) ≤ x + (j : ℝ) * d) := by
      rcases hcuts r (Nat.pos_of_ne_zero hr0) hrm hr with hc | hc
      · exact iff_of_true (hc.trans (hstay i hi).1.le) (hc.trans (hstay j hj).1.le)
      · exact iff_of_false (not_le.mpr ((hstay i hi).2.trans_le hc))
          (not_le.mpr ((hstay j hj).2.trans_le hc))
    have heq (s : ℕ) : (((s + r : ℕ) : ℝ) * alpha) =
        (s : ℝ) * alpha + (r : ℝ) * alpha := by push_cast; ring
    rw [heq, heq, floor_add_sub_floor, floor_add_sub_floor,
      floor_fract_add_indicator, floor_fract_add_indicator, hphase i hi, hphase j hj]
    by_cases hc : 1 - Int.fract ((r : ℝ) * alpha) ≤ x + (i : ℝ) * d
    · rw [if_pos hc, if_pos (htest.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (htest.mpr h))]
  have hletter (r i j : ℕ) (hrm : r < m)
      (hr : r + 1 ≤ k - 1 ∨ m - (k - 1) ≤ r) (hi : i < e) (hj : j < e) :
      lowerMechanicalWord alpha 0 (start + i * m + r) =
        lowerMechanicalWord alpha 0 (start + j * m + r) := by
    have hr' : r ≤ k - 1 ∨ m - (k - 1) ≤ r := by omega
    have hr'' : r + 1 ≤ k - 1 ∨ m - (k - 1) ≤ r + 1 := by omega
    have hbase := hinc r i j hrm.le hr' hi hj
    have hnext := hinc (r + 1) i j (by omega) hr'' hi hj
    have hletters : lowerMechanicalLetter alpha 0 (start + i * m + r) =
        lowerMechanicalLetter alpha 0 (start + j * m + r) := by
      simp only [lowerMechanicalLetter, zero_add]
      rw [show start + i * m + r + 1 = start + i * m + (r + 1) by omega,
        show start + j * m + r + 1 = start + j * m + (r + 1) by omega]
      omega
    simp only [lowerMechanicalWord, hletters]
  have hwindow (s : ℕ) : (lowerMechanicalFactor alpha 0 m s).count true =
      lowerMechanicalWindowTrueCount alpha 0 s m := by
    have hh : ∀ n : ℕ, (lowerMechanicalFactor alpha 0 n s).count true =
        lowerMechanicalWindowTrueCount alpha 0 s n := by
      intro n
      induction n with
      | zero => simp [lowerMechanicalFactor, lowerMechanicalWindowTrueCount]
      | succ n ih =>
        unfold lowerMechanicalFactor
        rw [List.ofFn_succ', List.concat_eq_append]
        change ((lowerMechanicalFactor alpha 0 n s) ++
          [lowerMechanicalWord alpha 0 (s + n)]).count true = _
        rw [List.count_append, List.count_singleton, ih]
        simp only [lowerMechanicalWindowTrueCount, Finset.range_add_one, Finset.filter_insert]
        by_cases hw : lowerMechanicalWord alpha 0 (s + n) = true
        · simp [hw, Finset.mem_filter, Finset.mem_range]
        · simp [hw]
    exact hh m
  have hzero : lowerMechanicalFactorSet alpha 0 0 = {[]} := by
    ext w
    simp only [mem_lowerMechanicalFactorSet, Finset.mem_singleton]
    constructor
    · rintro ⟨s, rfl⟩; simp [lowerMechanicalFactor]
    · rintro rfl; exact ⟨0, by simp [lowerMechanicalFactor]⟩
  have hocc (s : ℕ) (b : Bool) :
      occurrences (lowerMechanicalFactor alpha 0 m s) [b] =
        (lowerMechanicalFactor alpha 0 m s).count b := by
    have hh := mechanical_extension_mass alpha 0 m s 0 b
    simpa only [hzero, Finset.sum_singleton, List.nil_append, List.drop_zero] using hh
  have htotal (w : List Bool) : w.count true + w.count false = w.length := by
    induction w with
    | nil => simp
    | cons b w ih => cases b <;> simp only [List.count_cons, List.length_cons] <;>
        norm_num <;> omega
  refine ⟨start, ?_⟩
  intro i j hi hj
  apply mechanical_kabelian_of_boundaries h0 h1 hirr k m (start + i * m) (start + j * m)
  · have htrue : (lowerMechanicalFactor alpha 0 m (start + i * m)).count true =
        (lowerMechanicalFactor alpha 0 m (start + j * m)).count true := by
      rw [hwindow, hwindow, ← Nat.cast_inj (R := ℤ),
        lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1,
        lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1]
      simpa only [zero_add] using hinc m i j le_rfl (Or.inr (Nat.sub_le _ _)) hi hj
    intro z hz hz1
    obtain ⟨letter, rfl⟩ := List.length_eq_one_iff.mp (show z.length = 1 by omega)
    rw [hocc, hocc]
    cases letter
    · have hu := htotal (lowerMechanicalFactor alpha 0 m (start + i * m))
      have hv := htotal (lowerMechanicalFactor alpha 0 m (start + j * m))
      have hlength (s : ℕ) : (lowerMechanicalFactor alpha 0 m s).length = m := by
        simp only [lowerMechanicalFactor, List.length_ofFn]
      rw [hlength] at hu hv
      omega
    · exact htrue
  · apply List.ext_getElem
    · simp [lowerMechanicalFactor]
    · intro r hr hs
      have hrk : r < k - 1 := by simpa [lowerMechanicalFactor, Nat.min_eq_left hmk] using hr
      simp only [List.getElem_take, lowerMechanicalFactor, List.getElem_ofFn]
      exact hletter r i j (hrk.trans_le hmk) (Or.inl (by omega)) hi hj
  · apply List.ext_getElem
    · simp [lowerMechanicalFactor]
    · intro r hr hs
      have hrm : r + (m - (k - 1)) < m := by
        simp only [List.length_drop, lowerMechanicalFactor, List.length_ofFn] at hr
        omega
      simp only [List.getElem_drop, lowerMechanicalFactor, List.getElem_ofFn]
      simpa only [Nat.add_assoc, Nat.add_comm r (m - (k - 1))] using
        hletter (r + (m - (k - 1))) i j hrm (Or.inr (by omega)) hi hj

end D5.S1.Words.KAbelianLagrange
