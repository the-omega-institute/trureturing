/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePowerSpan
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePowerSpan
   mirror-E: none(waiver:mechanical-power-no-wrap)
   anchors: []
   utility: none
   digest: Equal block counts force an affine progression of all mechanical endpoint phases. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs D5.S1.Words.Mechanical

/-- A power has a single integer floor increment, including its final endpoint.
The progression is in ordinary coordinates, so its total displacement is less than one. -/
theorem kabelian_power_phase_span {alpha : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha < 1)
    {k m e start : ℕ} (hk : 1 ≤ k) (he : 0 < e)
    (hp : IsKAbelianPower alpha k m e start) :
    ∃ c : ℤ,
      (∀ i ≤ e, Int.fract (((start + i * m : ℕ) : ℝ) * alpha) =
        Int.fract ((start : ℝ) * alpha) + (i : ℝ) * ((m : ℝ) * alpha - c)) ∧
      (e : ℝ) * |(m : ℝ) * alpha - c| < 1 := by
  classical
  have hocc (s : ℕ) : occurrences (lowerMechanicalFactor alpha 0 m s) [true] =
      lowerMechanicalWindowTrueCount alpha 0 s m := by
    have hslice (t : ℕ) (ht : t < m) :
        ((lowerMechanicalFactor alpha 0 m s).drop t).take 1 =
          [lowerMechanicalWord alpha 0 (s + t)] := by
      apply List.ext_getElem
      · simp [lowerMechanicalFactor, Nat.min_eq_left (show 1 ≤ m - t by omega)]
      · intro a ha hb
        have ha0 : a = 0 := by simp at hb; omega
        subst a
        simp [lowerMechanicalFactor]
    have hpred (t : ℕ) :
        (t + [true].length ≤ (lowerMechanicalFactor alpha 0 m s).length ∧
          ((lowerMechanicalFactor alpha 0 m s).drop t).take [true].length = [true]) ↔
        t < m ∧ lowerMechanicalWord alpha 0 (s + t) = true := by
      simp only [List.length_singleton,
        show (lowerMechanicalFactor alpha 0 m s).length = m by simp [lowerMechanicalFactor]]
      constructor
      · rintro ⟨ht, hw⟩
        have ht' : t < m := by omega
        have hh := hslice t ht'
        rw [hw] at hh
        exact ⟨ht', by simpa using hh.symm⟩
      · rintro ⟨ht, hw⟩
        exact ⟨by omega, by simpa [hw] using hslice t ht⟩
    unfold occurrences lowerMechanicalWindowTrueCount
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    simp only [List.toFinset_filter, List.toFinset_range, decide_eq_true_eq]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [hpred]
    simp only [show (lowerMechanicalFactor alpha 0 m s).length = m by
      simp [lowerMechanicalFactor]]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by omega, h⟩
  let c : ℤ := lowerMechanicalWindowTrueCount alpha 0 start m
  let f (i : ℕ) : ℤ := ⌊((start + i * m : ℕ) : ℝ) * alpha⌋
  have hstep (i : ℕ) (hi : i < e) : f (i + 1) - f i = c := by
    have hc := hp i 0 hi he
    have hc' := hc [true] (by simp) (by simpa using hk)
    rw [hocc, hocc] at hc'
    simp only [Nat.zero_mul, Nat.add_zero] at hc'
    have hf := lowerMechanicalWindowTrueCount_eq_floor (rho := 0) h0 h1 (start + i * m) m
    simp only [zero_add] at hf
    rw [hc'] at hf
    simpa only [f, c, show start + i * m + m = start + (i + 1) * m by ring]
      using hf.symm
  have hf (i : ℕ) (hi : i ≤ e) : f i = f 0 + (i : ℤ) * c := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hs := hstep i (by omega)
      have hh := ih (by omega)
      calc
        f (i + 1) = f i + c := by omega
        _ = f 0 + ((i + 1 : ℕ) : ℤ) * c := by rw [hh]; push_cast; ring
  have hphase (i : ℕ) (hi : i ≤ e) :
      Int.fract (((start + i * m : ℕ) : ℝ) * alpha) =
        Int.fract ((start : ℝ) * alpha) + (i : ℝ) * ((m : ℝ) * alpha - c) := by
    have hh : ((f i : ℤ) : ℝ) = (f 0 : ℝ) + (i : ℝ) * (c : ℝ) := by
      exact_mod_cast hf i hi
    change _ - (f i : ℝ) = _ - ⌊(start : ℝ) * alpha⌋ + _
    rw [hh]
    simp only [f, Nat.zero_mul, Nat.add_zero]
    push_cast
    ring
  refine ⟨c, hphase, ?_⟩
  have hd : |Int.fract (((start + e * m : ℕ) : ℝ) * alpha) -
      Int.fract ((start : ℝ) * alpha)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [Int.fract_nonneg (((start + e * m : ℕ) : ℝ) * alpha),
      Int.fract_lt_one (((start + e * m : ℕ) : ℝ) * alpha),
      Int.fract_nonneg ((start : ℝ) * alpha), Int.fract_lt_one ((start : ℝ) * alpha)]
  rw [hphase e le_rfl, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg e)] at hd
  exact hd

end D5.S1.Words.KAbelianLagrange
