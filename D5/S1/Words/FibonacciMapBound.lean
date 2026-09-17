/- GID: D5/S1/Words/FibonacciMapBound
   generality: I
   mirror-B: D5/B/S1/Words/FibonacciMapBound
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Bound monochromatic progressions in the infinite Fibonacci word. -/

import D5.S1.Words.Mechanical.MechanicalGoldenBridge
import D5.S1.Depth.GoldenHurwitzBound
import D5.S1.Phase.ThreeGap.Returns

namespace D5.S1.Words

open D5.S1.Dynamics
open D5.S1.Words.Mechanical

/-- The maximum positive length attained by a monochromatic arithmetic progression
of difference `d` in the infinite zero-indexed Fibonacci word. -/
noncomputable def goldenMAPMaximum (d : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ i : ℕ, ∃ symbol : Bool,
    0 < n ∧ ∀ k < n, goldenWord (i + k * d) = symbol}

set_option maxHeartbeats 2000000 in
-- Localizing every auxiliary argument combines their elaboration cost in this declaration.
/-- Joshi and Rust, Conjecture 4.24, for the global maximum over all starts
and both letters of the infinite Fibonacci word. -/
theorem result (d : ℕ) (hd : 0 < d) :
    ((goldenMAPMaximum d - 1 : ℕ) : ℝ) / (d : ℝ) <
      Real.sqrt 5 / Real.goldenRatio := by
  have golden_word_phase (i : ℕ) :
      goldenWord i = true ↔
        1 - goldenMechanicalSlope ≤ goldenFractionalPart (i + 1) := by
    rw [← lowerMechanicalWord_golden, lowerMechanicalWord_eq_true_iff,
      lowerMechanicalLetter_golden, golden_mechanical_letter_eq_one_iff]
    exact and_iff_left (Int.fract_lt_one _)
  have golden_word_phase_strict (i : ℕ) :
      goldenWord i = true ↔
        1 - goldenMechanicalSlope < goldenFractionalPart (i + 1) := by
    have hboundary : 1 - goldenMechanicalSlope = 2 - Real.goldenRatio := by
      rw [goldenMechanicalSlope, Real.inv_goldenRatio, Real.goldenConj,
        Real.goldenRatio]
      ring
    have hne : goldenFractionalPart (i + 1) ≠
        1 - goldenMechanicalSlope := by
      intro heq
      rw [goldenFractionalPart, Int.fract, hboundary] at heq
      have hinteger :
          ((i + 2 : ℕ) : ℝ) * Real.goldenRatio =
            (((⌊((i + 1 : ℕ) : ℝ) * Real.goldenRatio⌋ + 2 : ℤ) : ℝ)) := by
        push_cast at heq ⊢
        nlinarith
      exact (Real.goldenRatio_irrational.natCast_mul
        (by omega : i + 2 ≠ 0)).ne_int _ hinteger
    constructor
    · intro h
      exact lt_of_le_of_ne ((golden_word_phase i).mp h) hne.symm
    · intro h
      exact (golden_word_phase i).mpr h.le
  have golden_phase_step (i d : ℕ) :
      goldenFractionalPart (i + d) =
        Int.fract (goldenFractionalPart i +
          Int.fract ((d : ℝ) * Real.goldenRatio)) := by
    rw [goldenFractionalPart, goldenFractionalPart,
      ThreeGap.fract_add_fract_eq]
    congr 1
    push_cast
    ring
  have interval_run_bound {lo hi step : ℝ} {x : ℕ → ℝ} {length : ℕ}
      (hstep : 0 < step) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
      (hgap : step < 1 - (hi - lo))
      (hmem : ∀ k < length, lo ≤ x k ∧ x k < hi)
      (horbit : ∀ k, k + 1 < length → x (k + 1) = Int.fract (x k + step))
      (hpos : 0 < length) : (length - 1 : ℕ) * step < hi - lo := by
    have hnext (k : ℕ) (hk : k + 1 < length) : x (k + 1) = x k + step := by
      have hx := hmem k (by omega)
      have hy := hmem (k + 1) hk
      by_cases hw : x k + step < 1
      · rw [horbit k hk, Int.fract_eq_self.mpr ⟨by linarith, hw⟩]
      · have hlt : x k + step < 2 := by linarith
        have hf : ⌊x k + step⌋ = (1 : ℤ) :=
          Int.floor_eq_iff.mpr ⟨by exact_mod_cast (show (1 : ℝ) ≤ x k + step by linarith),
            by exact_mod_cast (show x k + step < (1 : ℝ) + 1 by linarith)⟩
        have hy' : x (k + 1) = x k + step - 1 := by
          rw [horbit k hk, Int.fract, hf]
          norm_num
        linarith
    have hlinear (k : ℕ) (hk : k < length) : x k = x 0 + (k : ℝ) * step := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [hnext k (by simpa using hk), ih (by omega)]
          push_cast
          ring
    have hlast : length - 1 < length := by omega
    have hz := hmem 0 hpos
    have he := hmem (length - 1) hlast
    rw [hlinear _ hlast] at he
    nlinarith
  have interval_run_bound_reverse {lo hi step : ℝ} {x : ℕ → ℝ}
      {length : ℕ} (hstep : 0 < step) (hstep_lt : step < 1)
      (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
      (hgap : 1 - step < 1 - (hi - lo))
      (hmem : ∀ k < length, lo ≤ x k ∧ x k < hi)
      (horbit : ∀ k, k + 1 < length → x (k + 1) = Int.fract (x k + step))
      (hpos : 0 < length) : (length - 1 : ℕ) * (1 - step) < hi - lo := by
    let backwards : ℕ → ℝ := fun k => x (length - 1 - k)
    have hbackmem (k : ℕ) (hk : k < length) :
        lo ≤ backwards k ∧ backwards k < hi :=
      hmem _ (by omega)
    have hbackstep (k : ℕ) (hk : k + 1 < length) :
        backwards (k + 1) = Int.fract (backwards k + (1 - step)) := by
      let j := length - 1 - (k + 1)
      have hj : length - 1 - k = j + 1 := by dsimp [j]; omega
      have hfj : 0 ≤ x j ∧ x j < 1 := by
        have h := hmem j (by dsimp [j]; omega)
        exact ⟨hlo.trans h.1, h.2.trans_le hhi⟩
      have hdelta : Int.fract (1 - step) = 1 - step :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hf := ThreeGap.fract_add_fract_eq (x j + step) (1 - step)
      rw [← horbit j (by dsimp [j]; omega), hdelta,
        show x j + step + (1 - step) = x j + 1 by ring,
        Int.fract_add_one, Int.fract_eq_self.mpr hfj] at hf
      dsimp [backwards]
      rw [hj]
      exact hf.symm
    exact interval_run_bound (by linarith) hlo hhi hgap hbackmem hbackstep hpos
  have paired_rotation_bound {lo step : ℝ} {x : ℕ → ℝ} {length : ℕ}
      (_hlo : 0 < lo) (hthird : 1 < 3 * lo)
      (hstep : lo ≤ step) (hhalf : step < 1 / 2)
      (hmem : ∀ k < length, lo ≤ x k ∧ x k < 1)
      (horbit : ∀ k, k + 1 < length → x (k + 1) = Int.fract (x k + step))
      (hpos : 0 < length) :
      (((length - 1) / 2 : ℕ) : ℝ) * (1 - 2 * step) < 1 - lo - step := by
    let delta := 1 - 2 * step
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have htwo (k : ℕ) (hk : k + 2 < length) : x (k + 2) = x k - delta := by
      have h1 := horbit k (by omega)
      have h2 := horbit (k + 1) (by omega)
      rw [h1] at h2
      have hstep_fract : Int.fract step = step :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hcombine : Int.fract (Int.fract (x k + step) + step) =
          Int.fract (x k + step + step) := by
        simpa only [hstep_fract] using ThreeGap.fract_add_fract_eq (x k + step) step
      rw [hcombine] at h2
      have harg : 1 ≤ x k + step + step ∧ x k + step + step < 2 := by
        have hx := hmem k (by omega)
        constructor <;> linarith
      have hfloor : ⌊x k + step + step⌋ = (1 : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by exact_mod_cast harg.1,
          by exact_mod_cast (show x k + step + step < (1 : ℝ) + 1 by linarith [harg.2])⟩
      rw [Int.fract, hfloor] at h2
      push_cast at h2
      dsimp [delta]
      linarith
    have heven (m : ℕ) (hm : 2 * m < length) :
        x (2 * m) = x 0 - (m : ℝ) * delta := by
      induction m with
      | zero => simp
      | succ m ih =>
          have hm' : 2 * m < length := by omega
          have hnext := htwo (2 * m) (by omega)
          rw [show 2 * (m + 1) = 2 * m + 2 by omega, hnext, ih hm']
          push_cast
          ring
    have hodd (m : ℕ) (hm : 2 * m + 1 < length) :
        x (2 * m + 1) = x 1 - (m : ℝ) * delta := by
      induction m with
      | zero => simp
      | succ m ih =>
          have hm' : 2 * m + 1 < length := by omega
          have hnext := htwo (2 * m + 1) (by omega)
          rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
            hnext, ih hm']
          push_cast
          ring
    let m := (length - 1) / 2
    have hm : 2 * m < length := by dsimp [m]; omega
    have hdelta_m := heven m hm
    have hzero := hmem 0 hpos
    by_cases hlength : length = 1
    · subst length
      norm_num [m]
      linarith
    have hone := hmem 1 (by omega)
    have hfirst := horbit 0 (by omega)
    by_cases hnwrap : x 0 + step < 1
    · have hlinear : x 1 = x 0 + step := by
        rw [hfirst, Int.fract_eq_self.mpr ⟨by linarith [hzero.1], hnwrap⟩]
      have hlast := (hmem (2 * m) hm).1
      rw [hdelta_m] at hlast
      linarith
    · have hlt2 : x 0 + step < 2 := by linarith [hzero.2, hhalf]
      have hfloor : ⌊x 0 + step⌋ = (1 : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by exact_mod_cast (show (1 : ℝ) ≤ x 0 + step by linarith),
          by exact_mod_cast (show x 0 + step < (1 : ℝ) + 1 by linarith)⟩
      have hone_lt : x 1 < step := by
        rw [hfirst, Int.fract, hfloor]
        norm_num
        linarith [hzero.2]
      have hlast : lo + step ≤ x (2 * m) := by
        by_cases hmzero : m = 0
        · have h0 : x (2 * m) = x 0 := by simp [hmzero]
          have hfirst_lo : lo ≤ x 1 := hone.1
          rw [hfirst, Int.fract, hfloor] at hfirst_lo
          norm_num at hfirst_lo
          rw [h0]
          linarith [hhalf]
        · have hodd_idx : 2 * (m - 1) + 1 < length := by omega
          have hprev_lt : x (2 * (m - 1) + 1) < step := by
            rw [hodd (m - 1) hodd_idx]
            have hmnonneg : (0 : ℝ) ≤ (m - 1 : ℕ) * delta := by positivity
            linarith
          have hprev := hmem (2 * (m - 1) + 1) hodd_idx
          have hprev_step := horbit (2 * (m - 1) + 1) (by omega)
          have hnow : x (2 * m) = x (2 * (m - 1) + 1) + step := by
            calc
              x (2 * m) = x (2 * (m - 1) + 1 + 1) := by congr 1; omega
              _ = Int.fract (x (2 * (m - 1) + 1) + step) := hprev_step
              _ = x (2 * (m - 1) + 1) + step :=
                Int.fract_eq_self.mpr
                  ⟨by linarith [hprev.1], by linarith [hprev_lt, hhalf]⟩
          linarith [hprev.1]
      rw [hdelta_m] at hlast
      linarith [hzero.2]
  have paired_rotation_bound_reverse {lo step : ℝ} {x : ℕ → ℝ}
      {length : ℕ} (hlo : 0 < lo) (hthird : 1 < 3 * lo)
      (_hstep : 0 < step) (_hstep_lt : step < 1)
      (hlarge : lo ≤ 1 - step) (hhalf : 1 - step < 1 / 2)
      (hmem : ∀ k < length, lo ≤ x k ∧ x k < 1)
      (horbit : ∀ k, k + 1 < length → x (k + 1) = Int.fract (x k + step))
      (hpos : 0 < length) :
      (((length - 1) / 2 : ℕ) : ℝ) * (1 - 2 * (1 - step)) <
        1 - lo - (1 - step) := by
    let backwards : ℕ → ℝ := fun k => x (length - 1 - k)
    have hbackmem (k : ℕ) (hk : k < length) :
        lo ≤ backwards k ∧ backwards k < 1 := hmem _ (by omega)
    have hbackstep (k : ℕ) (hk : k + 1 < length) :
        backwards (k + 1) = Int.fract (backwards k + (1 - step)) := by
      let j := length - 1 - (k + 1)
      have hj : length - 1 - k = j + 1 := by dsimp [j]; omega
      have hfj : 0 ≤ x j ∧ x j < 1 := by
        have h := hmem j (by dsimp [j]; omega)
        exact ⟨le_trans hlo.le h.1, h.2⟩
      have hdelta : Int.fract (1 - step) = 1 - step :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hf := ThreeGap.fract_add_fract_eq (x j + step) (1 - step)
      rw [← horbit j (by dsimp [j]; omega), hdelta,
        show x j + step + (1 - step) = x j + 1 by ring,
        Int.fract_add_one, Int.fract_eq_self.mpr hfj] at hf
      dsimp [backwards]
      rw [hj]
      exact hf.symm
    exact paired_rotation_bound hlo hthird hlarge hhalf hbackmem hbackstep hpos
  have golden_map_right_small (i d length : ℕ) (symbol : Bool)
      (hpos : 0 < length)
      (hsmall : 0 < Int.fract ((d : ℝ) * Real.goldenRatio) ∧
        Int.fract ((d : ℝ) * Real.goldenRatio) <
          1 - goldenMechanicalSlope)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      (length - 1 : ℕ) * Int.fract ((d : ℝ) * Real.goldenRatio) <
        goldenMechanicalSlope := by
    let step := Int.fract ((d : ℝ) * Real.goldenRatio)
    let phase : ℕ → ℝ := fun k => goldenFractionalPart (i + k * d + 1)
    have hslope_pos : 0 < goldenMechanicalSlope := inv_pos.mpr Real.goldenRatio_pos
    have hslope_lt : goldenMechanicalSlope < 1 :=
      inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    have hslope_half : 1 - goldenMechanicalSlope ≤ goldenMechanicalSlope := by
      have hquad : goldenMechanicalSlope ^ 2 + goldenMechanicalSlope = 1 := by
        simpa [goldenMechanicalSlope] using
          (show Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 by
            rw [Real.inv_goldenRatio]
            nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj])
      nlinarith [sq_nonneg (goldenMechanicalSlope - 1 / 2)]
    have horbit (k : ℕ) : phase (k + 1) = Int.fract (phase k + step) := by
      simpa [phase, step, Nat.add_mul, add_assoc, add_left_comm, add_comm] using
        golden_phase_step (i + k * d + 1) d
    by_cases hsymbol : symbol = true
    · have hmem (k : ℕ) (hk : k < length) :
          1 - goldenMechanicalSlope ≤ phase k ∧ phase k < 1 := by
        have hw : goldenWord (i + k * d) = true := by simpa [hsymbol] using hmap k hk
        exact ⟨((golden_word_phase_strict _).mp hw).le, Int.fract_lt_one _⟩
      have hbound := interval_run_bound hsmall.1 (by linarith : 0 ≤ 1 - goldenMechanicalSlope)
        (le_refl (1 : ℝ)) (by nlinarith [hsmall.2])
        hmem (fun k _ => horbit k) hpos
      linarith
    · have hmem (k : ℕ) (hk : k < length) :
          0 ≤ phase k ∧ phase k < 1 - goldenMechanicalSlope := by
        have hw : goldenWord (i + k * d) = false := by
          cases symbol with
          | false => exact hmap k hk
          | true => exact (hsymbol rfl).elim
        exact ⟨Int.fract_nonneg _, lt_of_not_ge (fun h => by
          have ht := (golden_word_phase _).mpr h
          rw [hw] at ht
          cases ht)⟩
      have hbound := interval_run_bound hsmall.1 (le_refl (0 : ℝ))
        (by linarith : 1 - goldenMechanicalSlope ≤ 1)
        (by linarith [hsmall.2, hslope_half]) hmem (fun k _ => horbit k) hpos
      linarith only [hbound, hslope_half]
  have golden_map_left_small (i d length : ℕ) (symbol : Bool)
      (hpos : 0 < length)
      (hsmall : 0 < 1 - Int.fract ((d : ℝ) * Real.goldenRatio) ∧
        1 - Int.fract ((d : ℝ) * Real.goldenRatio) <
          1 - goldenMechanicalSlope)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      (length - 1 : ℕ) * (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) <
        goldenMechanicalSlope := by
    let step := Int.fract ((d : ℝ) * Real.goldenRatio)
    let phase : ℕ → ℝ := fun k => goldenFractionalPart (i + k * d + 1)
    have hslope_pos : 0 < goldenMechanicalSlope := inv_pos.mpr Real.goldenRatio_pos
    have hstep_pos : 0 < step := by
      dsimp [step]
      linarith [hsmall.2, hslope_pos]
    have hstep_lt : step < 1 := Int.fract_lt_one _
    have hslope_lt : goldenMechanicalSlope < 1 :=
      inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    have hslope_half : 1 - goldenMechanicalSlope ≤ goldenMechanicalSlope := by
      have hquad : goldenMechanicalSlope ^ 2 + goldenMechanicalSlope = 1 := by
        simpa [goldenMechanicalSlope] using
          (show Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 by
            rw [Real.inv_goldenRatio]
            nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj])
      nlinarith [sq_nonneg (goldenMechanicalSlope - 1 / 2)]
    have horbit (k : ℕ) : phase (k + 1) = Int.fract (phase k + step) := by
      simpa [phase, step, Nat.add_mul, add_assoc, add_left_comm, add_comm] using
        golden_phase_step (i + k * d + 1) d
    by_cases hsymbol : symbol = true
    · have hmem (k : ℕ) (hk : k < length) :
          1 - goldenMechanicalSlope ≤ phase k ∧ phase k < 1 := by
        have hw : goldenWord (i + k * d) = true := by simpa [hsymbol] using hmap k hk
        exact ⟨((golden_word_phase_strict _).mp hw).le, Int.fract_lt_one _⟩
      have hbound := interval_run_bound_reverse hstep_pos hstep_lt
        (by linarith : 0 ≤ 1 - goldenMechanicalSlope) (le_refl (1 : ℝ))
        (by nlinarith [hsmall.2]) hmem (fun k _ => horbit k) hpos
      linarith
    · have hmem (k : ℕ) (hk : k < length) :
          0 ≤ phase k ∧ phase k < 1 - goldenMechanicalSlope := by
        have hw : goldenWord (i + k * d) = false := by
          cases symbol with
          | false => exact hmap k hk
          | true => exact (hsymbol rfl).elim
        exact ⟨Int.fract_nonneg _, lt_of_not_ge (fun h => by
          have ht := (golden_word_phase _).mpr h
          rw [hw] at ht
          cases ht)⟩
      have hbound := interval_run_bound_reverse hstep_pos hstep_lt
        (le_refl (0 : ℝ)) (by linarith : 1 - goldenMechanicalSlope ≤ 1)
        (by linarith [hsmall.2, hslope_half]) hmem (fun k _ => horbit k) hpos
      linarith only [hbound, hslope_half]
  let goldenStepDistance (d : ℕ) : ℝ :=
    min (Int.fract ((d : ℝ) * Real.goldenRatio))
      (1 - Int.fract ((d : ℝ) * Real.goldenRatio))
  have golden_map_small_step (i d length : ℕ) (symbol : Bool)
      (hd : 0 < d) (hpos : 0 < length)
      (hsmall : goldenStepDistance d < 1 - goldenMechanicalSlope)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      (length - 1 : ℕ) * goldenStepDistance d < goldenMechanicalSlope := by
    have hspos : 0 < Int.fract ((d : ℝ) * Real.goldenRatio) := by
      have hnonneg := Int.fract_nonneg ((d : ℝ) * Real.goldenRatio)
      have hne : Int.fract ((d : ℝ) * Real.goldenRatio) ≠ 0 := by
        rw [Int.fract_ne_zero_iff]
        rintro ⟨z, hz⟩
        exact (Real.goldenRatio_irrational.natCast_mul (by omega : d ≠ 0)).ne_int z hz.symm
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    rcases le_total (Int.fract ((d : ℝ) * Real.goldenRatio))
        (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) with hright | hleft
    · change min (Int.fract ((d : ℝ) * Real.goldenRatio))
          (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) < _ at hsmall
      change (length - 1 : ℕ) * min (Int.fract ((d : ℝ) * Real.goldenRatio))
          (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) < _
      rw [min_eq_left hright] at hsmall ⊢
      exact golden_map_right_small i d length symbol hpos ⟨hspos, hsmall⟩ hmap
    · change min (Int.fract ((d : ℝ) * Real.goldenRatio))
          (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) < _ at hsmall
      change (length - 1 : ℕ) * min (Int.fract ((d : ℝ) * Real.goldenRatio))
          (1 - Int.fract ((d : ℝ) * Real.goldenRatio)) < _
      rw [min_eq_right hleft] at hsmall ⊢
      exact golden_map_left_small i d length symbol hpos
        ⟨by linarith [Int.fract_lt_one ((d : ℝ) * Real.goldenRatio)], hsmall⟩ hmap
  have golden_window_constants :
      (1 : ℝ) / 3 < 1 - goldenMechanicalSlope ∧
        1 - goldenMechanicalSlope < 1 / 2 := by
    have hr : 0 < goldenMechanicalSlope := inv_pos.mpr Real.goldenRatio_pos
    have hquad : goldenMechanicalSlope ^ 2 + goldenMechanicalSlope = 1 := by
      simpa [goldenMechanicalSlope] using
        (show Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 by
          rw [Real.inv_goldenRatio]
          nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj])
    constructor <;> nlinarith [sq_nonneg (goldenMechanicalSlope - 1 / 2),
      sq_nonneg (goldenMechanicalSlope - 2 / 3)]
  have golden_map_large_step (i d length : ℕ) (symbol : Bool)
      (hd : 0 < d) (hpos : 0 < length)
      (hlarge : 1 - goldenMechanicalSlope ≤ goldenStepDistance d)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      (((length - 1) / 2 : ℕ) : ℝ) * (1 - 2 * goldenStepDistance d) <
        goldenMechanicalSlope - goldenStepDistance d := by
    let step := Int.fract ((d : ℝ) * Real.goldenRatio)
    let lo := 1 - goldenMechanicalSlope
    let phase : ℕ → ℝ := fun k => goldenFractionalPart (i + k * d + 1)
    have hlo : 0 < lo := by
      dsimp [lo]
      linarith [golden_window_constants.1]
    have hthird : 1 < 3 * lo := by
      dsimp [lo]
      linarith [golden_window_constants.1]
    have hstep_lo : lo ≤ step := by
      have h := (le_min_iff.mp hlarge).1
      exact h
    have hstep_hi : step ≤ 1 - lo := by
      have h := (le_min_iff.mp hlarge).2
      linarith
    have horbit (k : ℕ) : phase (k + 1) = Int.fract (phase k + step) := by
      simpa [phase, step, Nat.add_mul, add_assoc, add_left_comm, add_comm] using
        golden_phase_step (i + k * d + 1) d
    have hhalf_ne : step ≠ 1 / 2 := by
      intro heq
      have htwice : Int.fract (((2 * d : ℕ) : ℝ) * Real.goldenRatio) = 0 := by
        have hadd := ThreeGap.fract_add_fract_eq
          ((d : ℝ) * Real.goldenRatio) ((d : ℝ) * Real.goldenRatio)
        have hcast : (((2 * d : ℕ) : ℝ) * Real.goldenRatio) =
            (d : ℝ) * Real.goldenRatio + (d : ℝ) * Real.goldenRatio := by
          push_cast
          ring
        rw [hcast, ← hadd, show Int.fract ((d : ℝ) * Real.goldenRatio) =
          (1 / 2 : ℝ) from heq]
        norm_num
      have hne : Int.fract (((2 * d : ℕ) : ℝ) * Real.goldenRatio) ≠ 0 := by
        rw [Int.fract_ne_zero_iff]
        rintro ⟨z, hz⟩
        exact (Real.goldenRatio_irrational.natCast_mul (by omega : 2 * d ≠ 0)).ne_int z hz.symm
      exact hne htwice
    have hslope_half : (1 : ℝ) / 2 < goldenMechanicalSlope := by
      linarith [golden_window_constants.2]
    by_cases hsingle : length = 1
    · subst length
      simp only [Nat.reduceSubDiff, Nat.zero_div, Nat.cast_zero, zero_mul]
      have hstep_max : goldenStepDistance d ≤ 1 / 2 := by
        change min step (1 - step) ≤ 1 / 2
        linarith [min_le_left step (1 - step), min_le_right step (1 - step)]
      linarith
    have htrue : symbol = true := by
      by_contra hb
      have hbfalse : symbol = false := by
        cases symbol with
        | false => rfl
        | true => exact (hb rfl).elim
      subst symbol
      have hword0 : goldenWord i = false := by
        simpa only [Nat.zero_mul, Nat.add_zero] using hmap 0 (by omega)
      have hword1 : goldenWord (i + d) = false := by
        simpa only [Nat.one_mul] using hmap 1 (by omega)
      have hphase0 : 0 ≤ phase 0 ∧ phase 0 < lo := by
        refine ⟨Int.fract_nonneg _, lt_of_not_ge ?_⟩
        intro h
        have ht := (golden_word_phase i).mpr (by simpa [phase, lo] using h)
        rw [hword0] at ht
        cases ht
      have hphase1 : phase 1 < lo := by
        apply lt_of_not_ge
        intro h
        have ht := (golden_word_phase (i + d)).mpr (by simpa [phase, lo] using h)
        rw [hword1] at ht
        cases ht
      have hnowrap : phase 0 + step < 1 := by linarith [hphase0.2, hstep_hi]
      have hshift : phase 1 = phase 0 + step := by
        rw [horbit 0, Int.fract_eq_self.mpr ⟨by linarith, hnowrap⟩]
      linarith [hstep_lo]
    have hmem (k : ℕ) (hk : k < length) : lo ≤ phase k ∧ phase k < 1 := by
      have hw : goldenWord (i + k * d) = true := by simpa [htrue] using hmap k hk
      exact ⟨((golden_word_phase_strict _).mp hw).le, Int.fract_lt_one _⟩
    rcases lt_or_gt_of_ne hhalf_ne with hright | hleft
    · have hmin : goldenStepDistance d = step := by
        dsimp [goldenStepDistance, step]
        exact min_eq_left (by linarith)
      rw [hmin]
      have hbound := paired_rotation_bound hlo hthird hstep_lo hright
        hmem (fun k _ => horbit k) hpos
      change (((length - 1) / 2 : ℕ) : ℝ) * (1 - 2 * step) <
        1 - lo - step at hbound
      dsimp [lo] at hbound
      linarith
    · have hmin : goldenStepDistance d = 1 - step := by
        dsimp [goldenStepDistance, step]
        exact min_eq_right (by linarith)
      rw [hmin]
      have hbound := paired_rotation_bound_reverse hlo hthird
        (by linarith [hstep_lo, hlo]) (by linarith [hstep_hi, hlo])
        (by linarith [hstep_hi]) (by linarith) hmem (fun k _ => horbit k) hpos
      change (((length - 1) / 2 : ℕ) : ℝ) * (1 - 2 * (1 - step)) <
        1 - lo - (1 - step) at hbound
      dsimp [lo] at hbound
      linarith
  have golden_slope_identity :
      Real.sqrt 5 * goldenMechanicalSlope = 3 - Real.goldenRatio := by
    rw [← Real.goldenRatio_sub_goldenConj, goldenMechanicalSlope,
      Real.inv_goldenRatio]
    nlinarith [Real.goldenRatio_mul_goldenConj, Real.goldenConj_sq,
      Real.goldenRatio_add_goldenConj]
  have golden_integer_form_nonzero (d : ℕ) (p : ℤ) (hd : 0 < d) :
      p ^ 2 - p * (d : ℤ) - (d : ℤ) ^ 2 ≠ 0 := by
    have hfactor :
        ((p ^ 2 - p * (d : ℤ) - (d : ℤ) ^ 2 : ℤ) : ℝ) =
          ((p : ℝ) - (d : ℝ) * Real.goldenRatio) *
            ((p : ℝ) - (d : ℝ) * Real.goldenConj) := by
      push_cast
      linear_combination
        (p : ℝ) * (d : ℝ) * Real.goldenRatio_add_goldenConj -
          (d : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj
    intro hz
    have hz' : (((p ^ 2 - p * (d : ℤ) - (d : ℤ) ^ 2 : ℤ) : ℝ)) = 0 := by
      exact_mod_cast hz
    rw [hfactor] at hz'
    rcases mul_eq_zero.mp hz' with h | h
    · exact (Real.goldenRatio_irrational.natCast_mul (by omega : d ≠ 0)).ne_int p
        (by linarith)
    · exact (Real.goldenConj_irrational.natCast_mul (by omega : d ≠ 0)).ne_int p
        (by linarith)
  have golden_small_arithmetic (d N : ℕ) (p : ℤ)
      (hd : 0 < d)
      (hdelta_pos : 0 < |(p : ℝ) - (d : ℝ) * Real.goldenRatio|)
      (hdelta_small : |(p : ℝ) - (d : ℝ) * Real.goldenRatio| <
        1 - goldenMechanicalSlope)
      (hwindow : (N : ℝ) * |(p : ℝ) - (d : ℝ) * Real.goldenRatio| <
        goldenMechanicalSlope) :
      (N : ℝ) < (3 - Real.goldenRatio) * d := by
    let err : ℝ := (p : ℝ) - (d : ℝ) * Real.goldenRatio
    let δ : ℝ := |err|
    let r : ℝ := goldenMechanicalSlope
    let root : ℝ := Real.sqrt 5
    have hr : 0 < r := inv_pos.mpr Real.goldenRatio_pos
    have hroot : 0 < root := Real.sqrt_pos.2 (by norm_num)
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    have hgap : (0 : ℝ) < 1 - r :=
      (by norm_num : (0 : ℝ) < 1 / 3).trans golden_window_constants.1
    have hδpos : 0 < δ := hdelta_pos
    have hδsmall : δ < 1 - r := hdelta_small
    have hNδ : (N : ℝ) * δ < r := hwindow
    by_contra h
    have hN : (3 - Real.goldenRatio) * (d : ℝ) ≤ (N : ℝ) := le_of_not_gt h
    have hslope : (3 - Real.goldenRatio) = root * r := golden_slope_identity.symm
    have hkey : root * (d : ℝ) * δ < 1 := by
      have hmul : (root * r * (d : ℝ)) * δ ≤ (N : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by rw [← hslope]; exact hN) hδpos.le
      nlinarith [hmul, hNδ]
    have hsum : Real.goldenRatio - Real.goldenConj = root :=
      Real.goldenRatio_sub_goldenConj
    have hfactor :
        (((p ^ 2 - p * (d : ℤ) - (d : ℤ) ^ 2 : ℤ) : ℝ)) =
          err * (root * (d : ℝ) + err) := by
      push_cast
      calc
        (p : ℝ) ^ 2 - (p : ℝ) * (d : ℝ) - (d : ℝ) ^ 2 =
            ((p : ℝ) - (d : ℝ) * Real.goldenRatio) *
              ((p : ℝ) - (d : ℝ) * Real.goldenConj) := by
                linear_combination
                  (p : ℝ) * (d : ℝ) * Real.goldenRatio_add_goldenConj -
                    (d : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj
        _ = err * (root * (d : ℝ) + err) := by
          dsimp [err]
          rw [← hsum]
          ring
    let form : ℤ := p ^ 2 - p * (d : ℤ) - (d : ℤ) ^ 2
    have hform : (1 : ℝ) ≤ |(form : ℝ)| := by
      exact_mod_cast Int.one_le_abs (golden_integer_form_nonzero d p hd)
    have herr_abs : |err| = δ := rfl
    have hformabs : |(form : ℝ)| = δ * |root * (d : ℝ) + err| := by
      rw [hfactor, abs_mul, herr_abs]
    have hlarge : 0 < root * (d : ℝ) + err := by
      have hδhalf : δ < 1 / 2 := by linarith [golden_window_constants.2]
      have hrootgt : 2 < root := by
        have hsqrt : root ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        nlinarith
      have herrbound := neg_abs_le err
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hrd : root ≤ root * d := by nlinarith [mul_nonneg hroot.le (sub_nonneg.mpr hd1)]
      linarith
    have hformeq : |(form : ℝ)| = δ * (root * (d : ℝ) + err) := by
      rw [hformabs, abs_of_pos hlarge]
    have herr_nonneg : 0 < err := by
      by_contra hh
      have he : err = -δ := by
        change err = -|err|
        rw [abs_of_nonpos (le_of_not_gt hh)]
        ring
      rw [he] at hformeq
      nlinarith [hform, hkey]
    have herr_eq : err = δ := (abs_of_pos herr_nonneg).symm
    have hformlt : |(form : ℝ)| < 2 := by
      rw [hformeq, herr_eq]
      have hδone : δ < 1 := by linarith
      nlinarith [hkey, mul_pos hδpos (sub_pos.mpr hδone)]
    have hform_one : |form| = 1 := by
      have hb : |form| < 2 := by exact_mod_cast hformlt
      have ha : 1 ≤ |form| := Int.one_le_abs (golden_integer_form_nonzero d p hd)
      omega
    have hnorm : δ * (root * (d : ℝ) + δ) = 1 := by
      have hfr : |(form : ℝ)| = 1 := by exact_mod_cast hform_one
      rw [herr_eq] at hformeq
      linarith
    have hNupper : (N : ℝ) < (3 - Real.goldenRatio) * d + r * δ := by
      have hmult : (N : ℝ) * δ <
          ((3 - Real.goldenRatio) * d + r * δ) * δ := by
        rw [hslope]
        nlinarith [hNδ, hnorm]
      exact (mul_lt_mul_iff_of_pos_right hδpos).mp hmult
    have hnear : (3 - Real.goldenRatio) * (d : ℝ) =
        ((3 * (d : ℤ) - p : ℤ) : ℝ) + δ := by
      rw [← herr_eq]
      dsimp [err]
      push_cast
      ring
    have hmargin : (1 + r) * δ < 1 := by
      have hquad : r ^ 2 + r = 1 := by
        simpa [r, goldenMechanicalSlope] using
          (show Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 by
            rw [Real.inv_goldenRatio]
            nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj])
      nlinarith [mul_pos hδpos (by linarith : 0 < 1 + r)]
    have hinteger : ((3 * (d : ℤ) - p : ℤ) : ℝ) + 1 ≤ (N : ℝ) := by
      have hk : (3 * (d : ℤ) - p : ℤ) < (N : ℤ) := by
        exact_mod_cast (by rw [hnear] at hN; linarith [hN, hδpos] :
          ((3 * (d : ℤ) - p : ℤ) : ℝ) < (N : ℝ))
      exact_mod_cast (Int.add_one_le_iff.mpr hk)
    rw [hnear] at hNupper
    linarith
  have golden_step_nearest_integer (d : ℕ) :
      ∃ p : ℤ, |(p : ℝ) - (d : ℝ) * Real.goldenRatio| = goldenStepDistance d := by
    let x : ℝ := (d : ℝ) * Real.goldenRatio
    by_cases hs : Int.fract x ≤ 1 / 2
    · refine ⟨⌊x⌋, ?_⟩
      have h : ((⌊x⌋ : ℤ) : ℝ) - x = -Int.fract x := by
        rw [Int.fract]
        ring
      rw [h, abs_neg, abs_of_nonneg (Int.fract_nonneg x)]
      change Int.fract x = min (Int.fract x) (1 - Int.fract x)
      exact (min_eq_left (by linarith)).symm
    · refine ⟨⌊x⌋ + 1, ?_⟩
      have h : (((⌊x⌋ + 1 : ℤ) : ℝ)) - x = 1 - Int.fract x := by
        rw [Int.fract]
        push_cast
        ring
      rw [h, abs_of_pos (by linarith [Int.fract_lt_one x] : 0 < 1 - Int.fract x)]
      change 1 - Int.fract x = min (Int.fract x) (1 - Int.fract x)
      exact (min_eq_right (by linarith)).symm
  have golden_step_positive (d : ℕ) (hd : 0 < d) :
      0 < goldenStepDistance d := by
    have hnonzero : Int.fract ((d : ℝ) * Real.goldenRatio) ≠ 0 := by
      rw [Int.fract_ne_zero_iff]
      rintro ⟨z, hz⟩
      exact (Real.goldenRatio_irrational.natCast_mul (by omega : d ≠ 0)).ne_int z hz.symm
    have ha : 0 < Int.fract ((d : ℝ) * Real.goldenRatio) :=
      lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hnonzero)
    have hb : 0 < 1 - Int.fract ((d : ℝ) * Real.goldenRatio) := by
      linarith [Int.fract_lt_one ((d : ℝ) * Real.goldenRatio)]
    exact lt_min ha hb
  have golden_map_small_conjecture (i d length : ℕ) (symbol : Bool)
      (hd : 0 < d) (hpos : 0 < length)
      (hsmall : goldenStepDistance d < 1 - goldenMechanicalSlope)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      ((length - 1 : ℕ) : ℝ) < (3 - Real.goldenRatio) * d := by
    obtain ⟨p, hp⟩ := golden_step_nearest_integer d
    exact golden_small_arithmetic d (length - 1) p hd
      (by rw [hp]; exact golden_step_positive d hd)
      (by rw [hp]; exact hsmall)
      (by rw [hp]; exact golden_map_small_step i d length symbol hd hpos hsmall hmap)
  have golden_approx_lower (q : ℕ) (p : ℤ) (hq : 0 < q)
      (herror : |(p : ℝ) - (q : ℝ) * Real.goldenRatio| < 1) :
      1 ≤ |(p : ℝ) - (q : ℝ) * Real.goldenRatio| *
        (Real.sqrt 5 * (q : ℝ) + 1) := by
    let err : ℝ := (p : ℝ) - (q : ℝ) * Real.goldenRatio
    let δ : ℝ := |err|
    have hroot : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hqreal : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hfactor :
        (((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ)) =
          err * (Real.sqrt 5 * (q : ℝ) + err) := by
      push_cast
      calc
        (p : ℝ) ^ 2 - (p : ℝ) * (q : ℝ) - (q : ℝ) ^ 2 =
            ((p : ℝ) - (q : ℝ) * Real.goldenRatio) *
              ((p : ℝ) - (q : ℝ) * Real.goldenConj) := by
                linear_combination
                  (p : ℝ) * (q : ℝ) * Real.goldenRatio_add_goldenConj -
                    (q : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj
        _ = err * (Real.sqrt 5 * (q : ℝ) + err) := by
          dsimp [err]
          rw [← Real.goldenRatio_sub_goldenConj]
          ring
    have hform : (1 : ℝ) ≤
        |(((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ))| := by
      exact_mod_cast Int.one_le_abs (golden_integer_form_nonzero q p hq)
    have htri : |Real.sqrt 5 * (q : ℝ) + err| ≤
        Real.sqrt 5 * (q : ℝ) + δ := by
      calc
        |Real.sqrt 5 * (q : ℝ) + err| ≤
            |Real.sqrt 5 * (q : ℝ)| + |err| := abs_add_le _ _
        _ = Real.sqrt 5 * (q : ℝ) + δ := by
          rw [abs_of_nonneg (mul_nonneg hroot hqreal)]
    calc
      (1 : ℝ) ≤ |(((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ))| := hform
      _ = δ * |Real.sqrt 5 * (q : ℝ) + err| := by
        rw [hfactor, abs_mul]
      _ ≤ δ * (Real.sqrt 5 * (q : ℝ) + δ) :=
        mul_le_mul_of_nonneg_left htri (abs_nonneg _)
      _ ≤ δ * (Real.sqrt 5 * (q : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith [herror]) (abs_nonneg _)
  have golden_large_arithmetic (d length : ℕ) (hd : 7 ≤ d)
      (δ : ℝ) (hδpos : 0 < δ)
      (hnorm : 1 ≤ δ * (Real.sqrt 5 * ((2 * d : ℕ) : ℝ) + 1))
      (hwindow : (((length - 1) / 2 : ℕ) : ℝ) * δ <
        goldenMechanicalSlope - (1 - δ) / 2) :
      ((length - 1 : ℕ) : ℝ) < (3 - Real.goldenRatio) * d := by
    let r : ℝ := goldenMechanicalSlope
    let root : ℝ := Real.sqrt 5
    have hr : 0 < r := inv_pos.mpr Real.goldenRatio_pos
    have hquad : r ^ 2 + r = 1 := by
      simpa [r, goldenMechanicalSlope] using
        (show Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 by
          rw [Real.inv_goldenRatio]
          nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj])
    have hroot : root = 1 + 2 * r := by
      change Real.sqrt 5 = 1 + 2 * Real.goldenRatio⁻¹
      rw [← Real.goldenRatio_sub_goldenConj, Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hr47 : (29 : ℝ) / 47 < r := by
      nlinarith [sq_nonneg (r - 29 / 47)]
    have hd7 : (7 : ℝ) ≤ d := by exact_mod_cast hd
    have hmult : (0 : ℝ) ≤ (7 * r - 4) * ((d : ℝ) - 7) := by
      apply mul_nonneg <;> linarith
    have hqd : (r ^ 2 + r - 1) * (d : ℝ) = 0 := by rw [show r ^ 2 + r - 1 = 0 by linarith]; ring
    have hcoeff : (2 * r - 1) * (root * ((2 * d : ℕ) : ℝ) + 1) ≤
        root * r * d - 2 := by
      push_cast
      nlinarith [hmult, hqd]
    by_contra h
    have hN : root * r * (d : ℝ) ≤ ((length - 1 : ℕ) : ℝ) := by
      have hN0 := le_of_not_gt h
      rw [← golden_slope_identity] at hN0
      exact hN0
    have hfloor : length - 1 ≤ 2 * ((length - 1) / 2) + 1 := by omega
    have hfloorR : ((length - 1 : ℕ) : ℝ) ≤
        2 * (((length - 1) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hfloor
    have hineq : (root * r * (d : ℝ) - 2) * δ < 2 * r - 1 := by
      have hmul : (root * r * (d : ℝ) - 1) * δ ≤
          2 * (((length - 1) / 2 : ℕ) : ℝ) * δ := by
        have ha : (root * r * (d : ℝ) - 1) ≤
            2 * (((length - 1) / 2 : ℕ) : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right ha hδpos.le
      have hwin : (((length - 1) / 2 : ℕ) : ℝ) * δ < r - (1 - δ) / 2 := hwindow
      nlinarith
    have hnorm' : 1 ≤ δ * (root * ((2 * d : ℕ) : ℝ) + 1) := hnorm
    have hnonneg : 0 ≤ 2 * r - 1 := by
      linarith [golden_window_constants.2]
    have hleft := mul_le_mul_of_nonneg_left hnorm' hnonneg
    have hright := mul_le_mul_of_nonneg_right hcoeff hδpos.le
    nlinarith [hineq, hleft, hright]
  have golden_double_step_nearest (d : ℕ) :
      |(((2 * ⌊(d : ℝ) * Real.goldenRatio⌋ + 1 : ℤ) : ℝ) -
        ((2 * d : ℕ) : ℝ) * Real.goldenRatio)| =
        1 - 2 * goldenStepDistance d := by
    let x : ℝ := (d : ℝ) * Real.goldenRatio
    let step : ℝ := Int.fract x
    have hrepr : ((⌊x⌋ : ℤ) : ℝ) + step = x := Int.floor_add_fract x
    have herr : (((2 * ⌊x⌋ + 1 : ℤ) : ℝ) -
        ((2 * d : ℕ) : ℝ) * Real.goldenRatio) = 1 - 2 * step := by
      push_cast
      dsimp [x] at hrepr
      linarith
    rw [herr]
    by_cases hs : step ≤ 1 / 2
    · have hmin : goldenStepDistance d = step := by
        change min step (1 - step) = step
        exact min_eq_left (by linarith)
      rw [hmin, abs_of_nonneg (by linarith)]
    · have hmin : goldenStepDistance d = 1 - step := by
        change min step (1 - step) = 1 - step
        exact min_eq_right (by linarith)
      rw [hmin, abs_of_nonpos (by linarith)]
      ring
  have golden_map_large_conjecture_of_seven (i d length : ℕ) (symbol : Bool)
      (hd : 7 ≤ d) (hpos : 0 < length)
      (hlarge : 1 - goldenMechanicalSlope ≤ goldenStepDistance d)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      ((length - 1 : ℕ) : ℝ) < (3 - Real.goldenRatio) * d := by
    let δ := 1 - 2 * goldenStepDistance d
    let p : ℤ := 2 * ⌊(d : ℝ) * Real.goldenRatio⌋ + 1
    have hδlt : δ < 1 := by
      dsimp [δ]
      linarith [golden_step_positive d (by omega : 0 < d)]
    have hnorm0 := golden_approx_lower (2 * d) p (by omega)
      (by simpa only [p, golden_double_step_nearest] using hδlt)
    have hnorm : 1 ≤ δ * (Real.sqrt 5 * ((2 * d : ℕ) : ℝ) + 1) := by
      simpa only [δ, p, golden_double_step_nearest] using hnorm0
    have hδpos : 0 < δ := by
      have hfactor : 0 < Real.sqrt 5 * ((2 * d : ℕ) : ℝ) + 1 := by positivity
      nlinarith [hnorm]
    apply golden_large_arithmetic d length hd δ hδpos hnorm
    have hgeom := golden_map_large_step i d length symbol (by omega) hpos hlarge hmap
    dsimp [δ]
    nlinarith [hgeom]
  have golden_small_denominator_windows :
      goldenStepDistance 1 = 1 - goldenMechanicalSlope ∧
      goldenStepDistance 2 < 1 - goldenMechanicalSlope ∧
      goldenStepDistance 3 < 1 - goldenMechanicalSlope ∧
      (47 : ℝ) / 100 < goldenStepDistance 4 ∧
      goldenStepDistance 4 < (19 : ℝ) / 40 ∧
      goldenStepDistance 5 < 1 - goldenMechanicalSlope ∧
      goldenStepDistance 6 < 1 - goldenMechanicalSlope := by
    have hroot : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hrootlo : (2236 : ℝ) / 1000 < Real.sqrt 5 := by
      nlinarith [Real.sqrt_nonneg 5]
    have hroothi : Real.sqrt 5 < (2237 : ℝ) / 1000 := by
      nlinarith [Real.sqrt_nonneg 5]
    have hfloors (n m : ℕ)
        (hlo : (m : ℝ) ≤ (n : ℝ) * Real.goldenRatio)
        (hhi : (n : ℝ) * Real.goldenRatio < m + 1) :
        Int.fract ((n : ℝ) * Real.goldenRatio) =
          (n : ℝ) * Real.goldenRatio - m := by
      have hf : ⌊(n : ℝ) * Real.goldenRatio⌋ = (m : ℤ) := by
        apply Int.floor_eq_iff.mpr
        exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
      rw [Int.fract, hf]
      push_cast
      ring
    have h1 : Int.fract ((1 : ℕ) * Real.goldenRatio) =
        Real.goldenRatio - 1 := by
      simpa using hfloors 1 1 (by norm_num [Real.goldenRatio]; linarith)
        (by norm_num [Real.goldenRatio]; linarith)
    have h2 : Int.fract ((2 : ℕ) * Real.goldenRatio) =
        2 * Real.goldenRatio - 3 := hfloors 2 3
          (by norm_num [Real.goldenRatio]; linarith)
          (by norm_num [Real.goldenRatio]; linarith)
    have h3 : Int.fract ((3 : ℕ) * Real.goldenRatio) =
        3 * Real.goldenRatio - 4 := hfloors 3 4
          (by norm_num [Real.goldenRatio]; linarith)
          (by norm_num [Real.goldenRatio]; linarith)
    have h4 : Int.fract ((4 : ℕ) * Real.goldenRatio) =
        4 * Real.goldenRatio - 6 := hfloors 4 6
          (by norm_num [Real.goldenRatio]; linarith)
          (by norm_num [Real.goldenRatio]; linarith)
    have h5 : Int.fract ((5 : ℕ) * Real.goldenRatio) =
        5 * Real.goldenRatio - 8 := hfloors 5 8
          (by norm_num [Real.goldenRatio]; linarith)
          (by norm_num [Real.goldenRatio]; linarith)
    have h6 : Int.fract ((6 : ℕ) * Real.goldenRatio) =
        6 * Real.goldenRatio - 9 := hfloors 6 9
          (by norm_num [Real.goldenRatio]; linarith)
          (by norm_num [Real.goldenRatio]; linarith)
    have hr : goldenMechanicalSlope = (Real.sqrt 5 - 1) / 2 := by
      rw [goldenMechanicalSlope, Real.inv_goldenRatio, Real.goldenConj]
      ring
    simp only [goldenStepDistance, h1, h2, h3, h4, h5, h6, hr]
    constructor
    · rw [min_eq_right (by rw [Real.goldenRatio]; linarith)]
      rw [Real.goldenRatio]
      ring
    constructor
    · apply lt_of_le_of_lt (min_le_left _ _)
      rw [Real.goldenRatio]
      linarith
    constructor
    · apply lt_of_le_of_lt (min_le_right _ _)
      rw [Real.goldenRatio]
      linarith
    constructor
    · rw [min_eq_left (by rw [Real.goldenRatio]; linarith)]
      rw [Real.goldenRatio]
      linarith
    constructor
    · apply lt_of_le_of_lt (min_le_left _ _)
      rw [Real.goldenRatio]
      linarith
    constructor
    · apply lt_of_le_of_lt (min_le_left _ _)
      rw [Real.goldenRatio]
      linarith
    · apply lt_of_le_of_lt (min_le_right _ _)
      rw [Real.goldenRatio]
      linarith
  have golden_map_large_conjecture_below_seven (i d length : ℕ) (symbol : Bool)
      (hdpos : 0 < d) (hdlt : d < 7) (hpos : 0 < length)
      (hlarge : 1 - goldenMechanicalSlope ≤ goldenStepDistance d)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      ((length - 1 : ℕ) : ℝ) < (3 - Real.goldenRatio) * d := by
    have hw := golden_small_denominator_windows
    interval_cases d
    · have hg : goldenStepDistance 1 = 1 - goldenMechanicalSlope := hw.1
      have hgeom := golden_map_large_step i 1 length symbol (by omega) hpos
        (by rw [hg]) (by simpa using hmap)
      rw [hg] at hgeom
      have hdelta : 0 < 1 - 2 * (1 - goldenMechanicalSlope) := by
        linarith [golden_window_constants.2]
      have hm : (length - 1) / 2 = 0 := by
        have hmlt : (((length - 1) / 2 : ℕ) : ℝ) < 1 := by
          nlinarith [hgeom]
        have : (length - 1) / 2 < 1 := by exact_mod_cast hmlt
        omega
      have hN : length - 1 ≤ 1 := by omega
      have hφ : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
      have hNR : ((length - 1 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hN
      norm_num
      linarith
    · exact False.elim ((not_le_of_gt hw.2.1) hlarge)
    · exact False.elim ((not_le_of_gt hw.2.2.1) hlarge)
    · have hglo : (47 : ℝ) / 100 < goldenStepDistance 4 := hw.2.2.2.1
      have hghi : goldenStepDistance 4 < (19 : ℝ) / 40 := hw.2.2.2.2.1
      have hgeom := golden_map_large_step i 4 length symbol (by omega) hpos
        hlarge (by simpa using hmap)
      have hrhi : goldenMechanicalSlope < (619 : ℝ) / 1000 := by
        rw [goldenMechanicalSlope, Real.inv_goldenRatio, Real.goldenConj]
        have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg 5]
      have hδpos : 0 < 1 - 2 * goldenStepDistance 4 := by linarith
      have hm : (length - 1) / 2 ≤ 2 := by
        by_contra hn
        have hm3 : (3 : ℝ) ≤ (((length - 1) / 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 3 ≤ (length - 1) / 2 by omega)
        have hmul := mul_le_mul_of_nonneg_right hm3 hδpos.le
        nlinarith [hgeom, hmul]
      have hN : length - 1 ≤ 5 := by omega
      have hφ : Real.goldenRatio < (7 : ℝ) / 4 := by
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      have hNR : ((length - 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hN
      norm_num
      linarith
    · exact False.elim ((not_le_of_gt hw.2.2.2.2.2.1) hlarge)
    · exact False.elim ((not_le_of_gt hw.2.2.2.2.2.2) hlarge)
  have golden_map_all_runs_bound (i d length : ℕ) (symbol : Bool)
      (hd : 0 < d) (hpos : 0 < length)
      (hmap : ∀ k < length, goldenWord (i + k * d) = symbol) :
      ((length - 1 : ℕ) : ℝ) < (3 - Real.goldenRatio) * d := by
    rcases lt_or_ge (goldenStepDistance d) (1 - goldenMechanicalSlope) with hs | hl
    · exact golden_map_small_conjecture i d length symbol hd hpos hs hmap
    · by_cases hseven : 7 ≤ d
      · exact golden_map_large_conjecture_of_seven i d length symbol hseven hpos hl hmap
      · exact golden_map_large_conjecture_below_seven i d length symbol
          hd (by omega) hpos hl hmap
  let lengths : Set ℕ := {n | ∃ i : ℕ, ∃ symbol : Bool,
    0 < n ∧ ∀ k < n, goldenWord (i + k * d) = symbol}
  have hnonempty : lengths.Nonempty := by
    refine ⟨1, 0, goldenWord 0, by omega, ?_⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp
  have hbounded : BddAbove lengths := by
    refine ⟨2 * d + 1, ?_⟩
    rintro n ⟨i, symbol, hn, hmap⟩
    have hrun := golden_map_all_runs_bound i d n symbol hd hn hmap
    have hφ : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hlt : ((n - 1 : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have hnat : n - 1 < 2 * d := by exact_mod_cast hlt
    omega
  have hmax : goldenMAPMaximum d ∈ lengths := by
    exact Nat.sSup_mem hnonempty hbounded
  obtain ⟨i, symbol, hpos, hmap⟩ := hmax
  have hrun := golden_map_all_runs_bound i d (goldenMAPMaximum d) symbol
    hd hpos hmap
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_lt_iff₀ hdR).2
  calc
    ((goldenMAPMaximum d - 1 : ℕ) : ℝ) <
        (3 - Real.goldenRatio) * d := hrun
    _ = (Real.sqrt 5 / Real.goldenRatio) * d := by
      rw [← golden_slope_identity]
      simp only [goldenMechanicalSlope, div_eq_mul_inv]

#print axioms result

end D5.S1.Words
