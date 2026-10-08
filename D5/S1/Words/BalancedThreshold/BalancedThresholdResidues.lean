/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdResidues
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdResidues
   mirror-E: none(waiver:infinite-denominator-residue-orbit)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence]
   utility: none
   digest: Two-step induction preserves the eight-state orbit of the actual denominators. -/

import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import D5.S1.Words.BalancedThreshold.BalancedThresholdExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

/-- The alternating continuant recurrence preserves the ordered residue states at every
index; the exceptional initial pair involving denominator zero is not on this orbit. -/
theorem uniform_denominator_residues (t : ℕ) (ht : 5 ≤ t) :
    let g := GenContFract.of (uniformSlope t / (1 - uniformSlope t))
    ∀ n, 1 ≤ n →
      (⌊g.dens n⌋ : ℝ) = g.dens n ∧
      ⌊g.dens n⌋ ≡
        (if n % 8 = 1 then 2 else if n % 8 = 2 then 1
          else if n % 8 = 3 then 0 else if n % 8 = 4 then 1
          else if n % 8 = 5 then -2 else if n % 8 = 6 then -1
          else if n % 8 = 7 then 0 else -1 : ℤ) [ZMOD (t : ℤ)] ∧
      ⌊g.dens n⌋ ≡ (if n % 2 = 0 then 0 else 1 : ℤ) [ZMOD (t : ℤ) + 1] := by
  let g := GenContFract.of (uniformSlope t / (1 - uniformSlope t))
  let q := fun n => ⌊g.dens n⌋
  let digit := fun n => if n = 0 then t + 2 else if n = 1 then t
    else if n % 2 = 0 then t - 2 else t + 1
  let residue := fun n : ℕ =>
    if n % 8 = 1 then (2 : ℤ) else if n % 8 = 2 then 1
    else if n % 8 = 3 then 0 else if n % 8 = 4 then 1
    else if n % 8 = 5 then -2 else if n % 8 = 6 then -1
    else if n % 8 = 7 then 0 else -1
  let parity := fun n : ℕ => if n % 2 = 0 then (0 : ℤ) else 1
  have digits : ∀ n, g.s.get? n = some ⟨1, (digit n : ℝ)⟩ :=
    (uniform_ratio_expansion t ht).2
  have g0 : g.dens 0 = 1 := GenContFract.zeroth_den_eq_one
  have g1 : g.dens 1 = (t : ℝ) + 2 := by
    simpa [digit] using GenContFract.first_den_eq (digits 0)
  have recR : ∀ n, g.dens (n + 2) =
      (digit (n + 1) : ℝ) * g.dens (n + 1) + g.dens n := by
    intro n
    simpa only [one_mul] using GenContFract.dens_recurrence (digits (n + 1)) rfl rfl
  have integral : ∀ n, (q n : ℝ) = g.dens n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [q, g0]
    | one => simp [q, g1]
    | more n hn hn1 =>
      have hid : g.dens (n + 2) =
          (((digit (n + 1) : ℤ) * q (n + 1) + q n : ℤ) : ℝ) := by
        rw [recR, ← hn, ← hn1]
        push_cast
        rfl
      simp only [q, hid, Int.floor_intCast]
  have q0 : q 0 = 1 := by simp [q, g0]
  have q1 : q 1 = (t : ℤ) + 2 := by simp [q, g1]
  have qrec : ∀ n, q (n + 2) =
      (digit (n + 1) : ℤ) * q (n + 1) + q n := by
    intro n
    have hid : g.dens (n + 2) =
        (((digit (n + 1) : ℤ) * q (n + 1) + q n : ℤ) : ℝ) := by
      rw [recR, ← integral n, ← integral (n + 1)]
      push_cast
      rfl
    simp only [q, hid, Int.floor_intCast]
  have q2 : q 2 = (t : ℤ) * ((t : ℤ) + 2) + 1 := by
    simpa [digit, q0, q1] using qrec 0
  have tail : ∀ n, 1 ≤ n → (digit (n + 1) : ℤ) =
      if (n + 1) % 2 = 0 then (t : ℤ) - 2 else (t : ℤ) + 1 := by
    intro n hn
    simp only [digit, if_neg (by omega : ¬ n + 1 = 0),
      if_neg (by omega : ¬ n + 1 = 1)]
    split_ifs <;> omega
  have coeffT : ∀ n, 1 ≤ n →
      (digit (n + 1) : ℤ) ≡
        (if (n + 1) % 2 = 0 then -2 else 1 : ℤ) [ZMOD (t : ℤ)] := by
    intro n hn
    rw [tail n hn]
    split_ifs
    · rw [Int.modEq_iff_dvd]
      exact ⟨-1, by ring⟩
    · rw [Int.modEq_iff_dvd]
      exact ⟨-1, by ring⟩
  have coeffT1 : ∀ n, 1 ≤ n →
      (digit (n + 1) : ℤ) ≡
        (if (n + 1) % 2 = 0 then -3 else 0 : ℤ) [ZMOD (t : ℤ) + 1] := by
    intro n hn
    rw [tail n hn]
    split_ifs <;> rw [Int.modEq_iff_dvd] <;> exact ⟨-1, by ring⟩
  have rrec : ∀ n, residue (n + 2) =
      (if (n + 1) % 2 = 0 then -2 else 1 : ℤ) * residue (n + 1) + residue n := by
    intro n
    have hn : n % 8 < 8 := Nat.mod_lt n (by norm_num)
    have hmod1 : (n + 1) % 8 = (n % 8 + 1) % 8 := by omega
    have hmod2 : (n + 2) % 8 = (n % 8 + 2) % 8 := by omega
    have hpar : (n + 1) % 2 = ((n % 8 + 1) % 8) % 2 := by omega
    dsimp only [residue]
    rw [hmod1, hmod2, hpar]
    interval_cases h : n % 8 <;> norm_num
  have prec : ∀ n, parity (n + 2) =
      (if (n + 1) % 2 = 0 then -3 else 0 : ℤ) * parity (n + 1) + parity n := by
    intro n
    dsimp [parity]
    by_cases h : n % 2 = 0
    · have h1 : (n + 1) % 2 ≠ 0 := by omega
      have h2 : (n + 2) % 2 = 0 := by omega
      simp [h, h1]
    · have h1 : (n + 1) % 2 = 0 := by omega
      have h2 : (n + 2) % 2 ≠ 0 := by omega
      simp [h, h1, h2]
  have states : ∀ n, q (n + 1) ≡ residue (n + 1) [ZMOD (t : ℤ)] ∧
      q (n + 1) ≡ parity (n + 1) [ZMOD (t : ℤ) + 1] := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      rw [q1]
      norm_num only [residue, parity, Nat.zero_add, Nat.reduceMod, Nat.reduceEqDiff,
        if_true, if_false]
      constructor <;> rw [Int.modEq_iff_dvd] <;> exact ⟨-1, by ring⟩
    | one =>
      rw [q2]
      constructor
      · norm_num [residue, Int.ModEq, Int.add_emod, Int.mul_emod]
      · rw [Int.modEq_iff_dvd]
        refine ⟨-((t : ℤ) + 1), ?_⟩
        norm_num [parity]
        ring
    | more n hn hn1 =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, qrec]
      constructor
      · rw [rrec]
        exact ((coeffT (n + 1) (by omega)).mul hn1.1).add hn.1
      · rw [prec]
        exact ((coeffT1 (n + 1) (by omega)).mul hn1.2).add hn.2
  change ∀ n, 1 ≤ n → (q n : ℝ) = g.dens n ∧
    q n ≡ residue n [ZMOD (t : ℤ)] ∧ q n ≡ parity n [ZMOD (t : ℤ) + 1]
  intro n hn
  refine ⟨integral n, ?_⟩
  simpa only [Nat.sub_add_cancel hn] using states (n - 1)

end D5.S1.Words.BalancedThreshold
