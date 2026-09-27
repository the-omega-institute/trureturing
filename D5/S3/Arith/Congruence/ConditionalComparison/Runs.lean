/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Runs
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Finite run laws from survival probabilities. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Runs.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Finite run laws from survival probabilities

Both comparison distributions in the proof are run lengths.  It is more
robust to specify such a law by its survival function.  The construction
below proves normalization by telescoping and supplies the Abel identity that
turns nested common gates into an exact run expectation.
-/

namespace Erdos7

/-- Survival data for a run taking values in `{0,…,a}`. -/
structure RunSpec (a : ℕ) where
  survival : ℕ → ℚ
  survival_zero : survival 0 = 1
  survival_after : survival (a + 1) = 0
  antitone_step : ∀ d ≤ a, survival (d + 1) ≤ survival d

namespace RunSpec

/-- The probability mass at `d` is the drop of the survival function there. -/
def weight {a : ℕ} (R : RunSpec a) (d : Fin (a + 1)) : ℚ :=
  R.survival d - R.survival (d + 1)

theorem weight_nonneg {a : ℕ} (R : RunSpec a) (d : Fin (a + 1)) :
    0 ≤ R.weight d := by
  unfold weight
  linarith [R.antitone_step d (Nat.le_of_lt_succ d.isLt)]

/-- The exact finite law induced by a survival specification. -/
def law {a : ℕ} (R : RunSpec a) : FiniteLaw (Fin (a + 1)) where
  weight := R.weight
  weight_nonneg := R.weight_nonneg
  weight_sum := by
    change (∑ d : Fin (a + 1),
      (fun n : ℕ ↦ R.survival n - R.survival (n + 1)) d) = 1
    rw [Fin.sum_univ_eq_sum_range
      (fun n : ℕ ↦ R.survival n - R.survival (n + 1)) (a + 1)]
    rw [Finset.sum_range_sub']
    rw [R.survival_zero, R.survival_after]
    norm_num

@[simp] theorem law_weight {a : ℕ} (R : RunSpec a) (d : Fin (a + 1)) :
    R.law.weight d = R.survival d - R.survival (d + 1) := rfl

private theorem sum_range_shift_sub (f : ℕ → ℚ) (k n : ℕ) :
    (∑ i ∈ Finset.range n, (f (k + i) - f (k + i + 1))) =
      f k - f (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The law reconstructed from a survival function has exactly that survival
function. -/
theorem law_prob_ge_eq_survival {a k : ℕ} (R : RunSpec a) (hka : k ≤ a) :
    R.law.prob (fun d ↦ k ≤ (d : ℕ)) = R.survival k := by
  unfold FiniteLaw.prob FiniteLaw.expect law weight
  rw [Fin.sum_univ_eq_sum_range
    (fun d : ℕ ↦ (R.survival d - R.survival (d + 1)) *
      (if k ≤ d then 1 else 0)) (a + 1)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.range (a + 1)).filter (k ≤ ·) =
      Finset.Ico k (a + 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [hfilter, Finset.sum_Ico_eq_sum_range]
  rw [sum_range_shift_sub]
  have hsum : k + (a + 1 - k) = a + 1 := by omega
  rw [hsum, R.survival_after]
  ring

/-- Abel summation for run laws. -/
theorem expect_eq_abel {a : ℕ} (R : RunSpec a) (f : ℕ → ℚ) :
    R.law.expect (fun d ↦ f d) =
      f 0 + ∑ d ∈ Finset.range a,
        R.survival (d + 1) * (f (d + 1) - f d) := by
  unfold FiniteLaw.expect law weight
  change (∑ d : Fin (a + 1),
      (fun n : ℕ ↦
        (R.survival n - R.survival (n + 1)) * f n) d) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ (R.survival n - R.survival (n + 1)) * f n) (a + 1)]
  have htel : ∀ n : ℕ,
      (∑ d ∈ Finset.range (n + 1),
          (R.survival d - R.survival (d + 1)) * f d) =
        f 0 + ∑ d ∈ Finset.range n,
          R.survival (d + 1) * (f (d + 1) - f d) -
            R.survival (n + 1) * f n := by
    intro n
    induction n with
    | zero => simp [R.survival_zero] <;> ring
    | succ n ih =>
        conv_lhs => rw [Finset.sum_range_succ]
        rw [ih]
        conv_rhs => rw [Finset.sum_range_succ]
        ring
  rw [htel a, R.survival_after]
  ring

/-- The expected run length is the sum of its positive survival values. -/
theorem expect_value {a : ℕ} (R : RunSpec a) :
    R.law.expect (fun d ↦ (d : ℚ)) =
      ∑ d ∈ Finset.range a, R.survival (d + 1) := by
  rw [R.expect_eq_abel (fun d ↦ (d : ℚ))]
  simp

/-- The expected shifted run `X=D+1`. -/
theorem expect_shifted_value {a : ℕ} (R : RunSpec a) :
    R.law.expect (fun d ↦ (d : ℚ) + 1) =
      1 + ∑ d ∈ Finset.range a, R.survival (d + 1) := by
  rw [R.expect_eq_abel (fun d ↦ (d : ℚ) + 1)]
  simp

/-- Stop-loss identity for an integer threshold. -/
theorem expect_natHinge {a k : ℕ} (R : RunSpec a) :
    R.law.expect (fun d ↦ ((d - k : ℕ) : ℚ)) =
      ∑ d ∈ (Finset.range a).filter (k ≤ ·), R.survival (d + 1) := by
  rw [R.expect_eq_abel (fun d ↦ ((d - k : ℕ) : ℚ))]
  simp only [Nat.zero_sub, Nat.cast_zero, zero_add]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdk : k ≤ d
  · simp only [hdk, ↓reduceIte]
    have h1 : d + 1 - k = (d - k) + 1 := by omega
    rw [h1, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [hdk, ↓reduceIte]
    have hzero : d - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hzero' : d + 1 - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [hzero, hzero']

end RunSpec

/-- A finite initial run of independent gates with open probability `r`. -/
def geometricRunSpec (a : ℕ) (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    RunSpec a where
  survival := fun d ↦ if d ≤ a then r ^ d else 0
  survival_zero := by simp
  survival_after := by simp
  antitone_step := by
    intro d hda
    by_cases hd : d < a
    · have hd1 : d + 1 ≤ a := by omega
      simp only [if_pos hda, if_pos hd1]
      rw [pow_succ]
      calc
        r ^ d * r ≤ r ^ d * 1 :=
          mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 d)
        _ = r ^ d := mul_one _
    · have hdeq : d = a := by omega
      subst d
      simp [pow_nonneg hr0]

@[simp] theorem geometricRunSpec_survival_of_le
    {a d : ℕ} {r : ℚ} {hr0 : 0 ≤ r} {hr1 : r ≤ 1} (hda : d ≤ a) :
    (geometricRunSpec a r hr0 hr1).survival d = r ^ d := by
  simp [geometricRunSpec, hda]

/-- The finite geometric run has shifted mean at most `(1-r)⁻¹`. -/
theorem geometricRun_expect_shifted_le
    {a : ℕ} {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (geometricRunSpec a r hr0 hr1.le).law.expect
        (fun d ↦ (d : ℚ) + 1) ≤ (1 - r)⁻¹ := by
  rw [(geometricRunSpec a r hr0 hr1.le).expect_shifted_value]
  have heq :
      1 + ∑ d ∈ Finset.range a,
          (geometricRunSpec a r hr0 hr1.le).survival (d + 1) =
        ∑ d ∈ Finset.range (a + 1), r ^ d := by
    have hsurv :
        (∑ d ∈ Finset.range a,
          (geometricRunSpec a r hr0 hr1.le).survival (d + 1)) =
          ∑ d ∈ Finset.range a, r ^ (d + 1) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact geometricRunSpec_survival_of_le (Finset.mem_range.mp hd)
    rw [hsurv]
    simp_rw [pow_succ, ← Finset.sum_mul]
    rw [geom_sum_succ]
    ring
  rw [heq, inv_eq_one_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).2
  rw [geom_sum_mul_neg]
  nlinarith [pow_nonneg hr0 (a + 1)]

/-- The survival caps supplied by the bottom-packed ternary selection. -/
def ternarySurvival (a d : ℕ) : ℚ :=
  if d = 0 then 1
  else if d < a then
    2 * (3 : ℚ) ^ (a - 1 - d) / ((3 : ℚ) ^ (a - 1) + 1)
  else if d = a then
    1 / ((3 : ℚ) ^ (a - 1) + 1)
  else 0

theorem ternarySurvival_zero (a : ℕ) : ternarySurvival a 0 = 1 := by
  simp [ternarySurvival]

theorem ternarySurvival_after {a : ℕ} (ha : 1 ≤ a) :
    ternarySurvival a (a + 1) = 0 := by
  simp [ternarySurvival]

theorem ternarySurvival_antitone_step {a : ℕ} (ha : 1 ≤ a)
    (d : ℕ) (hda : d ≤ a) :
    ternarySurvival a (d + 1) ≤ ternarySurvival a d := by
  have hden : (0 : ℚ) < (3 : ℚ) ^ (a - 1) + 1 := by positivity
  by_cases hd0 : d = 0
  · subst d
    by_cases ha1 : a = 1
    · subst a
      norm_num [ternarySurvival]
    · have ha2 : 2 ≤ a := by omega
      simp only [ternarySurvival, one_ne_zero, ↓reduceIte,
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨by omega, ha1⟩,
        if_pos (by omega : 1 < a), if_pos rfl]
      apply (div_le_iff₀ hden).2
      have hp : (3 : ℚ) ^ (a - 1) =
          (3 : ℚ) ^ (a - 2) * 3 := by
        rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
      rw [show a - 1 - (0 + 1) = a - 2 by omega, hp]
      nlinarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 3) (a - 2)]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hda' : d < a
    · by_cases hnext : d + 1 < a
      · simp only [ternarySurvival, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte, hnext, hd0, hda']
        apply (div_le_div_iff₀ hden hden).2
        have hexp : a - 1 - d = (a - 1 - (d + 1)) + 1 := by omega
        rw [hexp, pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 3)
          (a - 1 - (d + 1))]
      · have hnextEq : d + 1 = a := by omega
        have ha0 : a ≠ 0 := by omega
        simp only [ternarySurvival, hnextEq, ha0, ↓reduceIte, lt_self_iff_false,
          hd0, hda']
        have hexp : a - 1 - d = 0 := by omega
        rw [hexp, pow_zero]
        apply (div_le_div_iff₀ hden hden).2
        nlinarith
    · have hdeq : d = a := by omega
      subst d
      have ha0 : a ≠ 0 := by omega
      simp [ternarySurvival, ha0]
      positivity

/-- The finite ternary comparison run determined by the exact prefix caps. -/
def ternaryRunSpec (a : ℕ) (ha : 1 ≤ a) : RunSpec a where
  survival := ternarySurvival a
  survival_zero := ternarySurvival_zero a
  survival_after := ternarySurvival_after ha
  antitone_step := ternarySurvival_antitone_step ha

@[simp] theorem ternaryRunSpec_survival {a : ℕ} (ha : 1 ≤ a) (d : ℕ) :
    (ternaryRunSpec a ha).survival d = ternarySurvival a d := rfl

/-- Exact stop-loss transform of the finite bottom-packed ternary run. -/
theorem ternaryRun_stoploss_eq {a k : ℕ} (ha : 1 ≤ a) (hk : k < a) :
    (ternaryRunSpec a ha).law.expect
        (fun d ↦ ((d - k : ℕ) : ℚ)) =
      (3 : ℚ) ^ (a - k - 1) / ((3 : ℚ) ^ (a - 1) + 1) := by
  rw [(ternaryRunSpec a ha).expect_natHinge]
  let den : ℚ := (3 : ℚ) ^ (a - 1) + 1
  let n : ℕ := a - 1 - k
  have hfilter : (Finset.range a).filter (k ≤ ·) = Finset.Ico k a := by
    ext d
    simp [Finset.mem_Ico]
    tauto
  rw [hfilter]
  change (∑ d ∈ Finset.Ico k a, ternarySurvival a (d + 1)) = _
  have hka : k ≤ a - 1 := by omega
  have haform : a = (a - 1) + 1 := by omega
  have hsplit := Finset.sum_Ico_succ_top hka
    (fun d ↦ ternarySurvival a (d + 1))
  rw [← haform] at hsplit
  rw [hsplit]
  have ha0 : a ≠ 0 := by omega
  have hlast : ternarySurvival a a = 1 / den := by
    simp [ternarySurvival, den, ha0]
  rw [hlast]
  have hearly :
      (∑ d ∈ Finset.Ico k (a - 1), ternarySurvival a (d + 1)) =
        (2 / den) * ∑ i ∈ Finset.range n, (3 : ℚ) ^ i := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hcount : a - 1 - k = n := rfl
    rw [hcount]
    calc
      (∑ i ∈ Finset.range n, ternarySurvival a (k + i + 1)) =
          ∑ i ∈ Finset.range n,
            (2 / den) * (3 : ℚ) ^ (n - 1 - i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiN : i < n := Finset.mem_range.mp hi
            have hpos : k + i + 1 ≠ 0 := by omega
            have hlt : k + i + 1 < a := by
              dsimp [n] at hiN
              omega
            have hexp : a - 1 - (k + i + 1) = n - 1 - i := by
              dsimp [n]
              omega
            simp [ternarySurvival, hpos, hlt, den, hexp]
            ring
      _ = (2 / den) * ∑ i ∈ Finset.range n,
            (3 : ℚ) ^ (n - 1 - i) := by
            rw [Finset.mul_sum]
      _ = (2 / den) * ∑ i ∈ Finset.range n, (3 : ℚ) ^ i := by
            rw [Finset.sum_range_reflect]
  rw [hearly]
  have hgeom := geom_sum_mul (3 : ℚ) n
  norm_num at hgeom
  have hden : den ≠ 0 := by
    dsimp [den]
    positivity
  have hnexp : a - k - 1 = n := by
    dsimp [n]
    omega
  rw [hnexp]
  change (2 / den) * (∑ i ∈ Finset.range n, (3 : ℚ) ^ i) + 1 / den =
    (3 : ℚ) ^ n / den
  field_simp [hden]
  nlinarith

/-- The exact finite ternary run is dominated in stop-loss order by the
height-free transform `3⁻ᵏ`. -/
theorem ternaryRun_stoploss_lt {a k : ℕ} (ha : 1 ≤ a) (hk : k < a) :
    (ternaryRunSpec a ha).law.expect
        (fun d ↦ ((d - k : ℕ) : ℚ)) < (3 : ℚ)⁻¹ ^ k := by
  rw [ternaryRun_stoploss_eq ha hk]
  have hp : (0 : ℚ) < (3 : ℚ) ^ (a - 1) := by positivity
  have hpow : (3 : ℚ) ^ (a - k - 1) * (3 : ℚ) ^ k =
      (3 : ℚ) ^ (a - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [inv_pow]
  have hkpow : (0 : ℚ) < (3 : ℚ) ^ k := by positivity
  have hden : (0 : ℚ) < (3 : ℚ) ^ (a - 1) + 1 := by positivity
  apply (div_lt_iff₀ hden).2
  calc
    (3 : ℚ) ^ (a - k - 1) <
        ((3 : ℚ) ^ (a - 1) + 1) / (3 : ℚ) ^ k := by
      apply (lt_div_iff₀ hkpow).2
      rw [hpow]
      linarith
    _ = ((3 : ℚ) ^ k)⁻¹ * ((3 : ℚ) ^ (a - 1) + 1) := by
      field_simp

/-- Non-strict, height-uniform stop-loss domination, including thresholds
above the finite height. -/
theorem ternaryRun_stoploss_le {a : ℕ} (ha : 1 ≤ a) (k : ℕ) :
    (ternaryRunSpec a ha).law.expect
        (fun d ↦ ((d - k : ℕ) : ℚ)) ≤ (3 : ℚ)⁻¹ ^ k := by
  by_cases hk : k < a
  · exact (ternaryRun_stoploss_lt ha hk).le
  · have hzero : (fun d : Fin (a + 1) ↦ ((d - k : ℕ) : ℚ)) =
        (fun _ ↦ 0) := by
      funext d
      have hdk : (d : ℕ) ≤ k := by omega
      simp [Nat.sub_eq_zero_of_le hdk]
    rw [hzero, FiniteLaw.expect_zero]
    positivity

/-- The shifted bottom-packed run has mean at most the height-free value
`2`. -/
theorem ternaryRun_expect_shifted_le {a : ℕ} (ha : 1 ≤ a) :
    (ternaryRunSpec a ha).law.expect
        (fun d ↦ (d : ℚ) + 1) ≤ 2 := by
  have h0 := ternaryRun_stoploss_le ha 0
  have hmean : (ternaryRunSpec a ha).law.expect
      (fun d ↦ (d : ℚ)) ≤ 1 := by simpa using h0
  calc
    (ternaryRunSpec a ha).law.expect (fun d ↦ (d : ℚ) + 1) =
        (ternaryRunSpec a ha).law.expect (fun d ↦ (d : ℚ)) + 1 := by
          rw [FiniteLaw.expect_add]
          simp
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

end Erdos7
