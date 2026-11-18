/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact separation of the moving prime weight into its ramp and remainder. -/

import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper

/-- The localized weight around the moving prime cutoff. -/
def weight (P s t : ℝ) : ℝ :=
  log (1 + exp (-s * |log (t / P)|))

/-- The finite prime remainder at the integer counting endpoint. -/
def remainder (P s x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, weight P s p

private lemma softplus_split (v : ℝ) :
    log (1 + exp v) = max v 0 + log (1 + exp (-|v|)) := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv, max_eq_left hv]
    have h : 1 + exp v = exp v * (1 + exp (-v)) := by
      rw [mul_add, mul_one, ← exp_add]
      simp
      ring
    rw [h, log_mul (exp_ne_zero _) (by positivity), log_exp]
  · have hv' : v ≤ 0 := (lt_of_not_ge hv).le
    rw [abs_of_nonpos hv', max_eq_right hv', neg_neg, zero_add]

private lemma logWeight_split {P s t : ℝ} (hP : 0 < P) (ht : 0 < t)
    (hs : 0 ≤ s) :
    log (1 + P ^ s * t ^ (-s)) =
      (if t ≤ P then s * (log P - log t) else 0) + weight P s t := by
  have he : P ^ s * t ^ (-s) = exp (s * (log P - log t)) := by
    rw [rpow_def_of_pos hP, rpow_def_of_pos ht, ← exp_add]
    congr 1
    ring
  have hl : log (t / P) = log t - log P := log_div ht.ne' hP.ne'
  rw [he, softplus_split]
  have hab : |s * (log P - log t)| = s * |log (t / P)| := by
    rw [abs_mul, abs_of_nonneg hs, hl, ← abs_neg (log t - log P)]
    congr 2
    ring
  rw [hab]
  dsimp only [weight]
  rw [neg_mul]
  congr 1
  split_ifs with h
  · exact max_eq_left (mul_nonneg hs (sub_nonneg.mpr (log_le_log ht h)))
  · exact max_eq_right
      (mul_nonpos_of_nonneg_of_nonpos hs
        (sub_nonpos.mpr (log_le_log hP (le_of_not_ge h))))

/-- The moving remainder is nonnegative. -/
theorem weight_nonneg (P s t : ℝ) : 0 ≤ weight P s t := by
  apply log_nonneg
  have := exp_nonneg (-s * |log (t / P)|)
  linarith

theorem weight_continuousOn {P s a b : ℝ} (hP : 0 < P) (ha : 0 < a) :
    ContinuousOn (weight P s) (Set.Icc a b) := by
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hl : ContinuousAt (fun u : ℝ => log (u / P)) t :=
    (continuousAt_id.div_const P).log (div_pos ht0 hP).ne'
  have he : ContinuousAt (fun u : ℝ => 1 + exp (-s * |log (u / P)|)) t :=
    continuousAt_const.add ((hl.abs.const_mul (-s)).rexp)
  exact (he.log (by positivity)).continuousWithinAt

/-- The smooth extension of the weight on the left of its peak. -/
def leftWeight (P s t : ℝ) : ℝ :=
  logWeight s (P ^ s) t - s * (log P - log t)

theorem leftWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t)
    (hs : 0 ≤ s) (htP : t ≤ P) : leftWeight P s t = weight P s t := by
  have h := logWeight_split hP ht hs
  rw [if_pos htP] at h
  dsimp only [leftWeight, logWeight]
  rw [div_eq_mul_inv, ← rpow_neg ht.le]
  linarith only [h]

theorem rightWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t)
    (hs : 0 ≤ s) (hPt : P ≤ t) : logWeight s (P ^ s) t = weight P s t := by
  rcases hPt.eq_or_lt with rfl | hPt
  · have h := logWeight_split hP hP hs
    simp only [le_refl, ↓reduceIte, sub_self, mul_zero, zero_add] at h
    dsimp only [logWeight]
    rwa [div_eq_mul_inv, ← rpow_neg hP.le]
  · have h := logWeight_split hP ht hs
    rw [if_neg hPt.not_ge, zero_add] at h
    dsimp only [logWeight]
    rwa [div_eq_mul_inv, ← rpow_neg ht.le]

theorem leftWeight_deriv {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    HasDerivAt (leftWeight P s)
      (s / t - abelKernel s (P ^ s) t) t := by
  have h := (logWeight_deriv (s := s) (rpow_pos_of_pos hP s) ht).sub
    (((hasDerivAt_const t (log P)).sub (hasDerivAt_log ht.ne')).const_mul s)
  convert h using 1
  · rfl
  · simp only [div_eq_mul_inv]
    ring

theorem leftWeight_at_cutoff {P s : ℝ} (hP : 0 < P) : leftWeight P s P = log 2 := by
  dsimp only [leftWeight, logWeight]
  rw [div_self (rpow_pos_of_pos hP s).ne']
  norm_num

theorem rightWeight_at_cutoff {P s : ℝ} (hP : 0 < P) :
    logWeight s (P ^ s) P = log 2 := by
  dsimp only [logWeight]
  rw [div_self (rpow_pos_of_pos hP s).ne']
  norm_num

theorem leftWeight_deriv_nonneg {P s t : ℝ} (hP : 0 < P) (ht : 0 < t)
    (hs : 0 ≤ s) : 0 ≤ s / t - abelKernel s (P ^ s) t := by
  have htp : 0 < t ^ s := rpow_pos_of_pos ht s
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s
  dsimp only [abelKernel]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < t * (t ^ s + P ^ s)) ht).mpr
  nlinarith [mul_nonneg hs htp.le]

/-- The localized prime sum is the exact remainder after subtracting the
prime-counting ramp, with no asymptotic or endpoint error. -/
theorem prime_weight_split {P s x : ℝ} (hP : 0 < P) (hPx : P ≤ x)
    (hs : 0 ≤ s) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + P ^ s * (p : ℝ) ^ (-s))) =
      s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) +
        remainder P s x := by
  classical
  have hsub : Nat.primesLE ⌊P⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpP, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpP.trans (Nat.floor_le_floor hPx), hpp⟩
  have hfilter : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ P) =
      Nat.primesLE ⌊P⌋₊ := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hpP⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff hP.le).mpr hpP, (Nat.mem_primesLE.mp hp).2⟩
    · intro hp
      exact mem_filter.mpr ⟨hsub hp,
        (Nat.le_floor_iff hP.le).mp (Nat.mem_primesLE.mp hp).1⟩
  have heq :
      (∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if (p : ℝ) ≤ P then s * (log P - log p) else 0)) =
        s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) := by
    rw [← sum_filter, hfilter, ← mul_sum, sum_sub_distrib,
      sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting,
      Chebyshev.theta_eq_sum_primesLE]
  calc
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ((if (p : ℝ) ≤ P then s * (log P - log p) else 0) + weight P s p) := by
      apply sum_congr rfl
      intro p hp
      exact logWeight_split hP
        (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos) hs
    _ = _ := by rw [sum_add_distrib, heq]; rfl

end D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
