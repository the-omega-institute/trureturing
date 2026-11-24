/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchorLogMean
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchorLogMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A three-point Simpson bound controls the logarithmic mean on positive scalars. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-!
Omega original.

The scalar logarithmic mean is bounded above by the Simpson average of
the arithmetic and geometric means. This is the scalar kernel comparison
used after the two-slot Gram bound.
-/

namespace Omega.CovarianceToAnchor

noncomputable section

/-- The logarithmic mean on the positive reals, including its diagonal value. -/
def logarithmicMean (a b : ℝ) : ℝ :=
  if a = b then a else (a - b) / (Real.log a - Real.log b)

/-- The hyperbolic Simpson estimate with the denominator cleared. -/
theorem three_sinh_le_mul_cosh_add_two {s : ℝ} (hs : 0 ≤ s) :
    3 * Real.sinh s ≤ s * (Real.cosh s + 2) := by
  let f (n : ℕ) : ℝ := 3 * (s ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ))
  let g (n : ℕ) : ℝ := s * (s ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))
  have hf : HasSum f (3 * Real.sinh s) := (Real.hasSum_sinh s).mul_left 3
  have hg : HasSum g (s * Real.cosh s) := (Real.hasSum_cosh s).mul_left s
  have hfTail : Summable (fun n : ℕ => f (n + 1)) := (summable_nat_add_iff 1).2 hf.summable
  have hgTail : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff 1).2 hg.summable
  have hTerm (n : ℕ) : f (n + 1) ≤ g (n + 1) := by
    let k : ℕ := 2 * (n + 1)
    have hk : 3 ≤ k + 1 := by dsimp [k]; omega
    have hk' : (3 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
    have hkPos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hFac : (k.factorial : ℝ) ≠ 0 := by positivity
    change 3 * (s ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤ s * (s ^ k / (k.factorial : ℝ))
    calc
      _ = (3 / ((k + 1 : ℕ) : ℝ)) * (s * (s ^ k / (k.factorial : ℝ))) := by
        rw [pow_succ', Nat.factorial_succ, Nat.cast_mul]
        field_simp [hkPos.ne', hFac] <;> ring
      _ ≤ 1 * (s * (s ^ k / (k.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hkPos).2 (by simpa using hk'))
          (mul_nonneg hs (div_nonneg (pow_nonneg hs _) (Nat.cast_nonneg _)))
      _ = _ := one_mul _
  have hTail := hfTail.tsum_le_tsum hTerm hgTail
  have hf0 : f 0 = 3 * s := by norm_num [f, Nat.factorial]
  have hg0 : g 0 = s := by norm_num [g, Nat.factorial]
  have hfs := hf.summable.tsum_eq_zero_add
  have hgs := hg.summable.tsum_eq_zero_add
  rw [hf.tsum_eq, hf0] at hfs
  rw [hg.tsum_eq, hg0] at hgs
  nlinarith only [hTail, hfs, hgs]

private theorem log_quotient_le_simpson_of_lt {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    (a - b) / (Real.log a - Real.log b) ≤ (a + b + 4 * Real.sqrt (a * b)) / 6 := by
  have ha := lt_trans hb hba
  let s := (Real.log a - Real.log b) / 2
  let g := Real.exp ((Real.log a + Real.log b) / 2)
  have hs : 0 < s := div_pos (sub_pos.mpr (Real.log_lt_log hb hba)) (by norm_num)
  have hg : 0 ≤ g := (Real.exp_pos _).le
  have hPlus : g * Real.exp s = a := by
    dsimp [g, s]
    rw [← Real.exp_add, show (Real.log a + Real.log b) / 2 +
      (Real.log a - Real.log b) / 2 = Real.log a by ring, Real.exp_log ha]
  have hMinus : g * Real.exp (-s) = b := by
    dsimp [g, s]
    rw [← Real.exp_add, show (Real.log a + Real.log b) / 2 +
      -((Real.log a - Real.log b) / 2) = Real.log b by ring, Real.exp_log hb]
  have hSinh : 2 * g * Real.sinh s = a - b := by
    rw [Real.sinh_eq]
    linear_combination hPlus - hMinus
  have hCosh : 2 * g * Real.cosh s = a + b := by
    rw [Real.cosh_eq]
    linear_combination hPlus + hMinus
  have hSq : g ^ 2 = a * b := by
    dsimp [g]
    rw [pow_two, ← Real.exp_add, show (Real.log a + Real.log b) / 2 +
      (Real.log a + Real.log b) / 2 = Real.log a + Real.log b by ring,
      Real.exp_add, Real.exp_log ha, Real.exp_log hb]
  have hRoot : Real.sqrt (a * b) = g := by rw [← hSq, Real.sqrt_sq hg]
  have hLog : Real.log a - Real.log b = 2 * s := by dsimp [s]; ring
  have hRatio : Real.sinh s / s ≤ (Real.cosh s + 2) / 3 := by
    apply (div_le_iff₀ hs).2
    nlinarith only [three_sinh_le_mul_cosh_add_two hs.le]
  calc
    (a - b) / (Real.log a - Real.log b) = g * (Real.sinh s / s) := by
      rw [← hSinh, hLog]
      field_simp [hs.ne'] <;> ring
    _ ≤ g * ((Real.cosh s + 2) / 3) := mul_le_mul_of_nonneg_left hRatio hg
    _ = (2 * g * Real.cosh s + 4 * g) / 6 := by ring
    _ = _ := by rw [hCosh, hRoot]

/-- The logarithmic mean is at most one third of the arithmetic mean plus
two thirds of the geometric mean. The hypotheses are the positive spectral
weights of a faithful anchor and allow coincident weights. -/
theorem logarithmic_mean_le_simpson {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logarithmicMean a b ≤ (a + b + 4 * Real.sqrt (a * b)) / 6 := by
  rcases lt_trichotomy b a with hba | hba | hab
  · simpa only [logarithmicMean, if_neg hba.ne'] using log_quotient_le_simpson_of_lt hb hba
  · subst b
    rw [logarithmicMean, if_pos rfl, Real.sqrt_mul_self ha.le]
    linarith
  · have hSym : (a - b) / (Real.log a - Real.log b) =
        (b - a) / (Real.log b - Real.log a) := by
      rw [show a - b = -(b - a) by ring,
        show Real.log a - Real.log b = -(Real.log b - Real.log a) by ring, neg_div_neg_eq]
    simpa only [logarithmicMean, if_neg hab.ne, hSym, add_comm a b, mul_comm a b] using
      log_quotient_le_simpson_of_lt ha hab

end

end Omega.CovarianceToAnchor

#print axioms Omega.CovarianceToAnchor.three_sinh_le_mul_cosh_add_two
#print axioms Omega.CovarianceToAnchor.logarithmic_mean_le_simpson
