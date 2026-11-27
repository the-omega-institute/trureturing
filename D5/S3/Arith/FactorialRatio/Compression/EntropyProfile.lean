/- GID: D5/S3/Arith/FactorialRatio/Compression/EntropyProfile
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/EntropyProfile
   mirror-E: none(waiver:symbolic-entropy-analysis)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.BinaryEntropy, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: The continuous entropy profile has a unique minimum, and every compact factorial term has a uniform positive quadratic obstruction. -/

import D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
The entropy profile is the integral of `v log v + (1-v) log(1-v)`
along `v=t*u`, including both endpoints. A quadratic majorant of binary
entropy gives a uniform bound for both the integral and the actual finite
grid. The latter estimate combines with the finite Stirling estimate for
the compact factorial family; it does not concern arbitrary compositions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.EntropyProfile

open Finset Real Set
open scoped Topology
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier

/-- The continuous average of the signed binary entropy. -/
def entropyIntegral (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, -Real.binEntropy (t * u)

private def primitive (v : ℝ) : ℝ :=
  (-v * negMulLog v + (1 - v) * negMulLog (1 - v) - v) / 2

private theorem primitive_deriv {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt primitive (-binEntropy v) v := by
  have hd := ((((hasDerivAt_id v).neg.mul
      (hasDerivAt_negMulLog hv.ne')).add
      (((hasDerivAt_id v).const_sub 1).mul
        ((hasDerivAt_negMulLog (sub_pos.mpr hv1).ne').comp v
          ((hasDerivAt_id v).const_sub 1)))).sub
      (hasDerivAt_id v)).div_const 2
  convert hd using 1
  · funext y
    dsimp [primitive, negMulLog] <;> ring
  · dsimp [binEntropy, negMulLog]
    simp only [Real.log_inv]
    ring

private theorem profile_continuous : Continuous entropyIntegral := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem profile_scaled {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * entropyIntegral t = primitive t := by
  have hp : ∫ v in (0 : ℝ)..t, -binEntropy v = primitive t - primitive 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    · unfold primitive
      fun_prop
    · intro v hv
      exact primitive_deriv hv.1 (hv.2.trans_le ht1)
    · exact binEntropy_continuous.neg.intervalIntegrable _ _
  have hs := intervalIntegral.mul_integral_comp_mul_left
    (f := fun v : ℝ => -binEntropy v) (a := 0) (b := 1) t
  have hs' : t * entropyIntegral t = ∫ v in (0 : ℝ)..t, -binEntropy v := by
    simpa only [mul_zero, mul_one, entropyIntegral] using hs
  simpa [primitive, negMulLog_def] using hs'.trans hp

private theorem profile_closed {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    entropyIntegral t = t / 2 * log t -
      (1 - t) ^ 2 / (2 * t) * log (1 - t) - 1 / 2 := by
  have hp := profile_scaled ht.le ht1
  dsimp [primitive, negMulLog] at hp
  apply (mul_left_cancel₀ ht.ne')
  calc
    t * entropyIntegral t = _ := hp
    _ = t * (t / 2 * log t -
      (1 - t) ^ 2 / (2 * t) * log (1 - t) - 1 / 2) := by
      field_simp [ht.ne']
      <;> ring

theorem profile_strictConvex : StrictConvexOn ℝ (Icc 0 1) entropyIntegral := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hc (t : ℝ) : Continuous (fun u : ℝ => -binEntropy (t * u)) := by fun_prop
  have hlin : (∫ u in (0 : ℝ)..1,
      a * (-binEntropy (x * u)) + b * (-binEntropy (y * u))) =
      a * entropyIntegral x + b * entropyIntegral y := by
    rw [intervalIntegral.integral_add ((hc x).intervalIntegrable _ _ |>.const_mul a)
      ((hc y).intervalIntegrable _ _ |>.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  simp only [smul_eq_mul]
  rw [← hlin]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num)
  · fun_prop
  · fun_prop
  · intro u hu
    have hxu : x * u ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hx.1 hu.1.le,
        (mul_le_mul_of_nonneg_right hx.2 hu.1.le).trans (by simpa using hu.2)⟩
    have hyu : y * u ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hy.1 hu.1.le,
        (mul_le_mul_of_nonneg_right hy.2 hu.1.le).trans (by simpa using hu.2)⟩
    have hh := Real.strictConcave_binEntropy.concaveOn.2 hxu hyu ha.le hb.le hab
    simp only [smul_eq_mul] at hh
    have heq : (a * x + b * y) * u = a * (x * u) + b * (y * u) := by ring
    rw [heq]
    nlinarith only [hh]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    have hxu : x * (1 / 2) ∈ Icc (0 : ℝ) 1 := by constructor <;> nlinarith [hx.1, hx.2]
    have hyu : y * (1 / 2) ∈ Icc (0 : ℝ) 1 := by constructor <;> nlinarith [hy.1, hy.2]
    have hne : x * (1 / 2) ≠ y * (1 / 2) := by intro h; apply hxy; linarith
    have hh := Real.strictConcave_binEntropy.2 hxu hyu hne ha hb hab
    simp only [smul_eq_mul] at hh
    have heq : (a * x + b * y) * (1 / 2) =
        a * (x * (1 / 2)) + b * (y * (1 / 2)) := by ring
    rw [heq]
    nlinarith only [hh]

private def correctedEntropy (v : ℝ) : ℝ := binEntropy v + 2 * (v - 1 / 2) ^ 2

private theorem corrected_concave : ConcaveOn ℝ (Icc 0 1) correctedEntropy := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun v =>
      log (1 - v) - log v + 4 * (v - 1 / 2))
    (f'' := fun v => -1 / (1 - v) - 1 / v + 4) (convex_Icc 0 1)
  · unfold correctedEntropy
    fun_prop
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hd := (hasDerivAt_binEntropy hv.1.ne' (ne_of_lt hv.2)).add
      ((((hasDerivAt_id v).sub_const (1 / 2)).pow 2).const_mul 2)
    convert hd.hasDerivWithinAt using 1
    · funext y
      dsimp [correctedEntropy] <;> ring
    · dsimp <;> ring
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hd := (((((hasDerivAt_id v).const_sub 1).log
        (sub_pos.mpr hv.2).ne').sub (Real.hasDerivAt_log hv.1.ne')).add
      (((hasDerivAt_id v).sub_const (1 / 2)).const_mul 4))
    convert hd.hasDerivWithinAt using 1
    · funext y
      dsimp <;> ring
    · dsimp <;> ring
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hden : 0 < v * (1 - v) := mul_pos hv.1 (sub_pos.mpr hv.2)
    have heq : -1 / (1 - v) - 1 / v + 4 =
        (4 * v * (1 - v) - 1) / (v * (1 - v)) := by
      field_simp [hv.1.ne', (sub_pos.mpr hv.2).ne']
      <;> ring
    rw [heq]
    apply div_nonpos_of_nonpos_of_nonneg _ hden.le
    nlinarith [sq_nonneg (2 * v - 1)]

private theorem entropy_quadratic {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    binEntropy v ≤ log 2 - (2 * v - 1) ^ 2 / 2 := by
  have h := corrected_concave.2 ⟨hv, hv1⟩
    (show 1 - v ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hm : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • (1 - v) = 2⁻¹ := by
    simp only [smul_eq_mul]; ring
  rw [hm] at h
  simp only [correctedEntropy, binEntropy_one_sub, binEntropy_two_inv, smul_eq_mul] at h
  nlinarith

private theorem average_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -(log 2 - 1 / 8) ≤ entropyIntegral t := by
  have hint : IntervalIntegrable (fun u : ℝ => log 2 - (2 * (t * u) - 1) ^ 2 / 2)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hp : (∫ u in (0 : ℝ)..1, log 2 - (2 * (t * u) - 1) ^ 2 / 2) =
      log 2 - 1 / 2 + t - 2 / 3 * t ^ 2 := by
    let F : ℝ → ℝ := fun u => (log 2 - 1 / 2) * u + t * u ^ 2 - 2 / 3 * t ^ 2 * u ^ 3
    have hF (u : ℝ) : HasDerivAt F (log 2 - (2 * (t * u) - 1) ^ 2 / 2) u := by
      convert ((((hasDerivAt_id u).const_mul (log 2 - 1 / 2)).add
        (((hasDerivAt_id u).pow 2).const_mul t)).sub
        (((hasDerivAt_id u).pow 3).const_mul (2 / 3 * t ^ 2))) using 1
      · funext y
        dsimp [F] <;> ring
      · dsimp [F] <;> ring
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u) hint
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((by fun_prop : Continuous (fun u : ℝ => binEntropy (t * u))).intervalIntegrable _ _) hint
    (fun u hu => entropy_quadratic (mul_nonneg ht hu.1)
      ((mul_le_mul_of_nonneg_right ht1 hu.1).trans (by simpa using hu.2)))
  rw [hp] at hm
  rw [entropyIntegral, intervalIntegral.integral_neg]
  nlinarith [sq_nonneg (4 * t - 3)]

/-- The signed average is continuous, has its explicit closed form and endpoint
values, and has a unique minimum on the closed unit interval. Its negative is
uniformly smaller than the Euler--Mascheroni constant. -/
theorem entropy_profile :
    Continuous entropyIntegral ∧ entropyIntegral 0 = 0 ∧ entropyIntegral 1 = -1 / 2 ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 → entropyIntegral t =
        t / 2 * log t - (1 - t) ^ 2 / (2 * t) * log (1 - t) - 1 / 2) ∧
      (∃! t : ℝ, t ∈ Set.Icc 0 1 ∧ ∀ v ∈ Set.Icc 0 1, entropyIntegral t ≤ entropyIntegral v) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, -(log 2 - 1 / 8) ≤ entropyIntegral t ∧
        0 < Real.eulerMascheroniConstant + entropyIntegral t) := by
  refine ⟨profile_continuous, by simp [entropyIntegral], ?_,
    fun _ ht ht1 => profile_closed ht ht1, ?_, ?_⟩
  · simpa [primitive, negMulLog_def] using profile_scaled (t := 1) (by norm_num) le_rfl
  · obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) profile_continuous.continuousOn
    refine ⟨t, ⟨ht, hmin⟩, ?_⟩
    intro v hv
    exact profile_strictConvex.eq_of_isMinOn hv.2 hmin hv.1 ht
  · intro t ht
    have hb := average_bound ht.1 ht.2
    refine ⟨hb, ?_⟩
    have hg := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
    have hl := Real.log_two_lt_d9
    linarith only [hb, hg.1, hl]

private theorem quadratic_sum (r : ℕ) (w : ℝ) :
    (∑ i ∈ range r, (log 2 - (2 * ((i : ℝ) * w) - 1) ^ 2 / 2)) =
      (r : ℝ) * (log 2 - 1 / 2) + (r : ℝ) * ((r : ℝ) - 1) * w -
        (r : ℝ) * ((r : ℝ) - 1) * (2 * (r : ℝ) - 1) / 3 * w ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

private theorem grid_entropy_bound (r : ℕ) {w : ℝ} (hw : 0 ≤ w) (hrw : (r : ℝ) * w ≤ 1) :
    (∑ i ∈ range r, binEntropy ((i : ℝ) * w)) ≤ (r : ℝ) * (log 2 - 1 / 8) := by
  calc
    _ ≤ ∑ i ∈ range r, (log 2 - (2 * ((i : ℝ) * w) - 1) ^ 2 / 2) := by
      apply sum_le_sum
      intro i hi
      apply entropy_quadratic (mul_nonneg (Nat.cast_nonneg _) hw)
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hi).le) hw).trans hrw
    _ ≤ _ := by
      rw [quadratic_sum]
      have hpos : 0 ≤ (r : ℝ) * w * (1 - (r : ℝ) * w) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hw) (sub_nonneg.mpr hrw)
      have hid : (r : ℝ) * (log 2 - 1 / 8) -
          ((r : ℝ) * (log 2 - 1 / 2) + (r : ℝ) * ((r : ℝ) - 1) * w -
            (r : ℝ) * ((r : ℝ) - 1) * (2 * (r : ℝ) - 1) / 3 * w ^ 2) =
          (r : ℝ) / 24 * (4 * (r : ℝ) * w - 3) ^ 2 +
            (r : ℝ) * w * (1 - (r : ℝ) * w) + (r : ℝ) * w ^ 2 / 3 := by ring
      have hs : 0 ≤ (r : ℝ) / 24 * (4 * (r : ℝ) * w - 3) ^ 2 := by positivity
      have hs' : 0 ≤ (r : ℝ) * w ^ 2 / 3 := by positivity
      linarith

private theorem finite_entropy_bound (r s b : ℕ) (hb : r * b ≤ s) :
    (∑ i ∈ range r, binEntropy (((i * b : ℕ) : ℝ) / s)) ≤
      (r : ℝ) * (41 / 72 : ℝ) := by
  have hw : 0 ≤ (b : ℝ) / s := by positivity
  have hrw : (r : ℝ) * ((b : ℝ) / s) ≤ 1 := by
    by_cases hs : s = 0
    · simp [hs]
    · have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
      rw [← mul_div_assoc, div_le_one hsR]
      exact_mod_cast hb
  have hh := grid_entropy_bound r hw hrw
  have heq : (∑ i ∈ range r, binEntropy (((i * b : ℕ) : ℝ) / s)) =
      ∑ i ∈ range r, binEntropy ((i : ℝ) * ((b : ℝ) / s)) := by
    apply sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  rw [heq]
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith [Real.log_two_lt_d9]

/-- Every legal individual compact term has the entropy loss at most `41/72`,
with the actual finite Stirling error. The boundary term is nonnegative and
can be omitted in this lower bound. No limit or Riemann-sum premise is used. -/
theorem compact_single_term_lower_bound (r s b : ℕ) (hb : r * b ≤ s) :
    (r : ℝ) * s * (log s - 1 - 41 / 72) -
        2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1) ≤
      log (selbergFactorial r s b : ℝ) := by
  have hst := (abs_le.mp (compact_stirling_entropy_bound r s b hb)).1
  have hsum := mul_le_mul_of_nonneg_left (finite_entropy_bound r s b hb)
    (Nat.cast_nonneg s)
  have hboundary : 0 ≤ (r : ℝ) * b * log r := by
    exact mul_nonneg (by positivity) (Real.log_natCast_nonneg r)
  nlinarith only [hst, hsum, hboundary]

private theorem real_window_main {m : ℝ} (hm : 2 ≤ m) :
    m ^ 2 * (log (m ^ 2) - 1 - 41 / 72) - 2 * m - 2 * log (m + 1) ≤
      (m ^ 2 - 1) * (log (m * (m - 1)) - 1 - 41 / 72) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hfrac := Real.one_sub_inv_le_log_of_pos (div_pos hm1 hm0)
  have hlog : log (m * (m - 1)) = log (m ^ 2) + log ((m - 1) / m) := by
    rw [Real.log_mul hm0.ne' hm1.ne', Real.log_pow,
      Real.log_div hm1.ne' hm0.ne']
    ring
  have hinv : 1 - ((m - 1) / m)⁻¹ = -1 / (m - 1) := by
    field_simp [hm0.ne', hm1.ne']
    <;> ring
  rw [hinv] at hfrac
  have hden : -2 / m ≤ -1 / (m - 1) := by
    apply (div_le_div_iff₀ hm0 hm1).2
    nlinarith
  have hlower : log (m ^ 2) - 2 / m ≤ log (m * (m - 1)) := by
    rw [hlog]
    calc
      _ = log (m ^ 2) + (-2 / m) := by ring
      _ ≤ log (m ^ 2) + (-1 / (m - 1)) := add_le_add le_rfl hden
      _ ≤ _ := add_le_add le_rfl hfrac
  have hupper : log (m ^ 2) ≤ 2 * log (m + 1) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hm0 (by linarith)) (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hlower (show 0 ≤ m ^ 2 - 1 by nlinarith)
  have hid : (m ^ 2 - 1) * (log (m ^ 2) - 2 / m - 1 - 41 / 72) =
      m ^ 2 * (log (m ^ 2) - 1 - 41 / 72) - log (m ^ 2) + 1 + 41 / 72 -
        2 * m + 2 / m := by
    field_simp [hm0.ne']
    <;> ring
  have hmul : (m ^ 2 - 1) * (log (m ^ 2) - 2 / m - 1 - 41 / 72) ≤
      (m ^ 2 - 1) * (log (m * (m - 1)) - 1 - 41 / 72) := by nlinarith only [hprod]
  rw [hid] at hmul
  have hdiv : 0 ≤ 2 / m := by positivity
  linarith

/-- On `r=M+1`, `s=M(M-1)`, every legal single term exceeds the factorial
benchmark by a positive multiple of `M²`, up to the explicit error
`8*M*(log(M+1)+1)`. The inequality is uniform in the integer parameter. -/
theorem quadratic_window_obstruction (M b : ℕ) (hM : 2 ≤ M)
    (hb : (M + 1) * b ≤ M * (M - 1)) :
    0 < Real.eulerMascheroniConstant - 41 / 72 ∧
      (Real.eulerMascheroniConstant - 41 / 72) * (M : ℝ) ^ 2 -
          8 * (M : ℝ) * (log ((M : ℝ) + 1) + 1) ≤
        log (selbergFactorial (M + 1) (M * (M - 1)) b : ℝ) / M -
          ((M : ℝ) ^ 2 * log ((M : ℝ) ^ 2) -
            (1 + Real.eulerMascheroniConstant) * (M : ℝ) ^ 2) := by
  have hg := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  refine ⟨by linarith [hg.1], ?_⟩
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hs : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hst := compact_single_term_lower_bound (M + 1) (M * (M - 1)) b hb
  rw [hs, Nat.cast_add, Nat.cast_one] at hst
  have hd := div_le_div_of_nonneg_right hst hm0.le
  have heq : (((M : ℝ) + 1) * ((M : ℝ) * ((M : ℝ) - 1)) *
        (log ((M : ℝ) * ((M : ℝ) - 1)) - 1 - 41 / 72) -
        2 * ((M : ℝ) + 1) * (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1)) / M =
      ((M : ℝ) ^ 2 - 1) * (log ((M : ℝ) * ((M : ℝ) - 1)) - 1 - 41 / 72) -
        (2 * ((M : ℝ) + 1) / M) * (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1) := by
    field_simp [hm0.ne']
    <;> ring
  rw [heq] at hd
  have hc : 2 * ((M : ℝ) + 1) / M ≤ 3 := by
    apply (div_le_iff₀ hm0).2
    linarith
  have hlog : log ((M : ℝ) * ((M : ℝ) - 1) + 1) ≤ 2 * log ((M : ℝ) + 1) := by
    have hl := Real.log_le_log
      (show 0 < (M : ℝ) * ((M : ℝ) - 1) + 1 by nlinarith)
      (show (M : ℝ) * ((M : ℝ) - 1) + 1 ≤ ((M : ℝ) + 1) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  have hlogs : 0 ≤ log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1 := by
    have hl := Real.log_nonneg (show 1 ≤ (M : ℝ) * ((M : ℝ) - 1) + 1 by nlinarith)
    linarith
  have herror : (2 * ((M : ℝ) + 1) / M) *
        (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1) ≤
      6 * log ((M : ℝ) + 1) + 3 := by
    calc
      _ ≤ 3 * (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1) :=
        mul_le_mul_of_nonneg_right hc hlogs
      _ ≤ _ := by linarith
  have hmain := real_window_main hm
  have hL : 0 ≤ log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hML : 0 ≤ ((M : ℝ) - 1) * log ((M : ℝ) + 1) :=
    mul_nonneg (by linarith) hL
  nlinarith only [hd, herror, hmain, hML, hm]

end D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
