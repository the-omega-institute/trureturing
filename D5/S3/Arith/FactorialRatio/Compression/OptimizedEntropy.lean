/- GID: D5/S3/Arith/FactorialRatio/Compression/OptimizedEntropy
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/OptimizedEntropy
   mirror-E: none(waiver:symbolic-entropy-analysis)
   anchors: [mathlib/module/Mathlib.Analysis.SumIntegralComparisons, mathlib/module/Mathlib.Analysis.SpecialFunctions.BinaryEntropy]
   utility: none
   digest: The actual minimum of the legal compact factorial family has the exact optimized entropy coefficient with a finite error. -/

import D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

/-! The entropy integral determines the actual optimized finite factorial family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy

open Finset Real Set
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
open D5.S3.Arith.FactorialRatio.Compression.EntropyProfile

private theorem monotone_grid (r : ℕ) (hr : 0 < r) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc 0 1)) :
    0 ≤ (r : ℝ) * (∫ u in (0 : ℝ)..1, f u) - ∑ i ∈ range r, f ((i : ℝ) / r) ∧
      (r : ℝ) * (∫ u in (0 : ℝ)..1, f u) - ∑ i ∈ range r, f ((i : ℝ) / r) ≤ f 1 - f 0 := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hm : MonotoneOn (fun x : ℝ => f (x / r)) (Set.Icc 0 (0 + (r : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hrR.le, (div_le_one hrR).2 (by simpa using hx.2)⟩
    · exact ⟨div_nonneg hy.1 hrR.le, (div_le_one hrR).2 (by simpa using hy.2)⟩
    · exact div_le_div_of_nonneg_right hxy hrR.le
  have hlo := hm.sum_le_integral
  have hhi := hm.integral_le_sum
  have hscale : (∫ u in (0 : ℝ)..(r : ℝ), f (u / r)) =
      (r : ℝ) * (∫ u in (0 : ℝ)..1, f u) := by
    simpa only [zero_div, div_self hrR.ne', smul_eq_mul] using
      (intervalIntegral.integral_comp_div (f := f) (a := 0) (b := (r : ℝ)) hrR.ne')
  simp only [zero_add] at hlo hhi
  rw [hscale] at hlo hhi
  have hshift : (∑ i ∈ range r, f (((i + 1 : ℕ) : ℝ) / r)) =
      (∑ i ∈ range r, f ((i : ℝ) / r)) + f 1 - f 0 := by
    have h := sum_range_succ' (fun i : ℕ => f ((i : ℝ) / r)) r
    rw [sum_range_succ] at h
    simpa only [Nat.cast_zero, zero_div, div_self hrR.ne'] using (eq_sub_of_add_eq h.symm)
  rw [hshift] at hhi
  constructor <;> linarith

private theorem entropy_grid (r : ℕ) (hr : 0 < r) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    |(∑ i ∈ range r, binEntropy (t * ((i : ℝ) / r))) +
      (r : ℝ) * entropyIntegral t| ≤ 2 * log 2 := by
  let f : ℝ → ℝ := fun u => binEntropy (min (t * u) (1 / 2))
  let g : ℝ → ℝ := fun u => -binEntropy (max (t * u) (1 / 2))
  have hf : MonotoneOn f (Set.Icc 0 1) := by
    intro x hx y hy hxy
    apply binEntropy_strictMonoOn.monotoneOn
    · exact ⟨le_min (mul_nonneg ht.1 hx.1) (by norm_num), by norm_num⟩
    · exact ⟨le_min (mul_nonneg ht.1 hy.1) (by norm_num), by norm_num⟩
    · exact min_le_min_right _ (mul_le_mul_of_nonneg_left hxy ht.1)
  have hg : MonotoneOn g (Set.Icc 0 1) := by
    intro x hx y hy hxy
    apply neg_le_neg
    apply binEntropy_strictAntiOn.antitoneOn
    · exact ⟨by norm_num, max_le (by nlinarith [ht.1, ht.2, hx.1, hx.2]) (by norm_num)⟩
    · exact ⟨by norm_num, max_le (by nlinarith [ht.1, ht.2, hy.1, hy.2]) (by norm_num)⟩
    · exact max_le_max_right _ (mul_le_mul_of_nonneg_left hxy ht.1)
  have hsplit (u : ℝ) : binEntropy (t * u) = f u - g u - log 2 := by
    dsimp [f, g]
    have he : binEntropy (1 / 2 : ℝ) = log 2 := by
      convert binEntropy_two_inv using 1 <;> norm_num
    rcases le_total (t * u) (1 / 2) with h | h
    · rw [min_eq_left h, max_eq_right h]
      rw [he]
      ring
    · rw [min_eq_right h, max_eq_left h]
      rw [he]
      ring
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hi : entropyIntegral t = -((∫ u in (0 : ℝ)..1, f u) -
      (∫ u in (0 : ℝ)..1, g u) - log 2) := by
    simp only [entropyIntegral, intervalIntegral.integral_neg]
    simp_rw [hsplit]
    rw [intervalIntegral.integral_sub
      ((hfc.intervalIntegrable _ _).sub (hgc.intervalIntegrable _ _))
      (intervalIntegrable_const), intervalIntegral.integral_sub
      (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
    simp
  have hs : (∑ i ∈ range r, binEntropy (t * ((i : ℝ) / r))) =
      (∑ i ∈ range r, f ((i : ℝ) / r)) -
      (∑ i ∈ range r, g ((i : ℝ) / r)) - (r : ℝ) * log 2 := by
    simp_rw [hsplit]
    simp [sum_sub_distrib]
  have hF := monotone_grid r hr f hf
  have hG := monotone_grid r hr g hg
  have hfend : f 1 - f 0 ≤ log 2 := by
    dsimp [f]
    simp only [mul_one, mul_zero, min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2), binEntropy_zero]
    simpa only [sub_zero] using (binEntropy_le_log_two (p := min t (1 / 2)))
  have hgend : g 1 - g 0 ≤ log 2 := by
    dsimp [g]
    simp only [mul_one, mul_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hn := binEntropy_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_right t (1 / 2)))
      (max_le ht.2 (by norm_num))
    have he : binEntropy (1 / 2 : ℝ) = log 2 := by convert binEntropy_two_inv using 1 <;> norm_num
    rw [he]
    linarith
  rw [hs, hi]
  apply abs_le.mpr
  constructor <;> linarith [(Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- The optimizer of the continuous signed entropy on the closed unit interval. -/
def entropyOptimizer : ℝ := Classical.choose entropy_profile.2.2.2.2.1.exists

/-- The exact optimized entropy coefficient. -/
def kappa : ℝ := -entropyIntegral entropyOptimizer

private theorem optimizer_spec : entropyOptimizer ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ v ∈ Set.Icc (0 : ℝ) 1, entropyIntegral entropyOptimizer ≤ entropyIntegral v :=
  Classical.choose_spec entropy_profile.2.2.2.2.1.exists

private theorem optimizer_positive : 0 < entropyOptimizer := by
  have hh := optimizer_spec.2 1 (by simp)
  rw [entropy_profile.2.2.1] at hh
  have hn : entropyOptimizer ≠ 0 := by
    intro hz
    rw [hz, entropy_profile.2.1] at hh
    norm_num at hh
  exact lt_of_le_of_ne optimizer_spec.1.1 (Ne.symm hn)

private theorem kappa_bounds : 0 ≤ kappa ∧ kappa ≤ log 2 - 1 / 8 := by
  have hmin := optimizer_spec.2 1 (by simp)
  rw [entropy_profile.2.2.1] at hmin
  have hb := (entropy_profile.2.2.2.2.2 _ optimizer_spec.1).1
  dsimp [kappa]
  constructor <;> linarith

private theorem rounded_optimizer (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ b : ℕ, r * b ≤ s ∧
      entropyIntegral ((r : ℝ) * b / s) + kappa ≤
        (kappa / entropyOptimizer) * (r : ℝ) / s := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have ht := optimizer_positive
  let b : ℕ := ⌊entropyOptimizer * s / r⌋₊
  have hb : (b : ℝ) ≤ entropyOptimizer * s / r := Nat.floor_le (by positivity)
  have hb' : entropyOptimizer * s / r < (b : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrt : (r : ℝ) * b ≤ entropyOptimizer * s := by
    have hh := (le_div_iff₀ hrR).1 hb
    nlinarith only [hh]
  have hlegalR : (r : ℝ) * b ≤ s :=
    hrt.trans (mul_le_of_le_one_left hsR.le optimizer_spec.1.2)
  have hlegal : r * b ≤ s := by exact_mod_cast hlegalR
  have htb : (r : ℝ) * b / s ≤ entropyOptimizer := (div_le_iff₀ hsR).2 hrt
  have htb0 : 0 ≤ (r : ℝ) * b / s := by positivity
  have hgap : entropyOptimizer - (r : ℝ) * b / s ≤ (r : ℝ) / s := by
    have hh := (div_lt_iff₀ hrR).1 hb'
    apply (le_div_iff₀ hsR).2
    have hid : (entropyOptimizer - (r : ℝ) * b / s) * s =
        entropyOptimizer * s - (r : ℝ) * b := by field_simp <;> ring
    rw [hid]
    nlinarith only [hh]
  have hratio : 0 ≤ ((r : ℝ) * b / s) / entropyOptimizer := by positivity
  have hratio1 : ((r : ℝ) * b / s) / entropyOptimizer ≤ 1 :=
    (div_le_one ht).2 htb
  have hc := profile_strictConvex.convexOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) optimizer_spec.1
    (sub_nonneg.mpr hratio1) hratio (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, entropy_profile.2.1, mul_zero] at hc
  have heq : ((r : ℝ) * b / s / entropyOptimizer) * entropyOptimizer =
      (r : ℝ) * b / s := div_mul_cancel₀ _ ht.ne'
  rw [heq] at hc
  refine ⟨b, hlegal, ?_⟩
  have hK : 0 ≤ kappa / entropyOptimizer := div_nonneg kappa_bounds.1 ht.le
  have hg := mul_le_mul_of_nonneg_left hgap hK
  have hid : (kappa / entropyOptimizer) *
      (entropyOptimizer - (r : ℝ) * b / s) =
      kappa - ((r : ℝ) * b / s / entropyOptimizer) * kappa := by
    field_simp [ht.ne']
    <;> ring
  rw [hid] at hg
  have hright : (kappa / entropyOptimizer) * ((r : ℝ) / s) =
      (kappa / entropyOptimizer) * (r : ℝ) / s := by ring
  rw [hright] at hg
  dsimp only [kappa] at hc hg ⊢
  nlinarith only [hc, hg]

private def stirlingError (r s : ℕ) : ℝ :=
  2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1) + 2 * (s : ℝ) * log 2

private theorem finite_comparison (r s b : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hb : r * b ≤ s) :
    |log (selbergFactorial r s b : ℝ) -
      ((r : ℝ) * s * (log s - 1 + entropyIntegral ((r : ℝ) * b / s)) +
        (r : ℝ) * b * log r)| ≤ stirlingError r s := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have ht : (r : ℝ) * b / s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hsR).2
      exact_mod_cast hb
  have hg := entropy_grid r hr ht
  have hid (i : ℕ) : ((r : ℝ) * b / s) * ((i : ℝ) / r) =
      (((i * b : ℕ) : ℝ) / s) := by
    push_cast
    field_simp
    <;> ring
  simp_rw [hid] at hg
  have hst := compact_stirling_entropy_bound r s b hb
  have hsum : |(s : ℝ) * ((∑ i ∈ range r, binEntropy (((i * b : ℕ) : ℝ) / s)) +
      (r : ℝ) * entropyIntegral ((r : ℝ) * b / s))| ≤ (s : ℝ) * (2 * log 2) := by
    rw [abs_mul, abs_of_nonneg hsR.le]
    exact mul_le_mul_of_nonneg_left hg hsR.le
  have hh := (abs_add_le (log (selbergFactorial r s b : ℝ) -
      ((r : ℝ) * s * (log s - 1) + (r : ℝ) * b * log r -
        (s : ℝ) * ∑ i ∈ range r, binEntropy (((i * b : ℕ) : ℝ) / s)))
      (-((s : ℝ) * ((∑ i ∈ range r, binEntropy (((i * b : ℕ) : ℝ) / s)) +
        (r : ℝ) * entropyIntegral ((r : ℝ) * b / s))))).trans
    (add_le_add hst (by simpa only [abs_neg] using hsum))
  dsimp only [stirlingError]
  convert hh using 1 <;> congr 1 <;> ring

private theorem all_terms_lower (r s b : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hb : r * b ≤ s) :
    (r : ℝ) * s * (log s - 1 - kappa) - stirlingError r s ≤
      log (selbergFactorial r s b : ℝ) := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have ht : (r : ℝ) * b / s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hsR).2
      exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_left (optimizer_spec.2 _ ht)
    (mul_nonneg hrR.le hsR.le)
  have he := (abs_le.mp (finite_comparison r s b hr hs hb)).1
  have hbnd : 0 ≤ (r : ℝ) * b * log r :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg r)
  dsimp [kappa]
  nlinarith only [hm, he, hbnd]

private theorem attained_upper (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ b : ℕ, r * b ≤ s ∧ log (selbergFactorial r s b : ℝ) ≤
      (r : ℝ) * s * (log s - 1 - kappa) + stirlingError r s +
        (s : ℝ) * log r + (kappa / entropyOptimizer) * (r : ℝ) ^ 2 := by
  obtain ⟨b, hb, hg⟩ := rounded_optimizer r s hr hs
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have he := (abs_le.mp (finite_comparison r s b hr hs hb)).2
  have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg hrR.le hsR.le)
  have heq : (r : ℝ) * s * ((kappa / entropyOptimizer) * r / s) =
      (kappa / entropyOptimizer) * (r : ℝ) ^ 2 := by field_simp <;> ring
  rw [heq] at hm
  have hbnd : (r : ℝ) * b * log r ≤ (s : ℝ) * log r :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (Real.log_natCast_nonneg r)
  refine ⟨b, hb, ?_⟩
  nlinarith only [he, hm, hbnd]

private theorem window_main_error {m : ℝ} (hm : 2 ≤ m) :
    |(m ^ 2 - 1) * (log (m * (m - 1)) - 1 - kappa) -
      m ^ 2 * (log (m ^ 2) - 1 - kappa)| ≤
        4 * m * (log (m + 1) + 1) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hk0 := kappa_bounds.1
  have hk1 : kappa ≤ 1 := by linarith [kappa_bounds.2, Real.log_two_lt_d9]
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
  have hupper : log (m * (m - 1)) ≤ log (m ^ 2) :=
    Real.log_le_log (mul_pos hm0 hm1) (by nlinarith)
  have hL : 0 ≤ log (m + 1) := Real.log_nonneg (by linarith)
  have hlog0 : 0 ≤ log (m ^ 2) := Real.log_nonneg (by nlinarith)
  have hlog1 : log (m ^ 2) ≤ 2 * log (m + 1) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hm0 (by linarith)) (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hlower (show 0 ≤ m ^ 2 - 1 by nlinarith)
  have hprod' := mul_le_mul_of_nonneg_left hupper (show 0 ≤ m ^ 2 - 1 by nlinarith)
  have hid : (m ^ 2 - 1) * (log (m ^ 2) - 2 / m - 1 - kappa) =
      m ^ 2 * (log (m ^ 2) - 1 - kappa) - log (m ^ 2) + 1 + kappa -
        2 * m + 2 / m := by
    field_simp [hm0.ne']
    <;> ring
  have hlo : -2 * m - 2 * log (m + 1) ≤
      (m ^ 2 - 1) * (log (m * (m - 1)) - 1 - kappa) -
        m ^ 2 * (log (m ^ 2) - 1 - kappa) := by
    have hh : (m ^ 2 - 1) * (log (m ^ 2) - 2 / m - 1 - kappa) ≤
        (m ^ 2 - 1) * (log (m * (m - 1)) - 1 - kappa) := by nlinarith only [hprod]
    rw [hid] at hh
    have hp : 0 ≤ 2 / m := by positivity
    linarith
  have hhi : (m ^ 2 - 1) * (log (m * (m - 1)) - 1 - kappa) -
      m ^ 2 * (log (m ^ 2) - 1 - kappa) ≤ 2 := by
    nlinarith only [hprod', hlog0, hk1]
  have hmL : 0 ≤ (m - 1) * log (m + 1) := mul_nonneg (by linarith) hL
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Legal integer parameters of the quadratic window, including zero. -/
def legalParameters (M : ℕ) : Finset ℕ :=
  (range (M * (M - 1) + 1)).filter (fun b => (M + 1) * b ≤ M * (M - 1))

private theorem legal_nonempty (M : ℕ) : (legalParameters M).Nonempty := by
  refine ⟨0, ?_⟩
  simp [legalParameters]

/-- The loss of the actual compact factorial term relative to the factorial benchmark. -/
def windowLoss (M b : ℕ) : ℝ :=
  log (selbergFactorial (M + 1) (M * (M - 1)) b : ℝ) / M -
    ((M : ℝ) ^ 2 * log ((M : ℝ) ^ 2) -
      (1 + Real.eulerMascheroniConstant) * (M : ℝ) ^ 2)

/-- The actual finite minimum over all legal natural parameters. -/
def minimumLoss (M : ℕ) : ℝ :=
  (legalParameters M).inf' (legal_nonempty M) (windowLoss M)

private theorem legal_mem (M b : ℕ) (hb : (M + 1) * b ≤ M * (M - 1)) :
    b ∈ legalParameters M := by
  have hbs : b ≤ M * (M - 1) := (Nat.le_mul_of_pos_left b (by omega)).trans hb
  simp [legalParameters, hb, show b < M * (M - 1) + 1 by omega]

private theorem window_budget (M : ℕ) (hM : 2 ≤ M) :
    (stirlingError (M + 1) (M * (M - 1)) +
        ((M * (M - 1) : ℕ) : ℝ) * log (M + 1 : ℕ) +
        (kappa / entropyOptimizer) * ((M + 1 : ℕ) : ℝ) ^ 2) / M ≤
      (12 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
        (log ((M : ℝ) + 1) + 1) := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hs : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hK : 0 ≤ kappa / entropyOptimizer := div_nonneg kappa_bounds.1 optimizer_positive.le
  have hL : 0 ≤ log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogs : log ((M : ℝ) * ((M : ℝ) - 1) + 1) ≤
      2 * log ((M : ℝ) + 1) := by
    have hh := Real.log_le_log
      (show 0 < (M : ℝ) * ((M : ℝ) - 1) + 1 by nlinarith)
      (show (M : ℝ) * ((M : ℝ) - 1) + 1 ≤ ((M : ℝ) + 1) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogs0 : 0 ≤ log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1 := by
    have hh := Real.log_nonneg (show 1 ≤ (M : ℝ) * ((M : ℝ) - 1) + 1 by nlinarith)
    linarith
  have hst : 2 * ((M : ℝ) + 1) *
      (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1) ≤
        6 * (M : ℝ) * (log ((M : ℝ) + 1) + 1) := by
    calc
      _ ≤ 3 * (M : ℝ) * (log ((M : ℝ) * ((M : ℝ) - 1) + 1) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogs0
      _ ≤ 3 * (M : ℝ) * (2 * (log ((M : ℝ) + 1) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hscale : 6 * (M : ℝ) * (log ((M : ℝ) + 1) + 1) ≤
      3 * (M : ℝ) ^ 2 * (log ((M : ℝ) + 1) + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  have hlog2 : 2 * ((M : ℝ) * ((M : ℝ) - 1)) * log 2 ≤ 2 * (M : ℝ) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left (show log (2 : ℝ) ≤ 1 by linarith [Real.log_two_lt_d9])
      (show 0 ≤ 2 * ((M : ℝ) * ((M : ℝ) - 1)) by nlinarith)
    nlinarith only [hp, hm]
  have hboundary : ((M : ℝ) * ((M : ℝ) - 1)) * log ((M : ℝ) + 1) ≤
      (M : ℝ) ^ 2 * (log ((M : ℝ) + 1) + 1) := by nlinarith
  have hround : (kappa / entropyOptimizer) * ((M : ℝ) + 1) ^ 2 ≤
      3 * (kappa / entropyOptimizer) * (M : ℝ) ^ 2 :=
    by nlinarith [mul_nonneg hK (show 0 ≤ 3 * (M : ℝ) ^ 2 - ((M : ℝ) + 1) ^ 2 by nlinarith)]
  have hp : 0 ≤ (M : ℝ) ^ 2 * log ((M : ℝ) + 1) := mul_nonneg (sq_nonneg _) hL
  have hKp : 0 ≤ (kappa / entropyOptimizer) * ((M : ℝ) ^ 2 * log ((M : ℝ) + 1)) :=
    mul_nonneg hK hp
  rw [stirlingError, hs, Nat.cast_add, Nat.cast_one]
  apply (div_le_iff₀ hm0).2
  nlinarith only [hst, hscale, hlog2, hboundary, hround, hp, hKp,
    mul_nonneg hK (sq_nonneg (M : ℝ)), sq_nonneg (M : ℝ)]

/-- The exact entropy coefficient controls the actual finite minimum. Every legal
term obeys the lower bound, and a legal parameter attaining the minimum obeys
the matching two-sided bound, with error at most a constant times `M log M`. -/
theorem optimized_entropy_asymptotic :
    0 < Real.eulerMascheroniConstant - kappa ∧
      ∀ M : ℕ, 2 ≤ M →
        (∀ b : ℕ, (M + 1) * b ≤ M * (M - 1) →
          (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2 -
            (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
              (log ((M : ℝ) + 1) + 1) ≤ windowLoss M b) ∧
        ∃ b : ℕ, (M + 1) * b ≤ M * (M - 1) ∧ minimumLoss M = windowLoss M b ∧
          (∀ c : ℕ, (M + 1) * c ≤ M * (M - 1) → windowLoss M b ≤ windowLoss M c) ∧
          |minimumLoss M - (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2| ≤
            (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
              (log ((M : ℝ) + 1) + 1) := by
  have hgap := (entropy_profile.2.2.2.2.2 _ optimizer_spec.1).2
  refine ⟨by dsimp [kappa]; linarith only [hgap], ?_⟩
  intro M hM
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hr : 0 < M + 1 := by omega
  have hs0 : 0 < M * (M - 1) := Nat.mul_pos (by omega) (by omega)
  have hs : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  let E : ℝ := stirlingError (M + 1) (M * (M - 1)) +
    ((M * (M - 1) : ℕ) : ℝ) * log (M + 1 : ℕ) +
    (kappa / entropyOptimizer) * ((M + 1 : ℕ) : ℝ) ^ 2
  let A : ℝ := ((M + 1 : ℕ) : ℝ) * ((M * (M - 1) : ℕ) : ℝ) *
    (log (M * (M - 1) : ℕ) - 1 - kappa)
  let H : ℝ := (M : ℝ) ^ 2 * log ((M : ℝ) ^ 2) -
    (1 + Real.eulerMascheroniConstant) * (M : ℝ) ^ 2
  let T : ℝ := (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2
  have hA : |A / M - H - T| ≤ 4 * (M : ℝ) * (log ((M : ℝ) + 1) + 1) := by
    have heq : A / M - H - T =
        ((M : ℝ) ^ 2 - 1) * (log ((M : ℝ) * ((M : ℝ) - 1)) - 1 - kappa) -
          (M : ℝ) ^ 2 * (log ((M : ℝ) ^ 2) - 1 - kappa) := by
      dsimp [A, H, T]
      rw [hs, Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring
    rw [heq]
    exact window_main_error hm
  have hE := window_budget M hM
  change E / M ≤ _ at hE
  have hpad : 0 ≤ E - stirlingError (M + 1) (M * (M - 1)) := by
    have hl := Real.log_natCast_nonneg (M + 1)
    have hK : 0 ≤ kappa / entropyOptimizer := div_nonneg kappa_bounds.1 optimizer_positive.le
    have hid : E - stirlingError (M + 1) (M * (M - 1)) =
        ((M * (M - 1) : ℕ) : ℝ) * log (M + 1 : ℕ) +
          (kappa / entropyOptimizer) * ((M + 1 : ℕ) : ℝ) ^ 2 := by dsimp [E]; ring
    rw [hid]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl) (mul_nonneg hK (sq_nonneg _))
  have hlower (b : ℕ) (hb : (M + 1) * b ≤ M * (M - 1)) : A - E ≤
      log (selbergFactorial (M + 1) (M * (M - 1)) b : ℝ) := by
    have hh := all_terms_lower (M + 1) (M * (M - 1)) b hr hs0 hb
    change A - stirlingError (M + 1) (M * (M - 1)) ≤ _ at hh
    linarith only [hh, hpad]
  have hL : 0 ≤ (M : ℝ) * (log ((M : ℝ) + 1) + 1) :=
    mul_nonneg hm0.le (by linarith [Real.log_nonneg (show 1 ≤ (M : ℝ) + 1 by linarith)])
  have hK : 0 ≤ kappa / entropyOptimizer := div_nonneg kappa_bounds.1 optimizer_positive.le
  have hKL := mul_nonneg hK hL
  have hloss (b : ℕ) (hb : (M + 1) * b ≤ M * (M - 1)) :
      T - (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
        (log ((M : ℝ) + 1) + 1) ≤ windowLoss M b := by
    have hh := (div_le_div_of_nonneg_right (hlower b hb) hm0.le)
    rw [sub_div] at hh
    change _ ≤ log (selbergFactorial (M + 1) (M * (M - 1)) b : ℝ) / M at hh
    change T - _ ≤ _ - H
    nlinarith only [hh, (abs_le.mp hA).1, hE, hL, hKL]
  refine ⟨hloss, ?_⟩
  obtain ⟨b, hb, hmin⟩ := Finset.exists_mem_eq_inf' (legal_nonempty M) (windowLoss M)
  have hbLegal : (M + 1) * b ≤ M * (M - 1) := (mem_filter.mp hb).2
  have hminimal (c : ℕ) (hc : (M + 1) * c ≤ M * (M - 1)) : windowLoss M b ≤ windowLoss M c := by
    rw [← hmin]
    exact Finset.inf'_le _ (legal_mem M c hc)
  refine ⟨b, hbLegal, hmin, hminimal, ?_⟩
  obtain ⟨c, hc, hcup⟩ := attained_upper (M + 1) (M * (M - 1)) hr hs0
  have hcup' : log (selbergFactorial (M + 1) (M * (M - 1)) c : ℝ) ≤ A + E := by
    dsimp [A, E]
    nlinarith only [hcup]
  have hu := div_le_div_of_nonneg_right hcup' hm0.le
  rw [add_div] at hu
  have hmc := hminimal c hc
  have hlo := hloss b hbLegal
  rw [← hmin] at hlo hmc
  change minimumLoss M ≤ log (selbergFactorial (M + 1) (M * (M - 1)) c : ℝ) / M - H at hmc
  change T - (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
    (log ((M : ℝ) + 1) + 1) ≤ minimumLoss M at hlo
  apply abs_le.mpr
  constructor
  · change -_ ≤ minimumLoss M - T
    linarith only [hlo]
  · change minimumLoss M - T ≤ _
    nlinarith only [hu, hmc, (abs_le.mp hA).2, hE, hL, hKL]

end D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy
