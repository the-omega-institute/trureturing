/- GID: D5/S3/Weil/Analytic/MobiusCenteredHyperbola
   generality: I
   mirror-B: none(waiver:mobius-log-fourth-support)
   mirror-E: none(waiver:mobius-log-fourth)
   anchors: []
   utility: none
   digest: The centered Mangoldt recurrence has a finite head and an inverse-logarithmic tail. -/

import D5.S3.Weil.Analytic.DirichletHyperbolaSplit
import D5.S3.Weil.Mertens.Estimates
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The centered Möbius convolution and its tail at a hyperbola cutoff. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Asymptotics Finset Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology

namespace MobiusCenteredHyperbola

/-- Subtract the arithmetic function with value one at positive integers. -/
def centeredMangoldt : ArithmeticFunction ℝ :=
  vonMangoldt - (ζ : ArithmeticFunction ℝ)

def mobiusPrefix (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)

def centeredPrefix (x : ℝ) : ℝ := Chebyshev.psi x - (⌊x⌋₊ : ℝ)

def head (x y : ℝ) : ℝ :=
  ∑ d ∈ Ioc 0 ⌊y⌋₊, centeredMangoldt d * mobiusPrefix (x / (d : ℝ))

def tail (x y : ℝ) : ℝ :=
  ∑ m ∈ Ioc 0 ⌊x / ((⌊y⌋₊ + 1 : ℕ) : ℝ)⌋₊,
    (μ m : ℝ) * (centeredPrefix (x / (m : ℝ)) - centeredPrefix y)

theorem abs_mobiusPrefix_le_floor (x : ℝ) : |mobiusPrefix x| ≤ (⌊x⌋₊ : ℝ) := by
  unfold mobiusPrefix
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |(μ n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _ => by exact_mod_cast (abs_moebius_le_one (n := n))
    _ = (⌊x⌋₊ : ℝ) := by simp

theorem abs_mobiusPrefix_le {x : ℝ} (hx : 0 ≤ x) : |mobiusPrefix x| ≤ x :=
  (abs_mobiusPrefix_le_floor x).trans (Nat.floor_le hx)

/-- Discrete Abel summation uses the logarithm of the integer endpoint.
Moving that factor to the real endpoint costs at most one. -/
theorem abs_mobiusPrefix_mul_log_floor_gap {x : ℝ} (hx : 1 ≤ x) :
    |mobiusPrefix x * (Real.log x - Real.log (⌊x⌋₊ : ℝ))| ≤ 1 := by
  let N : ℝ := (⌊x⌋₊ : ℝ)
  have hN : 0 < N := by
    have hN₁ := (Nat.one_le_floor_iff x).mpr hx
    dsimp [N]
    exact_mod_cast (show 0 < ⌊x⌋₊ from zero_lt_one.trans_le hN₁)
  have hNx : N ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hxN : x ≤ N + 1 := (Nat.lt_floor_add_one x).le
  have hgap₀ : 0 ≤ Real.log x - Real.log N :=
    sub_nonneg.mpr (Real.log_le_log hN hNx)
  have hgap : Real.log x - Real.log N ≤ N⁻¹ := by
    rw [← Real.log_div (zero_lt_one.trans_le hx).ne' hN.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (zero_lt_one.trans_le hx) hN)).trans ?_
    have hinv : x / N ≤ (N + 1) / N := div_le_div_of_nonneg_right hxN hN.le
    rw [add_div, div_self hN.ne', one_div] at hinv
    linarith only [hinv]
  change |mobiusPrefix x * (Real.log x - Real.log N)| ≤ 1
  rw [abs_mul, abs_of_nonneg hgap₀]
  calc
    _ ≤ N * N⁻¹ := mul_le_mul (abs_mobiusPrefix_le_floor x) hgap hgap₀ hN.le
    _ = 1 := mul_inv_cancel₀ hN.ne'

private theorem centeredMangoldt_apply {n : ℕ} (hn : n ≠ 0) :
    centeredMangoldt n = vonMangoldt n - 1 := by
  simp [centeredMangoldt, sub_eq_add_neg, zeta_apply_ne hn]

private theorem centeredPrefix_eq_sum (x : ℝ) :
    centeredPrefix x = ∑ n ∈ Ioc 0 ⌊x⌋₊, centeredMangoldt n := by
  unfold centeredPrefix Chebyshev.psi
  have hcount : (∑ n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ)) = (⌊x⌋₊ : ℝ) := by simp
  rw [← hcount, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [centeredMangoldt_apply (mem_Ioc.mp hn).1.ne']

private def logWeightedMoebius : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) * Real.log n, by simp⟩

private theorem logWeightedMoebius_eq :
    logWeightedMoebius = -(vonMangoldt * (μ : ArithmeticFunction ℝ)) := by
  have h : logWeightedMoebius * (ζ : ArithmeticFunction ℝ) = -vonMangoldt := by
    ext n
    rw [coe_mul_zeta_apply]
    simpa only [logWeightedMoebius, coe_mk, ArithmeticFunction.neg_apply,
      ArithmeticFunction.log_apply]
      using (sum_moebius_mul_log_eq (n := n))
  have he := congrArg (fun f : ArithmeticFunction ℝ => f * (μ : ArithmeticFunction ℝ)) h
  simpa only [mul_assoc, coe_zeta_mul_coe_moebius, mul_one, neg_mul] using he

/-- The finite centered recurrence, before discrete Abel summation. -/
theorem sum_log_weighted_moebius (x y : ℝ) (hx : 1 ≤ x) (hy : y ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * Real.log (n : ℝ)) =
      -1 - head x y - tail x y := by
  have hconv : centeredMangoldt * (μ : ArithmeticFunction ℝ) =
      -logWeightedMoebius - 1 := by
    rw [centeredMangoldt, sub_mul, coe_zeta_mul_coe_moebius,
      logWeightedMoebius_eq, neg_neg]
  have hsplit := ArithmeticFunction.sum_convolution_split_at
    centeredMangoldt (μ : ArithmeticFunction ℝ) ⌊x⌋₊ ⌊y⌋₊ (Nat.floor_mono hy)
  have hunit : (∑ n ∈ Ioc 0 ⌊x⌋₊, (1 : ArithmeticFunction ℝ) n) = 1 := by
    have h1 : 1 ∈ Ioc 0 ⌊x⌋₊ := mem_Ioc.mpr ⟨by decide, Nat.one_le_floor_iff x |>.2 hx⟩
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp
    · intro n _ hn
      exact one_apply_ne hn
  have hsum : (∑ n ∈ Ioc 0 ⌊x⌋₊, (centeredMangoldt * (μ : ArithmeticFunction ℝ)) n) =
      -(∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * Real.log (n : ℝ)) - 1 := by
    have hterm (n : ℕ) : (-logWeightedMoebius - 1) n =
        -((μ n : ℝ) * Real.log (n : ℝ)) - (1 : ArithmeticFunction ℝ) n := by
      rfl
    rw [hconv]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hunit]
  have heq : (∑ n ∈ Ioc 0 ⌊x⌋₊, (centeredMangoldt * (μ : ArithmeticFunction ℝ)) n) =
      head x y + tail x y := by
    simpa only [head, tail, mobiusPrefix, centeredPrefix_eq_sum, Nat.floor_div_natCast,
      ArithmeticFunction.intCoe_apply] using hsplit
  rw [hsum] at heq
  linarith only [heq]

/-- The head coefficients cost at most two logarithms of the cutoff. -/
theorem sum_abs_centered_div_le {y : ℝ} (hy : 1 ≤ y) :
    (∑ d ∈ Ioc 0 ⌊y⌋₊, |centeredMangoldt d| / (d : ℝ)) ≤
      2 * Real.log y + (Real.log 4 + 5) := by
  have hΛ := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log hy)).2
  have hI : Ioc 0 ⌊y⌋₊ = Icc 1 ⌊y⌋₊ := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hH : (∑ d ∈ Ioc 0 ⌊y⌋₊, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log y := by
    rw [hI]
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using harmonic_floor_le_one_add_log y hy
  calc
    _ ≤ ∑ d ∈ Ioc 0 ⌊y⌋₊, (vonMangoldt d + 1) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd₀ := (mem_Ioc.mp hd).1
      have hdR : (0 : ℝ) ≤ d := by positivity
      apply div_le_div_of_nonneg_right _ hdR
      rw [centeredMangoldt_apply hd₀.ne']
      simpa only [abs_of_nonneg vonMangoldt_nonneg, abs_one] using abs_sub (vonMangoldt d) 1
    _ ≤ _ := by
      simp only [add_div, Finset.sum_add_distrib]
      linarith only [hΛ, hH]

/-- Bound the head using an envelope on the actual real quotient window. -/
theorem abs_head_le {x y R U : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hR : 0 ≤ R) (hU : 0 < U)
    (hbound : ∀ t : ℝ, x / y ≤ t → t ≤ x → |mobiusPrefix t| ≤ R * t / U) :
    |head x y| ≤ (x / U) * (R * (2 * Real.log y + (Real.log 4 + 5))) := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hRx : 0 ≤ x * R / U := by positivity
  unfold head
  calc
    _ ≤ ∑ d ∈ Ioc 0 ⌊y⌋₊, |centeredMangoldt d * mobiusPrefix (x / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 ⌊y⌋₊, (x * R / U) * (|centeredMangoldt d| / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hd₀ : (0 : ℝ) < d := zero_lt_one.trans_le hd₁
      have hdy : (d : ℝ) ≤ y := (Nat.le_floor_iff hy₀.le).1 (mem_Ioc.mp hd).2
      have hlt := div_le_div_of_nonneg_left hx₀ hd₀ hdy
      have hgt : x / (d : ℝ) ≤ x := (div_le_iff₀ hd₀).2
        (by nlinarith only [mul_nonneg hx₀ (sub_nonneg.mpr hd₁)])
      calc
        _ = |centeredMangoldt d| * |mobiusPrefix (x / (d : ℝ))| := abs_mul _ _
        _ ≤ |centeredMangoldt d| * (R * (x / (d : ℝ)) / U) :=
          mul_le_mul_of_nonneg_left (hbound _ hlt hgt) (abs_nonneg _)
        _ = _ := by ring
    _ = (x * R / U) * ∑ d ∈ Ioc 0 ⌊y⌋₊, |centeredMangoldt d| / (d : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (x * R / U) * (2 * Real.log y + (Real.log 4 + 5)) :=
      mul_le_mul_of_nonneg_left (sum_abs_centered_div_le hy) hRx
    _ = _ := by ring

private theorem harmonic_sum_le (K : ℕ) {x : ℝ} (hx : 1 ≤ x) (hK : (K : ℝ) ≤ x) :
    (∑ m ∈ Ioc 0 K, (m : ℝ)⁻¹) ≤ 1 + Real.log x := by
  by_cases hzero : K = 0
  · subst K
    simpa using add_nonneg zero_le_one (Real.log_nonneg hx)
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hset : Ioc 0 K = Icc 1 K := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset, ← show (harmonic K : ℝ) = ∑ m ∈ Icc 1 K, (m : ℝ)⁻¹ by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]]
  linarith only [harmonic_le_one_add_log K, Real.log_le_log hKpos hK]

/-- Suppose the centered prefix has relative error at most `δ` above `y`.
For every term of the tail, `x / m` is at least `⌊y⌋₊ + 1`. Applying
the same error bound at `x / m` and at `y` leaves a harmonic sum. -/
theorem abs_tail_le {x y δ : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hδ : 0 ≤ δ)
    (hprofile : ∀ t ≥ y, |centeredPrefix t| ≤ δ * t) :
    |tail x y| ≤ δ * (x * (2 + Real.log x)) := by
  let K := ⌊x / ((⌊y⌋₊ + 1 : ℕ) : ℝ)⌋₊
  have hY : y < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one y
  have hYpos : 0 < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by positivity
  have hK : (K : ℝ) ≤ x / ((⌊y⌋₊ + 1 : ℕ) : ℝ) :=
    Nat.floor_le (div_nonneg (zero_le_one.trans hx) hYpos.le)
  have hKy : (K : ℝ) * y ≤ x :=
    (mul_le_mul_of_nonneg_left hY.le (by positivity)).trans ((le_div_iff₀ hYpos).mp hK)
  have hKx : (K : ℝ) ≤ x :=
    (by simpa using mul_le_mul_of_nonneg_left hy (show 0 ≤ (K : ℝ) by positivity) :
      (K : ℝ) ≤ (K : ℝ) * y).trans hKy
  change |∑ m ∈ Ioc 0 K,
    (μ m : ℝ) * (centeredPrefix (x / (m : ℝ)) - centeredPrefix y)| ≤ _
  calc
    _ ≤ ∑ m ∈ Ioc 0 K, |(μ m : ℝ) *
        (centeredPrefix (x / (m : ℝ)) - centeredPrefix y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Ioc 0 K, δ * (x * (m : ℝ)⁻¹ + y) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (mem_Ioc.mp hm).1
      have hmK : (m : ℝ) ≤ K := by exact_mod_cast (mem_Ioc.mp hm).2
      have hmy : y ≤ x / (m : ℝ) := (le_div_iff₀ hmpos).mpr
        ((mul_le_mul_of_nonneg_left hmK (zero_le_one.trans hy)).trans (by simpa [mul_comm] using hKy))
      rw [abs_mul]
      have hμ : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := m))
      calc
        _ ≤ |centeredPrefix (x / (m : ℝ)) - centeredPrefix y| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
        _ ≤ |centeredPrefix (x / (m : ℝ))| + |centeredPrefix y| := abs_sub _ _
        _ ≤ δ * (x * (m : ℝ)⁻¹ + y) := by
          rw [mul_add, ← div_eq_mul_inv]
          exact add_le_add (hprofile _ hmy) (hprofile _ le_rfl)
    _ = δ * (x * (∑ m ∈ Ioc 0 K, (m : ℝ)⁻¹) + (K : ℝ) * y) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_const]
    _ ≤ δ * (x * (2 + Real.log x)) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      have h := add_le_add (mul_le_mul_of_nonneg_left (harmonic_sum_le K hx hKx)
        (zero_le_one.trans hx)) hKy
      linarith only [h]

/-- The stretched exponential in `MediumPNT` dominates every fixed
logarithmic power. -/
theorem log_pow_mul_medium_decay_tendsto_zero (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.log t ^ k *
      Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
  have htop : Tendsto (fun t : ℝ => Real.log t ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have hdec := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (k : ℝ)) c hc).comp htop
  apply hdec.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (0 : ℝ)] with t ht
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul ht, show ((1 : ℝ) / 10) * (10 * (k : ℝ)) = (k : ℝ) by ring,
    Real.rpow_natCast]

theorem centeredPrefix_log_power_bound (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ᶠ t : ℝ in atTop, |centeredPrefix t| ≤ C * t / Real.log t ^ k := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨D, hD, hpsi⟩ := isBigO_iff'.mp hO
  have hdec := (log_pow_mul_medium_decay_tendsto_zero k hc).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  have hf := (isLittleO_log_rpow_rpow_atTop (s := 1) (k : ℝ) zero_lt_one).eventuallyLE
  refine ⟨D + 1, by linarith, ?_⟩
  filter_upwards [hpsi, hdec, hf, eventually_gt_atTop (1 : ℝ)] with t hp hd hf ht
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hlogk : 0 < Real.log t ^ k := pow_pos hlog _
  change ‖Chebyshev.psi t - t‖ ≤ D * ‖t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))‖ at hp
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg ht₀.le (Real.exp_pos _).le)] at hp
  have hfloor : |t - (⌊t⌋₊ : ℝ)| ≤ 1 := Nat.abs_sub_floor_le ht₀.le
  have hlt : Real.log t ^ k ≤ t := by
    simpa only [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog.le _), abs_of_nonneg ht₀.le] using hf
  have hsplit : centeredPrefix t = (Chebyshev.psi t - t) + (t - (⌊t⌋₊ : ℝ)) := by
    unfold centeredPrefix
    ring
  apply (le_div_iff₀ hlogk).mpr
  have hscaled := mul_le_mul_of_nonneg_right
    ((by rw [hsplit]; exact (abs_add_le _ _).trans (add_le_add hp hfloor)) :
      |centeredPrefix t| ≤ D * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) + 1)
    hlogk.le
  change Real.log t ^ k * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) < 1 at hd
  have hterm := mul_le_mul_of_nonneg_left hd.le (mul_nonneg hD.le ht₀.le)
  calc
    _ ≤ D * t * (Real.log t ^ k * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) +
        Real.log t ^ k := by convert hscaled using 1 <;> ring
    _ ≤ D * t * 1 + t := add_le_add hterm hlt
    _ = _ := by ring

/-- At the eighth-root cutoff the tail is smaller than any fixed inverse
logarithmic power after division by `x`. -/
theorem abs_tail_eighth_root_le (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      |tail x (x ^ ((1 : ℝ) / 8))| ≤ C * x / Real.log x ^ k := by
  obtain ⟨B, hB, hprof⟩ := centeredPrefix_log_power_bound (k + 1)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hprof
  have hyTop : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 8)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  refine ⟨3 * B * (8 : ℝ) ^ (k + 1), by positivity, ?_⟩
  filter_upwards [hyTop.eventually_ge_atTop (max T 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), eventually_gt_atTop (1 : ℝ)]
    with x hy hlog hx
  let y := x ^ ((1 : ℝ) / 8)
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hylog : Real.log y = Real.log x / 8 := by
    dsimp [y]
    rw [Real.log_rpow (zero_lt_one.trans hx)]
    ring
  have hyl : 0 < Real.log y := by rw [hylog]; linarith
  have hxl : 0 < Real.log x := by linarith
  have hE (t : ℝ) (ht : y ≤ t) :
      |centeredPrefix t| ≤ (B / Real.log y ^ (k + 1)) * t := by
    have hty := Real.log_le_log (zero_lt_one.trans_le hy1) ht
    have hpow := pow_le_pow_left₀ hyl.le hty (k + 1)
    have ht0 : 0 < t := (zero_lt_one.trans_le hy1).trans_le ht
    exact (hT t ((le_max_left _ _).trans (hy.trans ht))).trans (by
      rw [div_mul_eq_mul_div₀]
      exact div_le_div_of_nonneg_left (mul_nonneg hB.le ht0.le) (pow_pos hyl _) hpow)
  have htail := abs_tail_le hx.le hy1 (div_nonneg hB.le (by positivity)) hE
  refine htail.trans ?_
  rw [hylog, div_pow]
  obtain h₁ := show 2 + Real.log x ≤ 3 * Real.log x by linarith
  calc
    _ ≤ (B / (Real.log x ^ (k + 1) / (8 : ℝ) ^ (k + 1))) * (x * (3 * Real.log x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ (zero_lt_one.trans hx).le)
        (by positivity)
    _ = _ := by
      rw [pow_succ (Real.log x)]
      field_simp [hxl.ne']

end MobiusCenteredHyperbola
