/- GID: D5/S3/PrimeGaps/ChiFourWeightedMangoldt
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/ChiFourWeightedMangoldt
   mirror-E: none(waiver:finite-character-convolution)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Leibniz]
   utility: none
   digest: Finite convolution bounds the weighted Mangoldt sum for the character modulo four. -/

import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
Admission basis: open-problem-resolution, as an auxiliary to McCormack--Zelinsky Question 44.
The character and convergence formula are Mathlib's. The finite character convolution and
Chebyshev estimate provide the classical analytic bound used by the relative-density proof.
The logarithmic sum is bounded by natural-order finite alternation beyond its first zero term.
No direct D5 imports or frozen D5 dependencies occur in this module.

Declaration proof shapes and live consumers:
* sum_chi_four_prefix: bind-only; character_abs_le_one and the two alternating-divisor
  hyperbola estimates in AndrewsElBachraouiCharacter and AndrewsElBachraouiWeighted.
* sum_chi_mul_eq_odds: bind-only; harmonic_error, sum_chi_log_div_le_one.
* leibniz_error: bind-only; harmonic_error.
* harmonic_error: bind-only; convolution_error.
* finite_convolution: bind-only; convolution_error.
* character_abs_le_one: bind-only; convolution_error.
* convolution_error: bind-only; abs_weighted_mangoldt_sum_le_twelve.
* finite_alternating_bounds: bind-only; odd_log_alternating_bound.
* odd_log_antitone: bind-only; odd_log_alternating_bound.
* odd_log_alternating_bound: bind-only; sum_chi_log_div_le_one.
* sum_chi_log_div_le_one: bind-only; sum_chi_log_div_le_two.
* sum_chi_log_div_le_two: bind-only; abs_weighted_mangoldt_sum_le_twelve.
* abs_weighted_mangoldt_sum_le_twelve: bind-only; the residue-class Mertens estimate
  in ModFourChebyshev, on the live path to StrongPseudoperfectEulerDensity.result.
The private harmonicSum definition is consumed by finite_convolution and harmonic_error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.PrimeGaps.ChiFourWeightedMangoldt

/-- The natural-order character prefix is either zero or one. -/
theorem sum_chi_four_prefix (X : ℕ) :
    (∑ b ∈ Ioc 0 X, ZMod.χ₄ (b : ZMod 4)) = (((X + 1) / 2 % 2 : ℕ) : ℤ) := by
  induction X with
  | zero => simp
  | succ X ih =>
      rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih,
        ZMod.χ₄_nat_eq_if_mod_four]
      have hX := Nat.mod_lt X (by decide : 0 < 4)
      interval_cases h : X % 4 <;> split_ifs <;> omega

private lemma sum_chi_mul_eq_odds (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, (ZMod.χ₄ (n : ZMod 4) : ℝ) * w n) =
      ∑ i ∈ range ((N + 1) / 2), (-1 : ℝ) ^ i * w (2 * i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_Ioc_succ_top (by omega : 0 ≤ N), ih]
      by_cases he : N % 2 = 0
      · have hl : (N + 1 + 1) / 2 = (N + 1) / 2 + 1 := by omega
        have hn : N + 1 = 2 * ((N + 1) / 2) + 1 := by omega
        rw [hl, sum_range_succ]
        congr 1
        rw [hn, ZMod.χ₄_eq_neg_one_pow (by omega)]
        push_cast
        rw [show (2 * ((N + 1) / 2) + 1) / 2 = (N + 1) / 2 by omega]
      · have hl : (N + 1 + 1) / 2 = (N + 1) / 2 := by omega
        have hn : (N + 1) % 2 = 0 := by omega
        have hz : ZMod.χ₄ ((N + 1 : ℕ) : ZMod 4) = 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos hn]
        simp only [hl, hz, Int.cast_zero, zero_mul, add_zero]

private lemma leibniz_error (N : ℕ) :
    |(π / 4) - ∑ i ∈ range N, (-1 : ℝ) ^ i / (2 * i + 1)| ≤
      (2 * (N : ℝ) + 1)⁻¹ := by
  let f : ℕ → ℝ := fun i => (2 * (i : ℝ) + 1)⁻¹
  have hf : Antitone f := antitone_iff_forall_lt.mpr fun _ _ _ => by
    dsimp [f]
    gcongr
  have ht : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i)
      atTop (𝓝 (π / 4)) := by
    simpa [f, div_eq_mul_inv] using Real.tendsto_sum_pi_div_four
  have upper := hf.alternating_series_le_tendsto ht
  have lower := hf.tendsto_le_alternating_series ht
  have hpos (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  change |π / 4 - ∑ i ∈ range N, (-1 : ℝ) ^ i * f i| ≤ f N
  obtain h | h := Nat.even_or_odd N
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp only [sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hpos (2 * n)))
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hpos (2 * n + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

private def harmonicSum (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (ZMod.χ₄ (n : ZMod 4) : ℝ) / n

private lemma harmonic_error {x : ℝ} (hx : 1 ≤ x) :
    |harmonicSum x - π / 4| ≤ x⁻¹ := by
  let K := (⌊x⌋₊ + 1) / 2
  have heq : harmonicSum x = ∑ i ∈ range K, (-1 : ℝ) ^ i / (2 * i + 1) := by
    simpa [harmonicSum, K, div_eq_mul_inv] using
      sum_chi_mul_eq_odds ⌊x⌋₊ (fun n => (n : ℝ)⁻¹)
  rw [heq, abs_sub_comm]
  refine (leibniz_error K).trans ?_
  apply inv_anti₀ (by linarith : 0 < x)
  have hn : ⌊x⌋₊ ≤ 2 * K := by dsimp [K]; omega
  have hc : (⌊x⌋₊ : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hn
  linarith [Nat.lt_floor_add_one x]

private lemma finite_convolution (x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (ZMod.χ₄ (n : ZMod 4) : ℝ) * log n / n) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊,
        ((ZMod.χ₄ (d : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt d / d) *
          harmonicSum (x / d) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => (ZMod.χ₄ (n : ZMod 4) : ℝ) / n, by simp⟩
  let g : ArithmeticFunction ℝ :=
    ⟨fun n => (ZMod.χ₄ (n : ZMod 4) : ℝ) *
      ArithmeticFunction.vonMangoldt n / n, by simp⟩
  have hp (n : ℕ) :
      (g * f) n = (ZMod.χ₄ (n : ZMod 4) : ℝ) * log n / n := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => g a * f b),
      ← ArithmeticFunction.vonMangoldt_sum, mul_sum, sum_div]
    apply sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have heq : (d : ℝ) * (n / d : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hdn
    have hc : (ZMod.χ₄ (d : ZMod 4) : ℝ) *
        (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℝ) =
          (ZMod.χ₄ (n : ZMod 4) : ℝ) := by
      rw [← Int.cast_mul, ← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdn]
    change ((ZMod.χ₄ (d : ZMod 4) : ℝ) *
      ArithmeticFunction.vonMangoldt d / d) *
      ((ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℝ) / (n / d : ℕ)) = _
    rw [div_mul_div_comm, heq]
    rw [show (ZMod.χ₄ (d : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt d *
        (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℝ) =
        ((ZMod.χ₄ (d : ZMod 4) : ℝ) *
        (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℝ)) *
        ArithmeticFunction.vonMangoldt d by ring, hc]
  calc
    _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, (g * f) n := by simp_rw [hp]
    _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, g d * ∑ m ∈ Ioc 0 (⌊x⌋₊ / d), f m :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum g f ⌊x⌋₊
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      simp only [g, f, harmonicSum, Nat.floor_div_natCast,
        ArithmeticFunction.coe_mk]

private lemma character_abs_le_one (n : ℕ) :
    |(ZMod.χ₄ (n : ZMod 4) : ℝ)| ≤ 1 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have h := sum_Ioc_succ_top (f := fun b => ZMod.χ₄ (b : ZMod 4))
        (show 0 ≤ n by omega)
      rw [sum_chi_four_prefix, sum_chi_four_prefix] at h
      have h₁ := Nat.mod_lt ((n + 1 + 1) / 2) (by decide : 0 < 2)
      have h₂ := Nat.mod_lt ((n + 1) / 2) (by decide : 0 < 2)
      have hz : |ZMod.χ₄ ((n + 1 : ℕ) : ZMod 4)| ≤ (1 : ℤ) := by
        rw [abs_le]
        constructor <;> omega
      exact_mod_cast hz

private lemma convolution_error {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, (ZMod.χ₄ (n : ZMod 4) : ℝ) * log n / n) -
      (π / 4) * ∑ d ∈ Ioc 0 ⌊x⌋₊,
        (ZMod.χ₄ (d : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt d / d| ≤ 6 := by
  have hx0 : 0 < x := by linarith
  rw [finite_convolution, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊,
        |((ZMod.χ₄ (d : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt d / d) *
          harmonicSum (x / d) - (π / 4) *
          ((ZMod.χ₄ (d : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt d / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / x := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < (d : ℝ) := by exact_mod_cast (mem_Ioc.mp hd).1
      have hdx : (d : ℝ) ≤ x :=
        (Nat.cast_le.mpr (mem_Ioc.mp hd).2).trans (Nat.floor_le hx0.le)
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt_nonneg
      calc
        _ = |(ZMod.χ₄ (d : ZMod 4) : ℝ)| *
            (ArithmeticFunction.vonMangoldt d / d) * |harmonicSum (x / d) - π / 4| := by
          rw [mul_comm (π / 4) _, ← mul_sub, abs_mul, abs_div, abs_mul,
            abs_of_nonneg hΛ, abs_of_pos hd0]
          ring
        _ ≤ 1 * (ArithmeticFunction.vonMangoldt d / d) * (x / d)⁻¹ := by
          gcongr
          · exact character_abs_le_one d
          · exact harmonic_error ((one_le_div hd0).mpr hdx)
        _ = ArithmeticFunction.vonMangoldt d / x := by field_simp
    _ = Chebyshev.psi x / x := by rw [← sum_div]; rfl
    _ ≤ 6 := by
      apply (div_le_iff₀ hx0).mpr
      have h := Chebyshev.psi_le_const_mul_self hx0.le
      have hl : log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
        have h2 : log 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
          norm_num at hh
          exact hh
        norm_num at *
        linarith
      nlinarith

private lemma finite_alternating_bounds (f : ℕ → ℝ) (hn : ∀ n, 0 ≤ f n)
    (ha : Antitone f) (N : ℕ) :
    0 ≤ ∑ i ∈ range N, (-1 : ℝ) ^ i * f i ∧
      ∑ i ∈ range N, (-1 : ℝ) ^ i * f i ≤ f 0 := by
  have hpair (k : ℕ) :
      0 ≤ ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * f i ∧
        ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * f i ≤ f 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := ha (show 2 * k ≤ 2 * k + 1 by omega)
        have hstep' := ha (show 2 * k + 1 ≤ 2 * k + 2 by omega)
        constructor
        · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
            sum_range_succ, sum_range_succ]
          simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
            pow_one, mul_neg, mul_one]
          linarith [ih.1]
        · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by omega,
            sum_range_succ, sum_range_succ]
          simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
            pow_one, mul_neg, mul_one]
          linarith [ih.2]
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hN
    have hp := hpair k
    constructor
    · exact hp.1
    · have h := hp.2
      rw [sum_range_succ] at h
      simp only [pow_mul, neg_one_sq, one_pow, one_mul] at h
      simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using
        (le_trans (le_add_of_nonneg_right (hn (2 * k))) h)
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hN
    have hp := hpair k
    constructor
    · rw [sum_range_succ]
      simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using
        (add_nonneg hp.1 (hn (2 * k)))
    · exact hp.2

private lemma odd_log_antitone :
    Antitone (fun i : ℕ => log (2 * (i : ℝ) + 3) / (2 * (i : ℝ) + 3)) := by
  intro i j hij
  apply Real.log_div_self_antitoneOn
  · exact Real.exp_one_lt_three.le.trans (by
      have := Nat.cast_nonneg (α := ℝ) i
      linarith)
  · exact Real.exp_one_lt_three.le.trans (by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith)
  · exact_mod_cast (show 2 * i + 3 ≤ 2 * j + 3 by omega)

private lemma odd_log_alternating_bound (N : ℕ) :
    |∑ i ∈ range N, (-1 : ℝ) ^ i *
      (log (2 * (i : ℝ) + 3) / (2 * (i : ℝ) + 3))| ≤ 1 := by
  have hb := finite_alternating_bounds
    (fun i : ℕ => log (2 * (i : ℝ) + 3) / (2 * (i : ℝ) + 3))
    (fun i => div_nonneg (log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) i
      linarith)) (by positivity))
    odd_log_antitone N
  rw [abs_of_nonneg hb.1]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at hb
  linarith [hb.2]

private lemma sum_chi_log_div_le_one (N : ℕ) :
    |∑ n ∈ Ioc 0 N, (ZMod.χ₄ (n : ZMod 4) : ℝ) * (log n / n)| ≤ 1 := by
  rw [sum_chi_mul_eq_odds]
  generalize (N + 1) / 2 = K
  cases K with
  | zero => simp
  | succ K =>
      rw [sum_range_succ']
      simp only [mul_zero, zero_add, Nat.cast_one, log_one,
        zero_div, mul_zero, add_zero, zero_add]
      have heq :
          (∑ i ∈ range K, (-1 : ℝ) ^ (i + 1) *
            (log ((2 * (i + 1) + 1 : ℕ) : ℝ) / ((2 * (i + 1) + 1 : ℕ) : ℝ))) =
            -(∑ i ∈ range K, (-1 : ℝ) ^ i *
              (log (2 * (i : ℝ) + 3) / (2 * (i : ℝ) + 3))) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i hi
        have harg : ((2 * (i + 1) + 1 : ℕ) : ℝ) = 2 * (i : ℝ) + 3 := by
          push_cast
          ring
        rw [harg, pow_succ]
        ring
      rw [heq, abs_neg]
      exact odd_log_alternating_bound K

private lemma sum_chi_log_div_le_two (x : ℝ) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (ZMod.χ₄ (n : ZMod 4) : ℝ) * log n / n| ≤ 2 := by
  have h := sum_chi_log_div_le_one ⌊x⌋₊
  simp only [mul_div_assoc] at h ⊢
  exact h.trans (by norm_num)


/-- The signed weighted Mangoldt sum for the character modulo four is uniformly bounded. -/
theorem abs_weighted_mangoldt_sum_le_twelve {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊,
      (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / n| ≤ 12 := by
  let J := ∑ n ∈ Ioc 0 ⌊x⌋₊, (ZMod.χ₄ (n : ZMod 4) : ℝ) * log n / n
  let T := ∑ n ∈ Ioc 0 ⌊x⌋₊,
    (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / n
  have he : |J - (π / 4) * T| ≤ 6 := convolution_error hx
  have hj : |J| ≤ 2 := sum_chi_log_div_le_two x
  have hprod : |(π / 4) * T| ≤ 8 := by
    calc
      _ = |J - (J - (π / 4) * T)| := by congr 1; ring
      _ ≤ |J| + |J - (π / 4) * T| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le J 0 (J - (π / 4) * T)
      _ ≤ 8 := by linarith
  rw [abs_mul, abs_of_pos (div_pos pi_pos (by norm_num))] at hprod
  have hpi : (2 / 3 : ℝ) ≤ π / 4 := by
    have ha : Antitone (fun i : ℕ => (2 * (i : ℝ) + 1)⁻¹) := by
      intro i j hij
      apply inv_anti₀ (by positivity : 0 < 2 * (i : ℝ) + 1)
      exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega)
    have ht : Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (2 * (i : ℝ) + 1)⁻¹) atTop (𝓝 (π / 4)) := by
      simpa [div_eq_mul_inv] using Real.tendsto_sum_pi_div_four
    have h := ha.alternating_series_le_tendsto ht 1
    norm_num [sum_range_succ] at h
    exact h
  have := mul_le_mul_of_nonneg_right hpi (abs_nonneg T)
  change |T| ≤ 12
  linarith

end D5.S3.PrimeGaps.ChiFourWeightedMangoldt
