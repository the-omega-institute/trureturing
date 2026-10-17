/- GID: D5/S3/Zeros/Jensen/JensenHermiteScaling
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/JensenHermiteScaling
   mirror-E: none(waiver:source-fixed-window-consumer)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Taylor, mathlib/module/Mathlib.RingTheory.Polynomial.Hermite.Basic]
   utility: none
   digest: Entire weighted series give Hermite scaling at every exact order. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.JensenAnalyticCoefficientRemainder
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Tactic.GCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow

open scoped BigOperators Topology
open Set Polynomial Metric
open private coefficient_derivative_series derivative_term_bound
  from D5.S3.Zeros.Jensen.JensenAnalyticCoefficientRemainder
open private correctionCoeff_nonneg correctionCoeff_top
  from D5.S3.Zeros.Jensen.JensenFiniteCoefficientRemainder

def IsExactRealOrder (F : ℂ → ℂ) (c : ℝ) (m : ℕ) : Prop :=
  iteratedDeriv m F c ≠ 0 ∧ ∀ k < m, iteratedDeriv k F c = 0

/-- Function estimate, separately quantified over every order v, including zero.
Its sourceH instance controls M; it makes no assertion that an actual node exists. -/
def ScaledFunctionEstimate (F : ℂ → ℂ) (a : ℕ → ℂ) (t0 sigma : ℝ) (v : ℕ) : Prop :=
  ∀ q : ℝ, 2 ≤ q → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
    ∀ u : ℂ, ‖u‖ ≤ q →
      ‖(coefficientPolynomial a n).eval ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ))) /
          (((t0 : ℂ) ^ v * iteratedDeriv v F t0 / (v.factorial : ℂ)) /
            (Real.sqrt n : ℂ) ^ v) - aeval u (Polynomial.hermite v)‖ ≤ C / Real.sqrt n

variable (a : ℕ → ℂ) (F : ℂ → ℂ)
variable (hseries : ∀ z, HasSum (fun j => a j * z ^ j) (F z))
variable (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))

include hseries hweighted in
theorem entire_derivative_bound (b : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖iteratedDeriv b F z‖ ≤ weightedNorm a b R := by
  exact (coefficient_derivative_series a F hseries hweighted b z).norm_le_of_bounded
    (hweighted b R (by linarith)).hasSum
    (fun j => derivative_term_bound (a j) j b R hR z hz)

include hseries hweighted in
private theorem entire_derivative_differentiable (b : ℕ) :
    Differentiable ℂ (iteratedDeriv b F) := by
  intro z
  let R : ℝ := max 1 ‖z‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [le_max_left (1 : ℝ) ‖z‖]
  have hz : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [le_max_right (1 : ℝ) ‖z‖]
  have he : (fun w : ℂ => ∑' j, a j * (j.descFactorial b : ℂ) * w ^ (j - b)) =
      iteratedDeriv b F := funext fun w =>
        (coefficient_derivative_series a F hseries hweighted b w).tsum_eq
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (hweighted b R (by linarith))
    (F := fun j w => a j * (j.descFactorial b : ℂ) * w ^ (j - b))
    (fun j => ((differentiable_const (a j * (j.descFactorial b : ℂ))).mul
      (differentiable_id.pow (j - b))).differentiableOn) isOpen_ball
    (fun j w hw => derivative_term_bound (a j) j b R hR w
      (le_of_lt (mem_ball_zero_iff.mp hw)))
  rw [he] at hd
  exact hd.differentiableAt (isOpen_ball.mem_nhds hz)

def loweredCoefficients (a : ℕ → ℂ) (j : ℕ) : ℂ :=
  -((2 * j + 2 : ℕ) : ℂ) * (2 * j + 1 : ℕ) * a (j + 1)

private theorem lowered_term_bound (L j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ‖loweredCoefficients a j‖ * (j : ℝ) ^ L * R ^ j ≤
      4 * (‖a (j + 1)‖ * ((j + 1 : ℕ) : ℝ) ^ (L + 2) * (max 1 R) ^ (j + 1)) := by
  have hS : 1 ≤ max 1 R := le_max_left _ _
  have hp : R ^ j ≤ (max 1 R) ^ (j + 1) :=
    (pow_le_pow_left₀ hR (le_max_right 1 R) j).trans
      (pow_le_pow_right₀ hS (by omega))
  have hj : (j : ℝ) ^ L ≤ ((j + 1 : ℕ) : ℝ) ^ L := by gcongr; norm_cast; omega
  have hc : ((2 * j + 2 : ℕ) : ℝ) * (2 * j + 1 : ℕ) ≤
      4 * ((j + 1 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  simp only [loweredCoefficients, norm_mul, norm_neg, Complex.norm_natCast]
  calc
    _ ≤ (4 * ((j + 1 : ℕ) : ℝ) ^ 2) * ‖a (j + 1)‖ *
        ((j + 1 : ℕ) : ℝ) ^ L * (max 1 R) ^ (j + 1) := by gcongr
    _ = _ := by rw [pow_add]; ring

include hweighted in
private theorem lowered_weighted_summable (L : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j => ‖loweredCoefficients a j‖ * (j : ℝ) ^ L * R ^ j) := by
  have hs := ((summable_nat_add_iff 1).mpr
    (hweighted (L + 2) (max 1 R) (by positivity))).mul_left 4
  exact hs.of_nonneg_of_le (fun j => by positivity)
    (fun j => lowered_term_bound a L j R hR)

include hweighted in
theorem lowered_weighted_data (L : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j => ‖loweredCoefficients a j‖ * (j : ℝ) ^ L * R ^ j) ∧
      weightedNorm (loweredCoefficients a) L R ≤
        4 * weightedNorm a (L + 2) (max 1 R) := by
  refine ⟨lowered_weighted_summable a hweighted L R hR, ?_⟩
  have hs := hweighted (L + 2) (max 1 R) (by positivity)
  have hshift := hs.sum_add_tsum_nat_add 1
  have hz : (∑' j, ‖a (j + 1)‖ * ((j + 1 : ℕ) : ℝ) ^ (L + 2) *
      (max 1 R) ^ (j + 1)) = weightedNorm a (L + 2) (max 1 R) := by
    simpa [weightedNorm] using hshift
  calc
    _ ≤ ∑' j, 4 * (‖a (j + 1)‖ * ((j + 1 : ℕ) : ℝ) ^ (L + 2) *
        (max 1 R) ^ (j + 1)) :=
      (lowered_weighted_summable a hweighted L R hR).tsum_le_tsum
        (fun j => lowered_term_bound a L j R hR)
        (((summable_nat_add_iff 1).mpr hs).mul_left 4)
    _ = _ := by rw [tsum_mul_left, hz]

include hseries hweighted in
theorem lowered_series (z : ℂ) :
    HasSum (fun j => loweredCoefficients a j * z ^ j)
      (-4 * z * iteratedDeriv 2 F z - 2 * deriv F z) := by
  have h1 := coefficient_derivative_series a F hseries hweighted 1 z
  have h2 := (coefficient_derivative_series a F hseries hweighted 2 z).mul_left z
  have hs1 : HasSum (fun j => ((j + 1 : ℕ) : ℂ) * a (j + 1) * z ^ j) (deriv F z) := by
    have hs := (hasSum_nat_add_iff' 1).mpr h1
    simpa [Nat.descFactorial_succ, mul_comm, mul_left_comm, mul_assoc] using hs
  have hs2 : HasSum (fun j : ℕ => (j : ℂ) * ((j + 1 : ℕ) : ℂ) * a (j + 1) * z ^ j)
      (z * iteratedDeriv 2 F z) := by
    have hs : HasSum (fun j : ℕ => z * (a (j + 1) *
        ((j + 1).descFactorial 2 : ℂ) * z ^ (j + 1 - 2)))
        (z * iteratedDeriv 2 F z) := by
      simpa using (hasSum_nat_add_iff' 1).mpr h2
    apply hs.congr_fun
    intro j
    cases j with
    | zero => simp
    | succ j =>
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one,
        show j + 1 + 1 - 2 = j by omega]
      push_cast
      simp only [pow_succ]
      ring
  have hs := (hs2.mul_left (-4)).sub (hs1.mul_left 2)
  have heq : (-4 : ℂ) * (z * iteratedDeriv 2 F z) - 2 * deriv F z =
      -4 * z * iteratedDeriv 2 F z - 2 * deriv F z := by ring
  rw [heq] at hs
  apply hs.congr_fun
  intro j
  simp only [loweredCoefficients]
  push_cast
  ring

include hseries hweighted in
private theorem segment_derivative (k m : ℕ) (c : ℝ) (y : ℂ) :
    iteratedDeriv m (fun t : ℝ => iteratedDeriv k F ((c : ℂ) + t * y)) =
      fun t : ℝ => y ^ m * iteratedDeriv (k + m) F ((c : ℂ) + t * y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd := (entire_derivative_differentiable a F hseries hweighted (k + m)
      ((c : ℂ) + t * y)).hasDerivAt
    have hc := hd.comp ((t : ℝ) : ℂ)
      ((hasDerivAt_const _ (c : ℂ)).add ((hasDerivAt_id _).mul_const y))
    have hr := (hc.const_mul (y ^ m)).comp_ofReal
    convert hr.deriv using 1 <;>
      simp [← iteratedDeriv_succ, pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm]

include hseries hweighted in
private theorem segment_smooth (k : ℕ) (c : ℝ) (y : ℂ) (m : ℕ) :
    ContDiff ℝ m (fun t : ℝ => iteratedDeriv k F ((c : ℂ) + t * y)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro i _
  rw [segment_derivative a F hseries hweighted]
  intro t
  have hd := (entire_derivative_differentiable a F hseries hweighted (k + i)
    ((c : ℂ) + t * y)).hasDerivAt
  exact (((hd.comp ((t : ℝ) : ℂ)
    ((hasDerivAt_const _ (c : ℂ)).add ((hasDerivAt_id _).mul_const y))).const_mul
      (y ^ i)).comp_ofReal).differentiableAt

include hseries hweighted in
theorem exact_order_taylor_bound (c sigma : ℝ) (hc : 0 < c) (hs : 0 < sigma)
    (v k : ℕ) (hk : k ≤ v) (ho : IsExactRealOrder F c v)
    (y : ℂ) (hy : ‖y‖ ≤ sigma) :
    ‖iteratedDeriv k F ((c : ℂ) + y) -
        iteratedDeriv v F c * y ^ (v - k) / ((v - k).factorial : ℂ)‖ ≤
      weightedNorm a (v + 1) (max 1 (c + sigma)) * ‖y‖ ^ (v - k + 1) /
        ((v - k).factorial : ℝ) := by
  let g : ℝ → ℂ := fun t => iteratedDeriv k F ((c : ℂ) + t * y)
  have hg (m : ℕ) : ContDiff ℝ m g := segment_smooth a F hseries hweighted k c y m
  have hi (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin m g (Icc 0 1) t =
        y ^ m * iteratedDeriv (k + m) F ((c : ℂ) + t * y) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hg m).contDiffAt ht]
    exact congrFun (segment_derivative a F hseries hweighted k m c y) t
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (v - k + 1) g (Icc 0 1) t‖ ≤
        weightedNorm a (v + 1) (max 1 (c + sigma)) * ‖y‖ ^ (v - k + 1) := by
    rw [hi _ t ht, norm_mul, norm_pow, show k + (v - k + 1) = v + 1 by omega]
    have hz : ‖(c : ℂ) + t * y‖ ≤ max 1 (c + sigma) := by
      calc
        _ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * y‖ := norm_add_le _ _
        _ = c + t * ‖y‖ := by simp [norm_mul, abs_of_pos hc, abs_of_nonneg ht.1]
        _ ≤ c + sigma := by
          exact add_le_add_right ((mul_le_of_le_one_left (norm_nonneg y) ht.2).trans hy) c
        _ ≤ _ := le_max_right _ _
    exact (mul_le_mul_of_nonneg_left
      (entire_derivative_bound a F hseries hweighted (v + 1) _ (le_max_left _ _) _ hz)
      (by positivity)).trans_eq (mul_comm _ _)
  have ht := taylor_mean_remainder_bound (f := g) (n := v - k)
    (by norm_num : (0 : ℝ) ≤ 1) (hg (v - k + 1)).contDiffOn
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hb
  have hp : taylorWithinEval g (v - k) (Icc 0 1) 0 1 =
      iteratedDeriv v F c * y ^ (v - k) / ((v - k).factorial : ℂ) := by
    rw [taylor_within_apply, Finset.sum_eq_single (v - k)]
    · rw [hi _ 0 (by simp), show k + (v - k) = v by omega]
      simp [Complex.real_smul, div_eq_mul_inv, mul_comm, mul_left_comm]
    · intro m hm hne
      rw [hi _ 0 (by simp)]
      have hkm : k + m < v := by have := Finset.mem_range.mp hm; omega
      simp [ho.2 (k + m) hkm]
    · simp
  simpa [g, hp] using ht

open scoped Nat

private theorem hermite_top_coefficient (v r : ℕ) (hr : 2 * r ≤ v) :
    (((Polynomial.hermite v).coeff (v - 2 * r) : ℤ) : ℂ) =
      (-1 : ℂ) ^ r * (correctionCoeff r (2 * r) : ℂ) *
        (v.factorial : ℂ) / ((v - 2 * r).factorial : ℂ) := by
  have hv : 2 * r + (v - 2 * r) = v := by omega
  have hf : (2 * r).factorial = 2 ^ r * r.factorial * (2 * r - 1)‼ := by
    cases r with
    | zero => norm_num
    | succ r =>
      have hh := Nat.factorial_eq_mul_doubleFactorial (2 * (r + 1) - 1)
      rw [show 2 * (r + 1) - 1 + 1 = 2 * (r + 1) by omega,
        Nat.doubleFactorial_two_mul] at hh
      exact hh
  have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le v (2 * r))
  rw [show v - (v - 2 * r) = 2 * r by omega, hf] at hchoose
  have hc : (v.choose (v - 2 * r) : ℂ) * ((v - 2 * r).factorial : ℂ) *
      ((2 : ℂ) ^ r * (r.factorial : ℂ) * ((2 * r - 1)‼ : ℂ)) =
        (v.factorial : ℂ) := by exact_mod_cast hchoose
  have hcoeff := Polynomial.coeff_hermite_explicit r (v - 2 * r)
  rw [hv] at hcoeff
  rw [hcoeff, correctionCoeff_top]
  push_cast
  have hrf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hdf : ((v - 2 * r).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [← hc]
  field_simp
  <;> ring

theorem hermite_normalization (v : ℕ) (u : ℂ) :
    aeval u (Polynomial.hermite v) =
      ∑ r ∈ Finset.range (v / 2 + 1), (-1 : ℂ) ^ r *
        (correctionCoeff r (2 * r) : ℂ) * (v.factorial : ℂ) /
          ((v - 2 * r).factorial : ℂ) * u ^ (v - 2 * r) := by
  have hp : (Polynomial.hermite v).map (Int.castRingHom ℂ) =
      ∑ r ∈ Finset.range (v / 2 + 1),
        C ((-1 : ℂ) ^ r * (correctionCoeff r (2 * r) : ℂ) * (v.factorial : ℂ) /
          ((v - 2 * r).factorial : ℂ)) * X ^ (v - 2 * r) := by
    apply Polynomial.ext
    intro h
    simp only [coeff_map,
      finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases hex : ∃ r ∈ Finset.range (v / 2 + 1), v - 2 * r = h
    · obtain ⟨r, hr, rfl⟩ := hex
      rw [Finset.sum_eq_single r]
      · simp only [ite_true]
        exact hermite_top_coefficient v r (by have := Finset.mem_range.mp hr; omega)
      · intro b hb hbr
        have hh : v - 2 * b ≠ v - 2 * r := by
          have := Finset.mem_range.mp hb
          have := Finset.mem_range.mp hr
          omega
        simp [hh, Ne.symm hh]
      · exact fun hn => False.elim (hn hr)
    · have hz : (Polynomial.hermite v).coeff h = 0 := by
        by_cases hv : v < h
        · exact Polynomial.coeff_hermite_of_lt hv
        · apply Polynomial.coeff_hermite_of_odd_add
          apply Nat.not_even_iff_odd.mp
          intro he
          obtain ⟨r, hr⟩ := (Nat.even_sub (by omega : h ≤ v)).mpr
            (Nat.even_add.mp he)
          apply hex
          refine ⟨r, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
      rw [hz]
      simp only [map_zero]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      have hh : v - 2 * r ≠ h := fun hh => hex ⟨r, hr, hh⟩
      simp [hh, Ne.symm hh]
  have he := congrArg (fun p : ℂ[X] => p.eval u) hp
  change (Polynomial.hermite v).eval₂ (Int.castRingHom ℂ) u = _
  simpa only [eval_map, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X] using he

theorem hermite_scaling_threshold (t0 sigma q : ℝ) (ht0 : 0 < t0)
    (hsigma : 0 < sigma) (hq : 2 ≤ q) :
    let T := max 1 (max (2 * q) (t0 * q / sigma))
    let N := max 1 ⌈T ^ 2⌉₊
    ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ 1 ≤ Real.sqrt n ∧
      q / Real.sqrt n ≤ 1 / 2 ∧ t0 * q / Real.sqrt n ≤ sigma := by
  intro T N n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hT : 1 ≤ T := le_max_left _ _
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hceil : T ^ 2 ≤ (n : ℝ) := (Nat.ceil_le.mp ((le_max_right _ _).trans hn))
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hTs : T ≤ Real.sqrt n := by nlinarith
  have h2q : 2 * q ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have htq : t0 * q / sigma ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hn1, hT.trans hTs, ?_, ?_⟩
  · apply (div_le_iff₀ hs).mpr; linarith
  · apply (div_le_iff₀ hs).mpr
    have := (div_le_iff₀ hsigma).mp (htq.trans hTs)
    nlinarith

private theorem shifted_power_bound (k : ℕ) (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    ‖1 + w‖ ^ k ≤ (2 : ℝ) ^ k ∧
      ‖(1 + w) ^ k - 1‖ ≤ (k : ℝ) * 2 ^ k * ‖w‖ := by
  have hb : ‖1 + w‖ ≤ (2 : ℝ) := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num at *; linarith
  refine ⟨pow_le_pow_left₀ (norm_nonneg _) hb k, ?_⟩
  have he := geom_sum_mul (1 + w) k
  simp only [add_sub_cancel_left] at he
  rw [← he, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range k, (1 + w) ^ i‖ ≤ (k : ℝ) * 2 ^ k := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, ‖(1 + w) ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) hb i).trans
          (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega))
      _ = _ := by simp
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

private theorem normalized_leading_identity (t s f : ℂ) (ht : t ≠ 0)
    (hs : s ≠ 0) (hf : f ≠ 0) (v r k : ℕ) (hk : k ≤ v)
    (c u w : ℂ) :
    ((-1 : ℂ) ^ r / (s ^ 2) ^ r * c * (t * w) ^ k *
        (f * (t * u / s) ^ (v - k) / ((v - k).factorial : ℂ))) /
      ((t ^ v * f / (v.factorial : ℂ)) / s ^ v) =
      (-1 : ℂ) ^ r * c * (v.factorial : ℂ) / ((v - k).factorial : ℂ) *
        u ^ (v - k) * w ^ k * (s ^ v / (s ^ (2 * r) * s ^ (v - k))) := by
  have htv : t ^ v = t ^ k * t ^ (v - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  simp only [mul_pow, div_pow, ← pow_mul]
  rw [htv]
  field_simp
  <;> ring

private theorem scaled_power_bound (s : ℝ) (hs : 1 ≤ s) (v A B : ℕ)
    (hv : v + 1 ≤ A + B) : s ^ v / (s ^ A * s ^ B) ≤ 1 / s := by
  have hpos : 0 < s := by linarith
  apply (div_le_div_iff₀ (by positivity) hpos).mpr
  rw [one_mul, ← pow_succ, ← pow_add]
  exact pow_le_pow_right₀ hs hv

private theorem normalized_leading_bound (s q A : ℝ) (hs : 1 ≤ s) (hq : 2 ≤ q)
    (hA : 0 ≤ A) (hqs : q / s ≤ 1 / 2) (v r k : ℕ) (hk : k ≤ 2 * r)
    (hr : 2 * r ≤ v) (u : ℂ) (hu : ‖u‖ ≤ q) :
    ‖(-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) * (1 + u / (s : ℂ)) ^ k *
        ((s ^ v / (s ^ (2 * r) * s ^ (v - k)) : ℝ) : ℂ) -
      (if k = 2 * r then (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) else 0)‖ ≤
      A * q ^ (v - k) * 2 ^ k * (1 + (k : ℝ) * q) / s := by
  have hspos : 0 < s := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hw : ‖u / (s : ℂ)‖ ≤ q / s := by
    simpa [norm_div, abs_of_pos hspos] using div_le_div_of_nonneg_right hu hspos.le
  have hp := shifted_power_bound k (u / (s : ℂ)) (hw.trans hqs)
  have huq : ‖u‖ ^ (v - k) ≤ q ^ (v - k) := pow_le_pow_left₀ (norm_nonneg _) hu _
  have hnorm : ‖(-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k)‖ = A * ‖u‖ ^ (v - k) := by
    simp [norm_mul, norm_pow, abs_of_nonneg hA]
  split_ifs with htop
  · have hratio : s ^ v / (s ^ (2 * r) * s ^ (v - k)) = 1 := by
      rw [← pow_add, ← htop, Nat.add_sub_of_le (hk.trans hr)]
      exact div_self (by positivity)
    rw [hratio, Complex.ofReal_one, mul_one]
    rw [show (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) * (1 + u / (s : ℂ)) ^ k -
        (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) =
      ((-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k)) * ((1 + u / (s : ℂ)) ^ k - 1) by ring,
      norm_mul, hnorm]
    calc
      _ ≤ (A * q ^ (v - k)) * ((k : ℝ) * 2 ^ k * (q / s)) := by
        gcongr
        exact hp.2.trans (mul_le_mul_of_nonneg_left hw (by positivity))
      _ ≤ _ := by
        apply (le_div_iff₀ hspos).mpr
        field_simp
        nlinarith [show 0 ≤ A * q ^ (v - k) * 2 ^ k by positivity]
  · rw [sub_zero, norm_mul, norm_mul, hnorm, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ A * q ^ (v - k) * 2 ^ k * (1 / s) := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left huq hA) hp.1 (by positivity) (by positivity))
          (scaled_power_bound s hs v (2 * r) (v - k) (by omega))
          (by positivity) (by positivity)
      _ ≤ _ := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_right _ hspos.le
        exact le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hq0))

private theorem normalized_taylor_bound (t s q B c : ℝ) (ht : 0 < t)
    (hs : 1 ≤ s) (hq : 2 ≤ q) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hqs : q / s ≤ 1 / 2) (cv : ℂ) (hcv : cv ≠ 0)
    (v r k : ℕ) (hk : k ≤ 2 * r) (hr : 2 * r ≤ v)
    (u E : ℂ) (hu : ‖u‖ ≤ q)
    (hE : ‖E‖ ≤ B * (t * q / s) ^ (v - k + 1) / ((v - k).factorial : ℝ)) :
    ‖((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (c : ℂ) *
        ((t : ℂ) * (1 + u / (s : ℂ))) ^ k * E) / (cv / (s : ℂ) ^ v)‖ ≤
      (c * 2 ^ k * B * t ^ (v + 1) * q ^ (v - k + 1) /
        (‖cv‖ * ((v - k).factorial : ℝ))) / s := by
  have hspos : 0 < s := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hnormcv : 0 < ‖cv‖ := norm_pos_iff.mpr hcv
  have hw : ‖u / (s : ℂ)‖ ≤ 1 / 2 := by
    calc
      _ = ‖u‖ / s := by simp [norm_div, abs_of_pos hspos]
      _ ≤ q / s := div_le_div_of_nonneg_right hu hspos.le
      _ ≤ _ := hqs
  have hp := (shifted_power_bound k (u / (s : ℂ)) hw).1
  have htv : t ^ (v + 1) = t ^ k * t ^ (v - k + 1) := by
    rw [← pow_add]; congr 1; omega
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos ht, abs_of_pos hspos]
  calc
    _ ≤ (1 / (s ^ 2) ^ r * c * (t ^ k * 2 ^ k) *
        (B * (t * q / s) ^ (v - k + 1) / ((v - k).factorial : ℝ))) /
          (‖cv‖ / s ^ v) := by
      rw [mul_pow]
      gcongr
    _ = (c * 2 ^ k * B * t ^ (v + 1) * q ^ (v - k + 1) /
          (‖cv‖ * ((v - k).factorial : ℝ))) *
        (s ^ v / (s ^ (2 * r) * s ^ (v - k + 1))) := by
      rw [htv]
      simp only [mul_pow, div_pow, ← pow_mul, inv_inv]
      field_simp
      <;> ring
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using scaled_power_bound s hs v (2 * r) (v - k + 1) (by omega)

include hseries hweighted in
private theorem scaled_correction_term_bound (t sigma s q : ℝ) (ht : 0 < t)
    (hsigma : 0 < sigma) (hs : 1 ≤ s) (hq : 2 ≤ q)
    (hqs : q / s ≤ 1 / 2) (htqs : t * q / s ≤ sigma)
    (v r k : ℕ) (ho : IsExactRealOrder F t v) (hk : k ≤ 2 * r) (hr : 2 * r ≤ v)
    (u : ℂ) (hu : ‖u‖ ≤ q) :
    let B := weightedNorm a (v + 1) (max 1 (t + sigma))
    let cv := (t : ℂ) ^ v * iteratedDeriv v F t / (v.factorial : ℂ)
    let A := correctionCoeff r k * (v.factorial : ℝ) / ((v - k).factorial : ℝ)
    ‖((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (correctionCoeff r k : ℂ) *
        ((t : ℂ) * (1 + u / (s : ℂ))) ^ k *
          iteratedDeriv k F ((t : ℂ) * (1 + u / (s : ℂ)))) / (cv / (s : ℂ) ^ v) -
      (if k = 2 * r then (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) else 0)‖ ≤
      (A * q ^ (v - k) * 2 ^ k * (1 + (k : ℝ) * q) +
        correctionCoeff r k * 2 ^ k * B * t ^ (v + 1) * q ^ (v - k + 1) /
          (‖cv‖ * ((v - k).factorial : ℝ))) / s := by
  intro B cv A
  have hspos : 0 < s := by linarith
  have hcv : cv ≠ 0 := div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')) ho.1)
    (by exact_mod_cast Nat.factorial_ne_zero v)
  have hB : 0 ≤ B := tsum_nonneg (fun j => by positivity)
  have hc := correctionCoeff_nonneg r k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let y : ℂ := (t : ℂ) * u / (s : ℂ)
  let z : ℂ := (t : ℂ) * (1 + u / (s : ℂ))
  let f : ℂ := iteratedDeriv v F t
  let lead : ℂ := f * y ^ (v - k) / ((v - k).factorial : ℂ)
  let Q : ℂ := ((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (correctionCoeff r k : ℂ) *
    z ^ k * iteratedDeriv k F z) / (cv / (s : ℂ) ^ v)
  let Qlead : ℂ := ((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (correctionCoeff r k : ℂ) *
    z ^ k * lead) / (cv / (s : ℂ) ^ v)
  let H : ℂ := if k = 2 * r then (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) else 0
  have hyq : ‖y‖ ≤ t * q / s := by
    dsimp [y]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos hspos]
    gcongr
  have htaylor : ‖iteratedDeriv k F z - lead‖ ≤
      B * (t * q / s) ^ (v - k + 1) / ((v - k).factorial : ℝ) := by
    have hb := exact_order_taylor_bound a F hseries hweighted t sigma ht hsigma
      v k (hk.trans hr) ho y (hyq.trans htqs)
    have hz : (t : ℂ) + y = z := by dsimp [y, z]; ring
    rw [hz] at hb
    exact hb.trans (by dsimp [B, lead, f]; gcongr)
  have htail := normalized_taylor_bound t s q B (correctionCoeff r k) ht hs hq
    hB hc hqs cv hcv v r k hk hr u (iteratedDeriv k F z - lead) hu htaylor
  have hdiff : ‖Q - Qlead‖ ≤
      (correctionCoeff r k * 2 ^ k * B * t ^ (v + 1) * q ^ (v - k + 1) /
        (‖cv‖ * ((v - k).factorial : ℝ))) / s := by
    calc
      _ = ‖((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (correctionCoeff r k : ℂ) *
          z ^ k * (iteratedDeriv k F z - lead)) / (cv / (s : ℂ) ^ v)‖ := by
        congr 1; dsimp [Q, Qlead]; ring
      _ ≤ _ := htail
  have heq : Qlead = (-1 : ℂ) ^ r * (A : ℂ) * u ^ (v - k) *
      (1 + u / (s : ℂ)) ^ k *
        ((s ^ v / (s ^ (2 * r) * s ^ (v - k)) : ℝ) : ℂ) := by
    have he := normalized_leading_identity (t : ℂ) (s : ℂ) f
      (Complex.ofReal_ne_zero.mpr ht.ne') (Complex.ofReal_ne_zero.mpr hspos.ne')
      ho.1 v r k (hk.trans hr) (correctionCoeff r k : ℂ) u (1 + u / (s : ℂ))
    simpa only [Qlead, lead, y, z, cv, f, A, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
      mul_div_assoc, mul_assoc] using he
  have hleading : ‖Qlead - H‖ ≤
      A * q ^ (v - k) * 2 ^ k * (1 + (k : ℝ) * q) / s := by
    rw [heq]
    exact normalized_leading_bound s q A hs hq hA hqs v r k hk hr u hu
  change ‖Q - H‖ ≤ _
  calc
    _ ≤ ‖Q - Qlead‖ + ‖Qlead - H‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := (add_le_add hdiff hleading).trans_eq (by ring)

include hseries hweighted in
theorem hermite_scaled_estimate (t0 sigma : ℝ) (ht0 : 0 < t0) (hsigma : 0 < sigma)
    (v : ℕ) (ho : IsExactRealOrder F t0 v) : ScaledFunctionEstimate F a t0 sigma v := by
  intro q hq
  let K := v / 2
  let R := max 1 (t0 + sigma)
  let B := weightedNorm a (v + 1) R
  let W := weightedNorm a (2 * K + 2) R
  let cv : ℂ := (t0 : ℂ) ^ v * iteratedDeriv v F t0 / (v.factorial : ℂ)
  let A : ℕ → ℕ → ℝ := fun r k =>
    correctionCoeff r k * (v.factorial : ℝ) / ((v - k).factorial : ℝ)
  let D : ℕ → ℕ → ℝ := fun r k =>
    A r k * q ^ (v - k) * 2 ^ k * (1 + (k : ℝ) * q) +
      correctionCoeff r k * 2 ^ k * B * t0 ^ (v + 1) * q ^ (v - k + 1) /
        (‖cv‖ * ((v - k).factorial : ℝ))
  let C : ℝ := 1 + 2 * W / ‖cv‖ +
    ∑ r ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (2 * r + 1), D r k
  have hq0 : 0 ≤ q := by linarith
  have hW : 0 ≤ W := tsum_nonneg (fun j => by positivity)
  have hB : 0 ≤ B := tsum_nonneg (fun j => by positivity)
  have hcv : cv ≠ 0 := div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht0.ne')) ho.1)
    (by exact_mod_cast Nat.factorial_ne_zero v)
  have hD (r k : ℕ) : 0 ≤ D r k := by
    have hc := correctionCoeff_nonneg r k
    dsimp [D, A]
    positivity
  have hsumD : 0 ≤ ∑ r ∈ Finset.range (K + 1),
      ∑ k ∈ Finset.range (2 * r + 1), D r k :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun k _ => hD r k
  have hC : 0 < C := by dsimp [C]; positivity
  let T := max 1 (max (2 * q) (t0 * q / sigma))
  let N : ℕ := max 1 ⌈T ^ 2⌉₊
  refine ⟨C, hC, N, ?_⟩
  intro n hn
  obtain ⟨hn1, hs1, hqs, htqs⟩ :=
    hermite_scaling_threshold t0 sigma q ht0 hsigma hq n hn
  refine ⟨hn1, ?_⟩
  intro u hu
  let s : ℝ := Real.sqrt n
  have hspos : 0 < s := by dsimp [s]; linarith
  have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hnR : (n : ℝ) = s ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have hnC : (n : ℂ) = (s : ℂ) ^ 2 := by exact_mod_cast hnR
  let y : ℂ := (t0 : ℂ) * u / (s : ℂ)
  let z : ℂ := (t0 : ℂ) * (1 + u / (s : ℂ))
  let den : ℂ := cv / (s : ℂ) ^ v
  let E : ℂ := (coefficientPolynomial a n).eval z -
    ∑ r ∈ Finset.range (K + 1), ((-1 : ℂ) ^ r / (n : ℂ) ^ r) * correctionOperator r F z
  let term : ℕ → ℕ → ℂ := fun r k =>
    ((-1 : ℂ) ^ r / ((s : ℂ) ^ 2) ^ r * (correctionCoeff r k : ℂ) *
      z ^ k * iteratedDeriv k F z) / den
  let top : ℕ → ℕ → ℂ := fun r k =>
    if k = 2 * r then (-1 : ℂ) ^ r * (A r k : ℂ) * u ^ (v - k) else 0
  have hy : ‖y‖ ≤ sigma := by
    calc
      _ = t0 * ‖u‖ / s := by simp [y, norm_div, norm_mul, abs_of_pos ht0, abs_of_pos hspos]
      _ ≤ t0 * q / s := by gcongr
      _ ≤ _ := htqs
  have hz : ‖z‖ ≤ R := by
    have heq : z = (t0 : ℂ) + y := by dsimp [z, y]; ring
    rw [heq]
    calc
      _ ≤ ‖(t0 : ℂ)‖ + ‖y‖ := norm_add_le _ _
      _ ≤ t0 + sigma := by simpa [abs_of_pos ht0] using add_le_add_right hy t0
      _ ≤ _ := le_max_right _ _
  have hE : ‖E‖ ≤ 2 / (n : ℝ) ^ (K + 1) * W := by
    simpa only [E, W, iteratedDeriv_zero] using
      analytic_coefficient_operator_error a F hseries hweighted n K 0 hn1
        R (le_max_left _ _) z hz
  have hEn : ‖E / den‖ ≤ (2 * W / ‖cv‖) / s := by
    simp only [den, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hspos]
    calc
      _ ≤ (2 / (n : ℝ) ^ (K + 1) * W) / (‖cv‖ / s ^ v) := by gcongr
      _ = (2 * W / ‖cv‖) * (s ^ v / (s ^ (2 * (K + 1)) * s ^ 0)) := by
        rw [hnR]
        simp only [← pow_mul, pow_zero]
        field_simp
        <;> ring
      _ ≤ _ := by
        rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [one_div] using
          scaled_power_bound s hs1 v (2 * (K + 1)) 0 (by dsimp [K]; omega)
  have hterms (r : ℕ) (hr : r ∈ Finset.range (K + 1))
      (k : ℕ) (hk : k ∈ Finset.range (2 * r + 1)) :
      ‖term r k - top r k‖ ≤ D r k / s := by
    have hr' : 2 * r ≤ v := by have := Finset.mem_range.mp hr; dsimp [K] at this; omega
    have hk' : k ≤ 2 * r := by have := Finset.mem_range.mp hk; omega
    exact scaled_correction_term_bound a F hseries hweighted t0 sigma s q ht0 hsigma
      hs1 hq hqs htqs v r k ho hk' hr' u hu
  have hH : aeval u (Polynomial.hermite v) =
      ∑ r ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (2 * r + 1), top r k := by
    rw [hermite_normalization]
    apply Finset.sum_congr rfl
    intro r hr
    simp [top, A, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
      mul_assoc, mul_div_assoc]
  have hfinite : (∑ r ∈ Finset.range (K + 1),
      ((-1 : ℂ) ^ r / (n : ℂ) ^ r) * correctionOperator r F z) / den =
      ∑ r ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (2 * r + 1), term r k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [correctionOperator, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [term]
    rw [hnC]
    ring
  have hdecomp : (coefficientPolynomial a n).eval z / den - aeval u (Polynomial.hermite v) =
      E / den + ∑ r ∈ Finset.range (K + 1),
        ∑ k ∈ Finset.range (2 * r + 1), (term r k - top r k) := by
    rw [hH]
    simp only [Finset.sum_sub_distrib]
    rw [← hfinite]
    dsimp [E]
    ring
  change ‖(coefficientPolynomial a n).eval z / den - aeval u (Polynomial.hermite v)‖ ≤ C / s
  rw [hdecomp]
  calc
    _ ≤ ‖E / den‖ + ‖∑ r ∈ Finset.range (K + 1),
        ∑ k ∈ Finset.range (2 * r + 1), (term r k - top r k)‖ := norm_add_le _ _
    _ ≤ (2 * W / ‖cv‖) / s + ∑ r ∈ Finset.range (K + 1),
        ∑ k ∈ Finset.range (2 * r + 1), D r k / s := by
      apply add_le_add hEn
      apply norm_sum_le_of_le
      intro r hr
      exact norm_sum_le_of_le _ (fun k hk => hterms r hr k hk)
    _ ≤ C / s := by
      simp only [← Finset.sum_div]
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hspos.le
      dsimp [C]
      linarith

#print axioms entire_derivative_bound
#print axioms lowered_weighted_data
#print axioms lowered_series
#print axioms exact_order_taylor_bound
#print axioms hermite_normalization
#print axioms hermite_scaling_threshold
#print axioms hermite_scaled_estimate

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
