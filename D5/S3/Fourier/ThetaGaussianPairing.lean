/- GID: D5/S3/Fourier/ThetaGaussianPairing
   generality: G
   mirror-B: D5/B/S3/Fourier/ThetaGaussianPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative pairing inequalities for translated Gaussian derivatives. -/

import D5.S3.Fourier.PlanarThetaFoundation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Quantitative Gaussian pairing -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- The normalized tail after the first positive Fourier mode. -/
def gaussianTail (v : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 *
    Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))

private lemma square_le_four_pow (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 ≤ 4 * (4 : ℝ) ^ k := by
  have h : (k : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 1) := by
    have h := Real.mul_add_one_le_add_one_pow (by norm_num : (0 : ℝ) ≤ 1) (k + 1)
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, one_add_one_eq_two,
      add_assoc] using h
  calc
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    _ = ((2 : ℝ) ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = 4 * (4 : ℝ) ^ k := by
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      rw [pow_succ]
      ring

private lemma exp_three_halves : (4 : ℝ) < Real.exp (3 / 2) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma exp_three : (20 : ℝ) < Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma tail_term_le (v : ℝ) (hv : 0 ≤ v) (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 * Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1)) ≤
      (4 * Real.exp (-3 * Real.pi * v)) ^ (k + 1) := by
  have he : -Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1) ≤
      (-3 * Real.pi * v) * ((k : ℝ) + 1) := by
    have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hp : 0 ≤ Real.pi * v := mul_nonneg Real.pi_pos.le hv
    nlinarith [mul_nonneg hp (show 0 ≤ (k : ℝ) ^ 2 + k by positivity)]
  calc
    _ ≤ (4 * (4 : ℝ) ^ k) * Real.exp ((-3 * Real.pi * v) * ((k : ℝ) + 1)) :=
      mul_le_mul (square_le_four_pow k) (Real.exp_le_exp.mpr he)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show (-3 * Real.pi * v) * ((k : ℝ) + 1) =
        (k + 1 : ℕ) * (-3 * Real.pi * v) by push_cast; ring,
        Real.exp_nat_mul, mul_pow, pow_succ (4 : ℝ)]
      ring

private lemma ratio_lt {v : ℝ} (hv : 1 / 2 ≤ v) :
    4 * Real.exp (-3 * Real.pi * v) < 1 / 16 := by
  have hp := Real.pi_gt_three
  have harg : (9 : ℝ) / 2 < 3 * Real.pi * v := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.pi - 3)
      (by linarith : 0 ≤ v - 1 / 2)]
  have he : (64 : ℝ) < Real.exp (9 / 2) := by
    have h := pow_lt_pow_left₀ exp_three_halves (by norm_num : (0 : ℝ) ≤ 4)
      (by decide : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    convert h using 1 <;> norm_num
  have hbig : (64 : ℝ) < Real.exp (3 * Real.pi * v) :=
    he.trans (Real.exp_lt_exp.mpr harg)
  rw [show -3 * Real.pi * v = -(3 * Real.pi * v) by ring, Real.exp_neg]
  have hpos := Real.exp_pos (3 * Real.pi * v)
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ hpos).mpr
  linarith

/-- A geometric majorant, including convergence and the uniform one-fifteenth bound. -/
theorem gaussian_tail_bound {v : ℝ} (hv : 1 / 2 ≤ v) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) ∧
    gaussianTail v ≤ (4 * Real.exp (-3 * Real.pi * v)) /
      (1 - 4 * Real.exp (-3 * Real.pi * v)) ∧ gaussianTail v < 1 / 15 := by
  let r := 4 * Real.exp (-3 * Real.pi * v)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r < 1 / 16 := ratio_lt hv
  have hr1 : r < 1 := by linarith
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_right r
  have hmajor (k : ℕ) :
      ((k : ℝ) + 2) ^ 2 * Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1)) ≤
        r ^ k * r := by
    simpa only [pow_succ] using tail_term_le v (by linarith) k
  have hsum := hs.of_nonneg_of_le (fun k => by positivity) hmajor
  have hb : gaussianTail v ≤ r / (1 - r) := by
    calc
      gaussianTail v ≤ ∑' k : ℕ, r ^ k * r := hsum.tsum_le_tsum hmajor hs
      _ = r / (1 - r) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]; ring
  refine ⟨hsum, hb, hb.trans_lt ?_⟩
  apply (div_lt_iff₀ (by linarith : 0 < 1 - r)).mpr
  linarith

/-- The small-parameter comparison retains an exponential margin in the tail. -/
theorem gaussian_tail_scaled_bound {s v : ℝ} (hs : 0 < s) (hs' : s ≤ Real.pi / 6)
    (hv : 3 / (4 * s) ≤ v) :
    Real.exp (Real.pi / (4 * s)) * gaussianTail v < 1 / 39999 := by
  have hv' : 1 / 2 ≤ v := by
    have hv0 : 0 < v := (by positivity : 0 < 3 / (4 * s)).trans_le hv
    have hvs := (div_le_iff₀ (by positivity : 0 < 4 * s)).mp hv
    have hs1 : s ≤ 1 := by linarith [Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_right hs1 hv0.le
    nlinarith
  let r := 4 * Real.exp (-12)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have he12 : (160000 : ℝ) < Real.exp 12 := by
    have h := pow_lt_pow_left₀ exp_three (by norm_num : (0 : ℝ) ≤ 20)
      (by decide : (4 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    convert h using 1 <;> norm_num
  have hr : r < 1 / 40000 := by
    dsimp [r]
    rw [Real.exp_neg]
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos 12)).mpr
    linarith
  have hr1 : r < 1 := by linarith
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_right r
  have hmajor (k : ℕ) :
      Real.exp (Real.pi / (4 * s)) *
        (((k : ℝ) + 2) ^ 2 *
          Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) ≤ r ^ k * r := by
    have hsq := square_le_four_pow k
    have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hvs := (div_le_iff₀ (by positivity : 0 < 4 * s)).mp hv
    have hp : (6 : ℝ) ≤ Real.pi / s := by
      apply (le_div_iff₀ hs).mpr
      linarith
    have he : Real.pi / (4 * s) - Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1) ≤
        (-12 : ℝ) * ((k : ℝ) + 1) := by
      have hn1 : 0 ≤ ((k : ℝ) + 2) ^ 2 - 1 := by nlinarith
      have h1 := mul_le_mul_of_nonneg_right hv hn1
      have h2 := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
      have heq : Real.pi / (4 * s) -
          Real.pi * (3 / (4 * s) * (((k : ℝ) + 2) ^ 2 - 1)) =
          -(Real.pi / s) * (3 * ((k : ℝ) + 2) ^ 2 - 4) / 4 := by field_simp [hs.ne']; ring
      have hpoly : 8 * ((k : ℝ) + 1) ≤ 3 * ((k : ℝ) + 2) ^ 2 - 4 := by
        nlinarith [sq_nonneg (k : ℝ)]
      have h3 := mul_le_mul_of_nonneg_left hpoly (by linarith : 0 ≤ Real.pi / s)
      have h4 := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (k : ℝ) + 1)
      linarith
    calc
      _ = ((k : ℝ) + 2) ^ 2 *
          Real.exp (Real.pi / (4 * s) - Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1)) := by
        rw [show Real.pi / (4 * s) -
          Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1) = Real.pi / (4 * s) +
          (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1)) by ring, Real.exp_add]
        ring
      _ ≤ (4 * (4 : ℝ) ^ k) * Real.exp ((-12 : ℝ) * ((k : ℝ) + 1)) :=
        mul_le_mul hsq (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
      _ = r ^ k * r := by
        dsimp [r]
        rw [show (-12 : ℝ) * ((k : ℝ) + 1) = (k + 1 : ℕ) * (-12 : ℝ) by
          push_cast; ring, Real.exp_nat_mul, mul_pow, pow_succ (Real.exp (-12))]
        ring
  have hsum := ((gaussian_tail_bound hv').1).mul_left (Real.exp (Real.pi / (4 * s)))
  calc
    _ = ∑' k : ℕ, Real.exp (Real.pi / (4 * s)) *
        (((k : ℝ) + 2) ^ 2 *
          Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) := by
      rw [gaussianTail, tsum_mul_left]
    _ ≤ ∑' k : ℕ, r ^ k * r := hsum.tsum_le_tsum hmajor hgeom
    _ = r / (1 - r) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]; ring
    _ < 1 / 39999 := (div_lt_iff₀ (by linarith : 0 < 1 - r)).mpr (by linarith)


/-- The normalized error in pairing Gaussian terms for translations at most one quarter. -/
def gaussianPairTail (a : ℝ) : ℝ :=
  ∑' k : ℕ, 4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
    Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))

private lemma exp_linear_weight {a d : ℝ} (ha : 6 ≤ a) (hd : 1 / 2 ≤ d) :
    a * Real.exp (-a * d) ≤ 6 * Real.exp (-6 * d) := by
  have h := Real.add_one_le_exp (d * (a - 6))
  have hm := mul_nonneg (show 0 ≤ d - 1 / 6 by linarith)
    (show 0 ≤ a - 6 by linarith)
  have hl : a ≤ 6 * Real.exp (d * (a - 6)) := by nlinarith
  calc
    _ ≤ (6 * Real.exp (d * (a - 6))) * Real.exp (-a * d) :=
      mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Explicit exponential control of the Gaussian-pairing tail, including convergence. -/
theorem gaussian_pair_tail_bound {a : ℝ} (ha : 6 ≤ a) :
    Summable (fun k : ℕ => 4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
      Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))) ∧
    gaussianPairTail a ≤ (27 / 2) * Real.exp (-3) +
      (96 * Real.exp (-18)) / (1 - 4 * Real.exp (-9)) := by
  have ha0 : 0 ≤ a := by linarith
  let f (k : ℕ) := 4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
    Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))
  let r := 4 * Real.exp (-9)
  let C := 96 * Real.exp (-18)
  have he9 : (8000 : ℝ) < Real.exp 9 := by
    have h := pow_lt_pow_left₀ exp_three (by norm_num : (0 : ℝ) ≤ 20)
      (by decide : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    convert h using 1 <;> norm_num
  have he18 : (64000000 : ℝ) < Real.exp 18 := by
    have h := pow_lt_pow_left₀ exp_three (by norm_num : (0 : ℝ) ≤ 20)
      (by decide : (6 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    convert h using 1 <;> norm_num
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r < 1 / 2 := by
    dsimp [r]
    rw [Real.exp_neg]
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos 9)).mpr
    linarith
  have hC : 2 * C < 1 / 40 := by
    dsimp [C]
    rw [Real.exp_neg]
    rw [← div_eq_mul_inv, ← mul_div_assoc]
    apply (div_lt_iff₀ (Real.exp_pos 18)).mpr
    linarith
  have hterm (k : ℕ) : f k ≤ 24 * ((k : ℝ) + 3 / 4) ^ 2 *
      Real.exp (-6 * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2)) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hd : 1 / 2 ≤ ((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left (exp_linear_weight ha hd)
      (show 0 ≤ 4 * ((k : ℝ) + 3 / 4) ^ 2 by positivity)
    dsimp [f]
    nlinarith only [h]
  have hmajor (k : ℕ) : f (k + 1) ≤ C * r ^ k := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : ((k : ℝ) + 1 + 3 / 4) ^ 2 ≤ 4 * (4 : ℝ) ^ k :=
      (by nlinarith : ((k : ℝ) + 1 + 3 / 4) ^ 2 ≤ ((k : ℝ) + 2) ^ 2).trans
        (square_le_four_pow k)
    have he : -6 * (((k : ℝ) + 1 + 1) ^ 2 - ((k : ℝ) + 1 + 1) / 2) ≤
        -9 * ((k : ℝ) + 2) := by nlinarith [sq_nonneg (k : ℝ)]
    calc
      f (k + 1) ≤ 24 * ((k : ℝ) + 1 + 3 / 4) ^ 2 *
          Real.exp (-6 * (((k : ℝ) + 1 + 1) ^ 2 - ((k : ℝ) + 1 + 1) / 2)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hterm (k + 1)
      _ ≤ 24 * (4 * (4 : ℝ) ^ k) * Real.exp (-9 * ((k : ℝ) + 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num))
          (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
      _ = C * r ^ k := by
        dsimp [C, r]
        rw [show -9 * ((k : ℝ) + 2) = -18 + (k : ℝ) * (-9) by ring,
          Real.exp_add, Real.exp_nat_mul, mul_pow]
        ring
  have hgeom := (summable_geometric_of_lt_one hr0 (by linarith : r < 1)).mul_left C
  have hsum : Summable (fun k => f (k + 1)) :=
    hgeom.of_nonneg_of_le (fun k => by dsimp [f]; positivity) hmajor
  have hfull : Summable f := (summable_nat_add_iff 1).mp hsum
  refine ⟨hfull, ?_⟩
  have hrest : (∑' k : ℕ, f (k + 1)) ≤ C / (1 - r) := by
    calc
      _ ≤ ∑' k : ℕ, C * r ^ k := hsum.tsum_le_tsum hmajor hgeom
      _ = C / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith : r < 1)]
        ring
  have hfirst : f 0 ≤ (27 / 2) * Real.exp (-3) := by
    have h := hterm 0
    norm_num only [Nat.cast_zero, zero_add] at h
    convert h using 1 <;> norm_num
  change (∑' k : ℕ, f k) ≤ _
  rw [← hfull.sum_add_tsum_nat_add 1, Finset.sum_range_one]
  dsimp [C, r] at hrest
  linarith

private def gaussianForceTerm (a u : ℝ) : ℝ := u * Real.exp (-a * u ^ 2)

private def gaussianSlope (a u : ℝ) : ℝ :=
  (2 * a * u ^ 2 - 1) * Real.exp (-a * u ^ 2)

/-- The signed Gaussian sum in the derivative of the periodized heat kernel. -/
def gaussianForce (a b : ℝ) : ℝ :=
  ∑' m : ℤ, (b - m) * Real.exp (-a * (b - m) ^ 2)

/-- A translated first Gaussian moment is summable, uniformly dominated by centered moments. -/
theorem summable_gaussian_force {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun m : ℤ => (b - m) * Real.exp (-a * (b - m) ^ 2)) := by
  apply Summable.of_norm
  convert HurwitzKernelBounds.summable_f_int 1 (-b) (div_pos ha Real.pi_pos) using 1
  ext m
  simp only [HurwitzKernelBounds.f_int, pow_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [show (m : ℝ) + -b = -(b - m) by ring, abs_neg, neg_sq]
  congr 2
  field_simp [Real.pi_ne_zero]
  <;> ring

private lemma forceTerm_hasDerivAt (a u : ℝ) :
    HasDerivAt (gaussianForceTerm a)
      ((1 - 2 * a * u ^ 2) * Real.exp (-a * u ^ 2)) u := by
  convert (hasDerivAt_id u).mul
    ((((hasDerivAt_id u).pow 2).const_mul (-a)).exp) using 1
  · funext x
    dsimp [gaussianForceTerm]
  · dsimp
    ring

private lemma slope_hasDerivAt (a u : ℝ) :
    HasDerivAt (gaussianSlope a)
      (2 * a * u * (3 - 2 * a * u ^ 2) * Real.exp (-a * u ^ 2)) u := by
  convert ((((hasDerivAt_id u).pow 2).const_mul (2 * a)).sub_const 1).mul
    ((((hasDerivAt_id u).pow 2).const_mul (-a)).exp) using 1
  · funext x
    dsimp [gaussianSlope]
  · dsimp
    ring

private lemma gaussianSlope_antitone {a : ℝ} (ha : 6 ≤ a) :
    AntitoneOn (gaussianSlope a) (Set.Ici (3 / 4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (by unfold gaussianSlope; fun_prop : Continuous (gaussianSlope a)).continuousOn
  · intro u _
    exact (slope_hasDerivAt a u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : (3 : ℝ) / 4 ≤ u := interior_subset hu
    have hu2 : (9 : ℝ) / 16 ≤ u ^ 2 := by nlinarith
    have hprod : 27 / 8 ≤ a * u ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ a - 6 by linarith) (sq_nonneg u)]
    rw [(slope_hasDerivAt a u).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

private lemma one_sub_exp_neg {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hp : 0 ≤ 1 - u / 2 := by linarith
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) hp
  have hpoly : 1 ≤ (1 - u / 2) * (u + 1) := by
    nlinarith [mul_nonneg hu (show 0 ≤ 1 - u by linarith)]
  have h := mul_le_mul_of_nonneg_right (hpoly.trans he) (Real.exp_pos (-u)).le
  have hid : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [one_mul, mul_assoc, hid, mul_one] at h
  linarith

/-- The first pair around one half has a uniform positive linear margin. -/
private theorem gaussian_pair_near_half {a b : ℝ} (ha : 6 ≤ a)
    (hb : 1 / 4 ≤ b) (hb' : b ≤ 1 / 2) :
    (1 / 2 - b) / 2 * Real.exp (-a / 4) ≤
      b * Real.exp (-a * b ^ 2) - (1 - b) * Real.exp (-a * (1 - b) ^ 2) := by
  let d := 1 / 2 - b
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hd' : d ≤ 1 / 4 := by dsimp [d]; linarith
  have hb0 : 0 ≤ b := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlinear : 1 - b ≤ b * (1 + 8 * d) := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ b - 1 / 4 by linarith)
      (show 0 ≤ 1 / 2 - b by linarith)]
  have hratio : 1 - b ≤ b * Real.exp (8 * d) :=
    hlinear.trans (mul_le_mul_of_nonneg_left (by
      simpa only [add_comm] using Real.add_one_le_exp (8 * d)) hb0)
  have htail : (1 - b) * Real.exp (-a * (1 - b) ^ 2) ≤
      b * Real.exp (-a * b ^ 2) * Real.exp (-4 * d) := by
    calc
      _ ≤ (b * Real.exp (8 * d)) * Real.exp (-a * (1 - b) ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
      _ = b * Real.exp (-a * b ^ 2) * Real.exp (-(2 * a - 8) * d) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        dsimp [d]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (show 0 ≤ a - 6 by linarith) hd]
  have hgap : 2 * d ≤ 1 - Real.exp (-4 * d) := by
    have h := one_sub_exp_neg (u := 4 * d) (by positivity) (by linarith)
    simpa only [show 4 * d / 2 = 2 * d by ring,
      show -(4 * d) = -4 * d by ring] using h
  have hexp : Real.exp (-a / 4) ≤ Real.exp (-a * b ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_nonneg ha0 (show 0 ≤ 1 / 4 - b ^ 2 by linarith)]
  have hmain := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ b * Real.exp (-a * b ^ 2) by positivity)
  have hmargin := mul_le_mul_of_nonneg_left hexp (show 0 ≤ d / 2 by positivity)
  have hcoeff : d / 2 * Real.exp (-a * b ^ 2) ≤
      b * Real.exp (-a * b ^ 2) * (2 * d) := by
    have h := mul_nonneg (show 0 ≤ b - 1 / 4 by linarith) hd
    nlinarith [mul_nonneg h (Real.exp_pos (-a * b ^ 2)).le]
  change d / 2 * Real.exp (-a / 4) ≤ _
  nlinarith [hmargin.trans hcoeff]

/-- For translations at most one quarter, each noncentral pair is bounded by the
corresponding summand of the normalized pairing tail. -/
private theorem gaussian_pair_near_zero {a b n : ℝ} (ha : 6 ≤ a)
    (hb : 0 ≤ b) (hb' : b ≤ 1 / 4) (hn : 1 ≤ n) :
    (n - b) * Real.exp (-a * (n - b) ^ 2) -
        (n + b) * Real.exp (-a * (n + b) ^ 2) ≤
      b * Real.exp (-a * b ^ 2) *
        (4 * a * (n - 1 / 4) ^ 2 * Real.exp (-a * (n ^ 2 - n / 2))) := by
  have ha0 : 0 ≤ a := by linarith
  have hbase : (3 : ℝ) / 4 ≤ n - 1 / 4 := by linarith
  have hd : ∀ u : ℝ, HasDerivAt (fun v => -gaussianForceTerm a v)
      (gaussianSlope a u) u := by
    intro u
    convert (forceTerm_hasDerivAt a u).neg using 1 <;> dsimp [gaussianSlope] <;> ring
  have hslope : ∀ u ∈ interior (Set.Icc (n - b) (n + b)),
      deriv (fun v => -gaussianForceTerm a v) u ≤ gaussianSlope a (n - 1 / 4) := by
    intro u hu
    have hu' : u ∈ Set.Icc (n - b) (n + b) := interior_subset hu
    rw [(hd u).deriv]
    have huBase : (3 : ℝ) / 4 ≤ u := by linarith [hu'.1]
    have horder : n - 1 / 4 ≤ u := by linarith [hu'.1]
    exact gaussianSlope_antitone ha hbase huBase horder
  have hm := (convex_Icc (n - b) (n + b)).image_sub_le_mul_sub_of_deriv_le
    (show ContinuousOn (fun v => -gaussianForceTerm a v) _ from
      (by unfold gaussianForceTerm
          fun_prop : Continuous (fun v => -gaussianForceTerm a v)).continuousOn)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt) hslope
    (n - b) (by constructor <;> linarith) (n + b)
      (by constructor <;> linarith)
    (by linarith)
  have hdrop : gaussianSlope a (n - 1 / 4) ≤
      2 * a * (n - 1 / 4) ^ 2 * Real.exp (-a * (n - 1 / 4) ^ 2) := by
    dsimp [gaussianSlope]
    nlinarith [Real.exp_pos (-a * (n - 1 / 4) ^ 2)]
  have hexp : Real.exp (-a * (n - 1 / 4) ^ 2) ≤
      Real.exp (-a * b ^ 2) * Real.exp (-a * (n ^ 2 - n / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb2 : b ^ 2 ≤ 1 / 16 := by nlinarith
    nlinarith [mul_nonneg ha0 (show 0 ≤ 1 / 16 - b ^ 2 by linarith)]
  have hprod := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ 4 * a * b * (n - 1 / 4) ^ 2 by positivity)
  have hm' := mul_le_mul_of_nonneg_right hdrop (show 0 ≤ 2 * b by positivity)
  dsimp [gaussianForceTerm] at hm
  nlinarith only [hm, hm', hprod]

private lemma natForce_summable {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun k : ℕ => gaussianForceTerm a ((k : ℝ) + b)) := by
  have hs := (summable_gaussian_force ha (-b)).neg.comp_injective
    (show Function.Injective (fun k : ℕ => (k : ℤ)) from Nat.cast_injective)
  convert hs using 1
  ext k
  dsimp [gaussianForceTerm]
  simp only [Int.cast_natCast]
  rw [show -b - (k : ℝ) = -((k : ℝ) + b) by ring, neg_sq]
  ring

private lemma forceTerm_antitone {a : ℝ} (ha : 6 ≤ a) :
    AntitoneOn (gaussianForceTerm a) (Set.Ici (3 / 4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (by unfold gaussianForceTerm; fun_prop : Continuous (gaussianForceTerm a)).continuousOn
  · intro u _
    exact (forceTerm_hasDerivAt a u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : (3 : ℝ) / 4 ≤ u := interior_subset hu
    have hu2 : (9 : ℝ) / 16 ≤ u ^ 2 := by nlinarith
    have hprod : 27 / 8 ≤ a * u ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ a - 6 by linarith) (sq_nonneg u)]
    rw [(forceTerm_hasDerivAt a u).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

private lemma gaussianForce_pair_zero {a : ℝ} (ha : 0 < a) (b : ℝ) :
    gaussianForce a b = b * Real.exp (-a * b ^ 2) -
      ∑' k : ℕ, (gaussianForceTerm a ((k : ℝ) + 1 - b) -
        gaussianForceTerm a ((k : ℝ) + 1 + b)) := by
  let f : ℤ → ℝ := fun m => (b - (m : ℝ)) * Real.exp (-a * (b - (m : ℝ)) ^ 2)
  have hf : Summable f := summable_gaussian_force ha b
  have h1 : Summable (fun k : ℕ => f ((k : ℤ) + 1)) :=
    hf.comp_injective (show Function.Injective (fun k : ℕ => (k : ℤ) + 1) from by
      intro i j h
      exact Int.ofNat_inj.mp (add_right_cancel h))
  have h2 : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) :=
    hf.comp_injective (show Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) from by
      intro i j h
      exact Int.ofNat_inj.mp (add_right_cancel (neg_injective h)))
  have hm : Summable (fun k : ℕ => gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
    have h := (summable_nat_add_iff 1).mpr (natForce_summable ha (-b))
    convert h using 1
    ext k
    simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg]
  have hp : Summable (fun k : ℕ => gaussianForceTerm a ((k : ℝ) + 1 + b)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (natForce_summable ha b)
  have he1 : (∑' k : ℕ, f ((k : ℤ) + 1)) =
      -(∑' k : ℕ, gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [f, gaussianForceTerm]
    push_cast
    rw [show b - ((k : ℝ) + 1) = -((k : ℝ) + 1 - b) by ring, neg_sq]
    ring
  have he2 : (∑' k : ℕ, f (-((k : ℤ) + 1))) =
      ∑' k : ℕ, gaussianForceTerm a ((k : ℝ) + 1 + b) := by
    apply tsum_congr
    intro k
    dsimp [f, gaussianForceTerm]
    push_cast
    rw [show b - -((k : ℝ) + 1) = (k : ℝ) + 1 + b by ring]
  change (∑' m : ℤ, f m) = _
  rw [tsum_of_add_one_of_neg_add_one (f := f) h1 h2, he1, he2, hm.tsum_sub hp]
  dsimp [f]
  simp only [Int.cast_zero, sub_zero]
  ring

/-- The full periodized Gaussian force has a positive margin on the first quarter. -/
private theorem gaussian_force_near_zero {a b : ℝ} (ha : 6 ≤ a)
    (hb : 0 ≤ b) (hb' : b ≤ 1 / 4) :
    3 / 10 * b * Real.exp (-a * b ^ 2) ≤ gaussianForce a b := by
  have ha0 : 0 < a := by linarith
  let f (k : ℕ) := gaussianForceTerm a ((k : ℝ) + 1 - b) -
    gaussianForceTerm a ((k : ℝ) + 1 + b)
  let c := b * Real.exp (-a * b ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn (k : ℕ) : 1 ≤ (k : ℝ) + 1 := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hnonneg (k : ℕ) : 0 ≤ f k := by
    have h := forceTerm_antitone ha
      (show (3 : ℝ) / 4 ≤ (k : ℝ) + 1 - b by
        have hk := Nat.cast_nonneg (α := ℝ) k
        linarith)
      (show (3 : ℝ) / 4 ≤ (k : ℝ) + 1 + b by
        have hk := Nat.cast_nonneg (α := ℝ) k
        linarith)
      (show (k : ℝ) + 1 - b ≤ (k : ℝ) + 1 + b by linarith)
    dsimp [f]
    linarith
  have hmajor (k : ℕ) : f k ≤ c *
      (4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
        Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))) := by
    dsimp [f, c, gaussianForceTerm]
    convert gaussian_pair_near_zero ha hb hb' (hn k) using 1 <;> ring
  have hs := (gaussian_pair_tail_bound ha).1.mul_left c
  have hf := hs.of_nonneg_of_le hnonneg hmajor
  have hle : (∑' k : ℕ, f k) ≤ c * gaussianPairTail a := by
    calc
      _ ≤ ∑' k : ℕ, c * (4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
          Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))) :=
        hf.tsum_le_tsum hmajor hs
      _ = _ := by rw [tsum_mul_left]; rfl
  have hcoarse : (27 / 2) * Real.exp (-3) +
      (96 * Real.exp (-18)) / (1 - 4 * Real.exp (-9)) < (7 : ℝ) / 10 := by
    have he9 : (8000 : ℝ) < Real.exp 9 := by
      have h := pow_lt_pow_left₀ exp_three (by norm_num : (0 : ℝ) ≤ 20)
        (by decide : (3 : ℕ) ≠ 0)
      rw [← Real.exp_nat_mul] at h
      convert h using 1 <;> norm_num
    have he18 : (64000000 : ℝ) < Real.exp 18 := by
      have h := pow_lt_pow_left₀ exp_three (by norm_num : (0 : ℝ) ≤ 20)
        (by decide : (6 : ℕ) ≠ 0)
      rw [← Real.exp_nat_mul] at h
      convert h using 1 <;> norm_num
    have h3 : Real.exp (-3) < (1 : ℝ) / 20 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact (div_lt_iff₀ (Real.exp_pos 3)).mpr (by linarith [exp_three])
    have h9 : 4 * Real.exp (-9) < (1 : ℝ) / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_lt_iff₀ (Real.exp_pos 9)).mpr (by linarith)
    have h18 : 2 * (96 * Real.exp (-18)) < (1 : ℝ) / 40 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, ← mul_div_assoc]
      exact (div_lt_iff₀ (Real.exp_pos 18)).mpr (by linarith)
    have hr : (96 * Real.exp (-18)) / (1 - 4 * Real.exp (-9)) ≤
        2 * (96 * Real.exp (-18)) := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - 4 * Real.exp (-9))).mpr
      nlinarith [mul_nonneg (by positivity : 0 ≤ 96 * Real.exp (-18))
        (show 0 ≤ 1 / 2 - 4 * Real.exp (-9) by linarith)]
    linarith
  have htail := mul_le_mul_of_nonneg_left
    ((gaussian_pair_tail_bound ha).2.trans_lt hcoarse).le hc
  rw [gaussianForce_pair_zero ha0 b]
  change 3 / 10 * b * Real.exp (-a * b ^ 2) ≤ c - ∑' k : ℕ, f k
  dsimp [c] at hle htail ⊢
  nlinarith

private lemma gaussianForce_pair_half {a : ℝ} (ha : 0 < a) (b : ℝ) :
    gaussianForce a b = ∑' k : ℕ, (gaussianForceTerm a ((k : ℝ) + b) -
      gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
  let f : ℤ → ℝ := fun m => gaussianForceTerm a ((m : ℝ) + b)
  have hf : Summable f := by
    convert (summable_gaussian_force ha b).comp_injective (Equiv.neg ℤ).injective using 1
    ext m
    dsimp [f, gaussianForceTerm]
    simp only [Equiv.neg_apply, Int.cast_neg]
    rw [show b - -(m : ℝ) = (m : ℝ) + b by ring]
  have h1 : Summable (fun k : ℕ => f (k : ℤ)) :=
    hf.comp_injective Nat.cast_injective
  have h2 : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) :=
    hf.comp_injective (show Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) from by
      intro i j h
      exact Int.ofNat_inj.mp (add_right_cancel (neg_injective h)))
  have hp := natForce_summable ha b
  have hm : Summable (fun k : ℕ => gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
    have h := (summable_nat_add_iff 1).mpr (natForce_summable ha (-b))
    convert h using 1
    ext k
    simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg]
  have he1 : (∑' k : ℕ, f (k : ℤ)) =
      ∑' k : ℕ, gaussianForceTerm a ((k : ℝ) + b) := by
    apply tsum_congr
    intro k
    simp only [f, Int.cast_natCast]
  have he2 : (∑' k : ℕ, f (-((k : ℤ) + 1))) =
      -(∑' k : ℕ, gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [f, gaussianForceTerm]
    push_cast
    rw [show -((k : ℝ) + 1) + b = -((k : ℝ) + 1 - b) by ring, neg_sq]
    ring
  calc
    gaussianForce a b = ∑' m : ℤ, f m := by
      rw [gaussianForce, ← (Equiv.neg ℤ).tsum_eq]
      apply tsum_congr
      intro m
      dsimp [f, gaussianForceTerm]
      simp only [Equiv.neg_apply, Int.cast_neg]
      rw [show b - -(m : ℝ) = (m : ℝ) + b by ring]
    _ = _ := by
      rw [tsum_of_nat_of_neg_add_one (f := f) h1 h2, he1, he2, hp.tsum_sub hm]
      ring

private theorem gaussian_force_near_half {a b : ℝ} (ha : 6 ≤ a)
    (hb : 1 / 4 ≤ b) (hb' : b ≤ 1 / 2) :
    (1 / 2 - b) / 2 * Real.exp (-a / 4) ≤ gaussianForce a b := by
  have ha0 : 0 < a := by linarith
  let f (k : ℕ) := gaussianForceTerm a ((k : ℝ) + b) -
    gaussianForceTerm a ((k : ℝ) + 1 - b)
  have hp := natForce_summable ha0 b
  have hm : Summable (fun k : ℕ => gaussianForceTerm a ((k : ℝ) + 1 - b)) := by
    convert (summable_nat_add_iff 1).mpr (natForce_summable ha0 (-b)) using 1
    ext k
    simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg]
  have hs : Summable f := hp.sub hm
  have hn (k : ℕ) : 0 ≤ f (k + 1) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have h := forceTerm_antitone ha
      (show (3 : ℝ) / 4 ≤ (k : ℝ) + 1 + b by linarith)
      (show (3 : ℝ) / 4 ≤ (k : ℝ) + 1 + 1 - b by linarith)
      (show (k : ℝ) + 1 + b ≤ (k : ℝ) + 1 + 1 - b by linarith)
    dsimp [f]
    push_cast
    linarith
  have ht : 0 ≤ ∑' k : ℕ, f (k + 1) := tsum_nonneg hn
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at he
  have hfirst : (1 / 2 - b) / 2 * Real.exp (-a / 4) ≤ f 0 := by
    simpa only [f, gaussianForceTerm, Nat.cast_zero, zero_add] using
      gaussian_pair_near_half ha hb hb'
  rw [gaussianForce_pair_half ha0 b]
  change _ ≤ ∑' k : ℕ, f k
  linarith

/-- The Gaussian representation supplies a sine-shaped nonnegative lower bound throughout
a closed half-period, including the difficult small-temperature regime. -/
theorem gaussian_force_lower {a b : ℝ} (ha : 6 ≤ a)
    (hb : 0 ≤ b) (hb' : b ≤ 1 / 2) :
    (3 / (20 * Real.pi)) * Real.exp (-a / 4) * Real.sin (2 * Real.pi * b) ≤
      gaussianForce a b := by
  have ha0 : 0 ≤ a := by linarith
  by_cases hquarter : b ≤ 1 / 4
  · have hsin := Real.sin_le (show 0 ≤ 2 * Real.pi * b by positivity)
    have hexp : Real.exp (-a / 4) ≤ Real.exp (-a * b ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [mul_nonneg ha0 (show 0 ≤ 1 / 4 - b ^ 2 by linarith)]
    calc
      _ ≤ (3 / (20 * Real.pi)) * Real.exp (-a / 4) * (2 * Real.pi * b) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = (3 / 10) * b * Real.exp (-a / 4) := by field_simp [Real.pi_ne_zero]; ring
      _ ≤ (3 / 10) * b * Real.exp (-a * b ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (3 / 10) * b * Real.exp (-a * b ^ 2) := by
        nlinarith [mul_nonneg hb (Real.exp_pos (-a * b ^ 2)).le]
      _ ≤ _ := gaussian_force_near_zero ha hb hquarter
  · let d := 1 / 2 - b
    have hd : 0 ≤ d := by dsimp [d]; linarith
    have hsin : Real.sin (2 * Real.pi * b) ≤ 2 * Real.pi * d := by
      rw [show 2 * Real.pi * b = Real.pi - 2 * Real.pi * d by dsimp [d]; ring,
        Real.sin_pi_sub]
      exact Real.sin_le (by positivity)
    calc
      _ ≤ (3 / (20 * Real.pi)) * Real.exp (-a / 4) * (2 * Real.pi * d) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = (3 * d / 10) * Real.exp (-a / 4) := by field_simp [Real.pi_ne_zero]; ring
      _ ≤ d / 2 * Real.exp (-a / 4) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ _ := gaussian_force_near_half ha (by linarith) hb'

end
end D5.S3.Fourier.PlanarTheta
