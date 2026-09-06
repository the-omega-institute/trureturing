/- GID: D5/S3/Zeros/PochhammerDeformation/QuadraticRadii
   generality: G
   mirror-B: D5/B/S3/Zeros/PochhammerDeformation/QuadraticRadii
   mirror-E: none(waiver:general-theorems-no-computational-artifact)
   anchors: []
   utility: none
   digest: The exact inner and outer quadratic root radii for the Pochhammer operator. -/

import D5.S3.Zeros.PochhammerDeformation.QuadraticInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.PochhammerDeformation.QuadraticRadii

open Polynomial
open QuadraticInterval

/-- The paper's degree-two class, with all transformed complex roots in [-1,0]. -/
def U2 (a : ℝ) : Set ℝ[X] :=
  {p | p.natDegree = 2 ∧ RealRootsInUnitInterval (lOp a p)}

/-- Norms of the complex zeros; the extremal definitions do not assume a formula. -/
def rootNorms (p : ℝ[X]) : Set ℝ :=
  {r | ∃ z : ℂ, aeval z p = 0 ∧ ‖z‖ = r}

def R2 (a : ℝ) : ℝ := sSup ((fun p => sSup (rootNorms p)) '' U2 a)

def r2 (a : ℝ) : ℝ := sSup ((fun p => sInf (rootNorms p)) '' U2 a)

/-- Monic inverse images, after multiplying the normalized image by a(a+1). -/
def normalQuadratic (a u v : ℝ) : ℝ[X] :=
  X ^ 2 + C ((a + 1) * (u + v) - 1) * X + C (a * (a + 1) * u * v)

private theorem quadratic_factors (A B c : ℂ) (hA : A ≠ 0) :
    ∃ z w : ℂ,
      (C A * X ^ 2 + C B * X + C c : ℂ[X]).roots = {z, w} ∧
      (C A * X ^ 2 + C B * X + C c : ℂ[X]) =
        C A * ((X - C z) * (X - C w)) := by
  let f : ℂ[X] := C A * X ^ 2 + C B * X + C c
  have hs := IsAlgClosed.splits f
  have hc : f.roots.card = 2 := by
    rw [← hs.natDegree_eq_card_roots]
    exact natDegree_quadratic hA
  obtain ⟨z, w, hzw⟩ := Multiset.card_eq_two.mp hc
  refine ⟨z, w, hzw, ?_⟩
  have hf := hs.eq_prod_roots
  simpa [f, hzw, leadingCoeff_quadratic hA] using hf

private theorem monic_quadratic_representation (p : ℝ[X]) (hp : p.natDegree = 2) :
    ∃ d b c : ℝ, d ≠ 0 ∧ p = C d * (X ^ 2 + C b * X + C c) := by
  have hd : p.coeff 2 ≠ 0 := by
    rw [← hp]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hp)
  refine ⟨p.coeff 2, p.coeff 1 / p.coeff 2, p.coeff 0 / p.coeff 2, hd, ?_⟩
  have he := p.as_sum_range_C_mul_X_pow
  rw [hp] at he
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one] at he
  conv_lhs => rw [he]
  simp only [mul_add, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hd]
  ring

private theorem lOp_monic_quadratic (a b c : ℝ) (ha : 0 < a) :
    lOp a (X ^ 2 + C b * X + C c) =
      C (a * (a + 1)) * X ^ 2 + C (a * (b + 1)) * X + C c := by
  have h0 : lOp a 1 = 1 := by
    simpa using lOp_definition a ha 0
  have h1 : lOp a (a⁻¹ • X) = X := by
    simpa [ascPochhammer_succ_right, descPochhammer_succ_right, smul_eq_C_mul]
      using lOp_definition a ha 1
  have hX : lOp a X = a • X := by
    have h := congrArg (fun q : ℝ[X] => a • q) h1
    simpa only [← map_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using h
  have hC : lOp a (C c) = C c := by
    have h := congrArg (fun q : ℝ[X] => c • q) h0
    simpa only [← map_smul, smul_eq_C_mul, mul_one] using h
  have hXX := lOp_quadratic a 0 ha
  simp only [C_0, add_zero, mul_zero, zero_add, mul_one, zero_pow (by decide : 2 ≠ 0)]
    at hXX
  have hbX : lOp a (C b * X) = b • (a • X) := by
    rw [← smul_eq_C_mul, map_smul, hX]
  rw [map_add, map_add, hXX, hbX, hC]
  simp only [smul_eq_C_mul, C_mul, C_add, C_1]
  ring

private theorem interval_C_mul (d : ℝ) (hd : d ≠ 0) (p : ℝ[X]) :
    RealRootsInUnitInterval (C d * p) ↔ RealRootsInUnitInterval p := by
  simp only [RealRootsInUnitInterval, Polynomial.map_mul, Polynomial.map_C,
    Complex.coe_algebraMap, roots_C_mul _ (show (d : ℂ) ≠ 0 by exact_mod_cast hd)]

private theorem normal_image (a u v : ℝ) (ha : 0 < a) :
    lOp a (normalQuadratic a u v) =
      C (a * (a + 1)) * ((X + C u) * (X + C v)) := by
  rw [normalQuadratic, lOp_monic_quadratic a _ _ ha]
  simp only [C_sub, C_add, C_mul, C_1]
  ring

private theorem normal_mem (a u v : ℝ) (ha : 0 < a)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    normalQuadratic a u v ∈ U2 a := by
  constructor
  · simpa [normalQuadratic] using
      (natDegree_quadratic (b := (a + 1) * (u + v) - 1)
        (c := a * (a + 1) * u * v) (by norm_num : (1 : ℝ) ≠ 0))
  · rw [normal_image a u v ha, interval_C_mul _ (by positivity)]
    intro z hz
    have hp : (((X + C u) * (X + C v) : ℝ[X]).map (algebraMap ℝ ℂ)) ≠ 0 := by
      simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_C]
      exact mul_ne_zero (monic_X_add_C _).ne_zero (monic_X_add_C _).ne_zero
    have he := (mem_roots hp).mp hz
    simp only [IsRoot, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, eval_mul, eval_add, eval_X, eval_C, mul_eq_zero,
      add_eq_zero_iff_eq_neg] at he
    rcases he with rfl | rfl <;> simp only [Complex.coe_algebraMap,
      Complex.neg_im, Complex.ofReal_im,
      neg_zero, Complex.neg_re, Complex.ofReal_re, Set.mem_Icc, true_and] <;>
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- The parameter square describes the entire paper class up to nonzero scalars. -/
theorem quadratic_normal_form (a : ℝ) (ha : 0 < a) (p : ℝ[X]) :
    p ∈ U2 a ↔ ∃ d u v : ℝ, d ≠ 0 ∧ u ∈ Set.Icc 0 1 ∧
      v ∈ Set.Icc 0 1 ∧ p = C d * normalQuadratic a u v := by
  constructor
  · rintro ⟨hp, hr⟩
    obtain ⟨d, b, c, hd, rfl⟩ := monic_quadratic_representation p hp
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, interval_C_mul d hd] at hr
    rw [lOp_monic_quadratic a b c ha] at hr
    have hA : (a * (a + 1) : ℝ) ≠ 0 := by positivity
    obtain ⟨z, w, hzw, hf⟩ := quadratic_factors (↑(a * (a + 1)) : ℂ)
      (↑(a * (b + 1)) : ℂ) c
      (by exact_mod_cast hA)
    have hmap : (C (a * (a + 1)) * X ^ 2 + C (a * (b + 1)) * X + C c : ℝ[X]).map
        (algebraMap ℝ ℂ) =
        C (↑(a * (a + 1)) : ℂ) * X ^ 2 + C (↑(a * (b + 1)) : ℂ) * X + C (c : ℂ) := by
      simp
    have hz := hr z (by rw [hmap, hzw]; simp)
    have hw := hr w (by rw [hmap, hzw]; simp)
    have hzR : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hz.1)
    have hwR : w = (w.re : ℂ) := Complex.ext (by simp) (by simpa using hw.1)
    rw [hzR, hwR] at hf
    have hb := congrArg (fun f : ℂ[X] => f.coeff 1) hf
    have hc := congrArg (fun f : ℂ[X] => f.coeff 0) hf
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, mul_sub, sub_mul,
      coeff_sub, coeff_mul_X, coeff_mul_C, coeff_X] at hb hc
    norm_num at hb hc
    have hbR : a * (b + 1) = -(a * (a + 1) * z.re) - a * (a + 1) * w.re := by
      exact_mod_cast hb
    have hcR : c = a * (a + 1) * (z.re * w.re) := by exact_mod_cast hc
    have hb' : b = (a + 1) * (-z.re + -w.re) - 1 := by
      have hh : a * (b + 1) = a * ((a + 1) * (-z.re + -w.re)) := by
        nlinarith [hbR]
      have := mul_left_cancel₀ ha.ne' hh
      linarith
    refine ⟨d, -z.re, -w.re, hd, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩,
      ⟨by linarith [hw.2.2], by linarith [hw.2.1]⟩, ?_⟩
    have hc' : c = a * (a + 1) * (-z.re) * (-w.re) := by nlinarith [hcR]
    simp only [normalQuadratic, ← hb', ← hc']
  · rintro ⟨d, u, v, hd, hu, hv, rfl⟩
    have hn := normal_mem a u v ha hu hv
    constructor
    · rw [natDegree_C_mul hd]
      exact hn.1
    · rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, interval_C_mul d hd]
      exact hn.2

private theorem aeval_normal (a u v : ℝ) (z : ℂ) :
    aeval z (normalQuadratic a u v) = z ^ 2 +
      (↑((a + 1) * (u + v) - 1) : ℂ) * z + ↑(a * (a + 1) * u * v) := by
  simp [normalQuadratic]

private theorem quadratic_pair (b c : ℝ) : ∃ z w : ℂ,
    z ^ 2 + (b : ℂ) * z + c = 0 ∧ w ^ 2 + (b : ℂ) * w + c = 0 ∧ z * w = c := by
  obtain ⟨z, w, _, hf⟩ := quadratic_factors 1 b c one_ne_zero
  refine ⟨z, w, ?_, ?_, ?_⟩
  · have h := congrArg (fun p : ℂ[X] => p.eval z) hf
    simpa using h
  · have h := congrArg (fun p : ℂ[X] => p.eval w) hf
    simpa using h
  · have h := congrArg (fun p : ℂ[X] => p.coeff 0) hf
    simpa using h.symm

/-- Uniform outer bound, including both real and nonreal zeros. -/
theorem normal_outer_bound (a u v : ℝ) (ha : 0 < a)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (z : ℂ) (hz : aeval z (normalQuadratic a u v) = 0) : ‖z‖ ≤ a + 1 := by
  have hu0 := hu.1
  have hu1 := hu.2
  have hv0 := hv.1
  have hv1 := hv.2
  let b := (a + 1) * (u + v) - 1
  let c := a * (a + 1) * u * v
  have hb0 : -1 ≤ b := by
    dsimp [b]
    nlinarith [mul_nonneg (show 0 ≤ a + 1 by linarith) (add_nonneg hu.1 hv.1)]
  have hb1 : b ≤ 2 * a + 1 := by
    dsimp [b]
    nlinarith [mul_nonneg (by linarith : 0 ≤ a + 1)
      (show 0 ≤ 2 - (u + v) by linarith [hu.2, hv.2])]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have huv : u * v ≤ 1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hv.2)]
  have hc1 : c ≤ a * (a + 1) := by
    have := mul_le_mul_of_nonneg_left huv (show 0 ≤ a * (a + 1) by positivity)
    dsimp [c]
    nlinarith
  have hend : 0 ≤ (a + 1) ^ 2 - b * (a + 1) + c := by
    have h := mul_nonneg (show 0 ≤ a * (a + 1) by positivity)
      (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2))
    dsimp [b, c] at *
    nlinarith
  rw [aeval_normal] at hz
  change z ^ 2 + (b : ℂ) * z + c = 0 at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] at hre
  simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  have hcases : z.im = 0 ∨ 2 * z.re + b = 0 := by
    apply mul_eq_zero.mp
    nlinarith [him]
  rcases hcases with hreal | hnonreal
  · have hx : z.re ^ 2 + b * z.re + c = 0 := by nlinarith [hre]
    have hl : -(a + 1) ≤ z.re := by
      by_contra! h
      have hmul := mul_pos_of_neg_of_neg
        (show b - 2 * (a + 1) < 0 by linarith)
        (show z.re + (a + 1) < 0 by linarith)
      nlinarith [sq_nonneg (z.re + (a + 1))]
    have hr : z.re ≤ a + 1 := by
      by_contra! h
      have hmul := mul_nonneg (show 0 ≤ b + 1 by linarith)
        (show 0 ≤ z.re by linarith)
      have hpos := mul_pos (show 0 < z.re by linarith)
        (show 0 < z.re - 1 by linarith)
      nlinarith
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hreal)
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨hl, hr⟩
  · have hnorm : ‖z‖ ^ 2 = c := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hh := congrArg (fun x : ℝ => x * z.re) hnonreal
      nlinarith [hre]
    nlinarith [norm_nonneg z]

/-- At least one zero has norm at most the sharp inner radius. -/
theorem normal_inner_bound (a u v : ℝ) (ha : 0 < a)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    ∃ z : ℂ, aeval z (normalQuadratic a u v) = 0 ∧
      ‖z‖ ≤ (a + Real.sqrt (a * (a + 1))) / 2 := by
  have hu0 := hu.1
  have hu1 := hu.2
  have hv0 := hv.1
  have hv1 := hv.2
  let s := Real.sqrt (a * (a + 1))
  let M := (a + s) / 2
  let b := (a + 1) * (u + v) - 1
  let c := a * (a + 1) * u * v
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a * (a + 1) := Real.sq_sqrt (by positivity)
  have hsa : a < s := by nlinarith
  have hsa1 : s < a + 1 := by nlinarith
  have hM0 : 0 < M := by dsimp [M]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  by_cases hc : c ≤ M ^ 2
  · obtain ⟨z, w, hz, hw, hprod⟩ := quadratic_pair b c
    have hn : ‖z‖ * ‖w‖ = c := by
      have h := congrArg norm hprod
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0] using h
    have hsmall : ‖z‖ ≤ M ∨ ‖w‖ ≤ M := by
      by_contra! h
      have := mul_lt_mul h.1 h.2.le hM0 (norm_nonneg z)
      nlinarith
    rcases hsmall with hzM | hwM
    · exact ⟨z, by simpa only [aeval_normal] using hz, hzM⟩
    · exact ⟨w, by simpa only [aeval_normal] using hw, hwM⟩
  · let t := Real.sqrt (u * v)
    let q := s * t
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have ht2 : t ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu.1 hv.1)
    have huv : u * v ≤ 1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hv.2)]
    have ht1 : t ≤ 1 := by nlinarith
    have ham : 2 * t ≤ u + v := by nlinarith [sq_nonneg (u - v)]
    have hq0 : 0 ≤ q := mul_nonneg hs0 ht0
    have hq2 : q ^ 2 = c := by dsimp [q, c]; nlinarith [sq_nonneg s, sq_nonneg t]
    have hqM : M < q := by nlinarith
    have hq1 : q < M + 1 := by
      have hqs : q ≤ s := by dsimp [q]; nlinarith [mul_nonneg hs0 (sub_nonneg.mpr ht1)]
      dsimp [M]
      linarith
    have hidentity : 2 * M * (a + 1) = s * (2 * M + 1) := by
      dsimp [M]
      nlinarith
    have hscaled : (2 * M + 1) * q ≤ M * (a + 1) * (u + v) := by
      have h := mul_le_mul_of_nonneg_left ham
        (show 0 ≤ M * (a + 1) by positivity)
      have hid := congrArg (fun x : ℝ => x * t) hidentity
      dsimp [q]
      nlinarith
    have hneg : (normalQuadratic a u v).eval (-M) < 0 := by
      have hproduct := mul_neg_of_pos_of_neg (sub_pos.mpr hqM)
        (show q - M - 1 < 0 by linarith)
      simp only [normalQuadratic, eval_add, eval_pow, eval_X, eval_mul, eval_C]
      change (-M) ^ 2 + b * (-M) + c < 0
      dsimp [b] at *
      nlinarith
    have hzero : 0 ≤ (normalQuadratic a u v).eval 0 := by
      simpa [normalQuadratic] using hc0
    obtain ⟨x, hx, hroot⟩ := intermediate_value_Icc
      (show -M ≤ (0 : ℝ) by linarith)
      (normalQuadratic a u v).continuous.continuousOn ⟨hneg.le, hzero⟩
    refine ⟨(x : ℂ), ?_, ?_⟩
    · rw [aeval_normal]
      have he : x ^ 2 + b * x + c = 0 := by simpa [normalQuadratic, b, c] using hroot
      exact_mod_cast he
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx.2]
      exact neg_le.mp hx.1

/-- The outer extremum is attained at the corner u=v=1. -/
theorem quadratic_outer_witness (a : ℝ) (ha : 0 < a) :
    normalQuadratic a 1 1 ∈ U2 a ∧
      normalQuadratic a 1 1 = (X + C a) * (X + C (a + 1)) := by
  refine ⟨normal_mem a 1 1 ha ⟨by norm_num, le_rfl⟩ ⟨by norm_num, le_rfl⟩, ?_⟩
  simp only [normalQuadratic, C_add, C_sub, C_mul, C_1, C_ofNat]
  ring

/-- The repeated-root witness is precisely the frozen interval's right endpoint. -/
theorem quadratic_inner_witness (a : ℝ) (ha : 0 < a) :
    let s := Real.sqrt (a * (a + 1))
    let M := (a + s) / 2
    a + c2 a = M ∧ M / s ∈ Set.Icc 0 1 ∧
      normalQuadratic a (M / s) (M / s) = (X + C M) ^ 2 ∧
      (X + C M) ^ 2 ∈ U2 a := by
  dsimp only
  let s := Real.sqrt (a * (a + 1))
  let M := (a + s) / 2
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = a * (a + 1) := Real.sq_sqrt (by positivity)
  have hsa : a < s := by nlinarith
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hMs : M ≤ s := by dsimp [M]; linarith
  have hs_alt : Real.sqrt (a ^ 2 + a) = s := by congr 1; ring
  have hfrozen := quadratic_interval_closed_form a ha
  have hc : a + c2 a = M := by rw [hfrozen.2.1, hs_alt]; dsimp [M]; ring
  refine ⟨hc, ⟨div_nonneg hM0.le hs0.le, (div_le_one hs0).mpr hMs⟩, ?_, ?_⟩
  · change normalQuadratic a (M / s) (M / s) = (X + C M) ^ 2
    have hlin : (a + 1) * (M / s + M / s) - 1 = 2 * M := by
      field_simp
      dsimp [M]
      nlinarith
    have hconst : a * (a + 1) * (M / s) * (M / s) = M ^ 2 := by
      rw [← hs2]
      field_simp
      <;> ring
    rw [normalQuadratic, hlin, hconst]
    simp only [C_mul, C_pow, C_ofNat]
    ring
  · constructor
    · simp
    · change M ∈ m2 a
      rw [hfrozen.1, hs_alt]
      constructor
      · dsimp [M]; linarith [hs0]
      · exact le_rfl

private theorem aeval_C_mul_iff (d : ℝ) (hd : d ≠ 0) (p : ℝ[X]) (z : ℂ) :
    aeval z (C d * p) = 0 ↔ aeval z p = 0 := by
  simp only [map_mul, aeval_C, Complex.coe_algebraMap, mul_eq_zero,
    show (d : ℂ) ≠ 0 by exact_mod_cast hd, false_or]

private theorem class_outer_bound (a : ℝ) (ha : 0 < a) (p : ℝ[X]) (hp : p ∈ U2 a)
    (z : ℂ) (hz : aeval z p = 0) : ‖z‖ ≤ a + 1 := by
  obtain ⟨d, u, v, hd, hu, hv, rfl⟩ := (quadratic_normal_form a ha p).mp hp
  exact normal_outer_bound a u v ha hu hv z ((aeval_C_mul_iff d hd _ z).mp hz)

private theorem class_inner_bound (a : ℝ) (ha : 0 < a) (p : ℝ[X]) (hp : p ∈ U2 a) :
    ∃ z : ℂ, aeval z p = 0 ∧ ‖z‖ ≤ (a + Real.sqrt (a * (a + 1))) / 2 := by
  obtain ⟨d, u, v, hd, hu, hv, rfl⟩ := (quadratic_normal_form a ha p).mp hp
  obtain ⟨z, hz, hn⟩ := normal_inner_bound a u v ha hu hv
  exact ⟨z, (aeval_C_mul_iff d hd _ z).mpr hz, hn⟩

private theorem rootNorms_bddBelow (p : ℝ[X]) : BddBelow (rootNorms p) := by
  refine ⟨0, ?_⟩
  rintro r ⟨z, _, rfl⟩
  exact norm_nonneg z

private theorem class_rootNorms_nonempty (a : ℝ) (ha : 0 < a) (p : ℝ[X])
    (hp : p ∈ U2 a) : (rootNorms p).Nonempty := by
  obtain ⟨z, hz, _⟩ := class_inner_bound a ha p hp
  exact ⟨‖z‖, z, hz, rfl⟩

private theorem class_sup_bound (a : ℝ) (ha : 0 < a) (p : ℝ[X]) (hp : p ∈ U2 a) :
    sSup (rootNorms p) ≤ a + 1 := by
  apply csSup_le (class_rootNorms_nonempty a ha p hp)
  rintro r ⟨z, hz, rfl⟩
  exact class_outer_bound a ha p hp z hz

private theorem rootNorms_square (t : ℝ) : rootNorms ((X + C t) ^ 2) = {|t|} := by
  ext r
  simp only [rootNorms, Set.mem_setOf_eq, Set.mem_singleton_iff, map_pow, map_add,
    aeval_X, aeval_C, Complex.coe_algebraMap, sq_eq_zero_iff, add_eq_zero_iff_eq_neg,
    exists_eq_left, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  exact eq_comm

/-- Open Problem 7.2 for n=2: the supremum of the largest root norms is a+1. -/
theorem quadratic_outer_radius (a : ℝ) (ha : 0 < a) : R2 a = a + 1 := by
  have hw := quadratic_outer_witness a ha
  have hb : BddAbove (rootNorms (normalQuadratic a 1 1)) := by
    refine ⟨a + 1, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact class_outer_bound a ha _ hw.1 z hz
  have hr : a + 1 ∈ rootNorms (normalQuadratic a 1 1) := by
    refine ⟨(-(a + 1) : ℂ), ?_, ?_⟩
    · rw [hw.2]
      simp
    · rw [norm_neg, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < a + 1)]
  have he : sSup (rootNorms (normalQuadratic a 1 1)) = a + 1 :=
    le_antisymm (class_sup_bound a ha _ hw.1) (le_csSup hb hr)
  have hg : IsGreatest ((fun p => sSup (rootNorms p)) '' U2 a) (a + 1) := by
    refine ⟨⟨normalQuadratic a 1 1, hw.1, he⟩, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    exact class_sup_bound a ha p hp
  exact hg.isLUB.csSup_eq ⟨a + 1, hg.1⟩

/-- Open Problem 7.1 for n=2: the published lower bound is the exact supremum. -/
theorem quadratic_inner_radius (a : ℝ) (ha : 0 < a) :
    r2 a = (a + Real.sqrt (a * (a + 1))) / 2 := by
  let M := (a + Real.sqrt (a * (a + 1))) / 2
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hw : (X + C M) ^ 2 ∈ U2 a := (quadratic_inner_witness a ha).2.2.2
  have he : sInf (rootNorms ((X + C M) ^ 2)) = M := by
    rw [rootNorms_square, csInf_singleton, abs_of_nonneg hM0]
  have hg : IsGreatest ((fun p => sInf (rootNorms p)) '' U2 a) M := by
    refine ⟨⟨(X + C M) ^ 2, hw, he⟩, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    obtain ⟨z, hz, hn⟩ := class_inner_bound a ha p hp
    exact (csInf_le (rootNorms_bddBelow p) ⟨z, hz, rfl⟩).trans hn
  exact hg.isLUB.csSup_eq ⟨M, hg.1⟩

#print axioms quadratic_normal_form
#print axioms quadratic_outer_radius
#print axioms quadratic_inner_radius

end D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
