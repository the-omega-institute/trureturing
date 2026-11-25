/- GID: D5/S3/Weil/MollifiedDyadicMeanSquare
   generality: I
   mirror-B: D5/B/S3/Weil/MollifiedDyadicMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform dyadic mean square for the actual Möbius-mollified zeta function. -/

import D5.S3.Analytic.Asymptotics.DirichletPolynomialMeanSquare
import D5.S3.Weil.MollifiedZetaPolynomial
import D5.S3.Weil.ZetaTruncationMeanSquare

/-! # The mollified zeta mean square on the padded dyadic band -/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius

namespace D5.S3.Weil.MollifiedDyadicMeanSquare

open ZetaTruncationMeanSquare (paddedBand vertical)
open ZetaPntBounds.MollifiedZetaPolynomial
  (coeff dirichletPolynomial mollifier tailPolynomial zetaPartialSum)

noncomputable section

private theorem paddedBand_eq_union {T : ℝ} (hT : 2 ≤ T) :
    paddedBand T = Set.Icc (-(2 * T + 1)) (-(T - 1)) ∪
      Set.Icc (T - 1) (2 * T + 1) := by
  ext t
  change (T - 1 ≤ |t| ∧ |t| ≤ 2 * T + 1) ↔
    (-(2 * T + 1) ≤ t ∧ t ≤ -(T - 1)) ∨ (T - 1 ≤ t ∧ t ≤ 2 * T + 1)
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exfalso
        linarith [h.2]
      · exact h
  · rw [abs_of_neg (lt_of_not_ge ht)]
    constructor
    · intro h
      exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
    · rintro (h | h)
      · exact ⟨by linarith [h.2], by linarith [h.1]⟩
      · exfalso
        linarith [h.1]

private theorem integral_paddedBand_eq {T : ℝ} (hT : 2 ≤ T) {f : ℝ → ℝ}
    (hf : IntegrableOn f (paddedBand T)) :
    (∫ t in paddedBand T, f t) =
      (∫ t in (-(2 * T + 1))..(-(T - 1)), f t) +
      (∫ t in (T - 1)..(2 * T + 1), f t) := by
  have hneg : -(2 * T + 1) ≤ -(T - 1) := by linarith
  have hpos : T - 1 ≤ 2 * T + 1 := by linarith
  have hdisj : Disjoint (Set.Icc (-(2 * T + 1)) (-(T - 1)))
      (Set.Icc (T - 1) (2 * T + 1)) := by
    refine Set.disjoint_left.mpr fun t htneg htpos => ?_
    linarith [htneg.2, htpos.1]
  rw [paddedBand_eq_union hT, integrableOn_union] at hf
  rw [paddedBand_eq_union hT, setIntegral_union hdisj measurableSet_Icc hf.1 hf.2]
  simp only [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hneg,
    intervalIntegral.integral_of_le hpos]

private theorem vertical_ne_one {T u t : ℝ} (hT : 2 ≤ T) (ht : t ∈ paddedBand T) :
    vertical u t ≠ 1 := by
  intro hs
  have hz : t = 0 := by
    simpa [vertical, Complex.add_im, Complex.mul_im] using congrArg Complex.im hs
  have h : T - 1 ≤ |t| := ht.1
  rw [hz, abs_zero] at h
  linarith

private theorem integrableOn_mollified {T u : ℝ} (hT : 2 ≤ T) (X : ℕ) :
    IntegrableOn (fun t => ‖riemannZeta (vertical u t) * mollifier X (vertical u t) - 1‖ ^ 2)
      (paddedBand T) := by
  have hz : Continuous (vertical u) := by unfold vertical; fun_prop
  have hζ : ContinuousOn (fun t => riemannZeta (vertical u t)) (paddedBand T) := by
    intro t ht
    exact ((differentiableAt_riemannZeta (vertical_ne_one hT ht)).continuousAt.comp
      hz.continuousAt).continuousWithinAt
  have hM : Continuous (mollifier X) := by
    unfold mollifier dirichletPolynomial
    apply continuous_finsetSum
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Icc.mp hn).1
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    exact continuous_const.div (continuous_const_cpow' hnC)
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
  have hCompact : IsCompact (paddedBand T) := by
    rw [paddedBand_eq_union hT]
    exact isCompact_Icc.union isCompact_Icc
  exact (((hζ.mul (hM.comp hz).continuousOn).sub continuousOn_const).norm.pow
    2).integrableOn_compact hCompact

private theorem zetaPartialSum_eq_polynomial (N : ℕ) (s : ℂ) :
    zetaPartialSum N s = ZetaTruncationMeanSquare.polynomial N s := rfl

private def tailCoeff (N X n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc X (N * X) then (coeff N X n : ℂ) else 0

private theorem tailPolynomial_eq_sum {N X : ℕ} (hX : 1 ≤ X) (s : ℂ) :
    tailPolynomial N X s =
      ∑ n ∈ Finset.Icc 1 (N * X), tailCoeff N X n * (n : ℂ) ^ (-s) := by
  unfold tailPolynomial dirichletPolynomial
  have hsub : Finset.Ioc X (N * X) ⊆ Finset.Icc 1 (N * X) := by
    intro n hn
    obtain ⟨hnX, hnL⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨hX.trans hnX.le, hnL⟩
  calc
    _ = ∑ n ∈ Finset.Ioc X (N * X), tailCoeff N X n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [tailCoeff, if_pos hn, Complex.cpow_neg, div_eq_mul_inv]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro n _ hn
      simp [tailCoeff, hn]

private theorem tail_interval_mean_square {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N)
    {A B a u d C : ℝ} (hAB : A ≤ B) (hau : a ≤ u)
    (hd : 0 < d) (hd' : d < 1 / 2) (hd_def : d = a - 1 / 2) (hC : 0 ≤ C)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → ‖(coeff N X n : ℂ)‖ ≤ C * (n : ℝ) ^ (d / 2)) :
    (∫ t in A..B, ‖tailPolynomial N X (vertical u t)‖ ^ 2) ≤
      C ^ 2 * ((B - A) * ((X : ℝ) ^ (-d) / d) +
        12 * Real.log (2 * ((N * X : ℕ) : ℝ)) *
          (((N * X : ℕ) : ℝ) ^ (1 - d) / (1 - d))) := by
  have hL : 1 ≤ N * X := Nat.mul_pos (hX.trans hXN) hX
  have hzero : ∀ n ∈ Finset.Icc 1 X, tailCoeff N X n = 0 := by
    intro n hn
    have hnot : n ∉ Finset.Ioc X (N * X) := fun h =>
      (not_lt_of_ge (Finset.mem_Icc.mp hn).2) (Finset.mem_Ioc.mp h).1
    simp [tailCoeff, hnot]
  have hbound : ∀ n ∈ Finset.Icc 1 (N * X), ‖tailCoeff N X n‖ ≤ C * (n : ℝ) ^ (d / 2) := by
    intro n hn
    by_cases h : n ∈ Finset.Ioc X (N * X)
    · simpa only [tailCoeff, if_pos h] using hcoeff n (ne_of_gt (Finset.mem_Icc.mp hn).1)
    · rw [tailCoeff, if_neg h, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h := DirichletPolynomialMeanSquare.vertical_mean_square_le hL hX hAB hau hC
    hd (by linarith : d < 1) (by linarith : d = 2 * (a - d / 2) - 1)
    (tailCoeff N X) hzero hbound
  simpa only [tailPolynomial_eq_sum hX, vertical] using h

private theorem dyadic_cutoff_bounds {d T : ℝ} (hd : 0 < d) (hd' : d < 1 / 2) (hT : 2 ≤ T) :
    let N : ℕ := ⌈T⌉₊
    let X : ℕ := ⌊T ^ (d / 4)⌋₊
    1 ≤ X ∧ X ≤ N ∧ T ^ (d / 4) / 2 ≤ (X : ℝ) ∧ (X : ℝ) ≤ T ^ (d / 4) ∧
      ((N * X : ℕ) : ℝ) ≤ 2 * T ^ (1 + d / 4) := by
  let N : ℕ := ⌈T⌉₊
  let X : ℕ := ⌊T ^ (d / 4)⌋₊
  change 1 ≤ X ∧ X ≤ N ∧ T ^ (d / 4) / 2 ≤ (X : ℝ) ∧ (X : ℝ) ≤ T ^ (d / 4) ∧
    ((N * X : ℕ) : ℝ) ≤ 2 * T ^ (1 + d / 4)
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ d / 4 := by linarith
  have hpow1 : 1 ≤ T ^ (d / 4) := Real.one_le_rpow hT1 hδ
  have hX : 1 ≤ X := (Nat.one_le_floor_iff _).mpr hpow1
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXupper : (X : ℝ) ≤ T ^ (d / 4) := Nat.floor_le (by positivity)
  have hXlower : T ^ (d / 4) / 2 ≤ (X : ℝ) := by
    have hfloor : T ^ (d / 4) < (X : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hpowT : T ^ (d / 4) ≤ T := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : d / 4 ≤ (1 : ℝ)))
  have hXN : X ≤ N := by
    exact_mod_cast hXupper.trans (hpowT.trans (Nat.le_ceil T))
  have hNupper : (N : ℝ) ≤ 2 * T := by
    have hceil : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    linarith
  refine ⟨hX, hXN, hXlower, hXupper, ?_⟩
  rw [Nat.cast_mul, Real.rpow_add hT0, Real.rpow_one]
  calc
    (N : ℝ) * (X : ℝ) ≤ (2 * T) * T ^ (d / 4) :=
      mul_le_mul hNupper hXupper (Nat.cast_nonneg X) (by positivity)
    _ = _ := by ring

private def tailBoundConstant (d : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ d / d +
    12 * (Real.log 4 + (1 + d / 4) / (d / 4)) * ((2 : ℝ) ^ (1 - d) / (1 - d))

private theorem tailBoundConstant_nonneg {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 2) :
    0 ≤ tailBoundConstant d := by
  have hden : 0 < 1 - d := by linarith
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold tailBoundConstant
  positivity

private theorem dyadic_tail_weights_le {d T len : ℝ} {X L : ℕ}
    (hd : 0 < d) (hd' : d < 1 / 2) (hT : 2 ≤ T) (hL : 1 ≤ L)
    (hXlower : T ^ (d / 4) / 2 ≤ (X : ℝ)) (hLupper : (L : ℝ) ≤ 2 * T ^ (1 + d / 4))
    (hlen : len ≤ 2 * T) :
    len * ((X : ℝ) ^ (-d) / d) +
        12 * Real.log (2 * (L : ℝ)) * ((L : ℝ) ^ (1 - d) / (1 - d)) ≤
      tailBoundConstant d * T ^ (1 - (d / 4) * d) := by
  let δ : ℝ := d / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; linarith
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hden : 0 < 1 - d := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : 0 < (L : ℝ) := zero_lt_one.trans_le hL1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hδpow : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hXpow : (X : ℝ) ^ (-d) ≤ (2 : ℝ) ^ d * T ^ (-(δ * d)) := calc
    _ ≤ (T ^ δ / 2) ^ (-d) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hXlower (neg_nonpos.mpr hd.le)
    _ = _ := by
      rw [Real.div_rpow (Real.rpow_nonneg hT0.le _) (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul hT0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm, mul_neg]
  have hdiag :
      len * ((X : ℝ) ^ (-d) / d) ≤
        (2 * (2 : ℝ) ^ d / d) * T ^ (1 - δ * d) := calc
    _ ≤ (2 * T) * ((X : ℝ) ^ (-d) / d) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    _ ≤ (2 * T) * (((2 : ℝ) ^ d * T ^ (-(δ * d))) / d) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hXpow hd.le) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg (1 : ℝ), Real.rpow_add hT0, Real.rpow_one]
      ring
  have hlogT : Real.log T ≤ T ^ δ / δ := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hT0 δ)
    rw [Real.log_rpow hT0] at h
    apply (le_div_iff₀ hδ).mpr
    rw [mul_comm]
    linarith only [h]
  have hlogL : Real.log (2 * (L : ℝ)) ≤ (Real.log 4 + (1 + δ) / δ) * T ^ δ := calc
    _ ≤ Real.log (4 * T ^ (1 + δ)) := by
      apply Real.log_le_log (by positivity)
      calc
        2 * (L : ℝ) ≤ 2 * (2 * T ^ (1 + δ)) :=
          mul_le_mul_of_nonneg_left hLupper (by norm_num)
        _ = _ := by ring
    _ = Real.log 4 + (1 + δ) * Real.log T := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos hT0 (1 + δ)).ne', Real.log_rpow hT0]
    _ ≤ Real.log 4 * T ^ δ + (1 + δ) * (T ^ δ / δ) := by
      exact add_le_add
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hδpow hlog4)
        (mul_le_mul_of_nonneg_left hlogT (by positivity))
    _ = _ := by ring
  have hLpow : (L : ℝ) ^ (1 - d) ≤ (2 : ℝ) ^ (1 - d) * T ^ ((1 + δ) * (1 - d)) := calc
    _ ≤ (2 * T ^ (1 + δ)) ^ (1 - d) := Real.rpow_le_rpow hL0.le hLupper hden.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hT0.le _),
        ← Real.rpow_mul hT0.le]
  have hoffExponent : δ + (1 + δ) * (1 - d) ≤ 1 - d / 2 := by
    have hdouble : 2 * δ = d / 2 := by dsimp [δ]; ring
    nlinarith only [hdouble, mul_nonneg hδ.le hd.le]
  have hsave : δ * d ≤ d / 2 := calc
    _ ≤ (1 / 2 : ℝ) * d := mul_le_mul_of_nonneg_right hδhalf hd.le
    _ = _ := by ring
  have hlogC : 0 ≤ Real.log 4 + (1 + δ) / δ := by positivity
  have hoff :
      12 * Real.log (2 * (L : ℝ)) * ((L : ℝ) ^ (1 - d) / (1 - d)) ≤
        (12 * (Real.log 4 + (1 + δ) / δ) * ((2 : ℝ) ^ (1 - d) / (1 - d))) *
          T ^ (1 - δ * d) := calc
    _ ≤ (12 * ((Real.log 4 + (1 + δ) / δ) * T ^ δ)) *
          (((2 : ℝ) ^ (1 - d) * T ^ ((1 + δ) * (1 - d))) / (1 - d)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogL (by norm_num))
        (div_le_div_of_nonneg_right hLpow hden.le) (by positivity) (by positivity)
    _ = (12 * (Real.log 4 + (1 + δ) / δ) * ((2 : ℝ) ^ (1 - d) / (1 - d))) *
          T ^ (δ + (1 + δ) * (1 - d)) := by
      rw [Real.rpow_add hT0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (hoffExponent.trans (sub_le_sub_left hsave 1)))
      (by positivity)
  calc
    _ ≤ _ := add_le_add hdiag hoff
    _ = _ := by unfold tailBoundConstant; dsimp only [δ]; ring

/-- On a fixed strip with lower edge `a`, the actual Möbius-mollified zeta function
has dyadic second moment bounded by a constant times `T ^ (1 - δ * d)`,
where `d = a - 1 / 2` and `δ = d / 4`. -/
theorem dyadic_mollified_zeta_mean_square {a b : ℝ} (ha : 1 / 2 < a) (ha' : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u T : ℝ, a ≤ u → u ≤ b → 2 ≤ T →
      let d : ℝ := a - 1 / 2
      let δ : ℝ := d / 4
      let X : ℕ := ⌊T ^ δ⌋₊
      let F : ℝ → ℝ := fun t =>
        ‖riemannZeta (vertical u t) * mollifier X (vertical u t) - 1‖ ^ 2
      IntegrableOn F (paddedBand T) ∧
        (∫ t in paddedBand T, F t) ≤ C * T ^ (1 - δ * d) := by
  let d : ℝ := a - 1 / 2
  let δ : ℝ := d / 4
  let K : ℝ := 250 + 2 * (b + 3) ^ 2 * (Real.pi / (4 * a))
  have ha0 : 0 < a := by linarith
  have hd : 0 < d := sub_pos.mpr ha
  have hd' : d < 1 / 2 := by dsimp [d]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨C₀, hC₀, hcoeff⟩ :=
    ZetaPntBounds.MollifiedZetaPolynomial.norm_coeff_subpower (d / 2) (by positivity)
  refine ⟨4 * (C₀ ^ 2 * tailBoundConstant d) + 2 * K, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg C₀) (tailBoundConstant_nonneg hd hd'))) (by positivity)
  intro u T hau hub hT
  let N : ℕ := ⌈T⌉₊
  let X : ℕ := ⌊T ^ δ⌋₊
  let F : ℝ → ℝ := fun t =>
    ‖riemannZeta (vertical u t) * mollifier X (vertical u t) - 1‖ ^ 2
  let E : ℝ → ℝ := fun t =>
    ‖riemannZeta (vertical u t) - ZetaTruncationMeanSquare.polynomial N (vertical u t)‖ ^ 2
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  obtain ⟨hX, hXN, hXlower, hXupper, hLupper⟩ := dyadic_cutoff_bounds hd hd' hT
  have hL : 1 ≤ N * X := Nat.mul_pos (hX.trans hXN) hX
  have hF : IntegrableOn F (paddedBand T) := integrableOn_mollified (u := u) hT X
  obtain ⟨hE, hEbound⟩ := ZetaTruncationMeanSquare.dyadic_truncation_mean_square ha hau hub hT
  change IntegrableOn E (paddedBand T) at hE
  change (∫ t in paddedBand T, E t) ≤ K * T ^ (2 - 2 * a) at hEbound
  have hErrPower : (X : ℝ) ^ 2 * T ^ (2 - 2 * a) ≤ T ^ (1 - δ * d) := calc
    _ ≤ (T ^ δ) ^ (2 : ℕ) * T ^ (2 - 2 * a) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg X) hXupper 2)
        (Real.rpow_nonneg hT0.le _)
    _ = T ^ (1 - 3 * d / 2) := by
      have hexp : δ * ((2 : ℕ) : ℝ) + (2 - 2 * a) = 1 - 3 * d / 2 := by
        dsimp [δ, d]
        norm_num <;> ring
      rw [← Real.rpow_mul_natCast hT0.le δ 2, ← Real.rpow_add hT0, hexp]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hT1
      have hδ : δ ≤ 1 / 2 := by dsimp [δ]; linarith
      nlinarith only [hd, mul_le_mul_of_nonneg_right hδ hd.le]
  have hInterval {A B : ℝ} (hAB : A ≤ B) (hlen : B - A ≤ 2 * T)
      (hsub : Set.Icc A B ⊆ paddedBand T) :
      (∫ t in A..B, F t) ≤ 2 * (C₀ ^ 2 * (tailBoundConstant d * T ^ (1 - δ * d))) +
        (2 * (X : ℝ) ^ 2) * (∫ t in A..B, E t) := by
    have hpoly := (tail_interval_mean_square hX hXN hAB hau hd hd' (rfl : d = a - 1 / 2)
      hC₀.le (hcoeff N X)).trans
        (mul_le_mul_of_nonneg_left
          (dyadic_tail_weights_le hd hd' hT hL hXlower hLupper hlen) (sq_nonneg C₀))
    have hmix := ZetaPntBounds.MollifiedZetaPolynomial.integral_norm_mollifiedZeta_sub_one_sq_le
      hX hXN (ha0.le.trans hau) hAB
      (fun t ht => vertical_ne_one hT (hsub ht))
    simp only [zetaPartialSum_eq_polynomial] at hmix
    change (∫ t in A..B, F t) ≤
      2 * (∫ t in A..B, ‖tailPolynomial N X (vertical u t)‖ ^ 2) +
        (2 * (X : ℝ) ^ 2) * (∫ t in A..B, E t) at hmix
    exact hmix.trans (add_le_add (mul_le_mul_of_nonneg_left hpoly (by norm_num)) le_rfl)
  have hneg := hInterval (A := -(2 * T + 1)) (B := -(T - 1)) (by linarith)
    (by linarith) (by rw [paddedBand_eq_union hT]; exact Set.subset_union_left)
  have hpos := hInterval (A := T - 1) (B := 2 * T + 1) (by linarith)
    (by linarith) (by rw [paddedBand_eq_union hT]; exact Set.subset_union_right)
  change IntegrableOn F (paddedBand T) ∧
    (∫ t in paddedBand T, F t) ≤
      (4 * (C₀ ^ 2 * tailBoundConstant d) + 2 * K) * T ^ (1 - δ * d)
  refine ⟨hF, ?_⟩
  calc
    _ ≤ 4 * (C₀ ^ 2 * tailBoundConstant d) * T ^ (1 - δ * d) +
          (2 * (X : ℝ) ^ 2) * (∫ t in paddedBand T, E t) := by
      rw [integral_paddedBand_eq hT hF, integral_paddedBand_eq hT hE]
      calc
        _ ≤ _ := add_le_add hneg hpos
        _ = _ := by ring
    _ ≤ 4 * (C₀ ^ 2 * tailBoundConstant d) * T ^ (1 - δ * d) +
          (2 * (X : ℝ) ^ 2) * (K * T ^ (2 - 2 * a)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hEbound (by positivity))
    _ = 4 * (C₀ ^ 2 * tailBoundConstant d) * T ^ (1 - δ * d) +
          (2 * K) * ((X : ℝ) ^ 2 * T ^ (2 - 2 * a)) := by ring
    _ ≤ 4 * (C₀ ^ 2 * tailBoundConstant d) * T ^ (1 - δ * d) +
          (2 * K) * T ^ (1 - δ * d) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hErrPower (by positivity))
    _ = _ := by ring

end

end D5.S3.Weil.MollifiedDyadicMeanSquare
