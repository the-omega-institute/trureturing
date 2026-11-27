/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Hilbert–Schmidt factorization and conjugation of the null-diamond operator. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondContour4D
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Frequency multipliers and square-integrable kernels for the four-dimensional null diamond. -/

noncomputable section

open Complex Filter MeasureTheory MeasureTheory.Measure Set
open D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder

namespace NullConeGravity

private local instance : SFinite phaseMeasure := by unfold phaseMeasure; infer_instance

/-- The radial normalization, with its removable value at zero. -/
def wgt (ν : ℝ) : ℝ :=
  if ν = 0 then 2 else ν * Real.cosh (ν / 2) / Real.sinh (ν / 2)

/-- The massless positive multiplier. -/
def a (ν : ℝ) : ℝ := 2 / (1 + Real.exp ν)

/-- The real frequency multiplier of the skew form. -/
def freqJ (ν : ℝ) : ℝ := a ν - 1

private theorem wgt_neg (ν : ℝ) : wgt (-ν) = wgt ν := by
  simp [wgt, neg_div, Real.cosh_neg, Real.sinh_neg, div_neg]

private theorem wgt_measurable : Measurable wgt := by
  unfold wgt
  exact Measurable.ite (measurableSet_singleton _) measurable_const (by fun_prop)

private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  let f := fun y : ℝ => y * Real.cosh y - Real.sinh y
  have hd (y : ℝ) : HasDerivAt f (y * Real.sinh y) y := by
    convert (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)) using 1
    · rfl
    · simp [id]
  have hm : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [(hd y).deriv]
    have hy' : 0 < y := by simpa using hy
    exact mul_nonneg hy'.le (Real.sinh_nonneg_iff.mpr hy'.le)
  have h := hm (mem_Ici.mpr (le_rfl : (0 : ℝ) ≤ 0)) hx hx
  exact sub_nonneg.mp (by simpa [f] using h)

/-- The frequency weight is bounded below by two and by the absolute frequency. -/
theorem wgt_bounds (ν : ℝ) : 2 ≤ wgt ν ∧ |ν| ≤ wgt ν ∧ wgt ν ≤ 2 + |ν| := by
  suffices h : ∀ x : ℝ, 0 ≤ x → 2 ≤ wgt x ∧ x ≤ wgt x ∧ wgt x ≤ 2 + x by
    have he : wgt |ν| = wgt ν := by
      rcases le_total 0 ν with hν | hν
      · rw [abs_of_nonneg hν]
      · rw [abs_of_nonpos hν, wgt_neg]
    simpa only [he] using h |ν| (abs_nonneg ν)
  intro x hx
  rcases hx.eq_or_lt with h | h
  · simp [← h, wgt]
  have hs := Real.sinh_pos_iff.mpr (show 0 < x / 2 by positivity)
  rw [wgt, ite_eq_right h.ne']
  refine ⟨(le_div_iff₀ hs).2 ?_, (le_div_iff₀ hs).2 ?_, (div_le_iff₀ hs).2 ?_⟩
  · linarith [sinh_le_mul_cosh (show 0 ≤ x / 2 by positivity)]
  · rw [Real.cosh_eq, Real.sinh_eq]
    linarith [mul_pos h (Real.exp_pos (-(x / 2)))]
  · rw [Real.cosh_eq, Real.sinh_eq]
    have he : Real.exp (x / 2) = Real.exp x * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ Real.exp x - (x + 1) by linarith [Real.add_one_le_exp x])
      (Real.exp_pos (-(x / 2))).le]

private theorem a_pos (ν : ℝ) : 0 < a ν := by unfold a; positivity

private theorem a_le (ν : ℝ) : a ν ≤ 2 := by
  rw [a, div_le_iff₀ (by positivity)]
  linarith [Real.exp_pos ν]

private theorem freqJ_neg (ν : ℝ) : freqJ (-ν) = -freqJ ν := by
  have h := Real.exp_pos ν
  simp only [freqJ, a, Real.exp_neg]
  field_simp
  ring

private theorem freqJ_eq_zero (ν : ℝ) : freqJ ν = 0 ↔ ν = 0 := by
  constructor
  · intro h
    have he : Real.exp ν = 1 := by
      have h' := (div_eq_iff (show 1 + Real.exp ν ≠ 0 by positivity)).mp (sub_eq_zero.mp h)
      linarith
    simpa using he
  · rintro rfl
    norm_num [freqJ, a]

private theorem invQuarter_le (ν : ℝ) :
    (a ν) ^ (- (1 / 4 : ℝ)) ≤ Real.exp (|ν| / 4) := by
  rw [Real.rpow_neg_eq_inv_rpow, ← show |ν| * (1 / 4 : ℝ) = |ν| / 4 by ring, Real.exp_mul]
  refine Real.rpow_le_rpow (by positivity [a_pos ν]) ?_ (by norm_num)
  rw [a, inv_div, div_le_iff₀ (by norm_num)]
  have h₁ : 1 ≤ Real.exp |ν| := Real.one_le_exp (abs_nonneg ν)
  have h₂ : Real.exp ν ≤ Real.exp |ν| := Real.exp_le_exp.mpr (le_abs_self ν)
  linarith

/-- The massive correction kernel in the normalized frequency representation. -/
def tKernel (M : ℝ) (p : Phase4D × Phase4D) : ℂ :=
  fourierG M p.1.1 p.2.1 (sphereDot p.1.2 p.2.2) /
    ((Real.sqrt (wgt p.1.1) * Real.sqrt (wgt p.2.1) : ℝ) : ℂ)

/-- The correction with an inverse quarter weight on each frequency. -/
def wKernel (M : ℝ) (p : Phase4D × Phase4D) : ℂ :=
  ((a p.1.1) ^ (- (1 / 4 : ℝ)) : ℝ) * tKernel M p * ((a p.2.1) ^ (- (1 / 4 : ℝ)) : ℝ)

private theorem a_measurable : Measurable a := by
  unfold a
  fun_prop

private theorem tKernel_measurable (M : ℝ) : Measurable (tKernel M) := by
  have h₁ : Measurable (fun p : Phase4D × Phase4D => p.1.1) :=
    measurable_fst.comp measurable_fst
  have h₂ : Measurable (fun p : Phase4D × Phase4D => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hd : Measurable (fun p : Phase4D × Phase4D => sphereDot p.1.2 p.2.2) := by
    unfold sphereDot
    fun_prop
  let coordinates := fun p : Phase4D × Phase4D => (p.1.1, p.2.1, sphereDot p.1.2 p.2.2)
  have hm : Measurable coordinates := h₁.prodMk (h₂.prodMk hd)
  have hg := (fourierG_measurable M).comp hm
  have hleft := wgt_measurable.comp h₁
  have hright := wgt_measurable.comp h₂
  have hden : Measurable (fun p : Phase4D × Phase4D =>
      ((Real.sqrt (wgt p.1.1) * Real.sqrt (wgt p.2.1) : ℝ) : ℂ)) := by fun_prop
  exact hg.div hden

private theorem wKernel_measurable (M : ℝ) : Measurable (wKernel M) := by
  have ht := tKernel_measurable M
  have h₁ := a_measurable.comp (measurable_fst.comp measurable_fst :
    Measurable (fun p : Phase4D × Phase4D => p.1.1))
  have h₂ := a_measurable.comp (measurable_fst.comp measurable_snd :
    Measurable (fun p : Phase4D × Phase4D => p.2.1))
  unfold wKernel
  fun_prop

private def realFourierSummand (M ν lam x r s : ℝ) : ℂ :=
  Complex.exp (-Complex.I*(ν : ℂ)*r + Complex.I*(lam : ℂ)*s) * stripG M r s x

private theorem fourierG_formula (M ν lam x : ℝ) :
    fourierG M ν lam x = (1/(2*(Real.pi : ℂ))) * ∫ r : ℝ, ∫ s : ℝ,
      realFourierSummand M ν lam x r s := rfl

private theorem sphereDot_ge_neg_one (n n' : Sphere4D) : -1 ≤ sphereDot n n' := by
  have h := abs_real_inner_le_norm (n : E3) (n' : E3)
  simp only [show ‖(n : E3)‖ = 1 by simp, show ‖(n' : E3)‖ = 1 by simp, mul_one] at h
  exact (abs_le.mp h).1

private theorem tKernel_bound {M C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ ν lam x : ℝ, -1 ≤ x → x < 1 →
      ‖fourierG M ν lam x‖ ≤
        C * Real.exp (-stripB * (|ν| + |lam|)) * (1 + |Real.log (1 - x)|))
    (p : Phase4D × Phase4D) :
    ‖tKernel M p‖ ≤
      C * Real.exp (-stripB * (|p.1.1| + |p.2.1|)) *
        (1 + |Real.log (1 - sphereDot p.1.2 p.2.2)|) := by
  have hroot (ν : ℝ) : 1 ≤ Real.sqrt (wgt ν) := by
    rw [Real.le_sqrt (by norm_num) (by linarith [(wgt_bounds ν).1])]
    linarith [(wgt_bounds ν).1]
  rw [tKernel, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine (div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le (hroot _) (hroot _))).trans ?_
  by_cases hx : sphereDot p.1.2 p.2.2 < 1
  · exact hb _ _ _ (sphereDot_ge_neg_one _ _) hx
  · have hz : fourierG M p.1.1 p.2.1 (sphereDot p.1.2 p.2.2) = 0 := by
      simp [fourierG_formula, realFourierSummand, stripG, hx]
    rw [hz, norm_zero]
    positivity

private def squareMajorant (c : ℝ) (p : Phase4D × Phase4D) : ℝ :=
  Real.exp (-(c * |p.1.1|)) * Real.exp (-(c * |p.2.1|)) *
    (2 * (1 + (Real.log (1 - sphereDot p.1.2 p.2.2)) ^ 2))

private theorem squareMajorant_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (squareMajorant c) (phaseMeasure.prod phaseMeasure) := by
  let μ : Measure ℝ := volume
  let σ := sphereMeasure
  have hrad := integrable_exp_neg_mul_abs hc
  have hang := (integrable_const (1 : ℝ)).add sphere_log_sq_integrable
  have hi : Integrable (fun z : (ℝ × ℝ) × (Sphere4D × Sphere4D) =>
      Real.exp (-(c * |z.1.1|)) * Real.exp (-(c * |z.1.2|)) *
        (2 * (1 + (Real.log (1 - sphereDot z.2.1 z.2.2)) ^ 2)))
      ((μ.prod μ).prod (σ.prod σ)) := (hrad.mul_prod hrad).mul_prod (hang.const_mul 2)
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : Sphere4D × ℝ ≃ᵐ ℝ × Sphere4D)
      (σ.prod μ) (μ.prod σ) := measurePreserving_swap
  have hfirst := measurePreserving_prodAssoc μ σ (μ.prod σ)
  have hsecond := (measurePreserving_prodAssoc σ μ σ).symm MeasurableEquiv.prodAssoc
  have hthird := hswap.prod (MeasurePreserving.id σ)
  have hfourth := measurePreserving_prodAssoc μ σ σ
  have hfifth := (measurePreserving_prodAssoc μ μ (σ.prod σ)).symm MeasurableEquiv.prodAssoc
  exact (hfifth.comp
    (((MeasurePreserving.id μ).prod (hfourth.comp (hthird.comp hsecond))).comp hfirst)
).integrable_comp_of_integrable hi

private theorem kernel_memLp_of_bound {K : Phase4D × Phase4D → ℂ}
    (hK : Measurable K) {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (hb : ∀ p : Phase4D × Phase4D, ‖K p‖ ≤
      C * Real.exp (-d * (|p.1.1| + |p.2.1|)) *
        (1 + |Real.log (1 - sphereDot p.1.2 p.2.2)|)) :
    MemLp K 2 (phaseMeasure.prod phaseMeasure) := by
  rw [memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable]
  refine ((squareMajorant_integrable (2 * d) (by positivity)).const_mul (C ^ 2)).mono'
    ((show Measurable (fun p => ‖K p‖ ^ 2) by fun_prop).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  refine ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hb p)).trans ?_
  simp only [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, squareMajorant]
  rw [show (2 : ℝ) * (-d * (|p.1.1| + |p.2.1|)) =
    -(2 * d * |p.1.1|) + -(2 * d * |p.2.1|) by ring, Real.exp_add]
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg (|Real.log (1 - sphereDot p.1.2 p.2.2)| - 1),
    sq_abs (Real.log (1 - sphereDot p.1.2 p.2.2))]

private theorem tKernel_memLp {M : ℝ} (hM : 0 < M) :
    MemLp (tKernel M) 2 (phaseMeasure.prod phaseMeasure) := by
  obtain ⟨C, hC, hb⟩ := fourierG_bound M hM
  exact kernel_memLp_of_bound (tKernel_measurable M) hC.le
    (by norm_num [stripB]) (tKernel_bound hC.le hb)

/-- The contour decay leaves a strictly positive exponential rate after both inverse weights. -/
theorem wKernel_memLp {M : ℝ} (hM : 0 < M) :
    MemLp (wKernel M) 2 (phaseMeasure.prod phaseMeasure) := by
  obtain ⟨C, hC, hb⟩ := fourierG_bound M hM
  refine kernel_memLp_of_bound (wKernel_measurable M) hC.le
    (d := stripB - 1 / 4) (by norm_num [stripB]) ?_
  intro p
  simp only [wKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (a_pos _).le _)]
  calc
    _ ≤ Real.exp (|p.1.1| / 4) *
        (C * Real.exp (-stripB * (|p.1.1| + |p.2.1|)) *
          (1 + |Real.log (1 - sphereDot p.1.2 p.2.2)|)) * Real.exp (|p.2.1| / 4) := by
      exact mul_le_mul (mul_le_mul (invQuarter_le _) (tKernel_bound hC.le hb p)
        (norm_nonneg _) (Real.exp_pos _).le) (invQuarter_le _)
        (Real.rpow_nonneg (a_pos _).le _) (by positivity)
    _ = _ := by
      rw [show -(stripB - 1 / 4) * (|p.1.1| + |p.2.1|) =
        |p.1.1| / 4 + -stripB * (|p.1.1| + |p.2.1|) + |p.2.1| / 4 by ring]
      rw [Real.exp_add, Real.exp_add]
      ring

private def powerSymbol (s : ℝ) (p : Phase4D) : ℂ := ((a p.1) ^ s : ℝ)

private theorem powerSymbol_memLp {s : ℝ} (hs : 0 ≤ s) :
    MemLp (powerSymbol s) ∞ phaseMeasure := by
  have hm : Measurable (powerSymbol s) := by
    have ha := a_measurable.comp (measurable_fst : Measurable (Prod.fst : Phase4D → ℝ))
    unfold powerSymbol
    fun_prop
  refine memLp_top_of_bound hm.aestronglyMeasurable (2 ^ s) (Eventually.of_forall fun p => ?_)
  rw [powerSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (a_pos _).le _)]
  exact Real.rpow_le_rpow (a_pos _).le (a_le _) hs

private def powerOp {s : ℝ} (hs : 0 ≤ s) : H4D →L[ℂ] H4D :=
  mulOp phaseMeasure (powerSymbol s) (powerSymbol_memLp hs)

/-- Positive massless multiplier on phase space. -/
def nullA : H4D →L[ℂ] H4D := powerOp (s := 1) zero_le_one

/-- Centered massless multiplier. -/
def nullJ : H4D →L[ℂ] H4D := nullA - 1

/-- Hilbert–Schmidt realization of the weighted kernel. -/
def nullW (M : ℝ) (hM : 0 < M) : H4D →L[ℂ] H4D :=
  integralKernelOp phaseMeasure (wKernel M) (wKernel_memLp hM)

/-- Hilbert–Schmidt realization of the normalized massive kernel. -/
def nullT (M : ℝ) (hM : 0 < M) : H4D →L[ℂ] H4D :=
  integralKernelOp phaseMeasure (tKernel M) (tKernel_memLp hM)

theorem nullW_hs (M : ℝ) (hM : 0 < M) : HilbertSchmidt.IsHilbertSchmidt (nullW M hM) :=
  integralKernelOp_hilbertSchmidt phaseMeasure _ _

theorem nullT_hs (M : ℝ) (hM : 0 < M) : HilbertSchmidt.IsHilbertSchmidt (nullT M hM) :=
  integralKernelOp_hilbertSchmidt phaseMeasure _ _

private theorem powerOp_ae {s : ℝ} (hs : 0 ≤ s) (f : H4D) :
    (powerOp hs f : Phase4D → ℂ) =ᵐ[phaseMeasure] fun p => powerSymbol s p * f p :=
  mulOp_ae phaseMeasure _ _ _

private theorem powerOp_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    powerOp hs * powerOp ht = powerOp (add_nonneg hs ht) := by
  ext1 f
  apply Lp.ext
  change (powerOp hs (powerOp ht f) : Phase4D → ℂ) =ᵐ[phaseMeasure] _
  filter_upwards [powerOp_ae hs (powerOp ht f), powerOp_ae ht f, powerOp_ae (add_nonneg hs ht) f]
    with p h₁ h₂ h₃
  rw [h₁, h₂, h₃, ← mul_assoc]
  simp only [powerSymbol, Real.rpow_add (a_pos _), Complex.ofReal_mul]

private theorem powerOp_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ powerOp hs := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have he : ⟪powerOp hs f, f⟫_ℂ =
      ((∫ p, (a p.1) ^ s * ‖f p‖ ^ 2 ∂phaseMeasure) : ℝ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [powerOp_ae hs f] with p hp
    rw [RCLike.inner_apply', hp, map_mul]
    simp only [powerSymbol, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [he]
  change _ ∧ 0 ≤ ∫ p, (a p.1) ^ s * ‖f p‖ ^ 2 ∂phaseMeasure
  exact ⟨rfl, integral_nonneg fun p => mul_nonneg (Real.rpow_nonneg (a_pos _).le _) (sq_nonneg _)⟩

theorem nullA_nonneg : 0 ≤ nullA := powerOp_nonneg zero_le_one

private theorem quarterRoot_of_squares {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A B C : H →L[ℂ] H}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBA : B * B = A) (hCB : C * C = B) :
    quarterRoot A = C := by
  rw [quarterRoot, CFC.sqrt_unique hBA hB, CFC.sqrt_unique hCB hC]

theorem nullT_factor (M : ℝ) (hM : 0 < M) :
    nullT M hM = quarterRoot nullA * nullW M hM * quarterRoot nullA := by
  have hHalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hQuarter : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have he : quarterRoot nullA = powerOp hQuarter :=
    quarterRoot_of_squares (powerOp_nonneg hHalf) (powerOp_nonneg hQuarter)
      (by simpa only [nullA, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using powerOp_add hHalf hHalf)
      (by simpa only [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num] using
        powerOp_add hQuarter hQuarter)
  rw [he, nullW, nullT, mul_assoc]
  change _ = mulOp phaseMeasure _ _ ∘L integralKernelOp phaseMeasure _ _ ∘L mulOp phaseMeasure _ _
  rw [integralKernelOp_mulOp_both]
  apply integralKernelOp_congr_ae
  refine Eventually.of_forall fun p => ?_
  have hc (ν : ℝ) : ((a ν) ^ (1 / 4 : ℝ) : ℝ) * (a ν) ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add (a_pos _)]
    norm_num
  have hc' (ν : ℝ) : (((a ν) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      (((a ν) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc ν
  simp only [powerSymbol, wKernel]
  symm
  calc
    _ = ((((a p.1.1) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (((a p.1.1) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) *
          tKernel M p *
          ((((a p.2.1) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (((a p.2.1) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hc', hc', one_mul, mul_one]

private theorem nullJ_ae (f : H4D) :
    (nullJ f : Phase4D → ℂ) =ᵐ[phaseMeasure] fun p => (freqJ p.1 : ℂ) * f p := by
  change (nullA f - f : H4D) =ᵐ[phaseMeasure] _
  filter_upwards [Lp.coeFn_sub (nullA f) f, powerOp_ae zero_le_one f] with p h₁ h₂
  rw [h₁, Pi.sub_apply, show nullA f p = powerSymbol 1 p * f p from h₂]
  simp only [powerSymbol, Real.rpow_one, freqJ, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem nullJ_ker : nullJ.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hz : nullJ f = 0 := LinearMap.mem_ker.mp hf
  have hzero : ∀ᵐ p : Phase4D ∂phaseMeasure, p.1 ≠ 0 := by
    have hr : ∀ᵐ ν : ℝ ∂volume, ν ≠ 0 := by
      apply ae_iff.mpr
      simp
    exact (quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := sphereMeasure)).ae hr
  change f = 0
  apply Lp.ext
  filter_upwards [nullJ_ae f, hzero, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := phaseMeasure)] with p hp hν h₀
  rw [hz, h₀] at hp
  rw [h₀]
  exact (mul_eq_zero.mp hp.symm).resolve_left fun h => hν ((freqJ_eq_zero _).mp (Complex.ofReal_eq_zero.mp h))


private theorem conj_besselP2_ofReal (t : ℝ) : conj (besselP2 t) = besselP2 t := by
  let F := fun k : ℕ => ((k + 1 : ℂ)^2 * pk k) * (t : ℂ)^k
  change conj (∑' k, F k) = ∑' k, F k
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp [F, pk]

private theorem conj_besselB2_ofReal (t : ℝ) : conj (besselB2 t) = besselB2 t := by
  change conj (∑' k : ℕ, ((((k + 1 : ℂ)^2 * bk k) - 2 * (k + 1 : ℂ)) * pk k) *
    (t : ℂ)^k) = _
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp [pk, bk, map_ofNat]

private theorem stripG_swap (M : ℝ) (r s : ℂ) (x : ℝ) :
    stripG M r s x = stripG M s r x := by
  unfold stripG
  simp only [mul_assoc, mul_left_comm, mul_comm, add_left_comm, add_comm]

private theorem conj_stripG_ofReal (M r s x : ℝ) (hM : 0 < M) :
    conj (stripG M r s x) = stripG M r s x := by
  by_cases hx : x < 1
  · rw [stripG_real M r s x hM hx]
    simp only [correction, ite_eq_left hx, correctionLog]
    let t := M^2 * (modularU r).re * (modularU s).re * (1-x)/2
    let G := (4 * modularUprime r * modularUprime s) *
      (((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)) *
        ((Real.log t : ℂ) * besselP2 (t : ℂ) - besselB2 (t : ℂ)))
    change conj G = G
    simp only [G, modularUprime, map_mul, map_div₀, map_pow, map_ofNat, map_sub, map_add,
      map_one, Complex.conj_ofReal, ← Complex.exp_conj, conj_besselP2_ofReal, conj_besselB2_ofReal]
  · simp [stripG, hx]

private theorem fourierG_reflect (M ν lam x : ℝ) (hM : 0 < M) :
    conj (fourierG M (-ν) (-lam) x) = fourierG M ν lam x := by
  simp [fourierG_formula, realFourierSummand, ← integral_conj, map_ofNat,
    conj_stripG_ofReal, hM, ← Complex.exp_conj]

private theorem realFourier_integrable (M ν lam x : ℝ) (hM : 0 < M)
    (hx0 : -1 ≤ x) (hx1 : x < 1) :
    Integrable (Function.uncurry (realFourierSummand M ν lam x))
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨C, hC, hbound⟩ := stripG_bound M hM
  let K := C * (1 + |Real.log (1-x)| + Real.pi⁻¹)
  unfold Function.uncurry realFourierSummand
  have base := D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability.integrable_exp_neg_mul_abs
    Real.pi_pos
  apply ((base.const_mul K).mul_prod base).mono'
  · have hP := besselP2_entire.continuous.measurable
    have hB := besselB2_entire.continuous.measurable
    have hlog := Complex.measurable_log
    unfold stripG correctionLog modularU modularUprime liftedLog
    simp only [ite_eq_left hx1]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [] with p
    have hmem (r : ℝ) : (r : ℂ) ∈ closedStrip := by norm_num [closedStrip, stripB]
    have hb := hbound (p.1 : ℂ) (p.2 : ℂ) (hmem _) (hmem _) x hx0 hx1
    simp only [Complex.ofReal_re] at hb
    simp [Complex.norm_exp, Complex.mul_re, Complex.add_re]
    refine hb.trans ?_
    let u := |p.1| + |p.2|
    have hu : 0 ≤ u := by dsimp [u]; positivity
    let L := |Real.log (1-x)|
    have hE : 1 ≤ Real.exp (Real.pi * u) := Real.one_le_exp_iff.mpr (by positivity)
    have hU : u ≤ Real.pi⁻¹ * Real.exp (Real.pi * u) := by
      rw [inv_mul_eq_div, le_div_iff₀ Real.pi_pos]
      linarith [Real.add_one_le_exp (Real.pi * u)]
    have hpoly : 1 + u + L ≤ (1 + L + Real.pi⁻¹) * Real.exp (Real.pi * u) := by
      rw [add_mul]
      linarith [mul_le_mul_of_nonneg_left hE (show 0 ≤ 1 + L by positivity)]
    calc
      _ = C * Real.exp (-2*Real.pi*u) * (1+u+L) := by dsimp [u,L]; ring
      _ ≤ C * Real.exp (-2*Real.pi*u) * ((1+L+Real.pi⁻¹) * Real.exp (Real.pi*u)) := by
        gcongr
      _ = _ := by
        dsimp [K, L]
        calc
          _ = (C * (1 + |Real.log (1-x)| + Real.pi⁻¹)) *
                (Real.exp (-2*Real.pi*u) * Real.exp (Real.pi*u)) := by ring
          _ = _ := by
            rw [← Real.exp_add, show -2*Real.pi*u + Real.pi*u =
              -(Real.pi * |p.1|) + -(Real.pi * |p.2|) by dsimp [u]; ring, Real.exp_add]
            ring

private theorem fourierG_conj_swap (M ν lam x : ℝ) (hM : 0 < M) (hx : -1 ≤ x) :
    conj (fourierG M lam ν x) = fourierG M ν lam x := by
  by_cases hx1 : x < 1
  · have hr := fourierG_reflect M (-lam) (-ν) x hM
    rw [neg_neg, neg_neg] at hr
    rw [hr, fourierG_formula, fourierG_formula]
    congr 1
    rw [integral_integral_swap (realFourier_integrable M (-lam) (-ν) x hM hx hx1)]
    apply integral_congr_ae
    filter_upwards [] with r
    apply integral_congr_ae
    filter_upwards [] with s
    simp [realFourierSummand, stripG_swap M (s : ℂ) (r : ℂ) x, add_comm, mul_comm, mul_left_comm]
  · simp [fourierG_formula, realFourierSummand, stripG, hx1]

/-- The Fourier kernel is Hermitian, so its integral realization is self-adjoint. -/
theorem nullT_selfAdjoint (M : ℝ) (hM : 0 < M) : IsSelfAdjoint (nullT M hM) := by
  change (nullT M hM).adjoint = _
  rw [nullT, integralKernelOp_adjoint]
  apply integralKernelOp_congr_ae
  filter_upwards [] with p
  have hs : sphereDot p.2.2 p.1.2 = sphereDot p.1.2 p.2.2 := by
    exact real_inner_comm _ _
  simp only [tKernel, hs, map_div₀, Complex.conj_ofReal, fourierG_conj_swap M _ _ _ hM (sphereDot_ge_neg_one _ _),
    mul_comm (Real.sqrt (wgt p.2.1)) (Real.sqrt (wgt p.1.1))]

private def reflectFrequency : Phase4D ≃ᵐ Phase4D :=
  (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Sphere4D)

private theorem reflectFrequency_mp :
    MeasurePreserving reflectFrequency phaseMeasure phaseMeasure :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id sphereMeasure)

private theorem reflectFrequency_apply (p : Phase4D) : reflectFrequency p = (-p.1, p.2) := rfl

private def nullConjLinear : H4D →ₗ[ℝ] H4D :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpₗ 2 phaseMeasure).comp
    (Lp.compMeasurePreservingₗ ℝ reflectFrequency reflectFrequency_mp)

private theorem nullConjLinear_ae (f : H4D) :
    (nullConjLinear f : Phase4D → ℂ) =ᵐ[phaseMeasure] fun p => conj (f (reflectFrequency p)) := by
  filter_upwards [(Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp
    (Lp.compMeasurePreserving reflectFrequency reflectFrequency_mp f),
    Lp.coeFn_compMeasurePreserving f reflectFrequency_mp] with p hp hq
  change ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
    (Lp.compMeasurePreserving reflectFrequency reflectFrequency_mp f)) p = _
  rw [hp, hq]
  exact Complex.conjCLE_apply _

private theorem nullConjLinear_involutive : Function.Involutive nullConjLinear := by
  intro f
  apply Lp.ext
  filter_upwards [nullConjLinear_ae (nullConjLinear f),
    reflectFrequency_mp.quasiMeasurePreserving.ae (nullConjLinear_ae f)] with p hp hq
  exact hp.trans (by rw [hq]; simp [reflectFrequency_apply])

/-- Complex conjugation after reversing the frequency coordinate. -/
def nullConj : H4D ≃ₗᵢ[ℝ] H4D where
  toLinearEquiv := LinearEquiv.ofInvolutive nullConjLinear nullConjLinear_involutive
  norm_map' f := by
    have hle (g : H4D) : ‖nullConjLinear g‖ ≤ ‖g‖ := by
      have hn : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
        Complex.conjLIE.toLinearIsometry.norm_toContinuousLinearMap
      exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_compLp_le
        (Lp.compMeasurePreserving reflectFrequency reflectFrequency_mp g)).trans_eq (by
          rw [hn, one_mul, Lp.norm_compMeasurePreserving])
    change ‖nullConjLinear f‖ = ‖f‖
    have hrev := hle (nullConjLinear f)
    rw [nullConjLinear_involutive f] at hrev
    exact le_antisymm (hle f) hrev

theorem nullConj_ae (f : H4D) :
    (nullConj f : Phase4D → ℂ) =ᵐ[phaseMeasure] fun p => star (f (-p.1, p.2)) := by
  change (nullConjLinear f : Phase4D → ℂ) =ᵐ[phaseMeasure] _
  simpa only [reflectFrequency_apply, Complex.star_def] using nullConjLinear_ae f

theorem nullConj_smul (c : ℂ) (f : H4D) : nullConj (c • f) = star c • nullConj f := by
  apply Lp.ext
  filter_upwards [nullConj_ae (c • f), Lp.coeFn_smul (star c) (nullConj f), nullConj_ae f,
    reflectFrequency_mp.quasiMeasurePreserving.ae (Lp.coeFn_smul c f)] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply, h₃, ← reflectFrequency_apply, h₄]
  simp [smul_eq_mul]

theorem nullConj_involutive (f : H4D) : nullConj (nullConj f) = f :=
  nullConjLinear_involutive f

private theorem tKernel_reflect (M : ℝ) (hM : 0 < M) (p q : Phase4D) :
    conj (tKernel M (reflectFrequency p, reflectFrequency q)) = tKernel M (p, q) := by
  simp only [tKernel, reflectFrequency_apply, wgt_neg, map_div₀, Complex.conj_ofReal,
    fourierG_reflect M _ _ _ hM]

theorem nullConj_comm_T (M : ℝ) (hM : 0 < M) (f : H4D) :
    nullConj (nullT M hM f) = nullT M hM (nullConj f) := by
  apply Lp.ext
  have h (g : H4D) : (nullT M hM g : Phase4D → ℂ) =ᵐ[phaseMeasure]
      fun p => ∫ q, tKernel M (p, q) * g q ∂phaseMeasure :=
    integralKernelOp_ae phaseMeasure (tKernel M) (tKernel_memLp hM) g
  filter_upwards [nullConj_ae (nullT M hM f), h (nullConj f),
    reflectFrequency_mp.quasiMeasurePreserving.ae (h f)] with p h₁ h₂ h₃
  rw [h₁, h₂, ← reflectFrequency_apply, h₃]
  change conj (∫ q, tKernel M (reflectFrequency p, q) * f q ∂phaseMeasure) = _
  rw [← integral_conj, ← reflectFrequency_mp.integral_comp' (f := reflectFrequency)
    (fun q => conj (tKernel M (reflectFrequency p, q) * f q))]
  apply integral_congr_ae
  filter_upwards [nullConj_ae f] with q hq
  rw [hq, ← reflectFrequency_apply]
  exact (map_mul (starRingEnd ℂ) _ _).trans (congrArg (· * conj (f (reflectFrequency q)))
    (tKernel_reflect M hM p q))

theorem nullConj_anti_J (f : H4D) : nullConj (nullJ f) = -(nullJ (nullConj f)) := by
  apply Lp.ext
  filter_upwards [nullConj_ae (nullJ f), nullJ_ae (nullConj f), nullConj_ae f,
    Lp.coeFn_neg (nullJ (nullConj f)), reflectFrequency_mp.quasiMeasurePreserving.ae (nullJ_ae f)]
    with p h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₄, Pi.neg_apply, h₂, h₃, ← reflectFrequency_apply, h₅]
  simp only [reflectFrequency_apply, freqJ_neg, Complex.ofReal_neg, neg_mul, star_mul,
    star_neg, Complex.star_def, Complex.conj_ofReal, mul_comm]

end NullConeGravity
