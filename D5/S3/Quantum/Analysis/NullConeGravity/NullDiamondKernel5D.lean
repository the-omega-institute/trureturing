/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Elementary five-dimensional modular kernel and weighted Hilbert–Schmidt factorization. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere5D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondContour4D
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.NullConeGravity.CCRConjugation
import D5.S3.Analysis.HalfIntegerBesselFourier
import D5.S3.Analysis.HalfIntegerBesselRadial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The five-dimensional null-diamond correction on radial frequency and celestial direction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory MeasureTheory.Measure Set
open D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder Topology

namespace NullConeGravity

open Omega.HalfIntegerBesselRadial

open Omega (modularRoot correction5D_holo kernelG5D fourierG5D
  fourierG5D_measurable fourierG5D_zero fourierG5D_reflect)

/-- The elementary massive-minus-massless bulk kernel in dimension five.
The complex power of exponent `1 / 2` is the principal square root. -/
def bulkDiff5D (M : ℝ) (q : ℂ) : ℂ :=
  let r := q ^ (1 / 2 : ℂ)
  (1 / (8 * (Real.pi : ℂ) ^ 2)) * (Complex.exp (-(M : ℂ) * r) * (1 + M * r) - 1) /
    (q * r)

/-- The dimension-five boundary correction at angular dot product `x`. -/
def correction5D (M u v x : ℝ) : ℝ :=
  let y := 2 * (1 - x)
  let z := M * Real.sqrt (u * v * y)
  (M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt y)) * Real.exp (-z) * (z - 2)

open Omega (logistic logistic_eq_exp modularRoot_ofReal modularJacobian)

private theorem correction5D_holo_ofReal (M r s x : ℝ) (hx : x < 1) :
    correction5D_holo M (r : ℂ) (s : ℂ) x =
      (correction5D M (logistic (2 * Real.pi) r) (logistic (2 * Real.pi) s) x : ℂ) := by
  let u := logistic (2 * Real.pi) r
  let v := logistic (2 * Real.pi) s
  let y := 2 * (1 - x)
  have hu : 0 ≤ u := by dsimp [u]; rw [logistic_eq_exp]; positivity
  have hv : 0 ≤ v := by dsimp [v]; rw [logistic_eq_exp]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hsqrt : Real.sqrt (u * v * y) = Real.sqrt u * Real.sqrt v * Real.sqrt y := by
    rw [Real.sqrt_mul (mul_nonneg hu hv), Real.sqrt_mul hu]
  unfold correction5D_holo correction5D
  rw [modularRoot_ofReal, modularRoot_ofReal]
  change ↑(M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt y) : ℝ) *
      Complex.exp (-((↑(M * Real.sqrt y) : ℂ) * ↑(Real.sqrt u) * ↑(Real.sqrt v))) *
      ((↑(M * Real.sqrt y) : ℂ) * ↑(Real.sqrt u) * ↑(Real.sqrt v) - 2) =
    ↑((M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt y)) *
      Real.exp (-(M * Real.sqrt (u * v * y))) * (M * Real.sqrt (u * v * y) - 2) : ℝ)
  rw [hsqrt]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_sub, Complex.ofReal_inj]
  rw [show M * Real.sqrt y * Real.sqrt u * Real.sqrt v =
    M * (Real.sqrt u * Real.sqrt v * Real.sqrt y) by ring]

private theorem modularJacobian_deriv_real (r : ℝ) :
    modularJacobian (r : ℂ) = ((deriv (logistic (2 * Real.pi)) r : ℝ) : ℂ) := by
  exact (Omega.logistic_complex_coordinates r).2.trans (congrArg ((↑) : ℝ → ℂ)
    (Omega.hasDerivAt_logistic (2 * Real.pi) r).deriv.symm)

/-- On the real axes, the modular kernel is the radial correction with the two change-of-variable
Jacobians and the covariance normalization factor. -/
theorem kernelG5D_ofReal (M r s x : ℝ) (hx : x < 1) :
    kernelG5D M (r : ℂ) (s : ℂ) x =
      ((4 * deriv (logistic (2 * Real.pi)) r * deriv (logistic (2 * Real.pi)) s *
        correction5D M (logistic (2 * Real.pi) r) (logistic (2 * Real.pi) s) x : ℝ) : ℂ) := by
  rw [kernelG5D, ite_eq_left hx, correction5D_holo_ofReal M r s x hx,
    modularJacobian_deriv_real, modularJacobian_deriv_real]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

private theorem scaledBulk_eq (M : ℝ) {u v y : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hy : 0 < y) : (((u * v) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      bulkDiff5D M (↑(u * v * y) : ℂ) = ↑(scaledProfile M y u v) := by
  have hp : 0 < u * v := mul_pos hu hv
  have hq : 0 < u * v * y := mul_pos hp hy
  have hroot : (↑(u * v * y) : ℂ) ^ (1 / 2 : ℂ) = ↑(Real.sqrt (u * v * y)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hq.le]
    push_cast
    rfl
  have hrpow : (u * v) ^ (3 / 2 : ℝ) = u * v * Real.sqrt (u * v) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold bulkDiff5D scaledProfile radialScale
  rw [hroot, hrpow]
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_inj]
  rw [Real.sqrt_mul hp.le]
  field_simp [(Real.sqrt_pos.mpr hp).ne', (Real.sqrt_pos.mpr hy).ne', Real.pi_ne_zero,
    hu.ne', hv.ne', hy.ne']

/-- The mixed real radial derivative of the scaled complex bulk difference, with the
principal square root evaluated on the positive spacelike separation. -/
theorem correction5D_mixed_deriv (M : ℝ) {u v x : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hx : x < 1) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (((s * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * bulkDiff5D M (↑(2 * s * t * (1 - x)) : ℂ)) v) u =
      ↑(correction5D M u v x) := by
  let y := 2 * (1 - x)
  have hy : 0 < y := by dsimp [y]; positivity
  have hinner (s : ℝ) (hs : 0 < s) :
      deriv (fun t : ℝ =>
        (((s * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * bulkDiff5D M (↑(2 * s * t * (1 - x)) : ℂ)) v =
      ↑(radialScale y * (-(M ^ 2 * s * y / 2) * Real.exp (-M * Real.sqrt (s * v * y))) : ℝ) := by
    have heq : (fun t : ℝ =>
        (((s * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * bulkDiff5D M (↑(2 * s * t * (1 - x)) : ℂ))
        =ᶠ[𝓝 v] (fun t : ℝ => (↑(scaledProfile M y s t) : ℂ)) := by
      filter_upwards [eventually_gt_nhds hv] with t ht
      rw [show 2 * s * t * (1 - x) = s * t * y by dsimp [y]; ring]
      exact scaledBulk_eq M hs ht hy
    rw [heq.deriv_eq]
    exact (firstRadialDerivative M hs hv hy).ofReal_comp.deriv
  have heq : (fun s : ℝ => deriv (fun t : ℝ =>
      (((s * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * bulkDiff5D M (↑(2 * s * t * (1 - x)) : ℂ)) v)
      =ᶠ[𝓝 u] (fun s : ℝ =>
        (↑(radialScale y * (-(M ^ 2 * s * y / 2) * Real.exp (-M * Real.sqrt (s * v * y))) : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_nhds hu] with s hs using hinner s hs
  rw [heq.deriv_eq]
  exact (secondRadialDerivative M hu hv hy).ofReal_comp.deriv

private theorem strip_cos_pos : 0 < Real.cos (Real.pi * stripB) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> unfold stripB <;> linarith [Real.pi_pos]

private theorem modularDenom_bound : Omega.ModularDenomBound (Real.cos (Real.pi * stripB)) :=
  strip_denom_lower

/-- The separate roots remain bounded on the closed contour strip. -/
theorem modularRoot_closedStrip_bound {z w : ℂ} (hz : z ∈ closedStrip) (hw : w ∈ closedStrip) :
    let R := 1 / Real.sqrt (Real.cos (Real.pi * stripB))
    ‖modularRoot z‖ ≤ R ∧ -(R * R) ≤ (modularRoot z * modularRoot w).re :=
  ⟨Omega.modularRoot_norm_le strip_cos_pos modularDenom_bound z hz,
    Omega.modularRoot_mul_re_lower strip_cos_pos modularDenom_bound hz hw⟩

private theorem radialDecay_integrable : Integrable Omega.modularRadialDecay := by
  unfold Omega.modularRadialDecay
  simpa only [neg_mul] using
    integrable_exp_neg_mul_abs (show 0 < 2 * Real.pi by positivity)

/-- Two horizontal Cauchy contour shifts give exponential decay in both frequencies. -/
theorem fourierG5D_bound (M : ℝ) (_hM : 0 < M) :
    ∃ C > (0 : ℝ), ∀ ν lam x : ℝ, -1 ≤ x → x < 1 →
      ‖fourierG5D M ν lam x‖ ≤ C * Real.exp (-(3/8) * (|ν| + |lam|)) *
        (1 / Real.sqrt (1 - x)) :=
  Omega.fourierG5D_bound_of_horizontal_shift strip_cos_pos modularDenom_bound radialDecay_integrable
    (fun _ _ hB hf hb y hy =>
      horizontal_shift hB (show 0 < 2 * Real.pi by positivity) hf
        (fun z hz => by simpa only [neg_mul] using hb z hz) y hy) M

abbrev Phase5D := ℝ × Sphere5D

/-- Lebesgue measure in frequency and round surface measure in direction. -/
def phase5DMeasure : Measure Phase5D := (volume : Measure ℝ).prod sphere5DMeasure

instance phase5DMeasure_sFinite : SFinite phase5DMeasure := by
  unfold phase5DMeasure
  infer_instance

abbrev H5D := Lp ℂ 2 phase5DMeasure

private theorem wgt_neg (ν : ℝ) : wgt (-ν) = wgt ν := by
  simp [wgt, neg_div, Real.cosh_neg, Real.sinh_neg, div_neg]

private theorem wgt_measurable : Measurable wgt := by
  unfold wgt
  exact Measurable.ite (measurableSet_singleton _) measurable_const (by fun_prop)

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
def tKernel5D (M : ℝ) (p : Phase5D × Phase5D) : ℂ :=
  fourierG5D M p.1.1 p.2.1 (sphere5DDot p.1.2 p.2.2) /
    ((Real.sqrt (wgt p.1.1) * Real.sqrt (wgt p.2.1) : ℝ) : ℂ)

/-- The correction with an inverse quarter weight on each frequency. -/
def wKernel5D (M : ℝ) (p : Phase5D × Phase5D) : ℂ :=
  ((a p.1.1) ^ (- (1 / 4 : ℝ)) : ℝ) * tKernel5D M p * ((a p.2.1) ^ (- (1 / 4 : ℝ)) : ℝ)

private theorem a_measurable : Measurable a := by
  unfold a
  fun_prop

private theorem tKernel5D_measurable (M : ℝ) : Measurable (tKernel5D M) := by
  have h₁ : Measurable (fun p : Phase5D × Phase5D => p.1.1) :=
    measurable_fst.comp measurable_fst
  have h₂ : Measurable (fun p : Phase5D × Phase5D => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hd : Measurable (fun p : Phase5D × Phase5D => sphere5DDot p.1.2 p.2.2) := by
    exact continuous_sphere5DDot_prod.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  let coordinates := fun p : Phase5D × Phase5D => (p.1.1, p.2.1, sphere5DDot p.1.2 p.2.2)
  have hm : Measurable coordinates := h₁.prodMk (h₂.prodMk hd)
  have hg := (fourierG5D_measurable M).comp hm
  have hleft := wgt_measurable.comp h₁
  have hright := wgt_measurable.comp h₂
  have hden : Measurable (fun p : Phase5D × Phase5D =>
      ((Real.sqrt (wgt p.1.1) * Real.sqrt (wgt p.2.1) : ℝ) : ℂ)) := by fun_prop
  exact hg.div hden

private theorem wKernel5D_measurable (M : ℝ) : Measurable (wKernel5D M) := by
  have ht := tKernel5D_measurable M
  have h₁ := a_measurable.comp (measurable_fst.comp measurable_fst :
    Measurable (fun p : Phase5D × Phase5D => p.1.1))
  have h₂ := a_measurable.comp (measurable_fst.comp measurable_snd :
    Measurable (fun p : Phase5D × Phase5D => p.2.1))
  unfold wKernel5D
  fun_prop

private theorem tKernel5D_bound {M C : ℝ}
    (hb : ∀ ν lam x : ℝ, -1 ≤ x → x < 1 →
      ‖fourierG5D M ν lam x‖ ≤
        C * Real.exp (-(3/8) * (|ν| + |lam|)) * (1 / Real.sqrt (1 - x)))
    (p : Phase5D × Phase5D) :
    ‖tKernel5D M p‖ ≤
      C * Real.exp (-(3/8) * (|p.1.1| + |p.2.1|)) *
        (1 / Real.sqrt (1 - sphere5DDot p.1.2 p.2.2)) := by
  have hroot (ν : ℝ) : 1 ≤ Real.sqrt (wgt ν) := by
    rw [Real.le_sqrt (by norm_num) (by linarith [(wgt_bounds ν).1])]
    linarith [(wgt_bounds ν).1]
  rw [tKernel5D, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine (div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le (hroot _) (hroot _))).trans ?_
  by_cases hx : sphere5DDot p.1.2 p.2.2 < 1
  · exact hb _ _ _ (sphere5D_dot_bounds _ _).1 hx
  · rw [fourierG5D_zero M _ _ (le_of_not_gt hx), norm_zero]
    simp [Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr (le_of_not_gt hx))]

private def angularWeight (p : Sphere5D × Sphere5D) : ℝ :=
  1 / Real.sqrt (1 - sphere5DDot p.1 p.2)

private theorem angularWeight_sq_integrable :
    Integrable (fun p => angularWeight p ^ 2) (sphere5DMeasure.prod sphere5DMeasure) := by
  have h := (memLp_two_iff_integrable_sq_norm sphere5D_inv_sqrt_memLp.aestronglyMeasurable).mp
    sphere5D_inv_sqrt_memLp
  convert h using 1
  ext p
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

private def squareMajorant (c : ℝ) (p : Phase5D × Phase5D) : ℝ :=
  Real.exp (-(c * |p.1.1|)) * Real.exp (-(c * |p.2.1|)) * angularWeight (p.1.2, p.2.2) ^ 2

private theorem squareMajorant_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (squareMajorant c) (phase5DMeasure.prod phase5DMeasure) := by
  let μ : Measure ℝ := volume
  let σ := sphere5DMeasure
  have hrad := integrable_exp_neg_mul_abs hc
  have hi := (hrad.mul_prod hrad).mul_prod angularWeight_sq_integrable
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : Sphere5D × ℝ ≃ᵐ ℝ × Sphere5D)
      (σ.prod μ) (μ.prod σ) := measurePreserving_swap
  have hfirst := measurePreserving_prodAssoc μ σ (μ.prod σ)
  have hsecond := (measurePreserving_prodAssoc σ μ σ).symm MeasurableEquiv.prodAssoc
  have hthird := hswap.prod (MeasurePreserving.id σ)
  have hfourth := measurePreserving_prodAssoc μ σ σ
  have hfifth := (measurePreserving_prodAssoc μ μ (σ.prod σ)).symm MeasurableEquiv.prodAssoc
  exact (hfifth.comp
    (((MeasurePreserving.id μ).prod (hfourth.comp (hthird.comp hsecond))).comp hfirst)
    ).integrable_comp_of_integrable hi

private theorem kernel_memLp_of_bound {K : Phase5D × Phase5D → ℂ}
    (hK : Measurable K) {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (hb : ∀ p : Phase5D × Phase5D, ‖K p‖ ≤
      C * Real.exp (-d * (|p.1.1| + |p.2.1|)) * angularWeight (p.1.2, p.2.2)) :
    MemLp K 2 (phase5DMeasure.prod phase5DMeasure) := by
  rw [memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable]
  refine ((squareMajorant_integrable (2 * d) (by positivity)).const_mul (C ^ 2)).mono'
    ((show Measurable (fun p => ‖K p‖ ^ 2) by fun_prop).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  refine ((sq_le_sq₀ (norm_nonneg _) (by unfold angularWeight; positivity)).2 (hb p)).trans ?_
  simp only [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, squareMajorant]
  rw [show (2 : ℝ) * (-d * (|p.1.1| + |p.2.1|)) =
    -(2 * d * |p.1.1|) + -(2 * d * |p.2.1|) by ring, Real.exp_add]
  rw [mul_assoc, mul_assoc]

private theorem tKernel5D_memLp {M : ℝ} (hM : 0 < M) :
    MemLp (tKernel5D M) 2 (phase5DMeasure.prod phase5DMeasure) := by
  obtain ⟨C, hC, hb⟩ := fourierG5D_bound M hM
  exact kernel_memLp_of_bound (tKernel5D_measurable M) hC.le (by norm_num) (tKernel5D_bound hb)

/-- The inverse quarter weights leave a positive exponential decay rate on each frequency. -/
theorem wKernel5D_memLp {M : ℝ} (hM : 0 < M) :
    MemLp (wKernel5D M) 2 (phase5DMeasure.prod phase5DMeasure) := by
  obtain ⟨C, hC, hb⟩ := fourierG5D_bound M hM
  refine kernel_memLp_of_bound (wKernel5D_measurable M) hC.le
    (d := 3/8 - 1/4) (by norm_num) ?_
  intro p
  simp only [wKernel5D, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (a_pos _).le _)]
  calc
    _ ≤ Real.exp (|p.1.1| / 4) *
        (C * Real.exp (-(3/8) * (|p.1.1| + |p.2.1|)) *
          angularWeight (p.1.2, p.2.2)) * Real.exp (|p.2.1| / 4) := by
      exact mul_le_mul (mul_le_mul (invQuarter_le _) (tKernel5D_bound hb p)
        (norm_nonneg _) (Real.exp_pos _).le) (invQuarter_le _)
        (Real.rpow_nonneg (a_pos _).le _) (by unfold angularWeight; positivity)
    _ = _ := by
      rw [show -(3/8 - 1/4 : ℝ) * (|p.1.1| + |p.2.1|) =
        |p.1.1| / 4 + -(3/8) * (|p.1.1| + |p.2.1|) + |p.2.1| / 4 by ring]
      rw [Real.exp_add, Real.exp_add]
      ring

private def powerSymbol (s : ℝ) (p : Phase5D) : ℂ := ((a p.1) ^ s : ℝ)

private theorem powerSymbol_memLp {s : ℝ} (hs : 0 ≤ s) :
    MemLp (powerSymbol s) ∞ phase5DMeasure := by
  have hm : Measurable (powerSymbol s) := by
    have ha := a_measurable.comp (measurable_fst : Measurable (Prod.fst : Phase5D → ℝ))
    unfold powerSymbol
    fun_prop
  refine memLp_top_of_bound hm.aestronglyMeasurable (2 ^ s) (Eventually.of_forall fun p => ?_)
  rw [powerSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (a_pos _).le _)]
  exact Real.rpow_le_rpow (a_pos _).le (a_le _) hs

private def powerOp {s : ℝ} (hs : 0 ≤ s) : H5D →L[ℂ] H5D :=
  mulOp phase5DMeasure (powerSymbol s) (powerSymbol_memLp hs)

/-- Positive massless multiplier on phase space. -/
def nullA5D : H5D →L[ℂ] H5D := powerOp (s := 1) zero_le_one

/-- Centered massless multiplier. -/
def nullJ5D : H5D →L[ℂ] H5D := nullA5D - 1

/-- Hilbert–Schmidt realization of the weighted kernel. -/
def nullW5D (M : ℝ) (hM : 0 < M) : H5D →L[ℂ] H5D :=
  integralKernelOp phase5DMeasure (wKernel5D M) (wKernel5D_memLp hM)

/-- Hilbert–Schmidt realization of the normalized massive kernel. -/
def nullT5D (M : ℝ) (hM : 0 < M) : H5D →L[ℂ] H5D :=
  integralKernelOp phase5DMeasure (tKernel5D M) (tKernel5D_memLp hM)

theorem nullW5D_hs (M : ℝ) (hM : 0 < M) : HilbertSchmidt.IsHilbertSchmidt (nullW5D M hM) :=
  integralKernelOp_hilbertSchmidt phase5DMeasure _ _

theorem nullT5D_hs (M : ℝ) (hM : 0 < M) : HilbertSchmidt.IsHilbertSchmidt (nullT5D M hM) :=
  integralKernelOp_hilbertSchmidt phase5DMeasure _ _

private theorem powerOp_ae {s : ℝ} (hs : 0 ≤ s) (f : H5D) :
    (powerOp hs f : Phase5D → ℂ) =ᵐ[phase5DMeasure] fun p => powerSymbol s p * f p :=
  mulOp_ae phase5DMeasure _ _ _

private theorem powerOp_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    powerOp hs * powerOp ht = powerOp (add_nonneg hs ht) := by
  ext1 f
  apply Lp.ext
  change (powerOp hs (powerOp ht f) : Phase5D → ℂ) =ᵐ[phase5DMeasure] _
  filter_upwards [powerOp_ae hs (powerOp ht f), powerOp_ae ht f, powerOp_ae (add_nonneg hs ht) f]
    with p h₁ h₂ h₃
  rw [h₁, h₂, h₃, ← mul_assoc]
  simp only [powerSymbol, Real.rpow_add (a_pos _), Complex.ofReal_mul]

private theorem powerOp_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ powerOp hs := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have he : ⟪powerOp hs f, f⟫_ℂ =
      ((∫ p, (a p.1) ^ s * ‖f p‖ ^ 2 ∂phase5DMeasure) : ℝ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [powerOp_ae hs f] with p hp
    rw [RCLike.inner_apply', hp, map_mul]
    simp only [powerSymbol, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [he]
  change _ ∧ 0 ≤ ∫ p, (a p.1) ^ s * ‖f p‖ ^ 2 ∂phase5DMeasure
  exact ⟨rfl, integral_nonneg fun p => mul_nonneg (Real.rpow_nonneg (a_pos _).le _) (sq_nonneg _)⟩

theorem nullA5D_nonneg : 0 ≤ nullA5D := powerOp_nonneg zero_le_one

private theorem quarterRoot_of_squares {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A B C : H →L[ℂ] H}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBA : B * B = A) (hCB : C * C = B) :
    quarterRoot A = C := by
  rw [quarterRoot, CFC.sqrt_unique hBA hB, CFC.sqrt_unique hCB hC]

theorem nullT5D_factor (M : ℝ) (hM : 0 < M) :
    nullT5D M hM = quarterRoot nullA5D * nullW5D M hM * quarterRoot nullA5D := by
  have hHalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hQuarter : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have he : quarterRoot nullA5D = powerOp hQuarter :=
    quarterRoot_of_squares (powerOp_nonneg hHalf) (powerOp_nonneg hQuarter)
      (by simpa only [nullA5D, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using powerOp_add hHalf hHalf)
      (by simpa only [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num] using
        powerOp_add hQuarter hQuarter)
  rw [he, nullW5D, nullT5D, mul_assoc]
  change _ = mulOp phase5DMeasure _ _ ∘L integralKernelOp phase5DMeasure _ _ ∘L mulOp phase5DMeasure _ _
  rw [integralKernelOp_mulOp_both]
  apply integralKernelOp_congr_ae
  refine Eventually.of_forall fun p => ?_
  have hc (ν : ℝ) : ((a ν) ^ (1 / 4 : ℝ) : ℝ) * (a ν) ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add (a_pos _)]
    norm_num
  have hc' (ν : ℝ) : (((a ν) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      (((a ν) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc ν
  simp only [powerSymbol, wKernel5D]
  symm
  calc
    _ = ((((a p.1.1) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (((a p.1.1) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) *
          tKernel5D M p *
          ((((a p.2.1) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (((a p.2.1) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hc', hc', one_mul, mul_one]

private theorem nullJ5D_ae (f : H5D) :
    (nullJ5D f : Phase5D → ℂ) =ᵐ[phase5DMeasure] fun p => (freqJ p.1 : ℂ) * f p := by
  change (nullA5D f - f : H5D) =ᵐ[phase5DMeasure] _
  filter_upwards [Lp.coeFn_sub (nullA5D f) f, powerOp_ae zero_le_one f] with p h₁ h₂
  rw [h₁, Pi.sub_apply, show nullA5D f p = powerSymbol 1 p * f p from h₂]
  simp only [powerSymbol, Real.rpow_one, freqJ, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem nullJ5D_ker : nullJ5D.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hz : nullJ5D f = 0 := LinearMap.mem_ker.mp hf
  have hzero : ∀ᵐ p : Phase5D ∂phase5DMeasure, p.1 ≠ 0 := by
    have hr : ∀ᵐ ν : ℝ ∂volume, ν ≠ 0 := by
      apply ae_iff.mpr
      simp
    exact (quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := sphere5DMeasure)).ae hr
  change f = 0
  apply Lp.ext
  filter_upwards [nullJ5D_ae f, hzero, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := phase5DMeasure)] with p hp hν h₀
  rw [hz, h₀] at hp
  rw [h₀]
  exact (mul_eq_zero.mp hp.symm).resolve_left fun h => hν ((freqJ_eq_zero _).mp (Complex.ofReal_eq_zero.mp h))


/-- The Fourier kernel is Hermitian, so its integral realization is self-adjoint. -/
theorem nullT5D_selfAdjoint (M : ℝ) (hM : 0 < M) : IsSelfAdjoint (nullT5D M hM) := by
  change (nullT5D M hM).adjoint = _
  rw [nullT5D, integralKernelOp_adjoint]
  apply integralKernelOp_congr_ae
  filter_upwards [] with p
  have hs : sphere5DDot p.2.2 p.1.2 = sphere5DDot p.1.2 p.2.2 := by
    exact real_inner_comm _ _
  simp only [tKernel5D, hs, map_div₀, Complex.conj_ofReal, Omega.fourierG5D_conj_swap strip_cos_pos modularDenom_bound radialDecay_integrable
      M _ _ _ (sphere5D_dot_bounds _ _).1,
    mul_comm (Real.sqrt (wgt p.2.1)) (Real.sqrt (wgt p.1.1))]

private def reflectFrequency : Phase5D ≃ᵐ Phase5D :=
  (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Sphere5D)

private theorem reflectFrequency_mp :
    MeasurePreserving reflectFrequency phase5DMeasure phase5DMeasure :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id sphere5DMeasure)

private theorem reflectFrequency_apply (p : Phase5D) : reflectFrequency p = (-p.1, p.2) := rfl

private def nullConjLinear : H5D →ₗ[ℝ] H5D :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpₗ 2 phase5DMeasure).comp
    (Lp.compMeasurePreservingₗ ℝ reflectFrequency reflectFrequency_mp)

private theorem nullConjLinear_ae (f : H5D) :
    (nullConjLinear f : Phase5D → ℂ) =ᵐ[phase5DMeasure] fun p => conj (f (reflectFrequency p)) := by
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

private def nullConjEquiv : H5D ≃ₗᵢ[ℝ] H5D where
  toLinearEquiv := LinearEquiv.ofInvolutive nullConjLinear nullConjLinear_involutive
  norm_map' f := by
    have hle (g : H5D) : ‖nullConjLinear g‖ ≤ ‖g‖ := by
      have hn : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
        Complex.conjLIE.toLinearIsometry.norm_toContinuousLinearMap
      exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_compLp_le
        (Lp.compMeasurePreserving reflectFrequency reflectFrequency_mp g)).trans_eq (by
          rw [hn, one_mul, Lp.norm_compMeasurePreserving])
    change ‖nullConjLinear f‖ = ‖f‖
    have hrev := hle (nullConjLinear f)
    rw [nullConjLinear_involutive f] at hrev
    exact le_antisymm (hle f) hrev

private theorem nullConjEquiv_ae (f : H5D) :
    (nullConjEquiv f : Phase5D → ℂ) =ᵐ[phase5DMeasure] fun p => star (f (-p.1, p.2)) := by
  change (nullConjLinear f : Phase5D → ℂ) =ᵐ[phase5DMeasure] _
  simpa only [reflectFrequency_apply, Complex.star_def] using nullConjLinear_ae f

private theorem nullConjEquiv_smul (c : ℂ) (f : H5D) : nullConjEquiv (c • f) = star c • nullConjEquiv f := by
  apply Lp.ext
  filter_upwards [nullConjEquiv_ae (c • f), Lp.coeFn_smul (star c) (nullConjEquiv f), nullConjEquiv_ae f,
    reflectFrequency_mp.quasiMeasurePreserving.ae (Lp.coeFn_smul c f)] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply, h₃, ← reflectFrequency_apply, h₄]
  simp [smul_eq_mul]

/-- Complex conjugation after reversing the frequency coordinate. -/
def nullConj5D : RealConjugation H5D where
  toLinearIsometryEquiv := nullConjEquiv
  involutive := nullConjLinear_involutive
  map_complex_smul := nullConjEquiv_smul

theorem nullConj5D_ae (f : H5D) :
    (nullConj5D.toLinearIsometryEquiv f : Phase5D → ℂ) =ᵐ[phase5DMeasure]
      fun p => star (f (-p.1, p.2)) := nullConjEquiv_ae f

private theorem tKernel5D_reflect (M : ℝ) (p q : Phase5D) :
    conj (tKernel5D M (reflectFrequency p, reflectFrequency q)) = tKernel5D M (p, q) := by
  simp only [tKernel5D, reflectFrequency_apply, wgt_neg, map_div₀, Complex.conj_ofReal,
    fourierG5D_reflect M _ _ _, neg_neg]

theorem nullConj5D_comm_T (M : ℝ) (hM : 0 < M) (f : H5D) :
    nullConj5D.toLinearIsometryEquiv (nullT5D M hM f) = nullT5D M hM (nullConj5D.toLinearIsometryEquiv f) := by
  apply Lp.ext
  have h (g : H5D) : (nullT5D M hM g : Phase5D → ℂ) =ᵐ[phase5DMeasure]
      fun p => ∫ q, tKernel5D M (p, q) * g q ∂phase5DMeasure :=
    integralKernelOp_ae phase5DMeasure (tKernel5D M) (tKernel5D_memLp hM) g
  filter_upwards [nullConj5D_ae (nullT5D M hM f), h (nullConj5D.toLinearIsometryEquiv f),
    reflectFrequency_mp.quasiMeasurePreserving.ae (h f)] with p h₁ h₂ h₃
  rw [h₁, h₂, ← reflectFrequency_apply, h₃]
  change conj (∫ q, tKernel5D M (reflectFrequency p, q) * f q ∂phase5DMeasure) = _
  rw [← integral_conj, ← reflectFrequency_mp.integral_comp' (f := reflectFrequency)
    (fun q => conj (tKernel5D M (reflectFrequency p, q) * f q))]
  apply integral_congr_ae
  filter_upwards [nullConj5D_ae f] with q hq
  rw [hq, ← reflectFrequency_apply]
  exact (map_mul (starRingEnd ℂ) _ _).trans (congrArg (· * conj (f (reflectFrequency q)))
    (tKernel5D_reflect M p q))

theorem nullConj5D_anti_J (f : H5D) : nullConj5D.toLinearIsometryEquiv (nullJ5D f) = -(nullJ5D (nullConj5D.toLinearIsometryEquiv f)) := by
  apply Lp.ext
  filter_upwards [nullConj5D_ae (nullJ5D f), nullJ5D_ae (nullConj5D.toLinearIsometryEquiv f), nullConj5D_ae f,
    Lp.coeFn_neg (nullJ5D (nullConj5D.toLinearIsometryEquiv f)), reflectFrequency_mp.quasiMeasurePreserving.ae (nullJ5D_ae f)]
    with p h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₄, Pi.neg_apply, h₂, h₃, ← reflectFrequency_apply, h₅]
  simp only [reflectFrequency_apply, freqJ_neg, Complex.ofReal_neg, neg_mul, star_mul,
    star_neg, Complex.star_def, Complex.conj_ofReal, mul_comm]

end NullConeGravity
