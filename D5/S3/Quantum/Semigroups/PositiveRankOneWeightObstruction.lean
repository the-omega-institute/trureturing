/- GID: D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive rank-one semigroup on the unit interval has no equivalent contractive weighted essential sup norm. -/

/- Source: Madou–Remizov–Vafadar (eds.), arXiv:2410.00416v2, §6,
Problem 22 and the positivity discussion on p. 18. Preregistration: #30423.
The unrestricted problem already has a repository counterexample; the target
here is its positive-semigroup restriction. No priority claim is made.
Admission basis: escape-witness. The proposed live witness constructs a
positive-measure subinterval excluding every positive essential lower bound
for a scalar multiple of x, and consumes it after rank-one rigidity.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction

/-- Lebesgue measure on the open unit interval. -/
def μ : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioo]⟩

/-- The complex Hilbert space over the same measure used for the essential sup norms. -/
abbrev H := Lp ℂ 2 μ

private lemma ae_interval : ∀ᵐ x ∂μ, 0 < x ∧ x < 1 :=
  ae_restrict_mem measurableSet_Ioo

private lemma h_memLp : MemLp (fun x : ℝ => (x : ℂ)) 2 μ := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [ae_interval] with x hx
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.le

/-- The actual L2 class of x↦x. -/
def h : H := h_memLp.toLp (fun x : ℝ => (x : ℂ))

private lemma h_rep : h =ᵐ[μ] (fun x : ℝ => (x : ℂ)) :=
  h_memLp.coeFn_toLp

private lemma integral_sq : ∫ x : ℝ, x ^ 2 ∂μ = 1 / 3 := by
  unfold μ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [integral_pow]

private lemma integral_linear : ∫ x : ℝ, x ∂μ = 1 / 2 := by
  unfold μ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [integral_id]

private lemma h_inner : ⟪h, h⟫_ℂ = (1 / 3 : ℂ) := by
  rw [L2.inner_def]
  calc
    (∫ x, ⟪h x, h x⟫_ℂ ∂μ) = ∫ x, ((x ^ 2 : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h_rep] with x hx
      simp only [hx, RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_pow]
      ring
    _ = (1 / 3 : ℂ) := by rw [integral_complex_ofReal, integral_sq]; norm_num

private lemma h_norm_sq : ‖h‖ ^ 2 = 1 / 3 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h_inner]
  norm_num

/-- Orthogonal rank-one projection onto the span of x↦x. -/
def P : H →L[ℂ] H := (ℂ ∙ h).starProjection

/-- Nonnegative bounded generator. -/
def A : H →L[ℂ] H := 1 - P

/-- The complex-time semigroup, with its orthogonal spectral decomposition. -/
def T (z : ℂ) : H →L[ℂ] H := P + Complex.exp (-z) • A

private lemma P_formula (f : H) : P f = (3 * ⟪h, f⟫_ℂ) • h := by
  rw [P, Submodule.starProjection_singleton, h_norm_sq]
  congr 1
  push_cast
  ring

private lemma P_rep (f : H) :
    P f =ᵐ[μ] (fun x => 3 * (x : ℂ) * ∫ y, (y : ℂ) * f y ∂μ) := by
  have hi : ⟪h, f⟫_ℂ = ∫ y, (y : ℂ) * f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h_rep] with y hy
    simp [hy, RCLike.inner_apply, mul_comm]
  rw [P_formula]
  filter_upwards [Lp.coeFn_smul (3 * ⟪h, f⟫_ℂ) h, h_rep] with x hx hh
  rw [hx]
  change (3 * ⟪h, f⟫_ℂ) * h x = _
  rw [hh, hi]
  ring

private lemma integrable_sq : Integrable (fun x : ℝ => x*x) μ := by
  have hi := (continuous_id.pow 2).integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := 1)
  exact (hi.mono_set Ioo_subset_Icc_self).congr (ae_of_all _ (fun x => by simp [pow_two]))

/-- Positivity of h makes the conserved rank-one functional faithful on its
nonnegative defect. This helper is consumed by the weighted obstruction. -/
private theorem superinvariant_eq {w : ℝ → ℝ}
    (hi : Integrable (fun x => x * w x) μ)
    (hs : ∀ᵐ x ∂μ, (3 * ∫ y, y * w y ∂μ) * x ≤ w x) :
    w =ᵐ[μ] (fun x => (3 * ∫ y, y * w y ∂μ) * x) := by
  let c : ℝ := 3 * ∫ y, y * w y ∂μ
  have hj : Integrable (fun x => x * (w x - c*x)) μ := by
    convert hi.sub (integrable_sq.const_mul c) using 1
    ext x
    dsimp
    ring
  have hz : ∫ x, x * (w x - c*x) ∂μ = 0 := by
    have hf : (fun x => x * (w x - c*x)) =
        (fun x => x * w x) - (fun x => c * (x*x)) := by ext x; dsimp; ring
    rw [hf]
    change (∫ x, x * w x - c * (x*x) ∂μ) = 0
    rw [integral_sub hi (integrable_sq.const_mul c), integral_const_mul]
    have hsquare : ∫ x : ℝ, x*x ∂μ = 1/3 := by simpa only [pow_two] using integral_sq
    rw [hsquare]
    dsimp [c]
    ring
  have hn : ∀ᵐ x ∂μ, 0 ≤ x * (w x - c*x) := by
    filter_upwards [ae_interval, hs] with x hx hxs
    exact mul_nonneg hx.1.le (sub_nonneg.mpr hxs)
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hj).mp hz
  filter_upwards [ae_interval, he] with x hx hzero
  have : w x - c*x = 0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hx.1)
  exact sub_eq_zero.mp this

private theorem linear_no_floor (c ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ᵐ x ∂μ, ε ≤ c*x) := by
  intro hf
  let δ : ℝ := min (1/2) (ε / (2*(|c| +1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hm : μ (Ioo 0 δ) ≠ 0 := by
    rw [μ, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioo le_rfl hδ1), Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by simpa using hδ))
  obtain ⟨x, hx, hxf⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hf)
  have hxδ : x < ε / (2*(|c| +1)) := hx.2.trans_le (min_le_right _ _)
  have he : x * (2*(|c| +1)) < ε := (lt_div_iff₀ (by positivity)).mp hxδ
  have hc : c*x < ε := by
    have hx0 := hx.1
    have hcx : c*x ≤ |c| *x := mul_le_mul_of_nonneg_right (le_abs_self c) hx.1.le
    have : 0 ≤ |c| *x := mul_nonneg (abs_nonneg _) hx.1.le
    nlinarith
  exact (not_lt_of_ge hxf) hc

private lemma T_rep (z : ℂ) (f : H) :
    T z f =ᵐ[μ] (fun x => Complex.exp (-z) * f x +
      (1 - Complex.exp (-z)) * (3 * (x : ℂ) * ∫ y, (y : ℂ) * f y ∂μ)) := by
  change (P f + Complex.exp (-z) • (f - P f) : H) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_add (P f) (Complex.exp (-z) • (f - P f)),
    Lp.coeFn_smul (Complex.exp (-z)) (f - P f), Lp.coeFn_sub f (P f),
    P_rep f] with x ha hs hd hp
  rw [ha]
  change P f x + (Complex.exp (-z) • (f - P f) : H) x = _
  rw [hs]
  change P f x + Complex.exp (-z) * (f - P f : H) x = _
  rw [hd]
  change P f x + Complex.exp (-z) * (f x - P f x) = _
  rw [hp]
  ring

private theorem no_weight (g : ℝ → ℝ) (hg : MemLp g ∞ μ)
    (hginv : MemLp (fun x => (g x)⁻¹) ∞ μ)
    (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hc : ∀ t : ℝ, 0 ≤ t → ∀ f : H, MemLp f ∞ μ →
      eLpNorm (fun x => (g x : ℂ) * T (t : ℂ) f x) ∞ μ ≤
        eLpNorm (fun x => (g x : ℂ) * f x) ∞ μ) : False := by
  let w : ℝ → ℝ := fun x => (g x)⁻¹
  have hw : MemLp w ∞ μ := hginv
  have hwc : MemLp (fun x => (w x : ℂ)) 2 μ := (hw.mono_exponent (by simp)).ofReal
  let f : H := hwc.toLp (fun x => (w x : ℂ))
  have hf : f =ᵐ[μ] (fun x => (w x : ℂ)) := hwc.coeFn_toLp
  have hf_top : MemLp f ∞ μ := (memLp_congr_ae hf).mpr hw.ofReal
  have hiw : Integrable (fun x : ℝ => x * w x) μ := by
    have hm : MemLp (fun x : ℝ => x) 2 μ := by
      apply MemLp.of_bound (by fun_prop) 1
      filter_upwards [ae_interval] with x hx
      simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.le
    change Integrable (((fun x : ℝ => x) : ℝ → ℝ) * w) μ
    exact hm.integrable_mul (hw.mono_exponent (by norm_num : (2:ℝ≥0∞) ≤ ∞))
  let c : ℝ := 3 * ∫ y, y * w y ∂μ
  have hint : (∫ y, (y : ℂ) * f y ∂μ) = ((∫ y, y * w y ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    simp [hy]
  have hinput : eLpNorm (fun x => (g x : ℂ) * f x) ∞ μ = 1 := by
    calc
      _ = eLpNorm (fun _ : ℝ => (1 : ℂ)) ∞ μ := by
        apply eLpNorm_congr_ae
        filter_upwards [hf, hpos] with x hx hxp
        simp [hx, w, ne_of_gt hxp]
      _ = 1 := by simp [eLpNorm_const, NeZero.ne μ]
  have hout := (hc 1 zero_le_one f hf_top).trans_eq hinput
  have hbound : ∀ᵐ x ∂μ, ‖(g x : ℂ) * T (1 : ℂ) f x‖ ≤ 1 := by
    filter_upwards [ae_le_eLpNormEssSup (f := fun x => (g x : ℂ) * T (1:ℂ) f x)] with x hx
    have hle := hx.trans (eLpNormEssSup_le_eLpNorm_top.trans hout)
    have : ‖(g x : ℂ) * T (1 : ℂ) f x‖ₑ ≤ ‖(1:ℂ)‖ₑ := by simpa using hle
    simpa using enorm_le_iff_norm_le.mp this
  have he0 : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
  have he1 : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hs : ∀ᵐ x ∂μ, c*x ≤ w x := by
    filter_upwards [hbound, T_rep 1 f, hf, hpos] with x hb ht hfx hpx
    have ht' : T (1:ℂ) f x =
        ((Real.exp (-1) * w x + (1 - Real.exp (-1)) * (c*x) : ℝ) : ℂ) := by
      rw [ht, hfx, hint]
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]
      dsimp [c]
      push_cast
      ring
    have hr := (Complex.re_le_norm ((g x:ℂ) * T (1:ℂ) f x)).trans hb
    rw [ht'] at hr
    have hr' : g x * (Real.exp (-1) * w x + (1 - Real.exp (-1)) * (c*x)) ≤ 1 := by
      simpa only [← Complex.ofReal_mul, Complex.ofReal_re] using hr
    have hgw : g x * w x = 1 := mul_inv_cancel₀ (ne_of_gt hpx)
    have hh : Real.exp (-1) * w x + (1 - Real.exp (-1)) * (c*x) ≤ w x :=
      (mul_le_mul_iff_right₀ hpx).mp (hr'.trans_eq hgw.symm)
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr he1)).mp
    nlinarith
  have heq := superinvariant_eq hiw hs
  let B : ℝ := max 1 (lpNorm g ∞ μ)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply linear_no_floor c B⁻¹ (inv_pos.mpr hB)
  filter_upwards [heq, hpos, ae_le_lpNorm_exponent_top hg] with x heqx hpx hgb
  have hgb' : g x ≤ B := (le_abs_self (g x)).trans (hgb.trans (le_max_right _ _))
  have hinv : B⁻¹ ≤ (g x)⁻¹ := (inv_le_inv₀ hB hpx).mpr hgb'
  exact hinv.trans_eq heqx

private lemma P_idem : P * P = P := (ℂ ∙ h).isIdempotentElem_starProjection

private lemma A_idem : A * A = A := by
  dsimp [A]
  noncomm_ring [P_idem]

private lemma PA : P * A = 0 := by
  rw [A, mul_sub, mul_one, P_idem, sub_self]

private lemma AP : A * P = 0 := by
  rw [A, sub_mul, one_mul, P_idem, sub_self]

private def spectralMap : (ℂ × ℂ) →ₐ[ℂ] (H →L[ℂ] H) :=
  { toFun := fun p => p.1 • P + p.2 • A
    map_one' := by simp [A]
    map_zero' := by simp
    map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
    map_mul' := by
      intro p q
      simp only [Prod.fst_mul, Prod.snd_mul, mul_add, add_mul, smul_mul_assoc,
        mul_smul_comm, P_idem, A_idem, PA, AP, smul_zero, add_zero, zero_add,
        smul_smul]
      congr 1 <;> congr 1 <;> ring
    commutes' := by intro c; simp [A, smul_sub, Algebra.algebraMap_eq_smul_one] }

private lemma T_exp (z : ℂ) : T z = NormedSpace.exp ((-z) • A) := by
  have hc : Continuous spectralMap := spectralMap.toLinearMap.continuous_of_finiteDimensional
  have hh := NormedSpace.map_exp spectralMap hc ((0, -z) : ℂ × ℂ)
  have harg : spectralMap ((0, -z) : ℂ × ℂ) = (-z) • A := by simp [spectralMap]
  rw [harg] at hh
  rw [← hh]
  change P + Complex.exp (-z) • A =
    (NormedSpace.exp ((0, -z) : ℂ × ℂ)).1 • P +
      (NormedSpace.exp ((0, -z) : ℂ × ℂ)).2 • A
  simp [Complex.exp_eq_exp_ℂ]

private lemma T_add (z w : ℂ) : T (z + w) = T z * T w := by
  simp only [T, neg_add, Complex.exp_add, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, P_idem, A_idem, PA, AP, smul_zero, zero_add, add_zero, smul_smul]
  congr 1
  congr 1
  ring

private lemma T_zero : T 0 = 1 := by simp [T, A]

private lemma A_orth : A = (ℂ ∙ h)ᗮ.starProjection := by
  exact (Submodule.starProjection_orthogonal _).symm

private lemma A_selfAdjoint : IsSelfAdjoint A := by
  rw [A_orth]
  exact isSelfAdjoint_starProjection _

private lemma A_inner (u : H) : ⟪u, A u⟫_ℂ = (‖A u‖ ^ 2 : ℝ) := by
  have horth : ⟪P u, A u⟫_ℂ = 0 := by
    have ho := (ℂ ∙ h).starProjection_inner_eq_zero u (P u)
      ((ℂ ∙ h).starProjection_apply_mem u)
    have : A u = u - P u := rfl
    change ⟪u - P u, P u⟫_ℂ = 0 at ho
    rw [← inner_conj_symm, this, ho, map_zero]
  have hu : u = P u + A u := by change u = P u + (u - P u); abel
  calc
    ⟪u, A u⟫_ℂ = ⟪P u + A u, A u⟫_ℂ := congrArg (fun v => ⟪v, A u⟫_ℂ) hu
    _ = (‖A u‖ ^ 2 : ℝ) := by rw [inner_add_left, horth, zero_add, inner_self_eq_norm_sq_to_K]; push_cast; rfl

private lemma T_contractive (z : ℂ) (hz : 0 ≤ z.re) (u : H) : ‖T z u‖ ≤ ‖u‖ := by
  have horth : ⟪P u, A u⟫_ℂ = 0 := by
    have ho := (ℂ ∙ h).starProjection_inner_eq_zero u (P u)
      ((ℂ ∙ h).starProjection_apply_mem u)
    change ⟪u - P u, P u⟫_ℂ = 0 at ho
    rw [← inner_conj_symm, show A u = u - P u from rfl, ho, map_zero]
  have hsplit : ‖u‖ ^ 2 = ‖P u‖ ^ 2 + ‖A u‖ ^ 2 := by
    simpa only [P, ← A_orth] using (ℂ ∙ h).norm_sq_eq_add_norm_sq_starProjection u
  have hnorm : ‖Complex.exp (-z)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (by simpa using neg_nonpos.mpr hz)
  have hsq : ‖T z u‖ ^ 2 = ‖P u‖ ^ 2 + ‖Complex.exp (-z)‖ ^ 2 * ‖A u‖ ^ 2 := by
    change ‖P u + Complex.exp (-z) • A u‖ ^ 2 = _
    have ho : ⟪P u, Complex.exp (-z) • A u⟫_ℂ = 0 := by
      rw [inner_smul_right, horth, mul_zero]
    simpa only [← pow_two, norm_smul, mul_pow] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  have he : ‖Complex.exp (-z)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (Complex.exp (-z))]
  have hp := mul_le_mul_of_nonneg_right he (sq_nonneg ‖A u‖)
  nlinarith [norm_nonneg (T z u), norm_nonneg u]

private lemma T_analytic (z : ℂ) : AnalyticAt ℂ T z := by
  change AnalyticAt ℂ (fun z : ℂ => P + Complex.exp (-z) • A) z
  exact analyticAt_const.add (((analyticAt_id.neg).cexp).smul analyticAt_const)

private lemma T_generator : HasDerivAt T (-A) 0 := by
  change HasDerivAt (fun z : ℂ => P + Complex.exp (-z) • A) (-A) 0
  convert (hasDerivAt_const (0:ℂ) P).add
    (((hasDerivAt_id (0:ℂ)).neg.cexp).smul_const A) using 1 <;> first | rfl | simp

private lemma integrable_linear : Integrable (fun x : ℝ => x) μ := by
  exact continuous_id.integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := 1)
    |>.mono_set Ioo_subset_Icc_self

private lemma T_positive (t : ℝ) (ht : 0 ≤ t) (f : H)
    (hf : ∀ᵐ x ∂μ, 0 ≤ (f x).re ∧ (f x).im = 0) :
    ∀ᵐ x ∂μ, 0 ≤ (T (t:ℂ) f x).re ∧ (T (t:ℂ) f x).im = 0 := by
  have hi : (∫ y, (y:ℂ) * f y ∂μ) = ((∫ y, y * (f y).re ∂μ : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hy.2]
  have hq : 0 ≤ ∫ y, y * (f y).re ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_interval, hf] with y hy hfy
    exact mul_nonneg hy.1.le hfy.1
  have he : 0 ≤ 1 - Real.exp (-t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  filter_upwards [T_rep (t:ℂ) f, ae_interval, hf] with x hx hxi hfx
  rw [hx, hi]
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, Complex.one_re, Complex.one_im, mul_zero]
    positivity
  · simp [Complex.mul_im, hfx.2]

private lemma T_linf_bound (t : ℝ) (ht : 0 ≤ t) (f : H) (hf : MemLp f ∞ μ) :
    eLpNorm (T (t:ℂ) f) ∞ μ ≤ ENNReal.ofReal (3/2 : ℝ) * eLpNorm f ∞ μ := by
  let b : ℝ := lpNorm f ∞ μ
  have hb : 0 ≤ b := lpNorm_nonneg
  have hq : ‖∫ y, (y:ℂ) * f y ∂μ‖ ≤ b/2 := by
    calc
      _ ≤ ∫ y, y*b ∂μ := by
        apply norm_integral_le_of_norm_le (integrable_linear.mul_const b)
        filter_upwards [ae_interval, ae_le_lpNorm_exponent_top hf] with y hy hfy
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy.1]
        exact mul_le_mul_of_nonneg_left hfy hy.1.le
      _ = b/2 := by rw [integral_mul_const, integral_linear]; ring
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hout : ∀ᵐ x ∂μ, ‖T (t:ℂ) f x‖ ≤ (3/2)*b := by
    filter_upwards [T_rep (t:ℂ) f, ae_interval, ae_le_lpNorm_exponent_top hf] with x hx hxi hfx
    have hp : ‖3 * (x:ℂ) * ∫ y, (y:ℂ)*f y ∂μ‖ ≤ (3/2)*b := by
      simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi.1]
      have hmul := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 3*x)
      have hx0 := hxi.1
      have hx1 := hxi.2
      nlinarith
    rw [hx]
    calc
      _ ≤ ‖Complex.exp (-(t:ℂ)) * f x‖ +
          ‖(1 - Complex.exp (-(t:ℂ))) * (3*(x:ℂ)*∫ y, (y:ℂ)*f y ∂μ)‖ := norm_add_le _ _
      _ = Real.exp (-t)*‖f x‖ + (1 - Real.exp (-t))*‖3*(x:ℂ)*∫ y, (y:ℂ)*f y ∂μ‖ := by
        simp only [norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos he0, abs_of_nonneg (sub_nonneg.mpr he1)]
      _ ≤ Real.exp (-t)*b + (1 - Real.exp (-t))*((3/2)*b) := by gcongr
      _ ≤ (3/2)*b := by nlinarith
  calc
    _ ≤ ENNReal.ofReal ((3/2)*b) := by
      simpa using eLpNorm_le_of_ae_bound (Lp.aestronglyMeasurable (T (t:ℂ) f)) hout
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ofReal_lpNorm hf]

/-- The source convention is linear in u, conjugate-linear in v. Lean's
inner product is conjugate-linear in its first argument, hence this order. -/
def form (u v : H) : ℂ := ⟪v, A u⟫_ℂ

/-- The full-domain form norm, not a substitute for the essential sup norm. -/
def formNorm (u : H) : ℝ := Real.sqrt (‖u‖ ^ 2 + (form u u).re)

private lemma form_diagonal (u : H) : form u u = (‖A u‖ ^ 2 : ℝ) := A_inner u

private lemma formNorm_bounds (u : H) :
    ‖u‖ ≤ formNorm u ∧ formNorm u ≤ Real.sqrt 2 * ‖u‖ := by
  have ha : ‖A u‖ ≤ ‖u‖ := by
    rw [A_orth]
    exact Submodule.norm_starProjection_apply_le _ _
  have hnorm : formNorm u ^ 2 = ‖u‖ ^ 2 + ‖A u‖ ^ 2 := by
    rw [formNorm, form_diagonal, Complex.ofReal_re, Real.sq_sqrt (by positivity)]
  have hn : 0 ≤ formNorm u := Real.sqrt_nonneg _
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 2 * ‖u‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  constructor <;> nlinarith [norm_nonneg u, norm_nonneg (A u)]

private lemma form_closed (s : ℕ → H)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      formNorm (s m - s n) < ε) :
    ∃ u : H, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      formNorm (s n - u) < ε := by
  have hc : CauchySeq s := Metric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm]
      exact (formNorm_bounds _).1.trans_lt (hN m hm n hn)⟩)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨u, fun ε hε => ?_⟩
  have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hu) (ε / Real.sqrt 2) (div_pos hε hsq)
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [dist_eq_norm] at hd
  calc
    formNorm (s n - u) ≤ Real.sqrt 2 * ‖s n - u‖ := (formNorm_bounds _).2
    _ < ε := by nlinarith [(lt_div_iff₀ hsq).mp hd]

end D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
