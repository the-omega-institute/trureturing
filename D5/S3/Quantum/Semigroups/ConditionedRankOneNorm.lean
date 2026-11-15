/- GID: D5/S3/Quantum/Semigroups/ConditionedRankOneNorm
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/ConditionedRankOneNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipped weights attain the sharp condition-constrained complex essential-sup bound for positive rank-one evolutions. -/

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! The measure is arbitrary, finite and nonzero; atoms are allowed.
Admission basis: escape-witness, preregistration #30862. The fixed_weight
construction proves the actual all-complex-input bound and reciprocal-weight
norm attainment, using the two-sided affine_top essential-norm identity.
This construction is on the live path to conditioned_optimum. The preregistered
fixed-weight least constant, actual norm inequalities and attaining input cover
this content; the essential-envelope comparison is a consumed bind-only step.
No claim of external novelty or open-problem resolution is made.
Direct frozen D5 dependencies: none; the suppliers are pinned Mathlib.
The general analytic declarations do not implement a finite certificate,
checker, numerical reduction or certified instance; utility is none.

Per-declaration proof shape and live consumers:
  envelope: bind-only; consumer=variational_excess. The upstream product bound,
    AE norm bounds and scalar normalization give the condition-budget estimate.
  fixed_weight: content; witness=the all-complex-input integral estimate and
    reciprocal-weight norm attainment; consumer=conditioned_optimum.
  conditioned_optimum: content; witness=the fixed_weight norm-attainment
    construction, used for the clipped optimizer and every admissible weight;
    consumer=PositiveRankOneWeightObstruction.conditioned_weight_optimum.
  affine_top: content; witness=the two-sided affine essential-norm identity,
    including the reverse estimate for a positive coefficient;
    consumer=fixed_weight.
  top_le: bind-only; consumers=height_le, clipped_weight, clipped_height,
    affine_top.
  top_pos: bind-only; consumers=clipped_weight, clipped_height,
    clipped_envelope, excess_zero_iff.
  mul_top, bounded_integrable: bind-only; consumers=square_integrable,
    fixed_weight, variational_excess, excess_zero_iff, optimum_one_iff.
  height_le: bind-only; specialization of the pinned essential-sup product
    bound to (1/g)*(g*h), with AE cancellation and finite norm conversion;
    consumers=envelope, clipped_height.
  clipped_weight: bind-only; consumers=clipped_height, conditioned_optimum.
  clipped_height: bind-only; consumers=excess_zero_iff, conditioned_optimum.
  square_integrable: bind-only; consumers=square_pos, variational_excess.
  square_pos: bind-only; consumers=fixed_weight, variational_excess,
    optimum_one_iff, conditioned_optimum.
  max_bounded: bind-only; consumers=variational_excess, excess_zero_iff,
    optimum_one_iff.
  clipped_envelope: bind-only; consumers=excess_zero_iff, conditioned_optimum.
  variational_excess, excess_zero_iff, optimum_one_iff: bind-only;
    consumer=conditioned_optimum.
  Weight, condition, evolve, Sharp, clipped, optimum: definitions consumed by
    the displayed theorems and the original interval semigroup.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace D5.S3.Quantum.Semigroups.ConditionedRankOneNorm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- All positive weights giving equivalent essential-sup norms. -/
structure Weight (μ : Measure X) (g : X → ℝ) : Prop where
  bounded : MemLp g ∞ μ
  inv_bounded : MemLp (fun x => (g x)⁻¹) ∞ μ
  positive : ∀ᵐ x ∂μ, 0 < g x

/-- The actual condition number of the multiplication operator. -/
def condition (μ : Measure X) (g : X → ℝ) : ℝ :=
  lpNorm g ∞ μ * lpNorm (fun x => (g x)⁻¹) ∞ μ

/-- The original complex rank-one evolution on raw representatives. -/
def evolve (μ : Measure X) (h : X → ℝ) (a : ℝ) (f : X → ℂ) : X → ℂ :=
  fun x => (a : ℂ) * f x + (1 - (a : ℂ)) *
    ((h x : ℂ) * (∫ y, (h y : ℂ) * f y ∂μ) / (∫ y, h y ^ 2 ∂μ : ℝ))

/-- A genuine all-input essential-sup estimate with a normalized attaining input.
The constant is not defined by a scalar norm formula. -/
def Sharp (μ : Measure X) (h : X → ℝ) (a : ℝ) (g : X → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧
  (∀ f : X → ℂ, MemLp f ∞ μ → MemLp f 2 μ →
    eLpNorm (fun x => (g x : ℂ) * evolve μ h a f x) ∞ μ ≤
      ENNReal.ofReal C * eLpNorm (fun x => (g x : ℂ) * f x) ∞ μ) ∧
  ∃ f : X → ℂ, MemLp f ∞ μ ∧ MemLp f 2 μ ∧
    eLpNorm (fun x => (g x : ℂ) * f x) ∞ μ = 1 ∧
    eLpNorm (fun x => (g x : ℂ) * evolve μ h a f x) ∞ μ = ENNReal.ofReal C

/-- The clipped feasible weight; its condition number may be below the budget. -/
def clipped (h : X → ℝ) (H κ : ℝ) : X → ℝ :=
  fun x => (max 1 (κ * h x / H))⁻¹

private lemma top_le {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : MemLp f ∞ μ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    lpNorm f ∞ μ ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_lpNorm hf]
  simpa using (eLpNorm_le_of_ae_bound (p := ∞) hf.aestronglyMeasurable hb)

private lemma top_pos [NeZero μ] {f : X → ℝ} (hf : MemLp f ∞ μ)
    (hp : ∀ᵐ x ∂μ, 0 < f x) : 0 < lpNorm f ∞ μ := by
  apply lt_of_le_of_ne lpNorm_nonneg
  intro hz
  have he := (lpNorm_eq_zero hf (by simp)).mp hz.symm
  have : ∀ᵐ x ∂μ, False := by
    filter_upwards [hp, he] with x hx hy
    exact (ne_of_gt hx) hy
  exact (NeZero.ne μ) (by simpa using this)

private lemma mul_top {f g : X → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    MemLp (fun x => f x * g x) ∞ μ := by
  exact hf.fun_mul hg

private lemma bounded_integrable [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : MemLp f ∞ μ) : Integrable f μ :=
  (hf.mono_exponent (by simp : (1 : ℝ≥0∞) ≤ ∞)).integrable (by simp)

private lemma height_le [NeZero μ] {h g : X → ℝ} (hh : MemLp h ∞ μ)
    (wg : Weight μ g) :
    lpNorm h ∞ μ ≤ lpNorm (fun x => (g x)⁻¹) ∞ μ *
      lpNorm (fun x => g x * h x) ∞ μ := by
  have hm := mul_top wg.bounded hh
  apply top_le hh (mul_nonneg lpNorm_nonneg lpNorm_nonneg)
  filter_upwards [wg.positive, ae_le_lpNorm_exponent_top wg.inv_bounded,
    ae_le_lpNorm_exponent_top hm] with x hp hb hc
  calc
    ‖h x‖ = ‖(g x)⁻¹ * (g x * h x)‖ := by rw [inv_mul_cancel_left₀ (ne_of_gt hp)]
    _ = ‖(g x)⁻¹‖ * ‖g x * h x‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul hb hc (norm_nonneg _) lpNorm_nonneg

/-- The all-weight essential envelope forced by a condition-number budget. -/
theorem envelope [NeZero μ] {h g : X → ℝ} (hh : MemLp h ∞ μ)
    (wg : Weight μ g) {κ : ℝ}
    (hκ : 1 ≤ κ) (hk : condition μ g ≤ κ) :
    ∀ᵐ x ∂μ, max (h x) (lpNorm h ∞ μ / κ) ≤
      lpNorm (fun y => g y * h y) ∞ μ / g x := by
  let H := lpNorm h ∞ μ
  let G := lpNorm g ∞ μ
  let B := lpNorm (fun x => (g x)⁻¹) ∞ μ
  let c := lpNorm (fun x => g x * h x) ∞ μ
  have hH : 0 ≤ H := lpNorm_nonneg
  have hB : 0 ≤ B := lpNorm_nonneg
  have hc : 0 ≤ c := lpNorm_nonneg
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hheight : H ≤ B*c := height_le hh wg
  have hbudget : G*B ≤ κ := hk
  filter_upwards [wg.positive, ae_le_lpNorm_exponent_top wg.bounded,
    ae_le_lpNorm_exponent_top (mul_top wg.bounded hh)] with x hg hG hgh
  have hG' : g x ≤ G := (le_abs_self _).trans hG
  have hgh' : g x * h x ≤ c := (le_abs_self _).trans hgh
  apply max_le
  · exact (le_div_iff₀ hg).mpr (by nlinarith only [hgh'])
  · apply (div_le_div_iff₀ hκ0 hg).mpr
    calc
      H * g x ≤ (B*c) * g x := mul_le_mul_of_nonneg_right hheight hg.le
      _ ≤ (B*c) * G := mul_le_mul_of_nonneg_left hG' (mul_nonneg hB hc)
      _ = c*(G*B) := by ring
      _ ≤ c*κ := mul_le_mul_of_nonneg_left hbudget hc

private lemma clipped_weight [NeZero μ] {h : X → ℝ} (hh : MemLp h ∞ μ)
    (hp : ∀ᵐ x ∂μ, 0 < h x) {κ : ℝ} (hκ : 1 ≤ κ) :
    Weight μ (clipped h (lpNorm h ∞ μ) κ) ∧
    lpNorm (clipped h (lpNorm h ∞ μ) κ) ∞ μ ≤ 1 ∧
    lpNorm (fun x => (clipped h (lpNorm h ∞ μ) κ x)⁻¹) ∞ μ ≤ κ := by
  let H := lpNorm h ∞ μ
  have hH : 0 < H := top_pos hh hp
  have hk0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hm : AEStronglyMeasurable (fun x => max 1 (κ*h x/H)) μ :=
    (aemeasurable_const.max ((hh.aestronglyMeasurable.aemeasurable.const_mul κ).div_const H)).aestronglyMeasurable
  have hmax : ∀ᵐ x ∂μ, 1 ≤ max 1 (κ*h x/H) ∧ max 1 (κ*h x/H) ≤ κ := by
    filter_upwards [ae_le_lpNorm_exponent_top hh] with x hx
    refine ⟨le_max_left _ _, max_le hκ ?_⟩
    apply (div_le_iff₀ hH).mpr
    have : h x ≤ H := (le_abs_self _).trans hx
    nlinarith
  have hg : MemLp (clipped h H κ) ∞ μ := by
    apply memLp_top_of_bound hm.aemeasurable.inv.aestronglyMeasurable 1
    filter_upwards [hmax] with x hx
    dsimp [clipped]
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hx.1))]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hx.1)).mpr hx.1
  have hgi : MemLp (fun x => (clipped h H κ x)⁻¹) ∞ μ := by
    apply memLp_top_of_bound (by simpa [clipped] using hm) κ
    filter_upwards [hmax] with x hx
    simpa [clipped, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx.1)] using hx.2
  refine ⟨⟨hg, hgi, ?_⟩, ?_, ?_⟩
  · exact ae_of_all _ fun x => inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  · apply top_le hg zero_le_one
    filter_upwards [hmax] with x hx
    simpa [clipped, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx.1)]
      using (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hx.1)).mpr hx.1
  · apply top_le hgi hk0.le
    filter_upwards [hmax] with x hx
    simpa [clipped, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx.1)] using hx.2

private lemma clipped_height [NeZero μ] {h : X → ℝ} (hh : MemLp h ∞ μ)
    (hp : ∀ᵐ x ∂μ, 0 < h x) {κ : ℝ} (hκ : 1 ≤ κ) :
    lpNorm (fun x => clipped h (lpNorm h ∞ μ) κ x * h x) ∞ μ =
      lpNorm h ∞ μ / κ := by
  let H := lpNorm h ∞ μ
  let g := clipped h H κ
  have hH : 0 < H := top_pos hh hp
  have hk0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  obtain ⟨wg, hG, hB⟩ := clipped_weight hh hp hκ
  apply le_antisymm
  · apply top_le (mul_top wg.bounded hh) (div_nonneg hH.le hk0.le)
    filter_upwards [hp] with x hx
    change ‖(max 1 (κ*h x/H))⁻¹ * h x‖ ≤ H/κ
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 (κ*h x/H)))) hx)]
    rw [inv_mul_eq_div]
    apply (div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hk0).mpr
    have hm := le_max_right 1 (κ*h x/H)
    have hm' := (div_le_iff₀ hH).mp hm
    nlinarith
  · apply (div_le_iff₀ hk0).mpr
    have hc : 0 ≤ lpNorm (fun x => g x * h x) ∞ μ := lpNorm_nonneg
    exact (height_le hh wg).trans (by nlinarith)

private lemma square_integrable [IsFiniteMeasure μ] {h : X → ℝ} (hh : MemLp h ∞ μ) :
    Integrable (fun x => h x ^ 2) μ := by
  simpa only [pow_two] using bounded_integrable (mul_top hh hh)

private lemma square_pos [IsFiniteMeasure μ] [NeZero μ] {h : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) : 0 < ∫ x, h x ^ 2 ∂μ := by
  have hn : ∀ᵐ x ∂μ, 0 ≤ h x ^ 2 := ae_of_all _ fun x => sq_nonneg _
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg_ae hn (square_integrable hh)).mp hz.symm
  have : ∀ᵐ x ∂μ, False := by
    filter_upwards [hp, he] with x hx he
    change h x ^ 2 = 0 at he
    nlinarith
  exact (NeZero.ne μ) (by simpa using this)

private lemma affine_top [NeZero μ] {q : X → ℝ} (hq : MemLp q ∞ μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ q x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lpNorm (fun x => a + b*q x) ∞ μ = a + b*lpNorm q ∞ μ := by
  have hm : MemLp (fun x => a + b*q x) ∞ μ := (memLp_top_const a).add (hq.const_mul b)
  have hn : ∀ᵐ x ∂μ, 0 ≤ a + b*q x := hp.mono fun x hx => by positivity
  have hbound : ∀ᵐ x ∂μ, a + b*q x ≤ lpNorm (fun x => a+b*q x) ∞ μ := by
    filter_upwards [ae_le_lpNorm_exponent_top hm] with x hx
    exact (le_abs_self _).trans hx
  apply le_antisymm
  · apply top_le hm (add_nonneg ha (mul_nonneg hb lpNorm_nonneg))
    filter_upwards [hp, ae_le_lpNorm_exponent_top hq] with x hx hqx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqx) hb) a
  · by_cases hb0 : b = 0
    · simp [hb0, lpNorm_const (p := ∞) (μ := μ) (by simp) (NeZero.ne μ), Real.norm_eq_abs, abs_of_nonneg ha]
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    obtain ⟨x, hx, hbx⟩ := (hp.and hbound).exists
    have hD : 0 ≤ (lpNorm (fun x => a+b*q x) ∞ μ - a)/b := by
      apply div_nonneg _ hb
      nlinarith
    have hle : lpNorm q ∞ μ ≤ (lpNorm (fun x => a+b*q x) ∞ μ - a)/b := by
      apply top_le hq hD
      filter_upwards [hp, hbound] with x hx hbx
      rw [Real.norm_eq_abs, abs_of_nonneg hx]
      exact (le_div_iff₀ hb').mpr (by nlinarith)
    have := (le_div_iff₀ hb').mp hle
    nlinarith

/-- The fixed-weight sharp constant for all bounded complex inputs, with the
actual attaining input equal almost everywhere to the reciprocal weight. -/
theorem fixed_weight [IsFiniteMeasure μ] [NeZero μ] {h g : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) (wg : Weight μ g)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Sharp μ h a g (a + (1-a) * lpNorm (fun x => g x*h x) ∞ μ *
      (∫ x, h x / g x ∂μ) / (∫ x, h x ^ 2 ∂μ)) := by
  let Q := ∫ x, h x ^ 2 ∂μ
  let J := ∫ x, h x / g x ∂μ
  let c := lpNorm (fun x => g x*h x) ∞ μ
  have hQ : 0 < Q := square_pos hh hp
  have hJint : Integrable (fun x => h x / g x) μ := by
    simpa only [div_eq_mul_inv] using bounded_integrable (mul_top hh wg.inv_bounded)
  have hJ : 0 ≤ J := integral_nonneg_of_ae (by
    filter_upwards [hp, wg.positive] with x hx hg
    exact (div_pos hx hg).le)
  have hc : 0 ≤ c := lpNorm_nonneg
  have hm := mul_top wg.bounded hh
  have hcoef : 0 ≤ (1-a)*J/Q := by positivity
  have hC : 0 ≤ a + (1-a)*c*J/Q := by positivity
  have hmeas (f : X → ℂ) (hf : MemLp f ∞ μ) :
      AEStronglyMeasurable (fun x => (g x : ℂ)*evolve μ h a f x) μ := by
    simp only [evolve, div_eq_mul_inv]
    exact wg.bounded.ofReal.aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.const_mul _).add
        (((hh.ofReal.aestronglyMeasurable.mul_const _).mul_const _).const_mul _))
  refine ⟨hC, ?_, ?_⟩
  · intro f hf hf2
    have hgf : MemLp (fun x => (g x : ℂ)*f x) ∞ μ := wg.bounded.ofReal.fun_mul hf
    let b := lpNorm (fun x => (g x : ℂ)*f x) ∞ μ
    have hb : 0 ≤ b := lpNorm_nonneg
    have hint : ‖∫ y, (h y : ℂ)*f y ∂μ‖ ≤ J*b := by
      calc
        _ ≤ ∫ y, h y/g y*b ∂μ := by
          apply norm_integral_le_of_norm_le (hJint.mul_const b)
          filter_upwards [hp, wg.positive, ae_le_lpNorm_exponent_top hgf] with y hy hg hfy
          have he : (h y : ℂ)*f y = ((h y/g y : ℝ):ℂ)*((g y:ℂ)*f y) := by
            push_cast
            field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hg)]
          rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos hy hg)]
          exact mul_le_mul_of_nonneg_left hfy (div_pos hy hg).le
        _ = J*b := integral_mul_const _ _
    have hout : ∀ᵐ x ∂μ, ‖(g x : ℂ)*evolve μ h a f x‖ ≤
        (a+(1-a)*c*J/Q)*b := by
      filter_upwards [hp, wg.positive, ae_le_lpNorm_exponent_top hgf,
        ae_le_lpNorm_exponent_top hm] with x hx hg hfx hcx
      have hcx' : g x*h x ≤ c := (le_abs_self _).trans hcx
      have he : (g x:ℂ)*evolve μ h a f x =
          (a:ℂ)*((g x:ℂ)*f x) + ((1-a)/Q : ℝ)*((g x*h x:ℝ):ℂ)*
            (∫ y, (h y:ℂ)*f y ∂μ) := by
        dsimp [evolve, Q]
        push_cast
        ring
      rw [he]
      calc
        _ ≤ ‖(a:ℂ)*((g x:ℂ)*f x)‖ +
          ‖(((1-a)/Q : ℝ):ℂ)*((g x*h x:ℝ):ℂ)*(∫ y, (h y:ℂ)*f y ∂μ)‖ := norm_add_le _ _
        _ = a*‖(g x:ℂ)*f x‖ + ((1-a)/Q)*(g x*h x)*‖∫ y, (h y:ℂ)*f y ∂μ‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ha, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ha1) hQ.le),
            abs_of_pos hg, abs_of_pos hx]
        _ ≤ a*b + ((1-a)/Q)*c*(J*b) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ ENNReal.ofReal ((a+(1-a)*c*J/Q)*b) := by simpa using (eLpNorm_le_of_ae_bound (p := ∞) (hmeas f hf) hout)
      _ = _ := by rw [ENNReal.ofReal_mul hC, ofReal_lpNorm hgf]
  · let f : X → ℂ := fun x => ((g x)⁻¹ : ℝ)
    have hf : MemLp f ∞ μ := wg.inv_bounded.ofReal
    have hin : eLpNorm (fun x => (g x:ℂ)*f x) ∞ μ = 1 := by
      calc
        _ = eLpNorm (fun _ : X => (1:ℂ)) ∞ μ := by
          apply eLpNorm_congr_ae
          filter_upwards [wg.positive] with x hx
          simp [f, ne_of_gt hx]
        _ = 1 := by simp [eLpNorm_const, NeZero.ne μ]
    refine ⟨f, hf, hf.mono_exponent (by simp), hin, ?_⟩
    have hint : (∫ y, (h y:ℂ)*f y ∂μ) = (J:ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [f, J, div_eq_mul_inv]
    have hrep : (fun x => (g x:ℂ)*evolve μ h a f x) =ᵐ[μ]
        (fun x => ((a + ((1-a)*J/Q)*(g x*h x):ℝ):ℂ)) := by
      filter_upwards [wg.positive] with x hx
      change (g x:ℂ) * ((a:ℂ)*f x + (1-(a:ℂ))*
        ((h x:ℂ)*(∫ y, (h y:ℂ)*f y ∂μ)/(Q:ℂ))) = _
      rw [hint]
      dsimp [f]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hx)]
    have hreal : MemLp (fun x => a + ((1-a)*J/Q)*(g x*h x)) ∞ μ :=
      (memLp_top_const a).add (hm.const_mul _)
    calc
      _ = eLpNorm (fun x => ((a + ((1-a)*J/Q)*(g x*h x):ℝ):ℂ)) ∞ μ := eLpNorm_congr_ae hrep
      _ = eLpNorm (fun x => a + ((1-a)*J/Q)*(g x*h x)) ∞ μ := by
        apply eLpNorm_congr_norm_ae hreal.ofReal.aestronglyMeasurable hreal.aestronglyMeasurable
        exact ae_of_all _ fun x => Complex.norm_real _
      _ = ENNReal.ofReal (a + ((1-a)*J/Q)*c) := by
        rw [← ofReal_lpNorm hreal, affine_top hm (by
          filter_upwards [wg.positive, hp] with x hg hx
          exact (mul_pos hg hx).le) ha hcoef]
      _ = _ := by congr 1; ring

private lemma max_bounded {h : X → ℝ} (hh : MemLp h ∞ μ) (d : ℝ) :
    MemLp (fun x => max (h x) d) ∞ μ := by
  apply memLp_top_of_bound
    ((hh.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable)
    (max (lpNorm h ∞ μ) |d|)
  filter_upwards [ae_le_lpNorm_exponent_top hh] with x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hl := (abs_le.mp hx).1
    exact (neg_le_neg (le_max_left _ _)).trans (hl.trans (le_max_left _ _))
  · exact max_le (((le_abs_self _).trans hx).trans (le_max_left _ _))
      ((le_abs_self _).trans (le_max_right _ _))

private lemma clipped_envelope [NeZero μ] {h : X → ℝ} (hh : MemLp h ∞ μ)
    (hp : ∀ᵐ x ∂μ, 0 < h x) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∀ x, (lpNorm h ∞ μ / κ) / clipped h (lpNorm h ∞ μ) κ x =
      max (h x) (lpNorm h ∞ μ / κ) := by
  let H := lpNorm h ∞ μ
  have hH : 0 < H := top_pos hh hp
  have hk0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  intro x
  change H/κ / (max 1 (κ*h x/H))⁻¹ = max (h x) (H/κ)
  rw [div_inv_eq_mul]
  by_cases hx : h x ≤ H/κ
  · have hm : κ*h x/H ≤ 1 := (div_le_iff₀ hH).mpr (by
      have := (le_div_iff₀ hk0).mp hx
      nlinarith)
    rw [max_eq_left hm, max_eq_right hx, mul_one]
  · have hx' := le_of_lt (lt_of_not_ge hx)
    have hm : 1 ≤ κ*h x/H := (le_div_iff₀ hH).mpr (by
      have := (div_le_iff₀ hk0).mp hx'
      nlinarith)
    rw [max_eq_right hm, max_eq_left hx']
    field_simp

/-- The explicit optimum value; `Sharp` separately expresses its genuine
operator meaning through all complex inputs and norm attainment. -/
def optimum (μ : Measure X) (h : X → ℝ) (a κ : ℝ) : ℝ :=
  1 + (1-a) / (∫ x, h x ^ 2 ∂μ) *
    ∫ x, h x * max (lpNorm h ∞ μ / κ - h x) 0 ∂μ

private lemma variational_excess [IsFiniteMeasure μ] [NeZero μ] {h g : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) (wg : Weight μ g)
    {κ a : ℝ} (hκ : 1 ≤ κ) (hk : condition μ g ≤ κ) :
    (a+(1-a)*lpNorm (fun x => g x*h x) ∞ μ * (∫ x, h x/g x ∂μ) /
      (∫ x, h x^2 ∂μ)) - optimum μ h a κ =
    (1-a)/(∫ x, h x^2 ∂μ) * ∫ x, h x *
      |lpNorm (fun y => g y*h y) ∞ μ / g x - max (h x) (lpNorm h ∞ μ/κ)| ∂μ := by
  let c := lpNorm (fun x => g x*h x) ∞ μ
  let d := lpNorm h ∞ μ/κ
  have hv := max_bounded hh d
  have hd := max_bounded ((memLp_top_const d).sub hh) 0
  have hi := bounded_integrable (mul_top hh wg.inv_bounded)
  have hiv := bounded_integrable (mul_top hh hv)
  have hid : Integrable (fun x => h x * max (d-h x) 0) μ :=
    bounded_integrable (mul_top hh hd)
  have hic : Integrable (fun x => h x*(c/g x)) μ := by
    convert hi.const_mul c using 1
    ext x
    simp only [div_eq_mul_inv]
    ring
  have he : ∀ᵐ x ∂μ, |c/g x - max (h x) d| = c/g x - max (h x) d := by
    filter_upwards [envelope hh wg hκ hk] with x hx
    exact abs_of_nonneg (sub_nonneg.mpr hx)
  have hint : (∫ x, h x * |c/g x - max (h x) d| ∂μ) =
      c * (∫ x, h x/g x ∂μ) - ∫ x, h x * max (h x) d ∂μ := by
    calc
      _ = ∫ x, h x*(c/g x) - h x*max (h x) d ∂μ := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
        ring
      _ = _ := by
        rw [integral_sub hic hiv]
        congr 1
        convert integral_const_mul c (fun x => h x/g x) using 1
        congr 1
        ext x
        ring
  have hsplit : (∫ x, h x * max (h x) d ∂μ) =
      (∫ x, h x^2 ∂μ) + ∫ x, h x * max (d-h x) 0 ∂μ := by
    rw [← integral_add (square_integrable hh) hid]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change h x * max (h x) d = h x^2 + h x * max (d-h x) 0
      by_cases hx : d ≤ h x
      · rw [max_eq_left hx, max_eq_right (sub_nonpos.mpr hx)]
        ring
      · have hx' := le_of_lt (lt_of_not_ge hx)
        rw [max_eq_right hx', max_eq_left (sub_nonneg.mpr hx')]
        ring
  rw [hint, hsplit]
  let Q := ∫ x, h x^2 ∂μ
  let J := ∫ x, h x/g x ∂μ
  let D := ∫ x, h x * max (d-h x) 0 ∂μ
  change a+(1-a)*c*J/Q - (1+(1-a)/Q*D) = (1-a)/Q*(c*J-(Q+D))
  have hQ : Q ≠ 0 := ne_of_gt (square_pos hh hp)
  field_simp [hQ]
  <;> ring

private lemma excess_zero_iff [IsFiniteMeasure μ] [NeZero μ] {h g : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) (wg : Weight μ g)
    {κ : ℝ} (hκ : 1 ≤ κ) :
    (∫ x, h x * |lpNorm (fun y => g y*h y) ∞ μ / g x -
      max (h x) (lpNorm h ∞ μ/κ)| ∂μ) = 0 ↔
      ∃ s : ℝ, 0 < s ∧ g =ᵐ[μ] (fun x => s*clipped h (lpNorm h ∞ μ) κ x) := by
  let c := lpNorm (fun y => g y*h y) ∞ μ
  let d := lpNorm h ∞ μ/κ
  let v := fun x => max (h x) d
  let w := clipped h (lpNorm h ∞ μ) κ
  have hd : 0 < d := div_pos (top_pos hh hp) (zero_lt_one.trans_le hκ)
  have hc : 0 < c := top_pos (mul_top wg.bounded hh) (by
    filter_upwards [wg.positive, hp] with x hx hy
    exact mul_pos hx hy)
  have hw : ∀ x, 0 < w x := fun x => inv_pos.mpr
    (zero_lt_one.trans_le (le_max_left _ _))
  have hv : ∀ x, 0 < v x := fun x => hd.trans_le (le_max_right _ _)
  have hcvm := (wg.inv_bounded.const_mul c).sub (max_bounded hh d)
  have hi : Integrable (fun x => h x*|c/g x-v x|) μ := by
    apply bounded_integrable
    convert mul_top hh hcvm.norm using 1
    ext x
    simp [Real.norm_eq_abs, v, div_eq_mul_inv]
  have hn : ∀ᵐ x ∂μ, 0 ≤ h x*|c/g x-v x| := by
    filter_upwards [hp] with x hx
    exact mul_nonneg hx.le (abs_nonneg _)
  constructor
  · intro hz
    have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    refine ⟨c/d, div_pos hc hd, ?_⟩
    filter_upwards [he, hp, wg.positive] with x hx hhx hgx
    change h x * |c/g x-v x| = 0 at hx
    have hz' := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hhx)
    have heq : c/g x = v x := sub_eq_zero.mp (abs_eq_zero.mp hz')
    have hew : d/w x = v x := clipped_envelope hh hp hκ x
    have hgval : g x = c/v x := by
      apply (eq_div_iff (ne_of_gt (hv x))).mpr
      have := (div_eq_iff (ne_of_gt hgx)).mp heq
      nlinarith
    have hwval : w x = d/v x := by
      apply (eq_div_iff (ne_of_gt (hv x))).mpr
      have := (div_eq_iff (ne_of_gt (hw x))).mp hew
      nlinarith
    change g x = c/d*w x
    rw [hgval, hwval]
    field_simp
  · rintro ⟨s, hs, he⟩
    have heprod : (fun x => g x*h x) =ᵐ[μ] (s • fun x => w x*h x) := by
      filter_upwards [he] with x hx
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hx]
      ring
    have hcs : c = s*d := by
      calc
        c = lpNorm (s • fun x => w x*h x) ∞ μ :=
          congrArg ENNReal.toReal (eLpNorm_congr_ae heprod)
        _ = s*d := by
          rw [lpNorm_const_smul]
          simp only [Real.nnnorm_of_nonneg hs.le, NNReal.coe_mk]
          rw [clipped_height hh hp hκ]
    apply integral_eq_zero_of_ae
    filter_upwards [he] with x hx
    change h x * |c/g x-v x| = 0
    have henv : d/w x = v x := clipped_envelope hh hp hκ x
    rw [hcs, hx, mul_div_mul_left _ _ (ne_of_gt hs), henv, sub_self, abs_zero, mul_zero]

private lemma optimum_one_iff [IsFiniteMeasure μ] [NeZero μ] {h : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) {a κ : ℝ} (ha : a < 1) :
    optimum μ h a κ = 1 ↔ ∀ᵐ x ∂μ, lpNorm h ∞ μ/κ ≤ h x := by
  let d := lpNorm h ∞ μ/κ
  have hd := max_bounded ((memLp_top_const d).sub hh) 0
  have hi : Integrable (fun x => h x*max (d-h x) 0) μ := bounded_integrable (mul_top hh hd)
  have hn : ∀ᵐ x ∂μ, 0 ≤ h x*max (d-h x) 0 := by
    filter_upwards [hp] with x hx
    exact mul_nonneg hx.le (le_max_right _ _)
  have hc : (1-a)/(∫ x, h x^2 ∂μ) ≠ 0 :=
    ne_of_gt (div_pos (sub_pos.mpr ha) (square_pos hh hp))
  constructor
  · intro he
    have hz : (∫ x, h x*max (d-h x) 0 ∂μ) = 0 := by
      apply (mul_eq_zero.mp (show (1-a)/(∫ x, h x^2 ∂μ) *
        (∫ x, h x*max (d-h x) 0 ∂μ) = 0 by
          change 1 + _ = 1 at he
          linarith)).resolve_left hc
    have heq := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    filter_upwards [heq, hp] with x hx hp
    change h x*max (d-h x) 0 = 0 at hx
    have hz' := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hp)
    have := (le_max_left (d-h x) 0).trans_eq hz'
    linarith
  · intro hf
    have hz : (∫ x, h x*max (d-h x) 0 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hf] with x hx
      change h x * max (d-h x) 0 = 0
      rw [max_eq_right (sub_nonpos.mpr hx), mul_zero]
    change 1 + _ * (∫ x, h x*max (d-h x) 0 ∂μ) = 1
    rw [hz, mul_zero, add_zero]

/-- Clipping attains the minimum over every condition-constrained positive
weight, for every bounded complex input. The excess is a weighted L1 quantity. -/
theorem conditioned_optimum [IsFiniteMeasure μ] [NeZero μ] {h : X → ℝ}
    (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) {κ a : ℝ}
    (hκ : 1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Weight μ (clipped h (lpNorm h ∞ μ) κ) ∧
    condition μ (clipped h (lpNorm h ∞ μ) κ) ≤ κ ∧
    Sharp μ h a (clipped h (lpNorm h ∞ μ) κ) (optimum μ h a κ) ∧
    ∀ g : X → ℝ, Weight μ g → condition μ g ≤ κ →
      ∃ C : ℝ, Sharp μ h a g C ∧ optimum μ h a κ ≤ C ∧
        C - optimum μ h a κ = (1-a)/(∫ x, h x^2 ∂μ) *
          ∫ x, h x * |lpNorm (fun y => g y*h y) ∞ μ / g x -
            max (h x) (lpNorm h ∞ μ/κ)| ∂μ ∧
        (a < 1 → (C = optimum μ h a κ ↔ ∃ s : ℝ, 0 < s ∧
          g =ᵐ[μ] (fun x => s*clipped h (lpNorm h ∞ μ) κ x))) ∧
        (a = 1 → C = 1) ∧
        (a < 1 → (optimum μ h a κ = 1 ↔ ∀ᵐ x ∂μ, lpNorm h ∞ μ/κ ≤ h x)) := by
  obtain ⟨wg, hG, hB⟩ := clipped_weight hh hp hκ
  have hk : condition μ (clipped h (lpNorm h ∞ μ) κ) ≤ κ := by
    unfold condition
    calc
      _ ≤ 1*κ := mul_le_mul hG hB lpNorm_nonneg zero_le_one
      _ = κ := one_mul κ
  refine ⟨wg, hk, ?_, ?_⟩
  · have he := variational_excess hh hp wg hκ hk (a := a)
    have hz : (∫ x, h x * |lpNorm (fun y => clipped h (lpNorm h ∞ μ) κ y*h y) ∞ μ /
        clipped h (lpNorm h ∞ μ) κ x - max (h x) (lpNorm h ∞ μ/κ)| ∂μ) = 0 := by
      rw [clipped_height hh hp hκ]
      simp only [clipped_envelope hh hp hκ, sub_self, abs_zero, mul_zero, integral_zero]
    rw [hz, mul_zero, sub_eq_zero] at he
    rw [← he]
    exact fixed_weight hh hp wg ha ha1
  · intro g wg hk
    let C := a+(1-a)*lpNorm (fun x => g x*h x) ∞ μ *
      (∫ x, h x/g x ∂μ)/(∫ x, h x^2 ∂μ)
    have he := variational_excess hh hp wg hκ hk (a := a)
    refine ⟨C, fixed_weight hh hp wg ha ha1, ?_, he, ?_, ?_, ?_⟩
    · have hi : 0 ≤ ∫ x, h x * |lpNorm (fun y => g y*h y) ∞ μ / g x -
          max (h x) (lpNorm h ∞ μ/κ)| ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [hp] with x hx
        exact mul_nonneg hx.le (abs_nonneg _)
      have hcoef : 0 ≤ (1-a)/(∫ x, h x^2 ∂μ) :=
        div_nonneg (sub_nonneg.mpr ha1) (square_pos hh hp).le
      have := mul_nonneg hcoef hi
      linarith
    · intro ha'
      rw [← excess_zero_iff hh hp wg hκ]
      have hcoef : (1-a)/(∫ x, h x^2 ∂μ) ≠ 0 :=
        ne_of_gt (div_pos (sub_pos.mpr ha') (square_pos hh hp))
      constructor
      · intro hz
        have hz' : C-optimum μ h a κ = 0 := sub_eq_zero.mpr hz
        rw [he] at hz'
        exact (mul_eq_zero.mp hz').resolve_left hcoef
      · intro hz
        have hz' := he
        rw [hz, mul_zero] at hz'
        exact sub_eq_zero.mp hz'
    · intro ha'
      dsimp [C]
      simp [ha']
    · exact fun ha' => optimum_one_iff hh hp ha'

end D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
