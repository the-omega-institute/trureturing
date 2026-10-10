/- GID: D5/S3/Quantum/Petz/KernelSmoothness
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smoothness and path derivatives of Dittmann's kernel on positive nodes. -/

import D5.S3.Quantum.Petz.SymmetricKernel
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod

namespace D5.S3.Quantum.Petz.KernelSmoothness

open Set MeasureTheory Filter BoundedContinuousFunction
open D5.S3.Quantum.PositiveResolvent.LogMeanResolvents
open D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference
open D5.S3.Quantum.Petz.SymmetricKernel
open scoped Topology ContDiff

/-- Product coordinates used for joint and path derivatives. -/
def pos : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}

private lemma weighted_integrable {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] {μ : Measure A} {w : A → ℝ} (hw : Integrable w μ)
    (f : A →ᵇ ℝ) : Integrable (fun t => w t * f t) μ :=
  hw.mul_bdd f.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall f.norm_coe_le_norm)

private noncomputable def weightedIntegral {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A] (μ : Measure A) (w : A → ℝ)
    (hw : Integrable w μ) : (A →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t, w t * f t ∂μ
      map_add' := fun f g => by
        simp only [BoundedContinuousFunction.add_apply, mul_add]
        exact integral_add (weighted_integrable hw f) (weighted_integrable hw g)
      map_smul' := fun c f => by
        simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [← mul_assoc, mul_comm (w _) c, mul_assoc]
        exact integral_const_mul c _ }
    (∫ t, ‖w t‖ ∂μ) (fun f => by
      calc
        ‖∫ t, w t * f t ∂μ‖ ≤ ∫ t, ‖w t * f t‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t, ‖w t‖ * ‖f‖ ∂μ := by
          apply integral_mono (weighted_integrable hw f).norm (hw.norm.mul_const _)
          intro t
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _)
        _ = (∫ t, ‖w t‖ ∂μ) * ‖f‖ := integral_mul_const _ _)

private noncomputable def positiveUnit {A : Type*} [TopologicalSpace A]
    (f : A →ᵇ ℝ) {c : ℝ} (hc : 0 < c) (h : ∀ t, c ≤ f t) : (A →ᵇ ℝ)ˣ where
  val := f
  inv := ofNormedAddCommGroup (fun t => (f t)⁻¹)
    (f.continuous.inv₀ (fun t => (hc.trans_le (h t)).ne')) (1 / c) (fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le (h t))), ← one_div]
      exact one_div_le_one_div_of_le hc (h t))
  val_inv := by ext t; exact mul_inv_cancel₀ (hc.trans_le (h t)).ne'
  inv_val := by ext t; exact inv_mul_cancel₀ (hc.trans_le (h t)).ne'

private lemma inverse_apply {A : Type*} [TopologicalSpace A]
    (f : A →ᵇ ℝ) {c : ℝ} (hc : 0 < c) (h : ∀ t, c ≤ f t) (t : A) :
    Ring.inverse f t = (f t)⁻¹ := by
  change Ring.inverse (positiveUnit f hc h : A →ᵇ ℝ) t = _
  rw [Ring.inverse_unit]
  rfl

private noncomputable def clip : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (fun t => min (max t 0) 1) (by fun_prop) 1 (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) zero_le_one)]
    exact min_le_right _ _)

private lemma clip_bounds (t : ℝ) : 0 ≤ clip t ∧ clip t ≤ 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

private lemma clip_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clip t = t :=
  by change min (max t 0) 1 = t; rw [max_eq_left ht.1, min_eq_left ht.2]

private noncomputable def affine (x y : ℝ) : ℝ →ᵇ ℝ := x • (1 - clip) + y • clip

private lemma affine_lower {x y : ℝ} (_hx : 0 < x) (_hy : 0 < y) (t : ℝ) :
    min x y ≤ affine x y t := by
  change min x y ≤ x * (1 - clip t) + y * clip t
  have hb := clip_bounds t
  nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left x y)) (sub_nonneg.mpr hb.2),
    mul_nonneg (sub_nonneg.mpr (min_le_right x y)) hb.1]

private lemma L_contDiffAt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => L p.1 p.2) (x, y) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let J := weightedIntegral μ (fun _ => 1) (integrable_const (1 : ℝ))
  have ha : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => affine p.1 p.2) (x, y) := by
    unfold affine
    fun_prop
  have hi := (contDiffAt_ringInverse ℝ (positiveUnit (affine x y)
    (lt_min hx hy) (affine_lower hx hy))).comp (x, y) ha
  have hj := J.contDiff.contDiffAt.comp (x, y) hi
  apply hj.congr_of_eventuallyEq
  have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (x, y), 0 < p.1 ∧ 0 < p.2 :=
    (continuousAt_fst.tendsto.eventually (eventually_gt_nhds hx)).and
      (continuousAt_snd.tendsto.eventually (eventually_gt_nhds hy))
  filter_upwards [he] with p hp
  change L p.1 p.2 = ∫ t in Ioc (0 : ℝ) 1, 1 * Ring.inverse (affine p.1 p.2) t
  rw [L, intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [inverse_apply _ (lt_min hp.1 hp.2) (affine_lower hp.1 hp.2)]
  simp only [affine, BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.coe_one,
    Pi.one_apply, smul_eq_mul,
    clip_eq ⟨ht.1.le, ht.2⟩, one_mul, one_div]
  congr 1
  ring

private noncomputable def decay : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (fun t => 1 / (1 + max t 0))
    (continuous_const.div (by fun_prop) (fun t => by positivity)) 1 (fun t => by
      have ht : 0 ≤ max t 0 := le_max_right _ _
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (one_div_le_one_div_of_le zero_lt_one (by linarith)).trans_eq (by norm_num))

private lemma decay_bounds (t : ℝ) : 0 ≤ decay t ∧ decay t ≤ 1 := by
  change 0 ≤ 1 / (1 + max t 0) ∧ 1 / (1 + max t 0) ≤ 1
  have ht : 0 ≤ max t 0 := le_max_right _ _
  constructor
  · positivity
  · exact (one_div_le_one_div_of_le zero_lt_one (by linarith)).trans_eq (by norm_num)

private noncomputable def normalized (x : ℝ) : ℝ →ᵇ ℝ := 1 + (x - 1) • decay

private lemma normalized_lower {x : ℝ} (_hx : 0 < x) (t : ℝ) :
    min 1 x ≤ normalized x t := by
  change min 1 x ≤ 1 + (x - 1) * decay t
  have hb := decay_bounds t
  nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left 1 x)) (sub_nonneg.mpr hb.2),
    mul_nonneg (sub_nonneg.mpr (min_le_right 1 x)) hb.1]

private lemma m_contDiffAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => m p.1 p.2.1 p.2.2) (x, y, z) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let w : ℝ → ℝ := fun t => 1 / ((1 + t) * (1 + t) * (1 + t))
  have hw : Integrable w μ := m_integrable zero_lt_one zero_lt_one zero_lt_one
  let J := weightedIntegral μ w hw
  have hn : ContDiff ℝ ⊤ normalized := by unfold normalized; fun_prop
  have hi {v : ℝ} (hv : 0 < v) : ContDiffAt ℝ ⊤ (fun u => Ring.inverse (normalized u)) v := by
    have hu : ContDiffAt ℝ ⊤ Ring.inverse (normalized v) :=
      contDiffAt_ringInverse ℝ (positiveUnit (normalized v)
        (lt_min zero_lt_one hv) (normalized_lower hv))
    exact hu.comp v hn.contDiffAt
  have hid : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p) (x, y, z) := contDiffAt_id
  have hj := J.contDiff.contDiffAt.comp (x, y, z)
    ((((hi hx).comp (x, y, z) hid.fst).mul
      ((hi hy).comp (x, y, z) hid.snd.fst)).mul
      ((hi hz).comp (x, y, z) hid.snd.snd))
  apply hj.congr_of_eventuallyEq
  have he : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (x, y, z), p ∈ pos :=
    (continuousAt_fst.tendsto.eventually (eventually_gt_nhds hx)).and
      (((continuousAt_fst.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hy)).and
        ((continuousAt_snd.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hz)))
  filter_upwards [he] with p hp
  change m p.1 p.2.1 p.2.2 = ∫ t in Ioi (0 : ℝ), w t *
    ((Ring.inverse (normalized p.1) * Ring.inverse (normalized p.2.1) *
      Ring.inverse (normalized p.2.2)) t)
  unfold m
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp only [BoundedContinuousFunction.mul_apply,
    inverse_apply _ (lt_min zero_lt_one hp.1) (normalized_lower hp.1),
    inverse_apply _ (lt_min zero_lt_one hp.2.1) (normalized_lower hp.2.1),
    inverse_apply _ (lt_min zero_lt_one hp.2.2) (normalized_lower hp.2.2)]
  change 1 / ((p.1 + t) * (p.2.1 + t) * (p.2.2 + t)) =
    w t * ((1 + (p.1 - 1) * (1 / (1 + max t 0)))⁻¹ *
      (1 + (p.2.1 - 1) * (1 / (1 + max t 0)))⁻¹ *
      (1 + (p.2.2 - 1) * (1 / (1 + max t 0)))⁻¹)
  rw [max_eq_left ht.le]
  dsimp [w]
  have h1 : 1 + t ≠ 0 := by positivity
  have hnz {a : ℝ} (ha : 0 < a) : 1 + (a - 1) * (1 / (1 + t)) ≠ 0 := by
    have heq : 1 + (a - 1) * (1 / (1 + t)) = (a + t) / (1 + t) := by
      field_simp; ring
    rw [heq]
    positivity
  field_simp [h1, hnz hp.1, hnz hp.2.1, hnz hp.2.2]
  ring

private noncomputable def squareS : (ℝ × ℝ) →ᵇ ℝ :=
  ofNormedAddCommGroup (fun t => clip t.1) (clip.continuous.comp continuous_fst)
    1 (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (clip_bounds _).1]; exact (clip_bounds _).2)

private noncomputable def squareT : (ℝ × ℝ) →ᵇ ℝ :=
  ofNormedAddCommGroup (fun t => clip t.2) (clip.continuous.comp continuous_snd)
    1 (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (clip_bounds _).1]; exact (clip_bounds _).2)

private lemma exp_apply {A : Type*} [TopologicalSpace A] (f : A →ᵇ ℝ) (t : A) :
    NormedSpace.exp f t = Real.exp (f t) := by
  let ev : (A →ᵇ ℝ) →+* ℝ :=
    { toFun := fun g => g t
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  exact (NormedSpace.map_exp ev (evalCLM ℝ t).continuous f).trans
    (congrFun Real.exp_eq_exp_ℝ (f t)).symm

private noncomputable def qFunction (p : ℝ × ℝ × ℝ) : (ℝ × ℝ) →ᵇ ℝ :=
  squareS * NormedSpace.exp (-(p.1 • (1 - squareS) +
    p.2.1 • (squareS * (1 - squareT)) + p.2.2 • (squareS * squareT)))

private lemma qFunction_contDiff : ContDiff ℝ ⊤ qFunction := by
  have hg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ =>
      -(p.1 • (1 - squareS) + p.2.1 • (squareS * (1 - squareT)) +
        p.2.2 • (squareS * squareT))) := by fun_prop
  have he : ContDiff ℝ ⊤
      (NormedSpace.exp : ((ℝ × ℝ) →ᵇ ℝ) → (ℝ × ℝ) →ᵇ ℝ) :=
    contDiff_iff_contDiffAt.mpr (fun p => (NormedSpace.exp_analytic (𝕂 := ℝ) p).contDiffAt)
  exact contDiff_const.mul (he.comp hg)

private lemma Q_contDiffAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => Q p.1 p.2.1 p.2.2) (x, y, z) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let J := weightedIntegral (μ.prod μ) (fun _ => 1) (integrable_const (1 : ℝ))
  have hq : (fun p : ℝ × ℝ × ℝ => Q p.1 p.2.1 p.2.2) =
      fun p => J (qFunction (Real.log p.1, Real.log p.2.1, Real.log p.2.2)) := by
    funext p
    change Q p.1 p.2.1 p.2.2 =
      ∫ t, 1 * qFunction (Real.log p.1, Real.log p.2.1, Real.log p.2.2) t ∂(μ.prod μ)
    simp only [one_mul]
    rw [integral_prod _ ((qFunction _).integrable (μ.prod μ))]
    unfold Q
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [qFunction, BoundedContinuousFunction.mul_apply, exp_apply,
      BoundedContinuousFunction.neg_apply, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.coe_one, Pi.one_apply, smul_eq_mul]
    change s * Real.exp (-((1 - s) * Real.log p.1 + s * (1 - t) * Real.log p.2.1 +
      s * t * Real.log p.2.2)) =
      clip s * Real.exp (-(Real.log p.1 * (1 - clip s) +
        Real.log p.2.1 * (clip s * (1 - clip t)) + Real.log p.2.2 * (clip s * clip t)))
    rw [clip_eq ⟨hs.1.le, hs.2⟩, clip_eq ⟨ht.1.le, ht.2⟩]
    congr 2
    ring
  rw [hq]
  have hid : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p) (x, y, z) := contDiffAt_id
  exact J.contDiff.contDiffAt.comp (x, y, z) (qFunction_contDiff.contDiffAt.comp (x, y, z)
    ((hid.fst.log hx.ne').prodMk ((hid.snd.fst.log hy.ne').prodMk (hid.snd.snd.log hz.ne'))))

/-- Analytic-order smoothness includes all positive partial and total coincidences. -/
theorem hs_contDiffOn : ContDiffOn ℝ ⊤
    (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) pos := by
  intro p hp
  have hid : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p) p := contDiffAt_id
  have hxy := (L_contDiffAt hp.1 hp.2.1).comp p (hid.fst.prodMk hid.snd.fst)
  have hxz := (L_contDiffAt hp.1 hp.2.2).comp p (hid.fst.prodMk hid.snd.snd)
  have hyz := (L_contDiffAt hp.2.1 hp.2.2).comp p (hid.snd.fst.prodMk hid.snd.snd)
  have hP : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => P p.1 p.2.1 p.2.2) p :=
    ((m_contDiffAt hp.1 hp.2.1 hp.2.2).pow 2).div ((hxy.mul hxz).mul hyz)
      (mul_ne_zero (mul_ne_zero (L_pos hp.1 hp.2.1).ne' (L_pos hp.1 hp.2.2).ne')
        (L_pos hp.2.1 hp.2.2).ne')
  exact ((hP.sub (contDiffAt_const.mul
    (Q_contDiffAt hp.1 hp.2.1 hp.2.2))).div_const 6).contDiffWithinAt

private lemma pos_isOpen : IsOpen pos :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)))

/-- Fréchet differentiability in the three product coordinates. -/
theorem hs_differentiableAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x, y, z) :=
  (hs_contDiffOn.contDiffAt (pos_isOpen.mem_nhds ⟨hx, hy, hz⟩)).differentiableAt (by simp)

/-- First-slot derivative of the canonical kernel. -/
noncomputable def hs1 (x y z : ℝ) : ℝ := deriv (fun u => hs u y z) x

/-- The second-slot derivative is the first-slot derivative after swapping the nodes. -/
theorem hs1_swap {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    deriv (fun u => hs x u z) y = hs1 y x z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hy] with u hu
  exact hs_symm hx hu hz

private lemma hs1_fderiv {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hs1 x y z = fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2)
      (x, y, z) (1, 0, 0) := by
  have hd := (hs_differentiableAt hx hy hz).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z)))
  simpa only [hs1, Function.comp_def, id_eq] using hd.deriv

private lemma hs2_fderiv {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    deriv (fun u => hs x u z) y =
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x, y, z) (0, 1, 0) := by
  have hd := (hs_differentiableAt hx hy hz).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z)))
  simpa only [Function.comp_def, id_eq] using hd.deriv

/-- Moving both repeated nodes gives twice the first-slot derivative. -/
theorem hs_deriv_repeated {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    deriv (fun u => hs u u z) x = 2 * hs1 x x z := by
  have hd := (hs_differentiableAt hx hx hz).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk ((hasDerivAt_id x).prodMk (hasDerivAt_const x z)))
  have he : deriv (fun u => hs u u z) x =
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x, x, z) (1, 1, 0) := by
    simpa only [Function.comp_def, id_eq] using hd.deriv
  rw [he]
  have hv : ((1, (1, 0)) : ℝ × ℝ × ℝ) = (1, (0, 0)) + (0, (1, 0)) := by ext <;> norm_num
  rw [hv, map_add, ← hs1_fderiv hx hx hz, ← hs2_fderiv hx hx hz, hs1_swap hx hx hz]
  ring

private lemma hs3_fderiv {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hs1 z y x = fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2)
      (x, y, z) (0, 0, 1) := by
  have he : (fun u => hs x y u) =ᶠ[𝓝 z] (fun u => hs u y x) := by
    filter_upwards [eventually_gt_nhds hz] with u hu
    exact (hs_symm_right hx hy hu).trans
      ((hs_symm hx hu hy).trans (hs_symm_right hu hx hy))
  have hd := (hs_differentiableAt hx hy hz).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z x).prodMk ((hasDerivAt_const z y).prodMk (hasDerivAt_id z)))
  have hf : deriv (fun u => hs x y u) z =
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x, y, z) (0, 0, 1) := by
    simpa only [Function.comp_def, id_eq] using hd.deriv
  exact he.deriv_eq.symm.trans hf

/-- Euler's identity for the degree minus one homogeneous kernel. -/
theorem hs_homog_deriv {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * hs1 x y z + y * hs1 y x z + z * hs1 z y x = -hs x y z := by
  let H := fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2
  let D := fderiv ℝ H (x, y, z)
  have hpath : HasDerivAt (fun c : ℝ => (c * x, c * y, c * z)) (x, y, z) 1 :=
    by simpa only [id_eq, one_mul] using
      ((hasDerivAt_id 1).mul_const x).prodMk
        (((hasDerivAt_id 1).mul_const y).prodMk ((hasDerivAt_id 1).mul_const z))
  have hF : HasFDerivAt H D (1 * x, 1 * y, 1 * z) := by
    simpa only [one_mul] using (hs_differentiableAt hx hy hz).hasFDerivAt
  have hd : HasDerivAt (fun c => hs (c * x) (c * y) (c * z)) (D (x, y, z)) 1 :=
    by simpa only [H, Function.comp_def] using hF.comp_hasDerivAt 1 hpath
  have he : (fun c => hs (c * x) (c * y) (c * z)) =ᶠ[𝓝 (1 : ℝ)]
      (fun c => c⁻¹ * hs x y z) := by
    filter_upwards [eventually_gt_nhds zero_lt_one] with c hc
    exact hs_homog hc hx hy hz
  have hr : HasDerivAt (fun c : ℝ => c⁻¹ * hs x y z) (-hs x y z) 1 := by
    simpa using (hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0)).mul_const (hs x y z)
  have hD := hd.unique (hr.congr_of_eventuallyEq he)
  have hv : (x, y, z) = x • ((1, 0, 0) : ℝ × ℝ × ℝ) +
      y • ((0, 1, 0) : ℝ × ℝ × ℝ) + z • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul] at hD
  change x * D (1, 0, 0) + y * D (0, 1, 0) + z * D (0, 0, 1) = _ at hD
  rw [← hs1_fderiv hx hy hz, ← hs2_fderiv hx hy hz, hs1_swap hx hy hz,
    ← hs3_fderiv hx hy hz] at hD
  exact hD

private lemma swap_hasDerivAt {a s z : ℝ} (hx : 0 < a - s) (hy : 0 < a + s)
    (hz : 0 < z) : HasDerivAt (fun u => hs (a - u) (a + u) z)
      (fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2)
        (a - s, a + s, z) (-1, 1, 0)) s := by
  have hd := (hs_differentiableAt hx hy hz).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_const s a).sub (hasDerivAt_id s)).prodMk
      (((hasDerivAt_const s a).add (hasDerivAt_id s)).prodMk (hasDerivAt_const s z)))
  simpa only [Function.comp_def, Pi.sub_apply, Pi.add_apply, id_eq, zero_sub, zero_add] using hd

/-- The swap-path second derivative is the ambient Hessian on its constant velocity. -/
theorem hs_deriv2_swap {a s z : ℝ} (hx : 0 < a - s) (hy : 0 < a + s) (hz : 0 < z) :
    deriv (deriv (fun u => hs (a - u) (a + u) z)) s =
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2))
        (a - s, a + s, z) (-1, 1, 0)) (-1, 1, 0) := by
  let H := fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2
  let v : ℝ × ℝ × ℝ := (-1, 1, 0)
  have hH : ContDiffAt ℝ ⊤ H (a - s, a + s, z) :=
    hs_contDiffOn.contDiffAt (pos_isOpen.mem_nhds ⟨hx, hy, hz⟩)
  have hD : DifferentiableAt ℝ (fderiv ℝ H) (a - s, a + s, z) :=
    (hH.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun u : ℝ => (a - u, a + u, z)) v s := by
    simpa only [v, Pi.sub_apply, Pi.add_apply, id_eq, zero_sub, zero_add] using
      ((hasDerivAt_const s a).sub (hasDerivAt_id s)).prodMk
        (((hasDerivAt_const s a).add (hasDerivAt_id s)).prodMk (hasDerivAt_const s z))
  have hg : HasDerivAt (fun u => fderiv ℝ H (a - u, a + u, z))
      (fderiv ℝ (fderiv ℝ H) (a - s, a + s, z) v) s :=
    hD.hasFDerivAt.comp_hasDerivAt s hpath
  have hd := hg.clm_apply (hasDerivAt_const s v)
  have he : deriv (fun u => hs (a - u) (a + u) z) =ᶠ[𝓝 s]
      (fun u => fderiv ℝ H (a - u, a + u, z) v) := by
    have he1 : ∀ᶠ u in 𝓝 s, 0 < a - u :=
      (by fun_prop : ContinuousAt (fun u : ℝ => a - u) s).tendsto.eventually
        (eventually_gt_nhds hx)
    have he2 : ∀ᶠ u in 𝓝 s, 0 < a + u :=
      (by fun_prop : ContinuousAt (fun u : ℝ => a + u) s).tendsto.eventually
        (eventually_gt_nhds hy)
    filter_upwards [he1, he2] with u hu1 hu2
    exact (swap_hasDerivAt hu1 hu2 hz).deriv
  rw [he.deriv_eq]
  simpa only [H, v, Function.comp_def, map_zero, add_zero] using hd.deriv

end D5.S3.Quantum.Petz.KernelSmoothness
