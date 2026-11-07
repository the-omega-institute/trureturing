/- GID: D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth moving differences obey scale, norm, and derivative square bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingDifferenceTransfer
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! Smooth moving differences on dyadic intervals and their enlarged domains. -/

namespace D5.S3.Arith.Robin.ForwardKernel.SmoothMovingDifference

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer CrossExponentDefs
open MovingDifferenceTransfer

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Smooth moving differences are bounded by their derivative scale, their norm,
and the norm of their derivative. -/
theorem smooth_moving_difference_bounds
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ u : ℝ → ℝ,
        ContDiffOn ℝ 1 u (Icc (X / 2) (4 * X)) →
        intervalL2 X (2 * X)
            (fun x => u (movingShift θ s x) - u x) ≤
          C * X ^ θ *
            intervalL2 (X / 2) (4 * X) (deriv u) ∧
        intervalL2 X (2 * X)
            (fun x => u (movingShift θ s x) - u x) ≤
          C * intervalL2 (X / 2) (4 * X) u ∧
        intervalL2 X (2 * X)
            (deriv (fun x => u (movingShift θ s x) - u x)) ≤
          C * intervalL2 (X / 2) (4 * X) (deriv u) := by
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX s hs u hu
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hLR : X / 2 ≤ 4 * X := by linarith
  have hLR' : X / 2 < 4 * X := by linarith
  let K := Icc (X / 2) (4 * X)
  let φ := movingShift θ s
  let dp : ℝ → ℝ := fun x => 1 + s * (θ * x ^ (θ - 1))
  have hφ : Continuous φ :=
    continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hθ.le))
  have hφd (x : ℝ) (hx : x ∈ Icc X (2 * X)) : HasDerivAt φ (dp x) x :=
    (hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul s)
  have hdp (x : ℝ) (hx : x ∈ Icc X (2 * X)) : dp x ∈ Icc (1 : ℝ) 2 := by
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hp0 := Real.rpow_nonneg (by linarith : 0 ≤ x) (θ - 1)
    have hp1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith : θ - 1 ≤ 0)
    have hst0 : 0 ≤ s * θ := mul_nonneg hs.1 hθ.le
    have hst1 : s * θ ≤ 1 := (mul_le_of_le_one_left hθ.le hs.2).trans hθ1.le
    dsimp [dp]
    constructor
    · nlinarith [mul_nonneg hst0 hp0]
    · nlinarith [mul_le_mul_of_nonneg_left hp1 hst0]
  have hgap (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      φ x - x ∈ Icc (0 : ℝ) (2 * X ^ θ) :=
    ⟨moving_shift_nonneg_gap hθ hs (by linarith [hx.1]),
      moving_shift_gap_le hθ hθ1 hs (by linarith) hx⟩
  have hcore (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      x ∈ Ioo (X / 2) (4 * X) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have himage (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      φ x ∈ Ioo (X / 2) (4 * X) := by
    have hp := Real.rpow_lt_self_of_one_lt (by linarith [hx.1] : 1 < x) hθ1
    have hsp := mul_le_of_le_one_left
      (Real.rpow_nonneg (by linarith [hx.1] : 0 ≤ x) θ) hs.2
    have hgap0 := (hgap x hx).1
    dsimp [φ, movingShift] at *
    constructor <;> linarith [hx.1, hx.2]
  let f : ℝ → ℝ := fun y => u (projIcc (X / 2) (4 * X) hLR y)
  let w : ℝ → ℝ := fun y => derivWithin u K (projIcc (X / 2) (4 * X) hLR y)
  have hf : Continuous f := hu.continuousOn.domRestrict.comp continuous_projIcc
  have hw : Continuous w :=
    (hu.continuousOn_derivWithin (uniqueDiffOn_Icc hLR') (by norm_num)).domRestrict.comp
      continuous_projIcc
  have hfeq (y : ℝ) (hy : y ∈ K) : f y = u y := by
    dsimp [f]
    rw [projIcc_of_mem hLR hy]
  have hweq (y : ℝ) (hy : y ∈ Ioo (X / 2) (4 * X)) : w y = deriv u y := by
    dsimp [w]
    rw [projIcc_of_mem hLR ⟨hy.1.le, hy.2.le⟩]
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  have hdU (y : ℝ) (hy : y ∈ Ioo (X / 2) (4 * X)) : HasDerivAt u (w y) y := by
    rw [hweq y hy]
    exact ((hu.contDiffAt (Icc_mem_nhds hy.1 hy.2)).differentiableAt one_ne_zero).hasDerivAt
  have hmemf : MemLp f 2 (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).mpr
      (((hf.pow 2).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hmemw : MemLp w 2 (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq hw.measurable.aestronglyMeasurable).mpr
      (((hw.pow 2).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hcompf := square_comp_le hXX hLR hf.measurable hmemf hφ.continuousOn
    (fun x hx => (hφd x hx).hasDerivWithinAt) (fun x hx => (hdp x hx).1)
    (fun x hx => ⟨(himage x hx).1.le, (himage x hx).2.le⟩)
  have hcompw := square_comp_le hXX hLR hw.measurable hmemw hφ.continuousOn
    (fun x hx => (hφd x hx).hasDerivWithinAt) (fun x hx => (hdp x hx).1)
    (fun x hx => ⟨(himage x hx).1.le, (himage x hx).2.le⟩)
  have hifcomp : IntervalIntegrable (fun x => f (φ x) ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    exact hcompf.1.mono_set Ioc_subset_Icc_self
  have hiwcomp : IntervalIntegrable (fun x => w (φ x) ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    exact hcompw.1.mono_set Ioc_subset_Icc_self
  have hifsq : IntervalIntegrable (fun x => f x ^ 2) volume X (2 * X) := by
    exact (show Continuous (fun x : ℝ => f x ^ 2) by fun_prop).intervalIntegrable X (2 * X)
  have hiwsq : IntervalIntegrable (fun x => w x ^ 2) volume X (2 * X) := by
    exact (show Continuous (fun x : ℝ => w x ^ 2) by fun_prop).intervalIntegrable X (2 * X)
  have hidf : (∫ x in X..(2 * X), f x ^ 2) ≤ ∫ y in (X / 2)..(4 * X), f y ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) hXX (by linarith)
      (Eventually.of_forall fun _ => sq_nonneg _)
      ((hf.pow 2).intervalIntegrable (μ := volume) (X / 2) (4 * X))
  have hidw : (∫ x in X..(2 * X), w x ^ 2) ≤ ∫ y in (X / 2)..(4 * X), w y ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) hXX (by linarith)
      (Eventually.of_forall fun _ => sq_nonneg _)
      ((hw.pow 2).intervalIntegrable (μ := volume) (X / 2) (4 * X))
  have hEf : (∫ y in (X / 2)..(4 * X), f y ^ 2) =
      ∫ y in (X / 2)..(4 * X), u y ^ 2 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hLR]
    intro y hy
    change f y ^ 2 = u y ^ 2
    rw [hfeq y hy]
  have hEw : (∫ y in (X / 2)..(4 * X), w y ^ 2) =
      ∫ y in (X / 2)..(4 * X), deriv u y ^ 2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le hLR
    intro y hy
    change w y ^ 2 = deriv u y ^ 2
    rw [hweq y hy]
  have hFTC (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      u (φ x) - u x = ∫ y in x..φ x, w y := by
    have hsub : Icc x (φ x) ⊆ K := by
      intro y hy
      exact ⟨(hcore x hx).1.le.trans hy.1, hy.2.trans (himage x hx).2.le⟩
    rw [← intervalIntegral.integral_deriv_of_contDiffOn_Icc (hu.mono hsub)
      (by linarith [(hgap x hx).1] : x ≤ φ x)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith [(hgap x hx).1] : x ≤ φ x)]
    intro y hy
    rw [hweq y ⟨lt_of_lt_of_le (hcore x hx).1 hy.1,
      lt_of_le_of_lt hy.2 (himage x hx).2⟩]
  have hshortnorm := sliding_primitive_l2_le hw.measurable hmemw hφ hXX
    (show 0 ≤ 2 * X ^ θ by positivity [Real.rpow_pos_of_pos hX0 θ])
    (show X / 2 ≤ X by linarith) (show 2 * X ≤ 4 * X by linarith) hgap
    (fun x hx => (himage x hx).2.le)
  have hnormeq : intervalL2 X (2 * X) (fun x => u (φ x) - u x) =
      intervalL2 X (2 * X) (fun x => ∫ y in x..φ x, w y) := by
    unfold intervalL2
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hXX]
    intro x hx
    exact congrArg (fun z : ℝ => z ^ 2) (hFTC x hx)
  rw [← hnormeq] at hshortnorm
  have hshort : (∫ x in X..(2 * X), (u (φ x) - u x) ^ 2) ≤
      (2 * X ^ θ) ^ 2 * ∫ y in (X / 2)..(4 * X), w y ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity [Real.rpow_pos_of_pos hX0 θ]) (Real.sqrt_nonneg _))).mpr
        hshortnorm
    rw [mul_pow, Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall hXX
      (fun x => sq_nonneg _)), Real.sq_sqrt
        (intervalIntegral.integral_nonneg_of_forall hLR (fun y => sq_nonneg _))] at hsq
    exact hsq
  have hnorm : (∫ x in X..(2 * X), (u (φ x) - u x) ^ 2) ≤
      4 * ∫ y in (X / 2)..(4 * X), f y ^ 2 := by
    calc
      _ ≤ ∫ x in X..(2 * X), 2 * f (φ x) ^ 2 + 2 * f x ^ 2 := by
        simp only [intervalIntegral.integral_of_le hXX]
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((hifcomp.const_mul 2).add (hifsq.const_mul 2)).1
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxc : x ∈ Icc X (2 * X) := ⟨hx.1.le, hx.2⟩
        rw [hfeq _ ⟨(himage x hxc).1.le, (himage x hxc).2.le⟩,
          hfeq _ ⟨(hcore x hxc).1.le, (hcore x hxc).2.le⟩]
        nlinarith [sq_nonneg (u (φ x) + u x)]
      _ = 2 * (∫ x in X..(2 * X), f (φ x) ^ 2) +
          2 * ∫ x in X..(2 * X), f x ^ 2 := by
        rw [intervalIntegral.integral_add (hifcomp.const_mul 2)
          (hifsq.const_mul 2), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith [hcompf.2]
  have hderiv (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      deriv (fun y => u (φ y) - u y) x = w (φ x) * dp x - w x :=
    (((hdU _ (himage x hx)).comp x (hφd x hx)).sub (hdU x (hcore x hx))).deriv
  have hnormd : (∫ x in X..(2 * X), deriv (fun y => u (φ y) - u y) x ^ 2) ≤
      10 * ∫ y in (X / 2)..(4 * X), w y ^ 2 := by
    calc
      _ ≤ ∫ x in X..(2 * X), 8 * w (φ x) ^ 2 + 2 * w x ^ 2 := by
        simp only [intervalIntegral.integral_of_le hXX]
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((hiwcomp.const_mul 8).add (hiwsq.const_mul 2)).1
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxc : x ∈ Icc X (2 * X) := ⟨hx.1.le, hx.2⟩
        rw [hderiv x hxc]
        have hdp2 : dp x ^ 2 ≤ 4 := by nlinarith [(hdp x hxc).1, (hdp x hxc).2]
        have hmul := mul_le_mul_of_nonneg_left hdp2 (sq_nonneg (w (φ x)))
        nlinarith [sq_nonneg (w (φ x) * dp x + w x)]
      _ = 8 * (∫ x in X..(2 * X), w (φ x) ^ 2) +
          2 * ∫ x in X..(2 * X), w x ^ 2 := by
        rw [intervalIntegral.integral_add (hiwcomp.const_mul 8)
          (hiwsq.const_mul 2), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith [hcompw.2]
  rw [hEw] at hshort hnormd
  rw [hEf] at hnorm
  have hEu := intervalIntegral.integral_nonneg_of_forall (μ := volume) hLR
    (fun y => sq_nonneg (u y))
  have hEd := intervalIntegral.integral_nonneg_of_forall (μ := volume) hLR
    (fun y => sq_nonneg (deriv u y))
  have hsEu := Real.sq_sqrt hEu
  have hsEd := Real.sq_sqrt hEd
  have hdelta := intervalIntegral.integral_nonneg_of_forall (μ := volume) hXX
    (fun x => sq_nonneg (u (φ x) - u x))
  have hdeltaD := intervalIntegral.integral_nonneg_of_forall (μ := volume) hXX
    (fun x => sq_nonneg (deriv (fun y => u (φ y) - u y) x))
  have hsδ := Real.sq_sqrt hdelta
  have hsδd := Real.sq_sqrt hdeltaD
  unfold intervalL2
  dsimp [φ] at *
  refine ⟨?_, ?_, ?_⟩
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, mul_pow, hsδ, hsEd]
    nlinarith [mul_nonneg (sq_nonneg (X ^ θ)) hEd]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, hsδ, hsEu]
    nlinarith
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, hsδd, hsEd]
    nlinarith

private lemma strip_volume_le {a s X l r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X)) :
    volume.real (endpointStrips a s l r) ≤ 4 * X ^ a := by
  have hl0 : 0 ≤ movingShift a s l - l :=
    moving_shift_nonneg_gap ha hs (by linarith [hl.1])
  have hr0 : 0 ≤ movingShift a s r - r :=
    moving_shift_nonneg_gap ha hs (by linarith [hl.1, hr.1])
  have hll := moving_shift_gap_le ha ha1 hs hX hl
  have hrr := moving_shift_gap_le ha ha1 hs hX ⟨hl.1.trans hr.1,hr.2⟩
  calc
    _ ≤ volume.real (Icc l (movingShift a s l)) +
        volume.real (Icc r (movingShift a s r)) :=
      measureReal_union_le _ _
    _ = (movingShift a s l - l) + (movingShift a s r - r) := by
      simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hl0,
        ENNReal.toReal_ofReal hr0]
    _ ≤ _ := by linarith

private lemma strip_l2_le {u : ℝ → ℝ} {a s X l r : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X))
    (hu : MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))))
    (hsub : endpointStrips a s l r ⊆ Icc (X / 2) (4 * X)) :
    (∫ y in endpointStrips a s l r, |u y|) ≤
      2 * Real.sqrt (X ^ a) * intervalL2 (X / 2) (4 * X) u := by
  let S := endpointStrips a s l r
  have hucc : MemLp u 2 (volume.restrict (Icc (X / 2) (4 * X))) := by
    rwa [← restrict_Ioc_eq_restrict_Icc]
  have huS := hucc.mono_measure (Measure.restrict_mono hsub le_rfl)
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨lt_of_le_of_lt (by simpa using measure_mono hsub) measure_Icc_lt_top⟩
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp u (ENNReal.ofReal 2) (volume.restrict S) by simpa using huS)
    (memLp_const (1 : ℝ) :
      MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict S))
  simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
    ←Real.sqrt_eq_rpow] at hc
  have hsq : (∫ y in S,u y^2) ≤ ∫ y in (X / 2)..(4 * X),u y^2 := by
    rw [intervalIntegral.integral_of_le (by linarith : X / 2 ≤ 4 * X),
      ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set hucc.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)
  have hvol : Real.sqrt (volume.real S) ≤ 2 * Real.sqrt (X ^ a) := by
    calc
      _ ≤ Real.sqrt (4 * X ^ a) :=
        Real.sqrt_le_sqrt (strip_volume_le ha ha1 hs hX hl hr)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show Real.sqrt (4 : ℝ) = 2 by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact hc.trans (by
    unfold intervalL2
    have := mul_le_mul (Real.sqrt_le_sqrt hsq) hvol (Real.sqrt_nonneg _) (by positivity)
    nlinarith)

private lemma strip_sup_le {u : ℝ → ℝ} {a s X l r U : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X)) (hU : 0 ≤ U)
    (hsub : endpointStrips a s l r ⊆ Icc (X / 2) (4 * X))
    (hub : ∀ y ∈ Icc (X / 2) (4 * X), |u y| ≤ U) :
    (∫ y in endpointStrips a s l r, |u y|) ≤ 4*X ^ a*U := by
  have hfin : volume (endpointStrips a s l r) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (f := fun y => |u y|) hfin
    (fun y hy => by simpa only [Real.norm_eq_abs, abs_abs] using hub y (hsub hy))
  have hv := mul_le_mul_of_nonneg_right (strip_volume_le ha ha1 hs hX hl hr) hU
  have hb' : |(∫ y in endpointStrips a s l r, |u y|)| ≤
      volume.real (endpointStrips a s l r) * U := by
    simpa only [Real.norm_eq_abs, mul_comm] using hb
  exact (le_abs_self _).trans (hb'.trans hv)

/-- Endpoint strips satisfy both square-norm and uniform pointwise bounds. -/
theorem endpoint_strips_integral_bounds
    {u : ℝ → ℝ} {a s X l r : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X))
    (hu : MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X)))) :
    (∫ y in endpointStrips a s l r, |u y|) ≤
        2 * Real.sqrt (X ^ a) * intervalL2 (X / 2) (4 * X) u ∧
      ∀ U : ℝ, 0 ≤ U →
        (∀ y ∈ Icc (X / 2) (4 * X), |u y| ≤ U) →
          (∫ y in endpointStrips a s l r, |u y|) ≤ 4 * X ^ a * U := by
  have hsub := endpointStrips_subset ha ha1 hs hX hl hr
  exact ⟨strip_l2_le ha ha1 hs hX hl hr hu hsub,
    fun _ hU hub => strip_sup_le ha ha1 hs hX hl hr hU hsub hub⟩

end
end D5.S3.Arith.Robin.ForwardKernel.SmoothMovingDifference
