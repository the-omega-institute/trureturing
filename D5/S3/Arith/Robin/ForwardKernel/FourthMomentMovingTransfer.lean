/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentMovingTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentMovingTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-order freezing transfers fixed-scale mixed moments to continuously varying lengths. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentFreezing
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentBlockTransfer
import D5.S3.Arith.Robin.ForwardKernel.FiniteProductMomentBounds
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.HeineCantor

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingTransfer

open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
open VarianceTransferDefs MomentTransferDefs MacroscopicVarianceDefs
open FourthMomentTransferDefs MovingLengthCells DyadicProbability

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma position_mem (X : ℝ) :
    ∀ᵐ x ∂dyadicProbabilityMeasure X, x / X ∈ Ioc (1 : ℝ) 2 := by
  by_cases hX : 0 < X
  · apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact ⟨(lt_div_iff₀ hX).2 (by simpa using hx.1), (div_le_iff₀ hX).2 hx.2⟩
  · have he : dyadicProbabilityMeasure X = 0 := by
      simp [dyadicProbabilityMeasure, Ioc_eq_empty_of_le (by linarith : 2 * X ≤ X)]
    simp [he]

private lemma increment_memLp_top {E : ℝ → ℝ} {X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X)
    {u : ℝ → ℝ} (hu : Continuous u) :
    MemLp (fun x => increment E (u x) x) ∞ (dyadicProbabilityMeasure X) := by
  let := dyadicProbabilityMeasure_isProbabilityMeasure hX
  obtain ⟨B, _, hB⟩ := VarianceTransfer.bounded_increment_comp hE isCompact_Icc hu continuous_id
  apply MemLp.of_bound ((hE.1.comp (continuous_id.add hu).measurable).sub hE.1).aestronglyMeasurable B
  filter_upwards [position_mem X] with x hx
  rw [Real.norm_eq_abs]
  exact hB x ⟨by simpa using (le_div_iff₀ hX).mp hx.1.le, (div_le_iff₀ hX).mp hx.2⟩

private lemma fixed_memLp_top {E : ℝ → ℝ} {θ X c : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X) :
    MemLp (fixedScaleB E θ c X) ∞ (dyadicProbabilityMeasure X) :=
  by
    unfold fixedScaleB
    simpa only [div_eq_mul_inv] using
      (increment_memLp_top hE hX (continuous_const (y := c * X ^ θ))).mul_const
        (Real.sqrt (X ^ θ * Real.log X))⁻¹

private lemma moving_memLp_top {E a : ℝ → ℝ} {θ X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X)
    (ha : ContinuousOn a (Icc (1 : ℝ) 2)) :
    MemLp (movingB E a θ X) ∞ (dyadicProbabilityMeasure X) := by
  let ae := IccExtend (by norm_num : (1 : ℝ) ≤ 2) (fun u : Icc (1 : ℝ) 2 => a u)
  have hae : Continuous ae := ha.domRestrict.Icc_extend'
  apply ((increment_memLp_top hE hX
    ((hae.comp (continuous_id.div_const X)).mul_const (X ^ θ))).mul_const
      (Real.sqrt (X ^ θ * Real.log X))⁻¹).ae_eq
  filter_upwards [position_mem X] with x hx
  change increment E (ae (x / X) * X ^ θ) x * _ =
    increment E (a (x / X) * X ^ θ) x / _
  rw [show ae (x / X) = a (x / X) from IccExtend_of_mem _ _ ⟨hx.1.le, hx.2⟩]
  rfl

private lemma frozen_memLp_top {E a : ℝ → ℝ} {θ X : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X) :
    MemLp (frozenB E a θ n X) ∞ (dyadicProbabilityMeasure X) := by
  unfold frozenB
  apply memLp_finsetSum (Finset.range n)
  intro j _
  have hh := (fixed_memLp_top (c := a (cellPoint n j)) (θ := θ) hE hX).indicator
    ((measurableSet_Ioc (a := cellPoint n j) (b := cellPoint n (j+1))).preimage (measurable_id.div_const X)).nullMeasurableSet
  convert hh using 1
  ext x
  simp [Set.indicator, dyadicU]

private lemma weight_memLp_top {w : ℝ → ℝ} {X : ℝ}
    (hX : 0 < X) (hw : ContinuousOn w (Icc (1 : ℝ) 2)) :
    MemLp (fun x => w (dyadicU X x)) ∞ (dyadicProbabilityMeasure X) := by
  let := dyadicProbabilityMeasure_isProbabilityMeasure hX
  let we := IccExtend (by norm_num : (1 : ℝ) ≤ 2) (fun u : Icc (1 : ℝ) 2 => w u)
  have hwe : Continuous we := hw.domRestrict.Icc_extend'
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  apply (MemLp.of_bound (p := ∞)
    (hwe.comp (continuous_id.div_const X)).aestronglyMeasurable B (by
      filter_upwards [position_mem X] with x hx
      simpa only [Function.comp_apply, id_eq, we, IccExtend_of_mem _ _ ⟨hx.1.le, hx.2⟩] using hB _ ⟨hx.1.le, hx.2⟩ )).ae_eq
  filter_upwards [position_mem X] with x hx
  simp [we, dyadicU, IccExtend_of_mem _ _ ⟨hx.1.le, hx.2⟩]

private lemma cell_exists {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Ioc (1 : ℝ) 2) :
    ∃ j ∈ Finset.range n, u ∈ Ioc (cellPoint n j) (cellPoint n (j + 1)) := by
  have hh := Ioc_subset_biUnion_Ioc n (cellPoint n)
  have hu' : u ∈ Ioc (cellPoint n 0) (cellPoint n n) := by simpa [cellPoint, hn.ne', one_add_one_eq_two] using hu
  simpa only [mem_iUnion, exists_prop] using hh hu'

private def frozenWeight (w : ℝ → ℝ) (n : ℕ) (X x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    (Ioc (cellPoint n j) (cellPoint n (j + 1))).indicator
      (fun _ => w (cellPoint n j)) (dyadicU X x)

private lemma frozenWeight_memLp_top (w : ℝ → ℝ) {n : ℕ} {X : ℝ} (hX : 0 < X) :
    MemLp (frozenWeight w n X) ∞ (dyadicProbabilityMeasure X) := by
  let := dyadicProbabilityMeasure_isProbabilityMeasure hX
  unfold frozenWeight
  apply memLp_finsetSum (Finset.range n)
  intro j _
  convert (memLp_const (p := ∞) (μ := dyadicProbabilityMeasure X) (w (cellPoint n j))).indicator
    ((measurableSet_Ioc (a := cellPoint n j) (b := cellPoint n (j+1))).preimage (measurable_id.div_const X)).nullMeasurableSet using 1
  ext x
  simp [Set.indicator, dyadicU]

private lemma top_product {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {k : ℕ} {f : Fin k → A → ℝ} (hf : ∀ i, MemLp (f i) ∞ μ) :
    MemLp (fun x => ∏ i, f i x) ∞ μ := by
  simpa using MemLp.fun_prod (s := Finset.univ) (fun i _ => hf i)

private lemma frozen_integral_eq {E : ℝ → ℝ} {θ X : ℝ} {k n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X) (hn : 0 < n)
    (b : Fin k → ℝ → ℝ) (w : ℝ → ℝ) :
    (∫ x, frozenWeight w n X x * (∏ i, frozenB E (b i) θ n X x)
      ∂dyadicProbabilityMeasure X) =
      ∑ j ∈ Finset.range n, w (cellPoint n j) * fixedBlockMoment E θ k
        (fun i => b i (cellPoint n j)) (cellPoint n j) (cellPoint n (j+1)) X := by
  let := dyadicProbabilityMeasure_isProbabilityMeasure hX
  let F := fun j x => (Ioc (cellPoint n j) (cellPoint n (j+1))).indicator
    (fun _ => w (cellPoint n j) * ∏ i, fixedScaleB E θ (b i (cellPoint n j)) X x)
      (dyadicU X x)
  have hi (j : ℕ) : Integrable (F j) (dyadicProbabilityMeasure X) := by
    have hh := ((top_product (fun i => fixed_memLp_top (θ := θ)
      (c := b i (cellPoint n j)) hE hX)).const_mul (w (cellPoint n j))).indicator
        ((measurableSet_Ioc (a := cellPoint n j) (b := cellPoint n (j+1))).preimage (measurable_id.div_const X)).nullMeasurableSet
    exact (hh.integrable (by simp)).congr (by filter_upwards [] with x; simp [F, Set.indicator, dyadicU])
  calc
    _ = ∫ x, ∑ j ∈ Finset.range n, F j x ∂dyadicProbabilityMeasure X := by
      apply integral_congr_ae
      filter_upwards [position_mem X] with x hx
      obtain ⟨j, hj, hu⟩ := cell_exists hn hx
      have he (i : Fin k) : frozenB E (b i) θ n X x =
          fixedScaleB E θ (b i (cellPoint n j)) X x :=
        cell_step_eval hj hu (fun l => fixedScaleB E θ (b i (cellPoint n l)) X x)
      simp_rw [he]
      rw [show frozenWeight w n X x = w (cellPoint n j) from
        cell_step_eval hj hu (fun l => w (cellPoint n l))]
      exact (cell_step_eval hj hu
        (fun l => w (cellPoint n l) * ∏ i, fixedScaleB E θ (b i (cellPoint n l)) X x)).symm
    _ = ∑ j ∈ Finset.range n, ∫ x, F j x ∂dyadicProbabilityMeasure X :=
      integral_finsetSum _ (fun j _ => hi j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [fixedBlockMoment, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [position_indicator_Icc_ae_eq_Ioc hX (cellPoint n j)
        (cellPoint n (j+1)) (fun _ => (1 : ℝ))] with x hx
      simp only [dyadicU]
      rw [hx]
      simp only [F, indicator_apply, dyadicU]
      split_ifs <;> ring

private lemma weighted_integral_error {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g v : A → ℝ} {K : ℝ}
    (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) (hv : MemLp v ∞ μ)
    (hb : ∀ᵐ x ∂μ, |v x| ≤ K) :
    |(∫ x, v x * f x ∂μ) - ∫ x, v x * g x ∂μ| ≤
      K * ∫ x, |f x - g x| ∂μ := by
  rw [← integral_sub ((hv.fun_mul (r := ∞) hf).integrable (by simp))
    ((hv.fun_mul (r := ∞) hg).integrable (by simp))]
  have hh := norm_integral_le_of_norm_le (f := fun x => v x * f x - v x * g x)
    (((hf.sub hg).integrable (by simp)).abs.const_mul K) (by
      filter_upwards [hb] with x hx
      change |v x * f x - v x * g x| ≤ K * |f x - g x|
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  simpa only [Real.norm_eq_abs, integral_const_mul, Pi.sub_apply] using hh

/-- Local fourth energy and fixed-scale mixed moments transfer to bounded differentiable moving lengths and continuous weights. -/
theorem moving_mixed_moments_tendsto
    {E : ℝ → ℝ} {α θ β C : ℝ} {k : ℕ} {W : (Fin k → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) (hk : 0 < k) (hk4 : k ≤ 4)
    (hW : Continuous W) (hF : FixedScaleMixedMoments E θ k W)
    (b : Fin k → ℝ → ℝ) (w : ℝ → ℝ) {M L : ℝ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (hb : ∀ i, MacroscopicLengthBounds (b i) M L)
    (hw : ContinuousOn w (Icc (1 : ℝ) 2)) :
    Tendsto (fun X : ℝ => ∫ x, w (dyadicU X x) *
      (∏ i, movingB E (b i) θ X x) ∂dyadicProbabilityMeasure X)
      atTop (𝓝 (∫ u, w u * W (fun i => b i u) ∂dyadicProbabilityMeasure 1)) := by
  let K := fourthK C M
  have hK : 0 ≤ K := by
    dsimp [K, fourthK]
    positivity [hV.1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  let P := ∏ _i : Fin k, K ^ (1 / 4 : ℝ)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hK _)
  obtain ⟨B, hBb⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  let V := |B| + 1
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hwb : ∀ u ∈ Icc (1 : ℝ) 2, |w u| ≤ V := by
    intro u hu
    have hh := hBb u hu
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [V]; linarith [le_abs_self B])
  let D := fun n : ℕ => freezeCoefficient C L n + (1 / (n : ℝ)) ^ 2
  have hD : ∀ n, 0 ≤ D n := by
    intro n
    dsimp [D, freezeCoefficient]
    positivity [hV.1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hDz : Tendsto D atTop (𝓝 0) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul
      (1312 * C * (1 + L) ^ 2 / (3 * Real.log 2) + 1)
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    dsimp [D, freezeCoefficient]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hErr : Tendsto (fun n => V * ((k : ℝ) * (D n) ^ (1 / 4 : ℝ) *
      K ^ (((k : ℝ) - 1) / 4))) atTop (𝓝 0) := by
    have hh := ((hDz.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))).const_mul
      (k : ℝ)).mul_const (K ^ (((k : ℝ) - 1) / 4))
    simpa using hh.const_mul V
  let f := fun u => w u * W (fun i => b i u)
  have hfc : ContinuousOn f (Icc (1 : ℝ) 2) :=
    hw.mul (hW.continuousOn.comp (continuousOn_pi.mpr (fun i => (hb i).1.continuousOn))
      (fun _ _ => mem_univ _))
  have hR := FourthMomentBlockTransfer.logarithmic_block_riemann f hfc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := ε / (6 * (P + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) d hd
  obtain ⟨n, hn, hnδ, hnR, hnE⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)).and
      ((hR.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))).and
        (hErr.eventually (gt_mem_nhds (by positivity : 0 < ε / 4)))))).exists
  let Q := fun X => ∑ j ∈ Finset.range n,
    w (cellPoint n j) * fixedBlockMoment E θ k (fun i => b i (cellPoint n j))
      (cellPoint n j) (cellPoint n (j+1)) X
  let q := ∑ j ∈ Finset.range n,
    f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
      (Icc (cellPoint n j) (cellPoint n (j+1)))
  have hQ : Tendsto Q atTop (𝓝 q) := by
    have hh := FourthMomentBlockTransfer.fixed_block_moments_tendsto hF b w
      (by linarith : 0 < M) hn (fun i j hj => (hb i).2.1 _ (cellPoint_mem hn hj.le))
    convert hh using 1
    dsimp [q, f]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnRp : |q - ∫ u, f u ∂dyadicProbabilityMeasure 1| < ε / 4 := hnR
  have hη : 0 < (1 / (n : ℝ)) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  filter_upwards [FourthMomentFreezing.moving_fourth_uniform hE hB hV hM hL,
    FourthMomentFreezing.frozen_fourth_uniform hE hB hV hM hL hn,
    FourthMomentFreezing.freezing_fourth_eventually hE hB hV hM hL hn _ hη,
    (Metric.tendsto_nhds.mp hQ) (ε / 4) (by positivity), eventually_gt_atTop (0 : ℝ)]
    with X hm hg he hQX hX
  let := dyadicProbabilityMeasure_isProbabilityMeasure hX
  let A := fun x => ∏ i, movingB E (b i) θ X x
  let G := fun x => ∏ i, frozenB E (b i) θ n X x
  have hAt : MemLp A ∞ (dyadicProbabilityMeasure X) :=
    top_product (fun i => moving_memLp_top hE hX (hb i).1.continuousOn)
  have hGt : MemLp G ∞ (dyadicProbabilityMeasure X) :=
    top_product (fun i => frozen_memLp_top hE hX)
  have hwt := weight_memLp_top hX hw
  have hwnt := frozenWeight_memLp_top (n := n) w hX
  have hprod : (∫ x, |G x| ∂dyadicProbabilityMeasure X) ≤ P :=
    FiniteProductMomentBounds.product_fourth_bound hk hk4
      (fun i => (frozen_memLp_top (a := b i) (θ := θ) (n := n) hE hX).mono_exponent le_top)
      (fun _ => hK) (fun i => hg _ (hb i))
  have hdiff : (∫ x, |A x - G x| ∂dyadicProbabilityMeasure X) ≤
      (k : ℝ) * (D n) ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4) :=
    FiniteProductMomentBounds.product_fourth_difference_bound hk hk4 hK (hD n)
      (fun i => ⟨(moving_memLp_top hE hX (hb i).1.continuousOn).mono_exponent le_top,
        (frozen_memLp_top hE hX).mono_exponent le_top⟩)
      (fun i => hm _ (hb i)) (fun i => hg _ (hb i)) (fun i => he _ (hb i))
  have hmove : |(∫ x, w (dyadicU X x) * A x ∂dyadicProbabilityMeasure X) -
      ∫ x, w (dyadicU X x) * G x ∂dyadicProbabilityMeasure X| < ε / 4 := by
    apply (weighted_integral_error hAt hGt hwt (by
      filter_upwards [position_mem X] with x hx
      exact hwb _ ⟨hx.1.le, hx.2⟩)).trans_lt
    exact (mul_le_mul_of_nonneg_left hdiff hV0).trans_lt hnE
  have hweight : ∀ᵐ x ∂dyadicProbabilityMeasure X,
      |w (dyadicU X x) - frozenWeight w n X x| ≤ d := by
    filter_upwards [position_mem X] with x hx
    obtain ⟨j, hj, hu⟩ := cell_exists hn hx
    rw [show frozenWeight w n X x = w (cellPoint n j) from
      cell_step_eval hj hu (fun l => w (cellPoint n l))]
    apply le_of_lt
    apply hmod _ ⟨hx.1.le, hx.2⟩ _ (cellPoint_mem hn (Finset.mem_range.mp hj).le)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
    exact (sub_le_sub_right hu.2 _).trans_lt ((cellPoint_step hn j).symm ▸ hnδ)
  have hfreeze : |(∫ x, w (dyadicU X x) * G x ∂dyadicProbabilityMeasure X) - Q X| < ε / 6 := by
    dsimp only [Q]
    rw [← frozen_integral_eq (θ := θ) hE hX hn b w]
    have hsub : (∫ x, w (dyadicU X x) * G x ∂dyadicProbabilityMeasure X) -
        (∫ x, frozenWeight w n X x * G x ∂dyadicProbabilityMeasure X) =
        ∫ x, (w (dyadicU X x) - frozenWeight w n X x) * G x ∂dyadicProbabilityMeasure X := by
      rw [← integral_sub ((hwt.fun_mul (r := ∞) hGt).integrable (by simp))
        ((hwnt.fun_mul (r := ∞) hGt).integrable (by simp))]
      congr 1
      ext x
      ring
    rw [hsub]
    have hh := weighted_integral_error hGt (MemLp.zero' : MemLp (fun _ : ℝ => (0 : ℝ)) ∞
      (dyadicProbabilityMeasure X)) (hwt.sub hwnt) hweight
    simp only [mul_zero, integral_zero, sub_zero] at hh
    apply hh.trans_lt
    apply (mul_le_mul_of_nonneg_left hprod hd.le).trans_lt
    have heq : d * (P + 1) = ε / 6 := by dsimp [d]; field_simp
    nlinarith
  rw [Real.dist_eq] at hQX ⊢
  change |(∫ x, w (dyadicU X x) * A x ∂dyadicProbabilityMeasure X) -
    ∫ u, f u ∂dyadicProbabilityMeasure 1| < ε
  have h₁ := abs_sub_le (∫ x, w (dyadicU X x) * A x ∂dyadicProbabilityMeasure X)
    (∫ x, w (dyadicU X x) * G x ∂dyadicProbabilityMeasure X)
    (∫ u, f u ∂dyadicProbabilityMeasure 1)
  have h₂ := abs_sub_le (∫ x, w (dyadicU X x) * G x ∂dyadicProbabilityMeasure X)
    (Q X) (∫ u, f u ∂dyadicProbabilityMeasure 1)
  have h₃ := abs_sub_le (Q X) q (∫ u, f u ∂dyadicProbabilityMeasure 1)
  linarith only [h₁, h₂, h₃, hmove, hfreeze, hQX, hnRp, hε]

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingTransfer
