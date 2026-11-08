/- GID: D5/S3/Arith/Robin/ForwardKernel/MomentTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MomentTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform increment moments transfer to every integrable real profile. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferWeights
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace D5.S3.Arith.Robin.ForwardKernel.MomentTransfer

open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
open VarianceTransferDefs ProfileKernelDefs MomentTransferDefs DyadicProbability
open MomentTransferWeights

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma ae_dyadic_mem (X : ℝ) :
    ∀ᵐ x ∂dyadicProbabilityMeasure X, x ∈ Icc X (2 * X) := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact ⟨hx.1.le, hx.2⟩

private lemma ae_cube_mem (k : ℕ) :
    ∀ᵐ s ∂cubeMeasure k, ∀ i, s i ∈ Icc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  apply Measure.tendsto_eval_ae_ae (i := i)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact ⟨hs.1.le, hs.2⟩

private lemma position_bounds {θ X x : ℝ} {k : ℕ} (hθ : θ < 1)
    (hX : 0 < X) (hx : x ∈ Icc X (2 * X)) :
    0 ≤ dyadicU X x ^ ((k : ℝ) * dyadicR θ) ∧
      dyadicU X x ^ ((k : ℝ) * dyadicR θ) ≤ 2 ^ ((k : ℝ) * dyadicR θ) := by
  have hu0 : 0 ≤ dyadicU X x := div_nonneg (hX.le.trans hx.1) hX.le
  have hu2 : dyadicU X x ≤ 2 := (div_le_iff₀ hX).mpr hx.2
  refine ⟨Real.rpow_nonneg hu0 _, Real.rpow_le_rpow hu0 hu2 ?_⟩
  dsimp [dyadicR, kappa]
  positivity

private lemma product_correction {ι : Type*} (t : Finset ι) {q : ι → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hq : ∀ i ∈ t, |q i - 1| ≤ η) :
    |(∏ i ∈ t, q i) - 1| ≤ (1 + η) ^ t.card - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hqi := hq i (Finset.mem_insert_self _ _)
    have hqt := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
    have habs : |q i| ≤ 1 + η := by
      have := abs_add_le (q i - 1) 1
      simp only [sub_add_cancel, abs_one] at this
      linarith
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    calc
      _ = |q i * ((∏ j ∈ t, q j) - 1) + (q i - 1)| := by congr 1; ring
      _ ≤ |q i| * |(∏ j ∈ t, q j) - 1| + |q i - 1| := by
        simpa only [abs_mul] using abs_add_le
          (q i * ((∏ j ∈ t, q j) - 1)) (q i - 1)
      _ ≤ (1 + η) * ((1 + η) ^ t.card - 1) + η :=
        add_le_add (mul_le_mul habs hqt (abs_nonneg _) (by positivity)) hqi
      _ = _ := by ring

private lemma product_moment_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ} (hk : 0 < k)
    {f : Fin k → α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (fun x => |f i x| ^ k) μ)
    (hp : Integrable (fun x => ∏ i, |f i x|) μ)
    (hb : ∀ i, (∫ x, |f i x| ^ k ∂μ) ≤ C) :
    (∫ x, ∏ i, |f i x| ∂μ) ≤ C := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have he (a : ℝ≥0∞) : (a ^ k) ^ (1 / (k : ℝ)) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    simp [hk0]
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i x => (ENNReal.ofReal |f i x|) ^ k)
    (p := fun _ => 1 / (k : ℝ))
    (fun i _ => by fun_prop)
    (by simp [hk0]) (fun _ _ => by positivity)
  simp only [he] at h
  have hl (i : Fin k) : (∫⁻ x, (ENNReal.ofReal |f i x|) ^ k ∂μ) ≤ ENNReal.ofReal C := by
    simp_rw [← ENNReal.ofReal_pow (abs_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (Eventually.of_forall (fun x => by positivity))]
    · exact ENNReal.ofReal_le_ofReal (hb i)
  have hc : (∏ _i : Fin k, (ENNReal.ofReal C) ^ (1 / (k : ℝ))) = ENNReal.ofReal C := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    simp [hk0]
  have hh : (∫⁻ x, ∏ i, ENNReal.ofReal |f i x| ∂μ) ≤ ENNReal.ofReal C :=
    h.trans ((Finset.prod_le_prod (fun i _ => ENNReal.rpow_le_rpow (hl i) (by positivity))).trans_eq hc)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg (f i _))] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => abs_nonneg _)))] at hh
  · exact (ENNReal.ofReal_le_ofReal_iff hC).mp hh

private def momentKernel (E : ℝ → ℝ) (θ X : ℝ) (k : ℕ)
    (q : ℝ → ℝ → ℝ) (s : Fin k → ℝ) (x : ℝ) : ℝ :=
  dyadicU X x ^ ((k : ℝ) * dyadicR θ) * ∏ i, q (s i) x * dyadicB E θ (s i) x

private lemma kernel_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (θ X : ℝ) (k : ℕ) {q : ℝ → ℝ → ℝ}
    (hq : Measurable (fun p : ℝ × ℝ => q p.1 p.2)) :
    Measurable (fun p : (Fin k → ℝ) × ℝ => momentKernel E θ X k q p.1 p.2) := by
  unfold momentKernel dyadicU
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_fun_prod
  intro i hi
  have hm : Measurable (fun p : (Fin k → ℝ) × ℝ => (p.1 i, p.2)) := by fun_prop
  have hb : Measurable (fun p : (Fin k → ℝ) × ℝ => dyadicB E θ (p.1 i) p.2) :=
    (MomentTransferDefs.dyadicB_measurable hE θ).comp hm
  exact (hq.comp hm).mul hb

private lemma kernel_bound {E : ℝ → ℝ} {θ X A D : ℝ} {k : ℕ}
    {q : ℝ → ℝ → ℝ} (hθ : θ < 1) (hX : 0 < X) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |dyadicB E θ s x| ≤ D)
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q s x| ≤ A)
    {s : Fin k → ℝ} {x : ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc X (2 * X)) :
    ‖momentKernel E θ X k q s x‖ ≤
      2 ^ ((k : ℝ) * dyadicR θ) * (A * D) ^ k := by
  obtain ⟨hU0, hU⟩ := position_bounds (k := k) hθ hX hx
  unfold momentKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0, Finset.abs_prod]
  apply mul_le_mul hU _ (Finset.prod_nonneg (fun i _ => abs_nonneg _)) (by positivity)
  calc
    _ ≤ ∏ _i : Fin k, A * D := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        rw [abs_mul]
        exact mul_le_mul (hq (s i) (hs i) x hx) (hB (s i) (hs i) x hx)
          (abs_nonneg _) hA
    _ = _ := by simp

private lemma kernel_integrable {E g : ℝ → ℝ} {θ X A : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ : θ < 1) (hX : 4 ≤ X) {q : ℝ → ℝ → ℝ}
    (hq : Measurable (fun p : ℝ × ℝ => q p.1 p.2)) (hA : 0 ≤ A)
    (hqb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q s x| ≤ A) :
    Integrable (fun p : (Fin k → ℝ) × ℝ =>
      (∏ i, g (p.1 i)) * momentKernel E θ X k q p.1 p.2)
      ((cubeMeasure k).prod (dyadicProbabilityMeasure X)) := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  obtain ⟨D, hD, hDb⟩ := dyadicB_uniform_bound hE θ hX
  have hi : Integrable (fun p : (Fin k → ℝ) × ℝ => ∏ i, g (p.1 i))
      ((cubeMeasure k).prod (dyadicProbabilityMeasure X)) := by
    simpa only [mul_one] using (Integrable.fintype_prod_dep (fun _i : Fin k => hg.2)).mul_prod
      (integrable_const (1 : ℝ) : Integrable _ (dyadicProbabilityMeasure X))
  apply hi.mul_bdd (kernel_measurable hE θ X k hq).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_cube_mem k),
    Measure.quasiMeasurePreserving_snd.ae (ae_dyadic_mem X)] with p hs hx
  exact kernel_bound hθ hX0 hA hD hDb hqb hs hx

private lemma kernel_section_integrable {E : ℝ → ℝ} {θ X A : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hθ : θ < 1) (hX : 4 ≤ X)
    {q : ℝ → ℝ → ℝ} (hq : Measurable (fun p : ℝ × ℝ => q p.1 p.2))
    (hA : 0 ≤ A)
    (hqb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q s x| ≤ A)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    Integrable (momentKernel E θ X k q s) (dyadicProbabilityMeasure X) := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  obtain ⟨D, hD, hDb⟩ := dyadicB_uniform_bound hE θ hX
  apply Integrable.of_bound
    ((kernel_measurable hE θ X k hq).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [ae_dyadic_mem X] with x hx
  exact kernel_bound hθ hX0 hA hD hDb hqb hs hx

private lemma absolute_moment_bound {E : ℝ → ℝ} {θ X C : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hθ : θ < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x => dyadicU X x ^ ((k : ℝ) * dyadicR θ) *
      ∏ i, |dyadicB E θ (s i) x|) (dyadicProbabilityMeasure X) ∧
    (∫ x, dyadicU X x ^ ((k : ℝ) * dyadicR θ) * ∏ i, |dyadicB E θ (s i) x|
      ∂dyadicProbabilityMeasure X) ≤ 2 ^ ((k : ℝ) * dyadicR θ) * C := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  obtain ⟨D, hD, hDb⟩ := dyadicB_uniform_bound hE θ hX
  have hm (i : Fin k) : Measurable (fun x => dyadicB E θ (s i) x) :=
    (dyadicB_measurable hE θ).comp (measurable_const.prodMk measurable_id)
  have hip (i : Fin k) : Integrable (fun x => |dyadicB E θ (s i) x| ^ k)
      (dyadicProbabilityMeasure X) := by
    apply Integrable.of_bound (by fun_prop) (D ^ k)
    filter_upwards [ae_dyadic_mem X] with x hx
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hDb (s i) (hs i) x hx) k
  have hp : Integrable (fun x => ∏ i, |dyadicB E θ (s i) x|)
      (dyadicProbabilityMeasure X) := by
    apply Integrable.of_bound (by fun_prop) (D ^ k)
    filter_upwards [ae_dyadic_mem X] with x hx
    rw [Real.norm_eq_abs, Finset.abs_prod]
    simp only [abs_abs]
    calc
      _ ≤ ∏ _i : Fin k, D := Finset.prod_le_prod₀
        (fun i _ => abs_nonneg _) (fun i _ => hDb (s i) (hs i) x hx)
      _ = _ := by simp
  have hholder := product_moment_bound hk hC hm hip hp (fun i => hb (s i) (hs i))
  have hU : ∀ᵐ x ∂dyadicProbabilityMeasure X,
      ‖dyadicU X x ^ ((k : ℝ) * dyadicR θ)‖ ≤ 2 ^ ((k : ℝ) * dyadicR θ) := by
    filter_upwards [ae_dyadic_mem X] with x hx
    obtain ⟨h0, h1⟩ := position_bounds (k := k) hθ hX0 hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hi := hp.bdd_mul
    ((measurable_id.div_const X).pow_const ((k : ℝ) * dyadicR θ)).aestronglyMeasurable hU
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 ^ ((k : ℝ) * dyadicR θ) * ∏ i, |dyadicB E θ (s i) x|
        ∂dyadicProbabilityMeasure X := by
      apply integral_mono_ae hi (hp.const_mul _)
      filter_upwards [ae_dyadic_mem X] with x hx
      exact mul_le_mul_of_nonneg_right (position_bounds (k := k) hθ hX0 hx).2
        (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = 2 ^ ((k : ℝ) * dyadicR θ) *
        (∫ x, ∏ i, |dyadicB E θ (s i) x| ∂dyadicProbabilityMeasure X) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hholder (by positivity)

private lemma mixed_moment_bound {E : ℝ → ℝ} {θ X C : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hθ : θ < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    ‖dyadicMixedMoment E θ X k s‖ ≤ 2 ^ ((k : ℝ) * dyadicR θ) * C := by
  obtain ⟨hi, hb'⟩ := absolute_moment_bound hE hθ hX hk hC hb hs
  apply (norm_integral_le_of_norm_le hi ?_).trans hb'
  filter_upwards [ae_dyadic_mem X] with x hx
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (position_bounds (k := k) hθ (by linarith : 0 < X) hx).1,
    Finset.abs_prod]

private def normalizedPrice (θ X s x : ℝ) : ℝ :=
  Real.sqrt (Real.log x / Real.log X) * priceRatio x (s * x ^ θ)

private lemma normalizedPrice_measurable (θ X : ℝ) :
    Measurable (fun p : ℝ × ℝ => normalizedPrice θ X p.1 p.2) := by
  unfold normalizedPrice
  apply Measurable.mul (by fun_prop)
  exact WeightRemoval.price_measurable.comp
    (measurable_snd.prodMk (measurable_fst.mul (measurable_snd.pow_const θ)))

private lemma correction_abs_bound {θ X η : ℝ}
    (hc : ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
      |normalizedPrice θ X s x - 1| ≤ η) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X),
      |normalizedPrice θ X s x| ≤ 1 + η := by
  intro s hs x hx
  have ha := abs_add_le (normalizedPrice θ X s x - 1) 1
  simp only [sub_add_cancel, abs_one] at ha
  linarith [hc x hx s hs]

private lemma weighted_moment_eq {E g : ℝ → ℝ} {θ X η : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hX : 4 ≤ X) (hη : 0 ≤ η)
    (hc : ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
      |normalizedPrice θ X s x - 1| ≤ η) :
    (∫ x, dyadicZ E θ g X x ^ k ∂dyadicProbabilityMeasure X) =
      ∫ s, (∏ i, g (s i)) *
        (∫ x, momentKernel E θ X k (normalizedPrice θ X) s x
          ∂dyadicProbabilityMeasure X) ∂cubeMeasure k := by
  letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
  have hi := kernel_integrable (k := k) hE hg hθ1 hX
    (normalizedPrice_measurable θ X) (show 0 ≤ 1 + η by linarith) (correction_abs_bound hc)
  have he : ∀ᵐ x ∂dyadicProbabilityMeasure X,
      dyadicZ E θ g X x ^ k =
        ∫ s, (∏ i, g (s i)) * momentKernel E θ X k (normalizedPrice θ X) s x
          ∂cubeMeasure k := by
    filter_upwards [ae_dyadic_mem X] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hz : dyadicZ E θ g X x = dyadicU X x ^ dyadicR θ *
        (∫ s, g s * (normalizedPrice θ X s x * dyadicB E θ s x) ∂unitMeasure) := by
      rw [dyadicZ_eq_weighted_integral hE hg hθ0 hX hx.1 hx.2]
      have hh : (∫ s, g s * (normalizedPrice θ X s x * dyadicB E θ s x) ∂unitMeasure) =
          Real.sqrt (Real.log x / Real.log X) *
            (∫ s, g s * dyadicB E θ s x * priceRatio x (s * x ^ θ) ∂unitMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => by unfold normalizedPrice; ring)
      rw [hh]; ring
    rw [hz, mul_pow]
    have hp := integral_fintype_prod_eq_pow (ι := Fin k) (μ := unitMeasure)
      (fun s => g s * (normalizedPrice θ X s x * dyadicB E θ s x))
    simp only [Fintype.card_fin] at hp
    rw [← hp, ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro s
    dsimp only
    have hpow : (dyadicU X x ^ dyadicR θ) ^ k =
        dyadicU X x ^ ((k : ℝ) * dyadicR θ) := by
      have hu : 0 ≤ dyadicU X x := (div_pos hx0 (by linarith : 0 < X)).le
      rw [← Real.rpow_mul_natCast hu, mul_comm]
    rw [hpow, Finset.prod_mul_distrib]
    unfold momentKernel
    ring
  rw [integral_congr_ae he, ← integral_integral_swap hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => integral_const_mul _ _)

private lemma replacement_error {E : ℝ → ℝ} {θ X C η : ℝ} {k : ℕ}
    (hE : LocallyBoundedMeasurable E) (hθ : θ < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    (hc : ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
      |normalizedPrice θ X s x - 1| ≤ η)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    ‖(∫ x, momentKernel E θ X k (normalizedPrice θ X) s x ∂dyadicProbabilityMeasure X) -
      dyadicMixedMoment E θ X k s‖ ≤
      ((1 + η) ^ k - 1) * (2 ^ ((k : ℝ) * dyadicR θ) * C) := by
  have hδ : 0 ≤ (1 + η) ^ k - 1 := by
    have : 1 ≤ (1 + η) ^ k := one_le_pow₀ (show 1 ≤ 1 + η by linarith)
    linarith
  obtain ⟨hi, hib⟩ := absolute_moment_bound hE hθ hX hk hC hb hs
  have hiq := kernel_section_integrable hE hθ hX (normalizedPrice_measurable θ X)
    (show 0 ≤ 1 + η by linarith) (correction_abs_bound hc) hs
  have hi1 := kernel_section_integrable hE hθ hX
    (q := fun _ _ => 1) measurable_const (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ _ _ _ => by norm_num) hs
  have he : dyadicMixedMoment E θ X k s =
      ∫ x, momentKernel E θ X k (fun _ _ => 1) s x ∂dyadicProbabilityMeasure X := by
    simp only [dyadicMixedMoment, momentKernel, one_mul]
  rw [he, ← integral_sub hiq hi1]
  apply (norm_integral_le_of_norm_le (hi.const_mul ((1 + η) ^ k - 1)) ?_).trans
    (by simpa only [integral_const_mul] using mul_le_mul_of_nonneg_left hib hδ)
  filter_upwards [ae_dyadic_mem X] with x hx
  have hpc := product_correction Finset.univ hη (fun i _ => hc x hx (s i) (hs i))
  have hU0 := (position_bounds (k := k) hθ (by linarith : 0 < X) hx).1
  have heq : momentKernel E θ X k (normalizedPrice θ X) s x -
      momentKernel E θ X k (fun _ _ => 1) s x =
      (∏ i, normalizedPrice θ X (s i) x) *
        (dyadicU X x ^ ((k : ℝ) * dyadicR θ) * ∏ i, dyadicB E θ (s i) x) -
        (dyadicU X x ^ ((k : ℝ) * dyadicR θ) * ∏ i, dyadicB E θ (s i) x) := by
    simp only [momentKernel, one_mul, Finset.prod_mul_distrib]
    ring
  rw [heq, ← sub_one_mul, norm_mul, Real.norm_eq_abs (dyadicU X x ^ _ * _),
    abs_mul, abs_of_nonneg hU0, Finset.abs_prod]
  apply mul_le_mul_of_nonneg_right
    (by simpa only [Real.norm_eq_abs, Finset.card_univ, Fintype.card_fin] using hpc)
    (mul_nonneg hU0 (Finset.prod_nonneg (fun i _ => abs_nonneg _)))

/-- Uniform absolute increment moments and mixed-moment limits transfer to every L¹ profile. -/
theorem moment_transfer {E g : ℝ → ℝ} {θ : ℝ} {k : ℕ}
    {M : (Fin k → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hk : 0 < k) (hg : ProfileIntegrable g) (hM : MomentInterface E θ k M) :
    Tendsto (fun X : ℝ => ∫ x, dyadicZ E θ g X x ^ k ∂dyadicProbabilityMeasure X)
      atTop (𝓝 (∫ s, (∏ i, g (s i)) * M s ∂cubeMeasure k)) := by
  obtain ⟨⟨C, hC, hb⟩, hMm, hlim⟩ := hM
  obtain ⟨η, hηlim, hη⟩ := eventually_normalized_price_factor hθ0 hθ1
  let H : ℝ := 2 ^ ((k : ℝ) * dyadicR θ) * C
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hgprod : Integrable (fun s : Fin k → ℝ => ∏ i, |g (s i)|) (cubeMeasure k) :=
    Integrable.fintype_prod_dep (fun _i : Fin k => hg.2.abs)
  have hgp : Measurable (fun s : Fin k → ℝ => ∏ i, g (s i)) := by
    apply Finset.measurable_fun_prod
    intro i hi
    exact hg.1.comp (measurable_pi_apply i)
  have hlim0 : Tendsto (fun X : ℝ =>
      ∫ s, (∏ i, g (s i)) * dyadicMixedMoment E θ X k s ∂cubeMeasure k)
      atTop (𝓝 (∫ s, (∏ i, g (s i)) * M s ∂cubeMeasure k)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun s => (∏ i, |g (s i)|) * H)
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
      letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
      have hm := (kernel_measurable hE θ X k (q := fun _ _ => 1) measurable_const).stronglyMeasurable
        |>.integral_prod_right' (ν := dyadicProbabilityMeasure X)
      apply (hgp.mul ?_).aestronglyMeasurable
      change Measurable (fun s : Fin k → ℝ => ∫ x, dyadicU X x ^ ((k : ℝ) * dyadicR θ) *
        ∏ i, dyadicB E θ (s i) x ∂dyadicProbabilityMeasure X)
      simpa only [momentKernel, one_mul] using hm.measurable
    · filter_upwards [eventually_ge_atTop (4 : ℝ), hb] with X hX hbX
      filter_upwards [ae_cube_mem k] with s hs
      rw [norm_mul, norm_prod]
      simp only [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (mixed_moment_bound hE hθ1 hX hk hC hbX hs)
        (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    · exact hgprod.mul_const H
    · filter_upwards [ae_cube_mem k] with s hs
      exact (hlim s hs).const_mul _
  have herr : ∀ᶠ X : ℝ in atTop,
      ‖(∫ x, dyadicZ E θ g X x ^ k ∂dyadicProbabilityMeasure X) -
        (∫ s, (∏ i, g (s i)) * dyadicMixedMoment E θ X k s ∂cubeMeasure k)‖ ≤
        (((1 + η X) ^ k - 1) * H) * profileL1 g ^ k := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), hb, hη] with X hX hbX hηX
    letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
    have hc : ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
        |normalizedPrice θ X s x - 1| ≤ η X := hηX.2
    have hiw := kernel_integrable (k := k) hE hg hθ1 hX
      (normalizedPrice_measurable θ X) (show 0 ≤ 1 + η X by linarith [hηX.1])
      (correction_abs_bound hc)
    have hi0 := kernel_integrable (k := k) hE hg hθ1 hX
      (q := fun _ _ => 1) measurable_const (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ _ _ _ => by norm_num)
    have hiw' : Integrable (fun s : Fin k → ℝ => (∏ i, g (s i)) *
        (∫ x, momentKernel E θ X k (normalizedPrice θ X) s x ∂dyadicProbabilityMeasure X))
        (cubeMeasure k) := by
      simpa only [integral_const_mul] using hiw.integral_prod_left
    have hi0' : Integrable (fun s : Fin k → ℝ =>
        (∏ i, g (s i)) * dyadicMixedMoment E θ X k s) (cubeMeasure k) := by
      simpa only [integral_const_mul, momentKernel, one_mul, dyadicMixedMoment]
        using hi0.integral_prod_left
    rw [weighted_moment_eq hE hg hθ0 hθ1 hX hηX.1 hc, ← integral_sub hiw' hi0']
    have heq : (∫ s : Fin k → ℝ, (((1 + η X) ^ k - 1) * H) *
        (∏ i, |g (s i)|) ∂cubeMeasure k) =
        (((1 + η X) ^ k - 1) * H) * profileL1 g ^ k := by
      rw [integral_const_mul]
      congr 1
      simpa only [Fintype.card_fin, profileL1] using
        integral_fintype_prod_eq_pow (ι := Fin k) (μ := unitMeasure) (fun s => |g s|)
    rw [← heq]
    apply norm_integral_le_of_norm_le (hgprod.const_mul _)
    filter_upwards [ae_cube_mem k] with s hs
    rw [← mul_sub, norm_mul, norm_prod]
    simp only [Real.norm_eq_abs]
    have he := replacement_error hE hθ1 hX hk hC hηX.1 hbX hc hs
    simpa only [Real.norm_eq_abs, H, mul_comm] using
      mul_le_mul_of_nonneg_left he
        (Finset.prod_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (g (s i))))
  have herrorlim : Tendsto (fun X : ℝ =>
      (∫ x, dyadicZ E θ g X x ^ k ∂dyadicProbabilityMeasure X) -
        (∫ s, (∏ i, g (s i)) * dyadicMixedMoment E θ X k s ∂cubeMeasure k))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' herr
    have hδ := ((((tendsto_const_nhds (x := (1 : ℝ))).add hηlim).pow k).sub
      (tendsto_const_nhds (x := (1 : ℝ)))).mul_const H
      |>.mul_const (profileL1 g ^ k)
    simpa only [add_zero, one_pow, sub_self, zero_mul] using hδ
  have hfinal := herrorlim.add hlim0
  simpa only [sub_add_cancel, zero_add] using hfinal

end
end D5.S3.Arith.Robin.ForwardKernel.MomentTransfer
