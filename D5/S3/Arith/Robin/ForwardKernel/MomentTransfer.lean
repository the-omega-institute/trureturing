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

/-- The dyadic probability measure is supported on its closed dyadic interval. -/
lemma ae_dyadic_mem (X : ℝ) :
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

private lemma position_bounds {X x : ℝ} {k : ℕ} {e : Fin k → ℝ} (he : ∀ i, e i < 1)
    (hX : 0 < X) (hx : x ∈ Icc X (2 * X)) :
    0 ≤ dyadicU X x ^ (∑ i, dyadicR (e i)) ∧
      dyadicU X x ^ (∑ i, dyadicR (e i)) ≤ 2 ^ (∑ i, dyadicR (e i)) := by
  have hu0 : 0 ≤ dyadicU X x := div_nonneg (hX.le.trans hx.1) hX.le
  have hu2 : dyadicU X x ≤ 2 := (div_le_iff₀ hX).mpr hx.2
  refine ⟨Real.rpow_nonneg hu0 _, Real.rpow_le_rpow hu0 hu2 ?_⟩
  exact Finset.sum_nonneg (fun i _ => by dsimp [dyadicR, kappa]; linarith [he i])

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

/-- Hölder bounds a finite product by the product of the individual moment roots. -/
lemma product_moment_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {k : ℕ} (hk : 0 < k) {f : Fin k → α → ℝ} {C : Fin k → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hi : ∀ i, Integrable (fun x => |f i x| ^ k) μ)
    (hp : Integrable (fun x => ∏ i, |f i x|) μ)
    (hb : ∀ i, (∫ x, |f i x| ^ k ∂μ) ≤ C i) :
    (∫ x, ∏ i, |f i x| ∂μ) ≤ ∏ i, C i ^ (1 / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have he (a : ℝ≥0∞) : (a ^ k) ^ (1 / (k : ℝ)) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    simp [hk0]
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i x => (ENNReal.ofReal |f i x|) ^ k)
    (p := fun _ => 1 / (k : ℝ))
    (fun i _ => by
      simpa only [Real.norm_eq_abs] using
        (hf i).norm.aemeasurable.ennreal_ofReal.pow_const k)
    (by simp [hk0]) (fun _ _ => by positivity)
  simp only [he] at h
  have hl (i : Fin k) : (∫⁻ x, (ENNReal.ofReal |f i x|) ^ k ∂μ) ≤ ENNReal.ofReal (C i) := by
    simp_rw [← ENNReal.ofReal_pow (abs_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (Eventually.of_forall (fun x => by positivity))]
    exact ENNReal.ofReal_le_ofReal (hb i)
  have hh := h.trans (Finset.prod_le_prod
    (fun i _ => ENNReal.rpow_le_rpow (hl i) (by positivity : 0 ≤ 1 / (k : ℝ))))
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg (f i _))] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => abs_nonneg _)))] at hh
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hC _) (by positivity : 0 ≤ 1 / (k : ℝ))] at hh
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hC i) _)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hC i) _))).mp hh

private def momentKernel (E : ℝ → ℝ) {k : ℕ} (e : Fin k → ℝ) (X : ℝ)
    (q : Fin k → ℝ → ℝ → ℝ) (s : Fin k → ℝ) (x : ℝ) : ℝ :=
  dyadicU X x ^ (∑ i, dyadicR (e i)) * ∏ i, q i (s i) x * dyadicB E (e i) (s i) x

private lemma kernel_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {k : ℕ} (e : Fin k → ℝ) (X : ℝ) {q : Fin k → ℝ → ℝ → ℝ}
    (hq : ∀ i, Measurable (fun p : ℝ × ℝ => q i p.1 p.2)) :
    Measurable (fun p : (Fin k → ℝ) × ℝ => momentKernel E e X q p.1 p.2) := by
  unfold momentKernel dyadicU
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_fun_prod
  intro i hi
  have hm : Measurable (fun p : (Fin k → ℝ) × ℝ => (p.1 i, p.2)) := by fun_prop
  have hb : Measurable (fun p : (Fin k → ℝ) × ℝ => dyadicB E (e i) (p.1 i) p.2) :=
    (MomentTransferDefs.dyadicB_measurable hE (e i)).comp hm
  exact ((hq i).comp hm).mul hb

private lemma kernel_bound {E : ℝ → ℝ} {X A : ℝ} {k : ℕ} {e D : Fin k → ℝ}
    {q : Fin k → ℝ → ℝ → ℝ} (he : ∀ i, e i < 1) (hX : 0 < X) (hA : 0 ≤ A)
    (hB : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |dyadicB E (e i) s x| ≤ D i)
    (hq : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q i s x| ≤ A)
    {s : Fin k → ℝ} {x : ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc X (2 * X)) :
    ‖momentKernel E e X q s x‖ ≤
      2 ^ (∑ i, dyadicR (e i)) * (∏ i, A * D i) := by
  obtain ⟨hU0, hU⟩ := position_bounds he hX hx
  unfold momentKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0, Finset.abs_prod]
  apply mul_le_mul hU _ (Finset.prod_nonneg (fun i _ => abs_nonneg _)) (by positivity)
  calc
    _ ≤ ∏ i : Fin k, A * D i := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        rw [abs_mul]
        exact mul_le_mul (hq i (s i) (hs i) x hx) (hB i (s i) (hs i) x hx)
          (abs_nonneg _) hA
    _ = _ := by simp

private lemma kernel_integrable {k : ℕ} {E : ℝ → ℝ} {G : Fin k → ℝ → ℝ} {X A : ℝ} {e : Fin k → ℝ}
    (hE : LocallyBoundedMeasurable E) (hG : ∀ i, ProfileIntegrable (G i))
    (he : ∀ i, e i < 1) (hX : 4 ≤ X) {q : Fin k → ℝ → ℝ → ℝ}
    (hq : ∀ i, Measurable (fun p : ℝ × ℝ => q i p.1 p.2)) (hA : 0 ≤ A)
    (hqb : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q i s x| ≤ A) :
    Integrable (fun p : (Fin k → ℝ) × ℝ =>
      (∏ i, G i (p.1 i)) * momentKernel E e X q p.1 p.2)
      ((cubeMeasure k).prod (dyadicProbabilityMeasure X)) := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  choose D hD hDb using (fun i => dyadicB_uniform_bound hE (e i) hX)
  have hi : Integrable (fun p : (Fin k → ℝ) × ℝ => ∏ i, G i (p.1 i))
      ((cubeMeasure k).prod (dyadicProbabilityMeasure X)) := by
    simpa only [mul_one] using (Integrable.fintype_prod_dep (fun i : Fin k => (hG i).2)).mul_prod
      (integrable_const (1 : ℝ) : Integrable _ (dyadicProbabilityMeasure X))
  apply hi.mul_bdd (kernel_measurable hE e X hq).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_cube_mem k),
    Measure.quasiMeasurePreserving_snd.ae (ae_dyadic_mem X)] with p hs hx
  exact kernel_bound he hX0 hA hDb hqb hs hx

private lemma kernel_section_integrable {E : ℝ → ℝ} {X A : ℝ} {k : ℕ} {e : Fin k → ℝ}
    (hE : LocallyBoundedMeasurable E) (he : ∀ i, e i < 1) (hX : 4 ≤ X)
    {q : Fin k → ℝ → ℝ → ℝ} (hq : ∀ i, Measurable (fun p : ℝ × ℝ => q i p.1 p.2))
    (hA : 0 ≤ A)
    (hqb : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X), |q i s x| ≤ A)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    Integrable (momentKernel E e X q s) (dyadicProbabilityMeasure X) := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  choose D hD hDb using (fun i => dyadicB_uniform_bound hE (e i) hX)
  apply Integrable.of_bound
    ((kernel_measurable hE e X hq).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [ae_dyadic_mem X] with x hx
  exact kernel_bound he hX0 hA hDb hqb hs hx

private lemma absolute_moment_bound {E : ℝ → ℝ} {X C : ℝ} {k : ℕ} {e : Fin k → ℝ}
    (hE : LocallyBoundedMeasurable E) (he : ∀ i, e i < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C)
    (hb : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E (e i) s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x => dyadicU X x ^ (∑ i, dyadicR (e i)) *
      ∏ i, |dyadicB E (e i) (s i) x|) (dyadicProbabilityMeasure X) ∧
    (∫ x, dyadicU X x ^ (∑ i, dyadicR (e i)) * ∏ i, |dyadicB E (e i) (s i) x|
      ∂dyadicProbabilityMeasure X) ≤ 2 ^ (∑ i, dyadicR (e i)) * C := by
  have hX0 : 0 < X := by linarith
  letI := dyadicProbabilityMeasure_isProbabilityMeasure hX0
  choose D hD hDb using (fun i => dyadicB_uniform_bound hE (e i) hX)
  have hm (i : Fin k) : Measurable (fun x => dyadicB E (e i) (s i) x) :=
    (dyadicB_measurable hE (e i)).comp (measurable_const.prodMk measurable_id)
  have hip (i : Fin k) : Integrable (fun x => |dyadicB E (e i) (s i) x| ^ k)
      (dyadicProbabilityMeasure X) := by
    apply Integrable.of_bound (by fun_prop) (D i ^ k)
    filter_upwards [ae_dyadic_mem X] with x hx
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hDb i (s i) (hs i) x hx) k
  have hp : Integrable (fun x => ∏ i, |dyadicB E (e i) (s i) x|)
      (dyadicProbabilityMeasure X) := by
    apply Integrable.of_bound (by fun_prop) (∏ i, D i)
    filter_upwards [ae_dyadic_mem X] with x hx
    rw [Real.norm_eq_abs, Finset.abs_prod]
    simp only [abs_abs]
    calc
      _ ≤ ∏ i : Fin k, D i := Finset.prod_le_prod₀
        (fun i _ => abs_nonneg _) (fun i _ => hDb i (s i) (hs i) x hx)
      _ = _ := by simp
  have hholder := product_moment_bound hk (fun _ => hC)
    (fun i => (hm i).aestronglyMeasurable) hip hp (fun i => hb i (s i) (hs i))
  have hconst : (∏ _i : Fin k, C ^ (1 / (k : ℝ))) = C := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    simp [Nat.cast_ne_zero.mpr hk.ne']
  rw [hconst] at hholder
  have hU : ∀ᵐ x ∂dyadicProbabilityMeasure X,
      ‖dyadicU X x ^ (∑ i, dyadicR (e i))‖ ≤ 2 ^ (∑ i, dyadicR (e i)) := by
    filter_upwards [ae_dyadic_mem X] with x hx
    obtain ⟨h0, h1⟩ := position_bounds he hX0 hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hi := hp.bdd_mul
    ((measurable_id.div_const X).pow_const (∑ i, dyadicR (e i))).aestronglyMeasurable hU
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 ^ (∑ i, dyadicR (e i)) * ∏ i, |dyadicB E (e i) (s i) x|
        ∂dyadicProbabilityMeasure X := by
      apply integral_mono_ae hi (hp.const_mul _)
      filter_upwards [ae_dyadic_mem X] with x hx
      exact mul_le_mul_of_nonneg_right (position_bounds he hX0 hx).2
        (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = 2 ^ (∑ i, dyadicR (e i)) *
        (∫ x, ∏ i, |dyadicB E (e i) (s i) x| ∂dyadicProbabilityMeasure X) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hholder (by positivity)

private lemma mixed_moment_bound {E : ℝ → ℝ} {X C : ℝ} {k : ℕ} {e : Fin k → ℝ}
    (hE : LocallyBoundedMeasurable E) (he : ∀ i, e i < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C)
    (hb : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E (e i) s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    ‖jointDyadicMixedMoment E e X s‖ ≤ 2 ^ (∑ i, dyadicR (e i)) * C := by
  obtain ⟨hi, hb'⟩ := absolute_moment_bound hE he hX hk hC hb hs
  apply (norm_integral_le_of_norm_le hi ?_).trans hb'
  filter_upwards [ae_dyadic_mem X] with x hx
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (position_bounds he (by linarith : 0 < X) hx).1,
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

private lemma weighted_moment_eq {k : ℕ} {E : ℝ → ℝ}
    {G : Fin k → ℝ → ℝ} {e : Fin k → ℝ} {X η : ℝ}
    (hE : LocallyBoundedMeasurable E) (hG : ∀ i, ProfileIntegrable (G i))
    (he0 : ∀ i, 0 < e i) (he1 : ∀ i, e i < 1) (hX : 4 ≤ X) (hη : 0 ≤ η)
    (hc : ∀ i, ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
      |normalizedPrice (e i) X s x - 1| ≤ η) :
    (∫ x, ∏ i, dyadicZ E (e i) (G i) X x ∂dyadicProbabilityMeasure X) =
      ∫ s, (∏ i, G i (s i)) *
        (∫ x, momentKernel E e X (fun i => normalizedPrice (e i) X) s x
          ∂dyadicProbabilityMeasure X) ∂cubeMeasure k := by
  letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
  have hi := kernel_integrable hE hG he1 hX
    (fun i => normalizedPrice_measurable (e i) X) (show 0 ≤ 1 + η by linarith)
    (fun i => correction_abs_bound (hc i))
  have heq : ∀ᵐ x ∂dyadicProbabilityMeasure X,
      (∏ i, dyadicZ E (e i) (G i) X x) =
        ∫ s, (∏ i, G i (s i)) *
          momentKernel E e X (fun i => normalizedPrice (e i) X) s x ∂cubeMeasure k := by
    filter_upwards [ae_dyadic_mem X] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hz (i : Fin k) : dyadicZ E (e i) (G i) X x = dyadicU X x ^ dyadicR (e i) *
        (∫ s, G i s * (normalizedPrice (e i) X s x * dyadicB E (e i) s x)
          ∂unitMeasure) := by
      rw [dyadicZ_eq_weighted_integral hE (hG i) (he0 i) hX hx.1 hx.2]
      have hh : (∫ s, G i s * (normalizedPrice (e i) X s x * dyadicB E (e i) s x)
          ∂unitMeasure) = Real.sqrt (Real.log x / Real.log X) *
            (∫ s, G i s * dyadicB E (e i) s x * priceRatio x (s * x ^ e i)
              ∂unitMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => by unfold normalizedPrice; ring)
      rw [hh]; ring
    simp_rw [hz]
    rw [Finset.prod_mul_distrib, ← integral_fintype_prod_eq_prod, ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro s
    have hpow : (∏ i, dyadicU X x ^ dyadicR (e i)) =
        dyadicU X x ^ (∑ i, dyadicR (e i)) :=
      (Real.rpow_sum_of_pos (div_pos hx0 (by linarith : 0 < X)) _ _).symm
    dsimp only
    rw [hpow, Finset.prod_mul_distrib]
    unfold momentKernel
    ring
  rw [integral_congr_ae heq, ← integral_integral_swap hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => integral_const_mul _ _)

private lemma replacement_error {E : ℝ → ℝ} {X C η : ℝ} {k : ℕ} {e : Fin k → ℝ}
    (hE : LocallyBoundedMeasurable E) (he : ∀ i, e i < 1) (hX : 4 ≤ X)
    (hk : 0 < k) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hb : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E (e i) s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C)
    (hc : ∀ i, ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
      |normalizedPrice (e i) X s x - 1| ≤ η)
    {s : Fin k → ℝ} (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    ‖(∫ x, momentKernel E e X (fun i => normalizedPrice (e i) X) s x ∂dyadicProbabilityMeasure X) -
      jointDyadicMixedMoment E e X s‖ ≤
      ((1 + η) ^ k - 1) * (2 ^ (∑ i, dyadicR (e i)) * C) := by
  have hδ : 0 ≤ (1 + η) ^ k - 1 := by
    have : 1 ≤ (1 + η) ^ k := one_le_pow₀ (show 1 ≤ 1 + η by linarith)
    linarith
  obtain ⟨hi, hib⟩ := absolute_moment_bound hE he hX hk hC hb hs
  have hiq := kernel_section_integrable hE he hX (fun i => normalizedPrice_measurable (e i) X)
    (show 0 ≤ 1 + η by linarith) (fun i => correction_abs_bound (hc i)) hs
  have hi1 := kernel_section_integrable hE he hX
    (q := fun _ _ _ => 1) (fun _ => measurable_const) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ _ _ _ _ => by norm_num) hs
  have hconst : jointDyadicMixedMoment E e X s =
      ∫ x, momentKernel E e X (fun _ _ _ => 1) s x ∂dyadicProbabilityMeasure X := by
    simp only [jointDyadicMixedMoment, momentKernel, one_mul]
  rw [hconst, ← integral_sub hiq hi1]
  apply (norm_integral_le_of_norm_le (hi.const_mul ((1 + η) ^ k - 1)) ?_).trans
    (by simpa only [integral_const_mul] using mul_le_mul_of_nonneg_left hib hδ)
  filter_upwards [ae_dyadic_mem X] with x hx
  have hpc := product_correction Finset.univ hη (fun i _ => hc i x hx (s i) (hs i))
  have hU0 := (position_bounds he (by linarith : 0 < X) hx).1
  have heq : momentKernel E e X (fun i => normalizedPrice (e i) X) s x -
      momentKernel E e X (fun _ _ _ => 1) s x =
      (∏ i, normalizedPrice (e i) X (s i) x) *
        (dyadicU X x ^ (∑ i, dyadicR (e i)) * ∏ i, dyadicB E (e i) (s i) x) -
        (dyadicU X x ^ (∑ i, dyadicR (e i)) * ∏ i, dyadicB E (e i) (s i) x) := by
    simp only [momentKernel, one_mul, Finset.prod_mul_distrib]
    ring
  rw [heq, ← sub_one_mul, norm_mul, Real.norm_eq_abs (dyadicU X x ^ _ * _),
    abs_mul, abs_of_nonneg hU0, Finset.abs_prod]
  apply mul_le_mul_of_nonneg_right
    (by simpa only [Real.norm_eq_abs, Finset.card_univ, Fintype.card_fin] using hpc)
    (mul_nonneg hU0 (Finset.prod_nonneg (fun i _ => abs_nonneg _)))

/-- Joint mixed increment limits transfer to products of integrable profile responses. -/
theorem joint_moment_transfer {E : ℝ → ℝ} {k : ℕ} {e : Fin k → ℝ}
    {G : Fin k → ℝ → ℝ} {M : (Fin k → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E) (he0 : ∀ i, 0 < e i)
    (he1 : ∀ i, e i < 1) (hk : 0 < k) (hG : ∀ i, ProfileIntegrable (G i))
    (hM : JointMomentInterface E e M) :
    Tendsto (fun X : ℝ => ∫ x, ∏ i, dyadicZ E (e i) (G i) X x
      ∂dyadicProbabilityMeasure X) atTop
      (𝓝 (∫ s, (∏ i, G i (s i)) * M s ∂cubeMeasure k)) := by
  obtain ⟨⟨C, hC, hb⟩, hlim⟩ := hM
  choose ηi hηilim hηi using (fun i => eventually_normalized_price_factor (he0 i) (he1 i))
  let η : ℝ → ℝ := fun X => ∑ i, |ηi i X|
  have hηlim : Tendsto η atTop (𝓝 0) := by
    simpa only [abs_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => (hηilim i).abs)
  have hη : ∀ᶠ X : ℝ in atTop, 0 ≤ η X ∧
      ∀ i, ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
        |normalizedPrice (e i) X s x - 1| ≤ η X := by
    filter_upwards [Filter.eventually_all.mpr hηi] with X hX
    refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
    intro i x hx s hs
    exact ((hX i).2 x hx s hs).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (ηi j X)) (Finset.mem_univ i)))
  let H : ℝ := 2 ^ (∑ i, dyadicR (e i)) * C
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hgprod : Integrable (fun s : Fin k → ℝ => ∏ i, |G i (s i)|) (cubeMeasure k) :=
    Integrable.fintype_prod_dep (fun i : Fin k => (hG i).2.abs)
  have hgp : Measurable (fun s : Fin k → ℝ => ∏ i, G i (s i)) := by
    apply Finset.measurable_fun_prod
    intro i hi
    exact (hG i).1.comp (measurable_pi_apply i)
  have hlim0 : Tendsto (fun X : ℝ =>
      ∫ s, (∏ i, G i (s i)) * jointDyadicMixedMoment E e X s ∂cubeMeasure k)
      atTop (𝓝 (∫ s, (∏ i, G i (s i)) * M s ∂cubeMeasure k)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun s => (∏ i, |G i (s i)|) * H)
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
      letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
      have hm := (kernel_measurable hE e X (q := fun _ _ _ => 1) (fun _ => measurable_const)).stronglyMeasurable
        |>.integral_prod_right' (ν := dyadicProbabilityMeasure X)
      apply (hgp.mul ?_).aestronglyMeasurable
      change Measurable (fun s : Fin k → ℝ => ∫ x, dyadicU X x ^ (∑ i, dyadicR (e i)) *
        ∏ i, dyadicB E (e i) (s i) x ∂dyadicProbabilityMeasure X)
      simpa only [momentKernel, one_mul] using hm.measurable
    · filter_upwards [eventually_ge_atTop (4 : ℝ), hb] with X hX hbX
      filter_upwards [ae_cube_mem k] with s hs
      rw [norm_mul, norm_prod]
      simp only [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (mixed_moment_bound hE he1 hX hk hC hbX hs)
        (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    · exact hgprod.mul_const H
    · filter_upwards [ae_cube_mem k] with s hs
      exact (hlim s hs).const_mul _
  have herr : ∀ᶠ X : ℝ in atTop,
      ‖(∫ x, (∏ i, dyadicZ E (e i) (G i) X x) ∂dyadicProbabilityMeasure X) -
        (∫ s, (∏ i, G i (s i)) * jointDyadicMixedMoment E e X s ∂cubeMeasure k)‖ ≤
        (((1 + η X) ^ k - 1) * H) * (∏ i, profileL1 (G i)) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), hb, hη] with X hX hbX hηX
    letI := dyadicProbabilityMeasure_isProbabilityMeasure (show 0 < X by linarith)
    have hc : ∀ i, ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
        |normalizedPrice (e i) X s x - 1| ≤ η X := hηX.2
    have hiw := kernel_integrable hE hG he1 hX
      (fun i => normalizedPrice_measurable (e i) X) (show 0 ≤ 1 + η X by linarith [hηX.1])
      (fun i => correction_abs_bound (hc i))
    have hi0 := kernel_integrable hE hG he1 hX
      (q := fun _ _ _ => 1) (fun _ => measurable_const) (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ _ _ _ _ => by norm_num)
    have hiw' : Integrable (fun s : Fin k → ℝ => (∏ i, G i (s i)) *
        (∫ x, momentKernel E e X (fun i => normalizedPrice (e i) X) s x ∂dyadicProbabilityMeasure X))
        (cubeMeasure k) := by
      simpa only [integral_const_mul] using hiw.integral_prod_left
    have hi0' : Integrable (fun s : Fin k → ℝ =>
        (∏ i, G i (s i)) * jointDyadicMixedMoment E e X s) (cubeMeasure k) := by
      simpa only [integral_const_mul, momentKernel, one_mul, jointDyadicMixedMoment]
        using hi0.integral_prod_left
    rw [weighted_moment_eq hE hG he0 he1 hX hηX.1 hc, ← integral_sub hiw' hi0']
    have heq : (∫ s : Fin k → ℝ, (((1 + η X) ^ k - 1) * H) *
        (∏ i, |G i (s i)|) ∂cubeMeasure k) =
        (((1 + η X) ^ k - 1) * H) * (∏ i, profileL1 (G i)) := by
      rw [integral_const_mul]
      congr 1
      simpa only [profileL1] using
        integral_fintype_prod_eq_prod (μ := fun _ : Fin k => unitMeasure)
          (fun i s => |G i s|)
    rw [← heq]
    apply norm_integral_le_of_norm_le (hgprod.const_mul _)
    filter_upwards [ae_cube_mem k] with s hs
    rw [← mul_sub, norm_mul, norm_prod]
    simp only [Real.norm_eq_abs]
    have he := replacement_error hE he1 hX hk hC hηX.1 hbX hc hs
    simpa only [Real.norm_eq_abs, H, mul_comm] using
      mul_le_mul_of_nonneg_left he
        (Finset.prod_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (G i (s i))))
  have herrorlim : Tendsto (fun X : ℝ =>
      (∫ x, (∏ i, dyadicZ E (e i) (G i) X x) ∂dyadicProbabilityMeasure X) -
        (∫ s, (∏ i, G i (s i)) * jointDyadicMixedMoment E e X s ∂cubeMeasure k))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' herr
    have hδ := ((((tendsto_const_nhds (x := (1 : ℝ))).add hηlim).pow k).sub
      (tendsto_const_nhds (x := (1 : ℝ)))).mul_const H
      |>.mul_const ((∏ i, profileL1 (G i)))
    simpa only [add_zero, one_pow, sub_self, zero_mul] using hδ
  have hfinal := herrorlim.add hlim0
  simpa only [sub_add_cancel, zero_add] using hfinal


/-- Uniform absolute increment moments and mixed-moment limits transfer to every L¹ profile. -/
theorem moment_transfer {E g : ℝ → ℝ} {θ : ℝ} {k : ℕ}
    {M : (Fin k → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hk : 0 < k) (hg : ProfileIntegrable g) (hM : MomentInterface E θ k M) :
    Tendsto (fun X : ℝ => ∫ x, dyadicZ E θ g X x ^ k ∂dyadicProbabilityMeasure X)
      atTop (𝓝 (∫ s, (∏ i, g (s i)) * M s ∂cubeMeasure k)) := by
  have hJ : JointMomentInterface E (fun _ : Fin k => θ) M := by
    obtain ⟨⟨C, hC, hb⟩, _hMm, hlim⟩ := hM
    refine ⟨⟨C, hC, ?_⟩, ?_⟩
    · filter_upwards [hb] with X hX
      exact fun _ => hX
    · intro s hs
      simpa only [jointDyadicMixedMoment, dyadicMixedMoment, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hlim s hs
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    joint_moment_transfer hE (fun _ => hθ0) (fun _ => hθ1) hk (fun _ => hg) hJ

end
end D5.S3.Arith.Robin.ForwardKernel.MomentTransfer
