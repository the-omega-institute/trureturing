/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second and fourth moment bounds control continuous sampling and weighted product replacement. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CellMomentBounds
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ContinuousSampling
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedIntegralTools

/-! Fourth moment errors and weighted product replacement on the fixed unit sampling interval. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_sampling_fourth_error (N H M a b : ℝ) (hN : 2 ≤ N)
    (hH : 1 ≤ H) (_hM : 1 ≤ M) (hMH : M * H ≤ N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) :
    (∫ t in (1 : ℝ)..2,
      |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| ^ 4) ≤
        ((2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N)) ^ 4 := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hQ : 0 < Real.sqrt (H * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 : ℝ)) (b := 2)
    (C := ((2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N)) ^ 4)
    (f := fun t => |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| ^ 4) ?_
  · exact (le_abs_self _).trans (by norm_num at hi ⊢; exact hi)
  intro t ht
  have ht0 : t ∈ Ioc (1 : ℝ) 2 := by norm_num [uIoc] at ht ⊢; exact ht
  have ht' : t ∈ Icc (1 : ℝ) 2 := ⟨ht0.1.le, ht0.2⟩
  have hx : N * t ∈ Icc N (2 * N) := by constructor <;> nlinarith [ht'.1, ht'.2]
  have hp := sampling_pointwise hN hH ha hab hb hMH hx
  have hdiff : |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| ≤
      (2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N) := by
    rw [Z, ← sub_div, abs_div, abs_of_pos hQ]
    exact div_le_div_of_nonneg_right hp hQ.le
  simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
    pow_le_pow_left₀ (abs_nonneg _) hdiff 4

private theorem p_sampling_error_rate (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, N ^ α ≤ H →
      (2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N) ≤ δ := by
  filter_upwards [sqrt_rate α (δ / 8) hα (by positivity),
    eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hsmall hN hL H hH
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 α).trans_le hH
  have hQ : 0 < Real.sqrt (H * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hnum : 2 * Real.log (4 * N) + 2 ≤ 8 * Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    linarith
  have he : Real.log N / Real.sqrt (H * Real.log N) = Real.sqrt (Real.log N / H) := by
    rw [Real.sqrt_mul hH0.le, div_mul_eq_div_div, div_right_comm, Real.div_sqrt,
      ← Real.sqrt_div (by linarith : 0 ≤ Real.log N)]
  calc
    _ ≤ (8 * Real.log N) / Real.sqrt (H * Real.log N) :=
      div_le_div_of_nonneg_right hnum hQ.le
    _ = 8 * Real.sqrt (Real.log N / H) := by rw [mul_div_assoc, he]
    _ ≤ 8 * (δ / 8) := mul_le_mul_of_nonneg_left (hsmall H hH) (by norm_num)
    _ = δ := by ring

private theorem p_fourth_bound_transfer (f g : ℝ → ℝ) (K D : ℝ)
    (hf : MemLp f 4 (volume.restrict (Icc (1 : ℝ) 2)))
    (hg : MemLp g 4 (volume.restrict (Icc (1 : ℝ) 2)))
    (hgb : (∫ t in (1 : ℝ)..2, |g t| ^ 4) ≤ K)
    (hdb : (∫ t in (1 : ℝ)..2, |f t - g t| ^ 4) ≤ D) :
    (∫ t in (1 : ℝ)..2, |f t| ^ 4) ≤ 8 * (K + D) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    ← integral_Icc_eq_integral_Ioc] at hgb hdb ⊢
  have hfi : Integrable (fun t => |f t| ^ 4) (volume.restrict (Icc (1 : ℝ) 2)) := by
    simpa only [Real.norm_eq_abs] using hf.integrable_norm_pow (by norm_num : 4 ≠ 0)
  have hgi : Integrable (fun t => |g t| ^ 4) (volume.restrict (Icc (1 : ℝ) 2)) := by
    simpa only [Real.norm_eq_abs] using hg.integrable_norm_pow (by norm_num : 4 ≠ 0)
  have hdi : Integrable (fun t => |f t - g t| ^ 4) (volume.restrict (Icc (1 : ℝ) 2)) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub hg).integrable_norm_pow (by norm_num : 4 ≠ 0)
  calc
    _ ≤ ∫ t in Icc (1 : ℝ) 2, 8 * (|g t| ^ 4 + |f t - g t| ^ 4) := by
      apply integral_mono hfi ((hgi.add hdi).const_mul 8)
      intro t
      have hp := (show Even 4 by decide).add_pow_le (a := g t) (b := f t - g t)
      rw [show g t + (f t - g t) = f t by ring] at hp
      norm_num only [Nat.reduceSub, Nat.reducePow] at hp
      simpa only [Even.pow_abs (show Even 4 by decide), Pi.add_apply] using hp
    _ = 8 * ((∫ t in Icc (1 : ℝ) 2, |g t| ^ 4) +
        (∫ t in Icc (1 : ℝ) 2, |f t - g t| ^ 4)) := by
      rw [integral_const_mul, integral_add hgi hdi]
    _ ≤ 8 * (K + D) := mul_le_mul_of_nonneg_left (add_le_add hgb hdb) (by norm_num)

/-- A bounded weight preserves the fourth moment bound for finite product replacement. -/
theorem weighted_product_difference (k : ℕ) (f g : Fin k → ℝ → ℝ)
    (w : ℝ → ℝ) (K D B : ℝ) (hk : 0 < k) (hk4 : k ≤ 4)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hf : ∀ i, MemLp (f i) 4 (volume.restrict (Icc (1 : ℝ) 2)) ∧
      MemLp (g i) 4 (volume.restrict (Icc (1 : ℝ) 2)))
    (hfb : ∀ i, (∫ t in (1 : ℝ)..2, |f i t| ^ 4) ≤ K)
    (hgb : ∀ i, (∫ t in (1 : ℝ)..2, |g i t| ^ 4) ≤ K)
    (hdb : ∀ i, (∫ t in (1 : ℝ)..2, |f i t - g i t| ^ 4) ≤ D)
    (hw : IntervalIntegrable w volume 1 2)
    (hwb : ∀ t ∈ Icc (1 : ℝ) 2, |w t| ≤ B) :
    |(∫ t in (1 : ℝ)..2, w t * (∏ i, f i t))-
      (∫ t in (1 : ℝ)..2, w t * (∏ i, g i t))| ≤
      B * (k : ℝ) * D ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4) := by
  let μ := volume.restrict (Icc (1 : ℝ) 2)
  let : IsProbabilityMeasure μ := unit_dyadic_probability
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    ← integral_Icc_eq_integral_Ioc] at hfb hgb hdb ⊢
  have hwi : IntegrableOn w (Icc (1 : ℝ) 2) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hw.1
  have hwm : AEStronglyMeasurable w μ := hwi.aestronglyMeasurable
  have hwb' : ∀ᵐ t ∂μ, ‖w t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (Real.norm_eq_abs _).le.trans (hwb t ht)
  have hif : Integrable (fun t => ∏ i, f i t) μ :=
    FourthTransfer.FiniteProductMomentBounds.product_integrable hk
      (fun i => (hf i).1.mono_exponent (by exact_mod_cast hk4))
  have hig : Integrable (fun t => ∏ i, g i t) μ :=
    FourthTransfer.FiniteProductMomentBounds.product_integrable hk
      (fun i => (hf i).2.mono_exponent (by exact_mod_cast hk4))
  have hwf := hif.bdd_mul hwm hwb'
  have hwg := hig.bdd_mul hwm hwb'
  have hrep := FourthTransfer.FiniteProductMomentBounds.product_fourth_difference_bound hk hk4 hK hD hf hfb hgb hdb
  rw [← integral_sub hwf hwg]
  calc
    _ ≤ ∫ t, |w t * (∏ i, f i t) - w t * (∏ i, g i t)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t, B * |(∏ i, f i t) - (∏ i, g i t)| ∂μ := by
      apply integral_mono_ae (hwf.sub hwg).abs ((hif.sub hig).abs.const_mul B)
      filter_upwards [hwb'] with t ht
      simp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using ht) (abs_nonneg _)
    _ = B * (∫ t, |(∏ i, f i t) - (∏ i, g i t)| ∂μ) := integral_const_mul _ _
    _ ≤ B * ((k : ℝ) * D ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4)) := mul_le_mul_of_nonneg_left hrep hB
    _ = _ := by ring

/-- A cubic product is stable under a uniformly bounded perturbation using only second
moment bounds. The separate cubic products are assumed integrable, with no bound on their
third moments. -/
theorem weighted_cubic_difference (f g : Fin 3 → ℝ → ℝ)
    (w : ℝ → ℝ) (K e B : ℝ) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (Icc (1 : ℝ) 2)) ∧
      MemLp (g i) 2 (volume.restrict (Icc (1 : ℝ) 2)))
    (hif : Integrable (fun t => ∏ i, f i t) (volume.restrict (Icc (1 : ℝ) 2)))
    (hig : Integrable (fun t => ∏ i, g i t) (volume.restrict (Icc (1 : ℝ) 2)))
    (hfb : ∀ i, (∫ t in (1 : ℝ)..2, |f i t| ^ 2) ≤ K)
    (hgb : ∀ i, (∫ t in (1 : ℝ)..2, |g i t| ^ 2) ≤ K)
    (hdb : ∀ i t, t ∈ Icc (1 : ℝ) 2 → |f i t - g i t| ≤ e)
    (hw : IntervalIntegrable w volume 1 2)
    (hwb : ∀ t ∈ Icc (1 : ℝ) 2, |w t| ≤ B) :
    |(∫ t in (1 : ℝ)..2, w t * (∏ i, f i t)) -
      (∫ t in (1 : ℝ)..2, w t * (∏ i, g i t))| ≤ 6 * B * e * K := by
  let μ := volume.restrict (Icc (1 : ℝ) 2)
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    ← integral_Icc_eq_integral_Ioc] at hfb hgb ⊢
  have hwi : IntegrableOn w (Icc (1 : ℝ) 2) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hw.1
  have hwb' : ∀ᵐ t ∂μ, ‖w t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs] using hwb t ht
  have hwf := hif.bdd_mul hwi.aestronglyMeasurable hwb'
  have hwg := hig.bdd_mul hwi.aestronglyMeasurable hwb'
  have hfi (i : Fin 3) : Integrable (fun t => |f i t| ^ 2) μ := by
    simpa only [Real.norm_eq_abs] using (hf i).1.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hgi (i : Fin 3) : Integrable (fun t => |g i t| ^ 2) μ := by
    simpa only [Real.norm_eq_abs] using (hf i).2.integrable_norm_pow (by norm_num : 2 ≠ 0)
  let U := fun t => (∑ i, |f i t| ^ 2) + ∑ i, |g i t| ^ 2
  have hUi : Integrable U μ :=
    (integrable_finsetSum _ (fun i _ => hfi i)).add
      (integrable_finsetSum _ (fun i _ => hgi i))
  have hpoint (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      |(∏ i, f i t) - (∏ i, g i t)| ≤ e * U t := by
    have htel : (∏ i, f i t) - (∏ i, g i t) =
        (f 0 t - g 0 t) * f 1 t * f 2 t +
        g 0 t * (f 1 t - g 1 t) * f 2 t +
        g 0 t * g 1 t * (f 2 t - g 2 t) := by
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      ring
    have h₀ := hdb 0 t ht
    have h₁ := hdb 1 t ht
    have h₂ := hdb 2 t ht
    have hp (u v : ℝ) : |u| * |v| ≤ (|u| ^ 2 + |v| ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u| - |v|)]
    calc
      _ ≤ |f 0 t - g 0 t| * |f 1 t| * |f 2 t| +
          |g 0 t| * |f 1 t - g 1 t| * |f 2 t| +
          |g 0 t| * |g 1 t| * |f 2 t - g 2 t| := by
        rw [htel]
        simpa only [abs_mul] using
          (abs_add_le ((f 0 t - g 0 t) * f 1 t * f 2 t +
            g 0 t * (f 1 t - g 1 t) * f 2 t)
            (g 0 t * g 1 t * (f 2 t - g 2 t))).trans
            (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ e * |f 1 t| * |f 2 t| + |g 0 t| * e * |f 2 t| +
          |g 0 t| * |g 1 t| * e := by gcongr
      _ ≤ e * U t := by
        dsimp [U]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        nlinarith [mul_le_mul_of_nonneg_left (hp (f 1 t) (f 2 t)) he,
          mul_le_mul_of_nonneg_left (hp (g 0 t) (f 2 t)) he,
          mul_le_mul_of_nonneg_left (hp (g 0 t) (g 1 t)) he,
          mul_nonneg he (sq_nonneg |f 0 t|),
          mul_nonneg he (sq_nonneg |f 1 t|),
          mul_nonneg he (sq_nonneg |g 1 t|),
          mul_nonneg he (sq_nonneg |g 2 t|)]
  rw [← integral_sub hwf hwg]
  calc
    _ ≤ ∫ t, |w t * (∏ i, f i t) - w t * (∏ i, g i t)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t, B * e * U t ∂μ := by
      apply integral_mono_ae (hwf.sub hwg).abs (hUi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ B * (e * U t) := mul_le_mul (hwb t ht) (hpoint t ht)
          (abs_nonneg _) hB
        _ = _ := by ring
    _ = B * e * ((∑ i, ∫ t, |f i t| ^ 2 ∂μ) +
        ∑ i, ∫ t, |g i t| ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add
        (integrable_finsetSum _ (fun i _ => hfi i))
        (integrable_finsetSum _ (fun i _ => hgi i)),
        integral_finsetSum _ (fun i _ => hfi i),
        integral_finsetSum _ (fun i _ => hgi i)]
    _ ≤ B * e * ((∑ _i : Fin 3, K) + ∑ _i : Fin 3, K) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (Finset.sum_le_sum (fun i _ => hfb i))
          (Finset.sum_le_sum (fun i _ => hgb i))) (mul_nonneg hB he)
    _ = _ := by simp; ring

/-- Continuous and cell increments have uniform second moments and a vanishing pointwise
sampling error. Membership in L4 records boundedness for each individual sampling scale;
no uniform fourth moment estimate is used. -/
theorem uniform_sampling_second (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 3)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL 3 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (MemLp (fun t => Z H a b (N * t) N) 4 (volume.restrict (Icc (1 : ℝ) 2)) ∧
         MemLp (fun t => S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)) 4
          (volume.restrict (Icc (1 : ℝ) 2))) ∧
        (∫ t in (1 : ℝ)..2, |Z H a b (N * t) N| ^ 2) ≤ C ∧
        (∫ t in (1 : ℝ)..2, |S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 2) ≤ C ∧
        (∀ t ∈ Icc (1 : ℝ) 2,
          |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ≤ δ) := by
  obtain ⟨Cg, hCg, hcell⟩ := uniform_cell_second SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  refine ⟨2 * (Cg + 1), by linarith, ?_⟩
  intro δ hδ
  filter_upwards [hcell, p_sampling_error_rate α (min δ 1) hα (lt_min hδ zero_lt_one),
    range_geometry α β M hα (by linarith) (by linarith)]
    with N hcell hsmall hgeom
  intro H hHlo hHhi a b ha hab hb
  obtain ⟨hH, _hHN, hMH⟩ := hgeom.2.2 H hHlo hHhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hmem := sampling_memLp N H M a b hgeom.1 hgeom.2.1 hH1 hM hMH ha hab hb
  have hg := hcell H hHlo hHhi a b ha hab hb
  have hN0 : 0 < N := by linarith [hgeom.1]
  have hL0 : 0 < Real.log N := by linarith [hgeom.2.1]
  have hQ : 0 < Real.sqrt ((H : ℝ) * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have herr (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ≤ min δ 1 := by
    have hx : N * t ∈ Icc N (2 * N) := by constructor <;> nlinarith [ht.1, ht.2]
    have hp := sampling_pointwise hgeom.1 hH1 ha hab hb hMH hx
    rw [Z, ← sub_div, abs_div, abs_of_pos hQ]
    exact (div_le_div_of_nonneg_right hp hQ.le).trans (hsmall H hHlo)
  have hf2 : (∫ t in (1 : ℝ)..2, |Z H a b (N * t) N| ^ 2) ≤ 2 * (Cg + 1) := by
    let f := fun t => Z H a b (N * t) N
    let g := fun t => S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)
    have hfi : IntervalIntegrable (fun t => |f t| ^ 2) volume 1 2 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      simpa only [Real.norm_eq_abs, f, IntegrableOn] using
        (hmem.1.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)).integrable_norm_pow (by norm_num : 2 ≠ 0)
    have hgi : IntervalIntegrable (fun t => |g t| ^ 2) volume 1 2 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      simpa only [Real.norm_eq_abs, g, IntegrableOn] using
        (hmem.2.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)).integrable_norm_pow (by norm_num : 2 ≠ 0)
    calc
      _ ≤ ∫ t in (1 : ℝ)..2, 2 * (|g t| ^ 2 + 1) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hfi
          ((hgi.add intervalIntegrable_const).const_mul 2)
        intro t ht
        have hd : |f t - g t| ≤ 1 := (herr t ht).trans (min_le_right δ 1)
        have ht' := abs_add_le (f t - g t) (g t)
        rw [sub_add_cancel] at ht'
        have hle : |f t| ≤ 1 + |g t| := by linarith
        have hs := pow_le_pow_left₀ (abs_nonneg (f t)) hle 2
        nlinarith [sq_nonneg (|g t| - 1)]
      _ = 2 * ((∫ t in (1 : ℝ)..2, |g t| ^ 2) + 1) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hgi intervalIntegrable_const]
        norm_num
      _ ≤ _ := by dsimp [g]; linarith
  exact ⟨hmem, hf2, hg.trans (by linarith),
    fun t ht => (herr t ht).trans (min_le_left δ 1)⟩

/-- Continuous and cell increments have uniform fourth moments and vanishing fourth error. -/
theorem uniform_sampling_fourth (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL4 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (MemLp (fun t => Z H a b (N * t) N) 4 (volume.restrict (Icc (1 : ℝ) 2)) ∧
         MemLp (fun t => S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)) 4
          (volume.restrict (Icc (1 : ℝ) 2))) ∧
        (∫ t in (1 : ℝ)..2, |Z H a b (N * t) N| ^ 4) ≤ C ∧
        (∫ t in (1 : ℝ)..2, |S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 4) ≤ C ∧
        (∫ t in (1 : ℝ)..2,
          |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 4) ≤ δ ^ 4 := by
  obtain ⟨Cg, hCg, hcell⟩ := uniform_cell_fourth SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  refine ⟨8 * (Cg + 1), by linarith, ?_⟩
  intro δ hδ
  filter_upwards [hcell, p_sampling_error_rate α (min δ 1) hα (lt_min hδ zero_lt_one),
    range_geometry α β M hα (by linarith) (by linarith)]
    with N hcell hsmall hgeom
  intro H hHlo hHhi a b ha hab hb
  obtain ⟨hH, _hHN, hMH⟩ := hgeom.2.2 H hHlo hHhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hmem := sampling_memLp N H M a b hgeom.1 hgeom.2.1 hH1 hM hMH ha hab hb
  have hg := hcell H hHlo hHhi a b ha hab hb
  have herr := p_sampling_fourth_error N H M a b hgeom.1 hH1 hM hMH ha hab hb
  have hlog : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith [hgeom.1])
  have hE0 : 0 ≤ (2 * Real.log (4 * N) + 2) / Real.sqrt ((H : ℝ) * Real.log N) := by positivity
  have hd : (∫ t in (1 : ℝ)..2,
      |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 4) ≤ δ ^ 4 :=
    herr.trans (pow_le_pow_left₀ hE0 ((hsmall H hHlo).trans (min_le_left δ 1)) 4)
  have hd1 : (∫ t in (1 : ℝ)..2,
      |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 4) ≤ 1 := by
    simpa only [one_pow] using
      herr.trans (pow_le_pow_left₀ hE0 ((hsmall H hHlo).trans (min_le_right δ 1)) 4)
  exact ⟨hmem, p_fourth_bound_transfer _ _ Cg 1 hmem.1 hmem.2 hg hd1,
    hg.trans (by linarith), hd⟩

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
