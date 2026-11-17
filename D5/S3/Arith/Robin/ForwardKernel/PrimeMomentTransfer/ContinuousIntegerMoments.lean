/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Continuous integer-length mixed moments inherit uniform discrete asymptotics. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteThirdAssembly
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteFourthAssembly
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SamplingErrorBounds

/-! Continuous replacement and cell quadrature give integer-length mixed moments. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem weighted_moment_scaling (N H : ℝ) (k : ℕ)
    (a b : Fin k → ℝ) (w : ℝ → ℝ) (hN : 0 < N) :
    weightedMoment N H a b w =
      ∫ t in (1 : ℝ)..2, w t * (∏ i, Z H (a i) (b i) (N * t) N) := by
  have hs := intervalIntegral.integral_comp_mul_left
    (fun x => w (x / N) * ∏ i, Z H (a i) (b i) x N) hN.ne' (a := 1) (b := 2)
  simpa only [weightedMoment, mul_one, mul_comm N 2, smul_eq_mul,
    inv_mul_eq_div, mul_div_cancel_left₀ _ hN.ne'] using hs.symm

private theorem uniform_continuous_cell_replacement :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/4 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL4 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℕ, N^α ≤ (H:ℝ) → (H:ℝ) ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ k : ℕ, (k=3 ∨ k=4) →
    ∀ a b : Fin k → ℝ, admissible M a b →
      |weightedMoment N H a b w-
        (∫ t in (1:ℝ)..2, w t*(∏ i,
          S H (a i) (b i) ⌊N*t⌋₊/Real.sqrt ((H:ℝ)*Real.log N)))| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  obtain ⟨C, hC, hs⟩ := uniform_sampling_fourth SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  let t := δ / (4 * C)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have ht : 0 < t := div_pos hδ (by positivity)
  filter_upwards [hs t ht, eventually_ge_atTop (1 : ℝ)] with N hs hN
  intro H hlo hhi B w hw k hk a b hab
  have hB : 0 ≤ B := hw.2.2.1
  have hdata := fun i => hs H hlo hhi (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have hk4 : k ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  have hp := weighted_product_difference k
    (fun i t => Z H (a i) (b i) (N * t) N)
    (fun i t => S H (a i) (b i) ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N))
    w C (t ^ 4) B hk0 hk4 hC0.le (by positivity) hw.2.2.1
    (fun i => (hdata i).1) (fun i => (hdata i).2.1)
    (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
    (hw.1.intervalIntegrable (subset_univ _)) (fun x _ => bv_sup_bound w B hw x)
  have htroot : (t ^ 4) ^ (1 / 4 : ℝ) = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hCp : C ^ (((k : ℝ) - 1) / 4) ≤ C :=
    Real.rpow_le_self_of_one_le hC (by
      have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
      linarith)
  rw [weighted_moment_scaling N H k a b w (zero_lt_one.trans_le hN)]
  apply hp.trans
  rw [htroot]
  calc
    B * (k : ℝ) * t * C ^ (((k : ℝ) - 1) / 4) ≤ B * 4 * t * C := by
      apply mul_le_mul _ hCp (Real.rpow_nonneg hC0.le _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hk4) hw.2.2.1) ht.le
    _ = B * δ := by dsimp [t]; field_simp

private theorem uniform_continuous_cell_replacement_three :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/3 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL 3 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℕ, N^α ≤ (H:ℝ) → (H:ℝ) ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B →
    ∀ a b : Fin 3 → ℝ, admissible M a b →
      |weightedMoment N H a b w-
        (∫ t in (1:ℝ)..2, w t*(∏ i,
          S H (a i) (b i) ⌊N*t⌋₊/Real.sqrt ((H:ℝ)*Real.log N)))| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  obtain ⟨C, hC, hs⟩ := uniform_sampling_second SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  let t := δ / (6 * C)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have ht : 0 < t := div_pos hδ (by positivity)
  filter_upwards [hs t ht, eventually_ge_atTop (1 : ℝ)] with N hs hN
  intro H hlo hhi B w hw a b hab
  have hdata := fun i => hs H hlo hhi (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  let f := fun i t => Z H (a i) (b i) (N * t) N
  let g := fun i t => S H (a i) (b i) ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)
  have hif : Integrable (fun t => ∏ i, f i t) (volume.restrict (Icc (1 : ℝ) 2)) :=
    FourthTransfer.FiniteProductMomentBounds.product_integrable (by norm_num : 0 < 3)
      (fun i => (hdata i).1.1.mono_exponent (by norm_num : (3 : ENNReal) ≤ 4))
  have hig : Integrable (fun t => ∏ i, g i t) (volume.restrict (Icc (1 : ℝ) 2)) :=
    FourthTransfer.FiniteProductMomentBounds.product_integrable (by norm_num : 0 < 3)
      (fun i => (hdata i).1.2.mono_exponent (by norm_num : (3 : ENNReal) ≤ 4))
  have hp := weighted_cubic_difference f g w C t B ht.le hw.2.2.1
    (fun i => ⟨(hdata i).1.1.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4),
      (hdata i).1.2.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)⟩)
    hif hig (fun i => (hdata i).2.1) (fun i => (hdata i).2.2.1)
    (fun i t ht => (hdata i).2.2.2 t ht)
    (hw.1.intervalIntegrable (subset_univ _)) (fun x _ => bv_sup_bound w B hw x)
  rw [weighted_moment_scaling N H 3 a b w (zero_lt_one.trans_le hN)]
  apply hp.trans
  have hbudget : 6 * B * t * C = B * δ := by dsimp [t]; field_simp
  exact hbudget.le

private theorem uniform_weighted_cell_error :
∀ (α β M : ℝ), 0 < α → α < β → β < 1/2 → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℕ, N^α ≤ (H:ℝ) → (H:ℝ) ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ k : ℕ, (k=3 ∨ k=4) →
    ∀ a b : Fin k → ℝ, admissible M a b →
      |(∫ t in (1:ℝ)..2, w t*(∏ i,
        S H (a i) (b i) ⌊N*t⌋₊/Real.sqrt ((H:ℝ)*Real.log N)))-
        discreteRaw N H a b w/(N*(Real.sqrt ((H:ℝ)*Real.log N))^k)| ≤ B*δ := by
  intro α β M hα hαβ hβ hM δ hδ
  let C := 4 * (M + 1)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let t := δ / (3 * C ^ 4)
  have ht : 0 < t := div_pos hδ (by positivity)
  filter_upwards [range_geometry α β M hα (by linarith) (by linarith),
    cell_rate β t 4 (by linarith) hβ le_rfl ht] with N hgeom hrate
  intro H hlo hhi B w hw k hk a b hab
  have hN0 : 0 < N := by linarith [hgeom.1]
  obtain ⟨hH2, _, hMH⟩ := hgeom.2.2 H hlo hhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hH0 : 0 < (H : ℝ) := by linarith
  have hL : 0 < Real.log N := zero_lt_one.trans_le hgeom.2.1
  have hB : 0 ≤ B := hw.2.2.1
  have hk4 : k ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  let Q := Real.sqrt ((H : ℝ) * Real.log N)
  have hQ : 1 ≤ Q := Real.one_le_sqrt.mpr
    (one_le_mul_of_one_le_of_one_le hH1 hgeom.2.1)
  have hQ4 : Q ^ 4 = ((H : ℝ) * Real.log N) ^ 2 :=
    (normalizer_powers H (Real.log N) hH0 hL).2.2.2
  let F : ℕ → ℝ := fun n => ∏ i, S H (a i) (b i) n / Q
  let A := C ^ 4 * ((H : ℝ) * Real.log N) ^ 2
  have hF : ∀ n, ⌊N⌋₊ ≤ n → n ≤ ⌈2 * N⌉₊ → |F n| ≤ A := by
    intro n hnlo hnhi
    have hb := (normalized_crude_bounds N H M hgeom.1 hgeom.2.1 hH1 hM hMH).1
    calc
      |F n| = ∏ i, |S H (a i) (b i) n / Q| := by
        change |∏ i, S H (a i) (b i) n / Q| = _
        exact Finset.abs_prod _ _
      _ ≤ ∏ _i : Fin k, C * Q := Finset.prod_le_prod₀
        (fun i _ => abs_nonneg _) (fun i _ =>
          hb (a i) (b i) n (hab i).1 (hab i).2.1 (hab i).2.2 hnlo hnhi)
      _ = C ^ k * Q ^ k := by simp only [Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, mul_pow]
      _ ≤ C ^ 4 * Q ^ 4 := mul_le_mul
        (pow_le_pow_right₀ hC hk4) (pow_le_pow_right₀ hQ hk4) (by positivity) (by positivity)
      _ = A := by rw [hQ4]
  have hquad := cell_quadrature N A B F w hgeom.1 (by dsimp [A]; positivity) hw hF
  have hscale : (∫ t in (1 : ℝ)..2, w t * F ⌊N * t⌋₊) =
      (∫ x in N..2 * N, w (x / N) * F ⌊x⌋₊) / N := by
    simpa only [mul_one, mul_comm N 2, smul_eq_mul, inv_mul_eq_div,
      mul_div_cancel_left₀ _ hN0.ne'] using
      intervalIntegral.integral_comp_mul_left (fun x => w (x / N) * F ⌊x⌋₊)
        hN0.ne' (a := 1) (b := 2)
  have hsum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) * F n) =
      discreteRaw N H a b w / Q ^ k := by
    simp only [F, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← mul_div_assoc, ← Finset.sum_div, discreteRaw]
  change |(∫ t in (1 : ℝ)..2, w t * F ⌊N * t⌋₊) -
    discreteRaw N H a b w / (N * Q ^ k)| ≤ _
  rw [hscale, show discreteRaw N H a b w / (N * Q ^ k) =
    (discreteRaw N H a b w / Q ^ k) / N by ring, ← hsum, ← sub_div,
    abs_div, abs_of_pos hN0]
  calc
    _ ≤ (3 * A * B) / N := div_le_div_of_nonneg_right hquad hN0.le
    _ = B * (3 * C ^ 4) * (((H : ℝ) * Real.log N) ^ 2 / N) := by dsimp [A]; ring
    _ ≤ B * (3 * C ^ 4) * t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two]
        using hrate H hH1 hhi
    _ = B * δ := by dsimp [t]; field_simp

/-- Continuous cubic mixed moments vanish uniformly for integer lengths. -/
theorem integer_third :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/3 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL 3 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℕ, N^α ≤ (H:ℝ) → (H:ℝ) ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 3 → ℝ, admissible M a b →
      |weightedMoment N H a b w| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  have ht : 0 < δ / 3 := by positivity
  filter_upwards [uniform_continuous_cell_replacement_three SS α β M
      hα hαβ hβ hSS hSS1 hMS hcor hM (δ / 3) ht,
    uniform_weighted_cell_error α β M hα hαβ (by linarith) hM (δ / 3) ht,
    eventual_discrete_third SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM (δ / 3) ht,
    eventually_ge_atTop (2 : ℝ)] with N hr hc hd hN
  intro H hlo hhi B w hw a b hab
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < (H : ℝ) := (Real.rpow_pos_of_pos hN0 α).trans_le hlo
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hn := (normalizer_powers H (Real.log N) hH0 hL).2.2.1
  have hr' := hr H hlo hhi B w hw a b hab
  have hc' := hc H hlo hhi B w hw 3 (Or.inl rfl) a b hab
  rw [hn] at hc'
  have hd' := hd H hlo hhi B w hw a b hab
  let T := ∫ t in (1 : ℝ)..2, w t * ∏ i, S H (a i) (b i) ⌊N * t⌋₊ /
    Real.sqrt ((H : ℝ) * Real.log N)
  let D := discreteRaw N H a b w / (N * ((H : ℝ) * Real.log N) ^ (3 / 2 : ℝ))
  have htri := (abs_sub_le (weightedMoment N H a b w) T 0).trans
    (add_le_add hr' (abs_sub_le T D 0))
  simp only [sub_zero] at htri
  linarith

/-- Integer-length fourth mixed moments converge uniformly to the overlap pairing. -/
theorem integer_fourth :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/4 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL4 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℕ, N^α ≤ (H:ℝ) → (H:ℝ) ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 4 → ℝ, admissible M a b →
      |weightedMoment N H a b w-
        (∫ t in (1:ℝ)..2, w t)*(kappa N H)^2*W4 a b| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  have ht : 0 < δ / 3 := by positivity
  filter_upwards [uniform_continuous_cell_replacement SS α β M
      hα hαβ hβ hSS hSS1 hMS hcor hM (δ / 3) ht,
    uniform_weighted_cell_error α β M hα hαβ (by linarith) hM (δ / 3) ht,
    eventual_discrete_fourth SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM (δ / 3) ht,
    eventually_ge_atTop (2 : ℝ)] with N hr hc hd hN
  intro H hlo hhi B w hw a b hab
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < (H : ℝ) := (Real.rpow_pos_of_pos hN0 α).trans_le hlo
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hn := (normalizer_powers H (Real.log N) hH0 hL).2.2.2
  have hr' := hr H hlo hhi B w hw 4 (Or.inr rfl) a b hab
  have hc' := hc H hlo hhi B w hw 4 (Or.inr rfl) a b hab
  rw [hn] at hc'
  have hd' := hd H hlo hhi B w hw a b hab
  let T := ∫ t in (1 : ℝ)..2, w t * ∏ i, S H (a i) (b i) ⌊N * t⌋₊ /
    Real.sqrt ((H : ℝ) * Real.log N)
  let D := discreteRaw N H a b w / (N * ((H : ℝ) * Real.log N) ^ 2)
  let A := (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b
  have htri := (abs_sub_le (weightedMoment N H a b w) T A).trans
    (add_le_add hr' (abs_sub_le T D A))
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
