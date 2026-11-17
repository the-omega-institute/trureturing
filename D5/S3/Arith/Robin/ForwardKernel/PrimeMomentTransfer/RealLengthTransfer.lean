/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Exact endpoint rescaling extends uniform mixed moment asymptotics to real lengths. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ContinuousIntegerMoments
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.RealLengthRescaling

/-! Real lengths inherit the integer asymptotics by rescaling their physical endpoints. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_fourth_main_cancel (N H K : ℝ) (a b : Fin 4 → ℝ)
    (hH : 0 < H) (hK : 0 < K) :
    (K / H) ^ 2 * (kappa N K) ^ 2 *
      W4 (fun i => (H / K) * a i) (fun i => (H / K) * b i) =
        (kappa N K) ^ 2 * W4 a b := by
  rw [w4_rescale (H / K) a b (by positivity)]
  field_simp

/-- Cubic mixed moments vanish uniformly for all real lengths in the band. -/
theorem real_third :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/3 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL 3 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℝ, N^α ≤ H → H ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 3 → ℝ, admissible M a b →
      |weightedMoment N H a b w| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  filter_upwards [integer_third SS (α / 2) β (2 * M)
      (half_pos hα) (by linarith) hβ hSS hSS1 hMS hcor (by linarith) δ hδ,
    floor_range α β hα hαβ (by linarith),
    eventually_ge_atTop (2 : ℝ)] with N hint hfloor hN
  intro H hlo hhi B w hw a b hab
  obtain ⟨hK1, hKlo, hKhi, hr1, hr2⟩ := hfloor H hlo hhi
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 α).trans_le hlo
  have hK0 : 0 < (⌊H⌋₊ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hK1)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hKH : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH0.le
  have hJ := rescaled_admissible M (H / (⌊H⌋₊ : ℝ)) 3 a b
    (by positivity) hr2 hab
  have hi := hint ⌊H⌋₊ hKlo hKhi B w hw _ _ hJ
  have hp0 : 0 ≤ ((⌊H⌋₊ : ℝ) / H) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp1 : ((⌊H⌋₊ : ℝ) / H) ^ (3 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by positivity) ((div_le_one hH0).mpr hKH) (by norm_num)
  rw [moment_rescale N H (⌊H⌋₊ : ℝ) 3 a b w hN0 hL hH0 hK0]
  norm_num only [Nat.cast_ofNat]
  rw [abs_mul, abs_of_nonneg hp0]
  calc
    _ ≤ ((⌊H⌋₊ : ℝ) / H) ^ (3 / 2 : ℝ) * (B * δ) :=
      mul_le_mul_of_nonneg_left hi hp0
    _ ≤ 1 * (B * δ) := mul_le_mul_of_nonneg_right hp1 (mul_nonneg hw.2.2.1 hδ.le)
    _ = B * δ := one_mul _

/-- Real-length fourth mixed moments converge uniformly to their overlap pairing. -/
theorem real_fourth :
∀ (SS : Finset ℕ → ℝ) (α β M : ℝ), 0 < α → α < β → β < 1/4 →
  SS ∅ = 1 → (∀ d, SS {d} = 1) → MeanSquareHL4 SS β → IntervalCorrelations SS → 1 ≤ M →
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℝ in atTop,
    ∀ H : ℝ, N^α ≤ H → H ≤ N^β →
    ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 4 → ℝ, admissible M a b →
      |weightedMoment N H a b w-
        (∫ t in (1:ℝ)..2, w t)*(kappa N H)^2*W4 a b| ≤ B*δ := by
  intro SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM δ hδ
  let t := δ / (2 * (3 * M ^ 2 + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  filter_upwards [integer_fourth SS (α / 2) β (2 * M)
      (half_pos hα) (by linarith) hβ hSS hSS1 hMS hcor (by linarith) (δ / 2) (half_pos hδ),
    floor_range α β hα hαβ (by linarith),
    floor_variance_rate α β t hα hαβ (by linarith) ht,
    eventually_ge_atTop (2 : ℝ)] with N hint hfloor hvar hN
  intro H hlo hhi B w hw a b hab
  obtain ⟨hK1, hKlo, hKhi, hr1, hr2⟩ := hfloor H hlo hhi
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 α).trans_le hlo
  have hK0 : 0 < (⌊H⌋₊ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hK1)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hKH : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH0.le
  have hB : 0 ≤ B := hw.2.2.1
  let r := (⌊H⌋₊ : ℝ) / H
  let W := ∫ t in (1 : ℝ)..2, w t
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrle : r ≤ 1 := (div_le_one hH0).mpr hKH
  have hrpow : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (r - 1)]
  have hJ := rescaled_admissible M (H / (⌊H⌋₊ : ℝ)) 4 a b (by positivity) hr2 hab
  have hi := hint ⌊H⌋₊ hKlo hKhi B w hw _ _ hJ
  have hcancel := p_fourth_main_cancel N H (⌊H⌋₊ : ℝ) a b hH0 hK0
  have hres := moment_rescale N H (⌊H⌋₊ : ℝ) 4 a b w hN0 hL hH0 hK0
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two] at hres
  have he : |weightedMoment N H a b w - W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 * W4 a b| ≤ B * (δ / 2) := by
    have hidentity : weightedMoment N H a b w - W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 * W4 a b =
        r ^ 2 * (weightedMoment N (⌊H⌋₊ : ℝ)
          (fun i => (H / (⌊H⌋₊ : ℝ)) * a i)
          (fun i => (H / (⌊H⌋₊ : ℝ)) * b i) w -
          W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 *
            W4 (fun i => (H / (⌊H⌋₊ : ℝ)) * a i) (fun i => (H / (⌊H⌋₊ : ℝ)) * b i)) := by
      rw [hres]
      dsimp [r]
      linear_combination W * hcancel
    rw [hidentity, abs_mul, abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_left hi (sq_nonneg r)).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hrpow (by positivity : 0 ≤ B * (δ / 2)))
  have hW : |W| ≤ B := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := 2) (f := w) (C := B)
      (fun x _ => by simpa only [Real.norm_eq_abs] using bv_sup_bound w B hw x)
    simpa only [W, Real.norm_eq_abs, show (2 : ℝ) - 1 = 1 by norm_num, abs_one, mul_one] using hb
  obtain ⟨hW40, hW4⟩ := w4_bound M a b (by linarith) hab
  have hm : |W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 * W4 a b -
      W * (kappa N H) ^ 2 * W4 a b| ≤ B * (δ / 2) := by
    rw [show W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 * W4 a b - W * (kappa N H) ^ 2 * W4 a b =
      W * ((kappa N (⌊H⌋₊ : ℝ)) ^ 2 - (kappa N H) ^ 2) * W4 a b by ring,
      abs_mul, abs_mul, abs_of_nonneg hW40]
    calc
      _ ≤ B * t * (3 * M ^ 2) := mul_le_mul (mul_le_mul hW (hvar H hlo hhi)
        (abs_nonneg _) hB) hW4 hW40 (by positivity)
      _ ≤ B * (δ / 2) := by
        have hbudget : t * (3 * M ^ 2) ≤ δ / 2 := by
          calc
            _ ≤ t * (3 * M ^ 2 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) ht.le
            _ = δ / 2 := by dsimp [t]; field_simp
        calc
          _ = B * (t * (3 * M ^ 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hB
  have htri := (abs_sub_le (weightedMoment N H a b w)
    (W * (kappa N (⌊H⌋₊ : ℝ)) ^ 2 * W4 a b) (W * (kappa N H) ^ 2 * W4 a b)).trans (add_le_add he hm)
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
