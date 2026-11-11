/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: A supported cutoff weight yields a uniform discrete fourth power bound. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteFourthAssembly
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CutoffWeights

/-! Uniform fourth power bounds for discrete short interval increments. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Discrete increments have uniformly bounded normalized fourth moments. -/
theorem uniform_discrete_fourth_bound (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL4 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 4) ≤
          C * N * ((H : ℝ) * Real.log N) ^ 2 := by
  let w : ℝ → ℝ := (Icc (1 : ℝ) 2).indicator (fun _ => 1)
  have hw : BVBound w 3 := cutoff_bv 1 2 le_rfl (by norm_num) le_rfl
  have hi : (∫ t in (1 : ℝ)..2, w t) = 1 := by
    calc
      _ = ∫ _t in (1 : ℝ)..2, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact Set.indicator_of_mem (by simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
          using ht) _
      _ = _ := by norm_num
  refine ⟨3 + 3 * M ^ 2, by positivity, ?_⟩
  filter_upwards [eventual_discrete_fourth SS α β M hα hαβ hβ hSS hSS1 hMS hcor hM
    1 zero_lt_one, range_geometry α β M hα (by linarith) (by linarith)]
    with N hfourth hgeom
  intro H hHlo hHhi a b ha hab hb
  have hN0 : 0 < N := by linarith [hgeom.1]
  obtain ⟨hH2, hHN, _⟩ := hgeom.2.2 H hHlo hHhi
  have hL : 0 < Real.log N := by linarith [hgeom.2.1]
  have hQ : 0 < N * ((H : ℝ) * Real.log N) ^ 2 := by positivity
  have hab' : admissible M (fun _ : Fin 4 => a) (fun _ => b) :=
    fun _ => ⟨ha, hab, hb⟩
  have hd : discreteRaw N H (fun _ : Fin 4 => a) (fun _ => b) w =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 4 := by
    unfold discreteRaw
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
    have hnN : N < (n : ℝ) := (Nat.floor_lt hN0.le).mp hnlo
    have hn2 : (n : ℝ) ≤ 2 * N := (Nat.le_floor_iff (by positivity)).mp hnhi
    have hmem : (n : ℝ) / N ∈ Icc (1 : ℝ) 2 :=
      ⟨(le_div_iff₀ hN0).2 (by linarith), (div_le_iff₀ hN0).2 hn2⟩
    have hwval : w ((n : ℝ) / N) = 1 := Set.indicator_of_mem hmem _
    rw [hwval, one_mul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (Even.pow_abs (by decide : Even 4) _).symm
  have hbound := hfourth H hHlo hHhi 3 w hw
    (fun _ : Fin 4 => a) (fun _ => b) hab'
  rw [hd, hi, one_mul, mul_one] at hbound
  have hk := variance_ratio_bounds N H hgeom.1 (by linarith) hHN
  have hk2 : (kappa N H) ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
  have hW := w4_bound M (fun _ : Fin 4 => a) (fun _ => b) (by linarith) hab'
  have hmain : (kappa N H) ^ 2 * W4 (fun _ : Fin 4 => a) (fun _ => b) ≤
      3 * M ^ 2 := by
    exact (mul_le_mul_of_nonneg_right hk2 hW.1).trans (by simpa using hW.2)
  have hratio : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 4) /
      (N * ((H : ℝ) * Real.log N) ^ 2) ≤ 3 + 3 * M ^ 2 := by
    linarith [(le_abs_self _).trans hbound]
  have hfinal := (div_le_iff₀ hQ).mp hratio
  convert hfinal using 1
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
