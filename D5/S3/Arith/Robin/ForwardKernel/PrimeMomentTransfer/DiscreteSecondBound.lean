/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteSecondBound
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteSecondBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-point mean-square correlations give uniform normalized second moment bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedArithmeticTransfer
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CutoffWeights
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedIntegralTools

/-! The quadratic arithmetic transfer supplies the L2 bounds used in cubic sampling.
The moment range agrees with the k=2 case of Montgomery--Soundararajan's Theorem 3;
the uniform interval and weight application is derived from the interval correlation input. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Discrete second moments have the variance size throughout the cubic length range. -/
theorem uniform_discrete_second_bound (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 3)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL 3 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 2) ≤
          C * N * ((H : ℝ) * Real.log N) := by
  let ε : ℝ := (1 / 2 - β) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hdecay : 0 < 1 / 2 - ε - β := by dsimp [ε]; linarith
  obtain ⟨A, hA, harith⟩ := arithmetic_transfer SS α β hα hαβ (by linarith)
    hSS hSS1 hMS M hM ε hε
  obtain ⟨C, hC, hformal⟩ := formal_interval_second_bound SS α β M hα (by linarith)
    hSS hSS1 hcor hM
  let w : ℝ → ℝ := (Icc (1 : ℝ) 2).indicator (fun _ => 1)
  have hw : BVBound w 3 := cutoff_bv 1 2 le_rfl (by norm_num) le_rfl
  refine ⟨3 * A + 3 * C, by positivity, ?_⟩
  filter_upwards [harith, hformal, range_geometry α β M hα (by linarith) (by linarith),
    (tendsto_rpow_neg_atTop hdecay).eventually_le_const zero_lt_one]
    with N harith hformal hgeom hsmall
  intro H hlo hhi a b ha hab hb
  have hN0 : 0 < N := by linarith [hgeom.1]
  have hL : 1 ≤ Real.log N := hgeom.2.1
  have hH1 : 1 ≤ (H : ℝ) := by linarith [(hgeom.2.2 H hlo hhi).1]
  have hhab : admissible M (fun _ : Fin 2 => a) (fun _ => b) := fun _ => ⟨ha, hab, hb⟩
  have hd : discreteRaw N H (fun _ : Fin 2 => a) (fun _ => b) w =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 2 := by
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
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, sq_abs]
  have hi : |∫ x in N..2 * N, w (x / N) *
      Phi SS H (Real.log x) (fun _ : Fin 2 => a) (fun _ => b)| ≤
      3 * C * (H : ℝ) * Real.log N * N := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := N) (b := 2 * N) (C := 3 * C * (H : ℝ) * Real.log N)
      (f := fun x => w (x / N) * Phi SS H (Real.log x)
        (fun _ : Fin 2 => a) (fun _ => b)) ?_
    · simpa only [Real.norm_eq_abs, show 2 * N - N = N by ring,
        abs_of_pos hN0] using h
    intro x hx
    have hx' : x ∈ Icc N (2 * N) := by
      rw [uIoc_of_le (by linarith : N ≤ 2 * N)] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hslo : Real.log N ≤ Real.log x := Real.log_le_log hN0 hx'.1
    have hshi : Real.log x ≤ Real.log N + Real.log 2 := by
      calc
        _ ≤ Real.log (2 * N) := Real.log_le_log (hN0.trans_le hx'.1) hx'.2
        _ = _ := by rw [Real.log_mul (by norm_num) hN0.ne']; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 3 * (C * (H : ℝ) * Real.log N) :=
        mul_le_mul (bv_sup_bound w 3 hw _) (hformal H (Real.log x) hlo hhi hslo hshi a b ha hab hb)
          (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hpower : N ^ (1 / 2 + ε) * (H : ℝ) ≤ N := by
    have hh : N ^ (1 / 2 + ε) * (H : ℝ) / N ≤ 1 := by
      calc
        _ ≤ N ^ (1 / 2 + ε) * N ^ β / N := by gcongr
        _ = N ^ (-(1 / 2 - ε - β)) := by
          rw [show -(1 / 2 - ε - β) = (1 / 2 + ε + β) - 1 by ring,
            Real.rpow_sub hN0, Real.rpow_one,
            Real.rpow_add hN0 (1 / 2 + ε) β]
        _ ≤ 1 := hsmall
    exact (div_le_one hN0).mp hh
  have herror : N ^ (1 / 2 + ε) * (H : ℝ) ^ 2 ≤
      N * ((H : ℝ) * Real.log N) := by
    calc
      _ = (N ^ (1 / 2 + ε) * (H : ℝ)) * (H : ℝ) := by ring
      _ ≤ N * (H : ℝ) := mul_le_mul_of_nonneg_right hpower (by positivity)
      _ ≤ N * (H : ℝ) * Real.log N := le_mul_of_one_le_right (by positivity) hL
      _ = _ := by ring
  have ht := harith H hlo hhi 3 w hw 2 ⟨by norm_num, by norm_num⟩ _ _ hhab
  rw [hd] at ht
  have htri := abs_sub_le
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 2)
    (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x)
      (fun _ : Fin 2 => a) (fun _ => b)) 0
  simp only [sub_zero] at htri
  have he := mul_le_mul_of_nonneg_left herror (show 0 ≤ A * 3 by positivity)
  nlinarith [(le_abs_self (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ 2))]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
