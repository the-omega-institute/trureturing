/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/LogPowerExchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/LogPowerExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed prime exchange entropy at a positive logarithmic power scale. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange

open D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
open private fixed_grid_outputs from D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange

/-- At a positive logarithmic power scale, a strict normalized reserve and full
signed bin capacities give an actual squarefree family with the paired entropy. -/
theorem log_power_grid_lower {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (q : Fin m → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (base : ℝ → Finset ℕ) (reserve : ℝ → ℝ) (B zeta : ℝ) (hzeta : 0 < zeta) :
    let s := fun P : ℝ => C * log P ^ a
    let W := fun P : ℝ => (P / log P) / s P
    let delta := fun i : Fin m => t i.succ - t i.castSucc
    (2 * ∑ i, t i.succ * (delta i * q i) < B) →
    (∀ i, Tendsto (fun P => ((donorBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    (∀ i, Tendsto (fun P => ((recipientBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    Tendsto (fun P => reserve P / (W P / s P)) atTop (𝓝 B) →
    (∀ᶠ P in atTop, base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      (∀ i, donorBin t P (s P) i ⊆ base P) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - reserve P) →
    ∀ᶠ P in atTop,
      let h := fun i => ⌊q i * (min (donorBin t P (s P) i).card
        (recipientBin t P (s P) i).card : ℕ)⌋₊
      let outputs := pairedOutputs (base P) (donorBin t P (s P)) (recipientBin t P (s P)) h
      outputs.card = (∏ i, (donorBin t P (s P) i).card.choose (h i) *
        (recipientBin t P (s P) i).card.choose (h i)) ∧
      0 < outputs.card ∧
      (∀ n ∈ outputs, 0 < n ∧ Squarefree n ∧ ArithmeticFunction.cardDistinctFactors n =
        (base P).card ∧ (n : ℝ) < exp P) ∧
      (2 * ∑ i, delta i * binEntropy (q i) - zeta) * W P ≤ log (outputs.card : ℝ) := by
  intro s W delta hslack hd hr hreserve hbase
  have hW : Tendsto W atTop atTop := by
    apply (((tendsto_exp_div_rpow_atTop (1 + a)).comp tendsto_log_atTop).atTop_div_const hC).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    change exp (log P) / log P ^ (1 + a) / C = (P / log P) / (C * log P ^ a)
    rw [exp_log (zero_lt_one.trans hP), rpow_add (log_pos hP), rpow_one, div_div, div_div]
    ring_nf
  have hdelta (i : Fin m) : 0 < delta i := sub_pos.mpr (ht i.castSucc_lt_succ)
  let M (i : Fin m) (P : ℝ) :=
    min (donorBin t P (s P) i).card (recipientBin t P (s P) i).card
  let h (i : Fin m) (P : ℝ) := ⌊q i * (M i P : ℝ)⌋₊
  have hδM (i : Fin m) : Tendsto (fun P => (M i P : ℝ) / W P) atTop (𝓝 (delta i)) := by
    have hmin := (hd i).min (hr i)
    rw [min_self] at hmin
    apply hmin.congr'
    filter_upwards [hW.eventually_gt_atTop 0] with P hWP
    simp only [M, Nat.cast_min, min_div_div_right hWP.le]
  have hh (i : Fin m) : Tendsto (fun P => (h i P : ℝ) / W P) atTop
      (𝓝 (delta i * q i)) := by
    have hM : Tendsto (fun P => (M i P : ℝ)) atTop atTop := by
      apply (hW.atTop_mul_pos (hdelta i) (hδM i)).congr'
      filter_upwards [hW.eventually_gt_atTop 0] with P hWP
      exact mul_div_cancel₀ _ hWP.ne'
    have hf := ((tendsto_nat_floor_mul_div_atTop (hq0 i).le).comp hM).mul (hδM i)
    rw [mul_comm (q i) (delta i)] at hf
    apply hf.congr'
    filter_upwards [hM.eventually_gt_atTop 0] with P hMP
    change (h i P : ℝ) / (M i P : ℝ) * ((M i P : ℝ) / W P) = _
    rw [div_mul_div_cancel₀ hMP.ne']
  have hfit (i : Fin m) (P : ℝ) : h i P ≤ M i P := by
    have hm : (0 : ℝ) ≤ M i P := Nat.cast_nonneg _
    exact (Nat.floor_le_of_le (by nlinarith [mul_nonneg (sub_nonneg.mpr (hq1 i).le) hm]))
  have hnormalized :
      Tendsto (fun P => 2 * ∑ i, t i.succ * ((h i P : ℝ) / W P)) atTop
        (𝓝 (2 * ∑ i, t i.succ * (delta i * q i))) :=
    (tendsto_finsetSum univ (fun i _ => (hh i).const_mul (t i.succ))).const_mul 2
  have hbudget := hnormalized.eventually_lt hreserve hslack
  have hrl (i : Fin m) : 0 < delta i * q i := mul_pos (hdelta i) (hq0 i)
  have hru (i : Fin m) : delta i * q i < delta i :=
    mul_lt_of_lt_one_right (hdelta i) (hq1 i)
  have hentropy := tendsto_finsetSum univ (fun i _ =>
    ((Entropy.log_choose_scaled W (fun P => (donorBin t P (s P) i).card) (h i)
      hW (hdelta i) (hrl i) (hru i) (hd i) (hh i)).add
    (Entropy.log_choose_scaled W (fun P => (recipientBin t P (s P) i).card) (h i)
      hW (hdelta i) (hrl i) (hru i) (hr i) (hh i))))
  have heq (i : Fin m) : delta i * q i / delta i = q i :=
    mul_div_cancel_left₀ _ (hdelta i).ne'
  simp only [heq, ← two_mul, ← mul_sum] at hentropy
  have hlow := hentropy.eventually_const_lt
    (sub_lt_self (2 * ∑ i, delta i * binEntropy (q i)) hzeta)
  filter_upwards [hbudget, hlow, hW.eventually_gt_atTop 0, eventually_gt_atTop 1, hbase]
    with P hbudgetP hlowP hWP hP hbaseP
  have hsP : 0 < s P := mul_pos hC (rpow_pos_of_pos (log_pos hP) a)
  have hcost : (2 / s P) * (∑ i, t i.succ * (h i P : ℝ)) < reserve P := by
    have hh := (lt_div_iff₀ (div_pos hWP hsP)).mp hbudgetP
    convert hh using 1
    simp only [mul_assoc, sum_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    field_simp [hsP.ne', hWP.ne']
    <;> ring
  let d : Fin m → ℕ := fun i => (donorBin t P (s P) i).card.choose (h i P)
  let r : Fin m → ℕ := fun i => (recipientBin t P (s P) i).card.choose (h i P)
  have hdp (i : Fin m) : (0 : ℝ) < d i := by
    dsimp [d]
    exact_mod_cast Nat.choose_pos ((hfit i P).trans (min_le_left _ _))
  have hrp (i : Fin m) : (0 : ℝ) < r i := by
    dsimp [r]
    exact_mod_cast Nat.choose_pos ((hfit i P).trans (min_le_right _ _))
  have hprod : (0 : ℝ) < ((∏ i, d i * r i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp only [Nat.cast_mul]
    exact prod_pos fun i _ => mul_pos (hdp i) (hrp i)
  have hlog : log ((∏ i, d i * r i : ℕ) : ℝ) =
      ∑ i, (log (d i : ℝ) + log (r i : ℝ)) := by
    rw [Nat.cast_prod, log_prod (fun i _ => by
      simpa only [Nat.cast_mul] using (mul_pos (hdp i) (hrp i)).ne')]
    simp only [Nat.cast_mul, log_mul (hdp _).ne' (hrp _).ne']
  have hsum : (2 * ∑ i, delta i * binEntropy (q i)) - zeta <
      (∑ i, (log (d i : ℝ) + log (r i : ℝ))) / W P := by
    rw [sum_div]
    simp only [add_div]
    exact hlowP
  obtain ⟨hcard, hout⟩ := fixed_grid_outputs t ht ht0 P (s P) (reserve P)
    (zero_lt_one.trans hP) hsP (base P) (fun i => h i P)
    hbaseP.1 hbaseP.2.1 hbaseP.2.2 hcost
  refine ⟨hcard, ?_, hout, ?_⟩
  · rw [hcard]
    exact Nat.cast_pos.mp hprod
  · rw [hcard, hlog]
    exact ((lt_div_iff₀ hWP).mp hsum).le

end D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange
