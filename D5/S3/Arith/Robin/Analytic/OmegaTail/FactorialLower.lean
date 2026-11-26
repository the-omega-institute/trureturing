/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/FactorialLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp lower transfer at the strict fixed factorial threshold. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
import D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange
import D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity

/-! Sharp lower bounds from factorial-scale prime reserves and signed exchange. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
open Exchange LogisticGrid LogPowerExchange MovingBoxCapacity
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

/-- A prime base above the strict factorial threshold with the eventual donor
window and a reserve asymptotic to the factorial scale gives the sharp lower
bound for the literal distinct-prime count. -/
theorem factorial_tail_lower (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (base : ℝ → Finset ℕ) (D : ℝ → ℝ)
    (hD : Tendsto (fun P => D P / (P / log P ^ r)) atTop (𝓝 (r.factorial : ℝ))) :
    let T := fun P : ℝ => P * ∑ j ∈ range r, (j.factorial : ℝ) / log P ^ (j + 1)
    (∀ᶠ P in atTop, base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      T P < ((base P).card : ℝ) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - D P ∧
      (∀ p : ℕ, Nat.Prime p → 3 * P / 4 < (p : ℝ) → (p : ℝ) ≤ P → p ∈ base P)) →
    ∀ᶠ P in atTop,
      let tailCount := ((Icc 1 ⌊exp P⌋₊).filter (fun n : ℕ =>
        T P < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card
      0 < tailCount ∧
      (π * sqrt (2 * (r.factorial : ℝ) / 3) - ε) *
        (P / log P ^ (((r : ℝ) + 1) / 2)) ≤ log (tailCount : ℝ) := by
  intro T hbase
  let f : ℝ := r.factorial
  have hf : 0 < f := by
    dsimp only [f]
    exact_mod_cast Nat.factorial_pos r
  have hπ : 0 < π := pi_pos
  let A : ℝ := π ^ 2 / 6
  let c : ℝ := π / sqrt (6 * f)
  let K : ℝ := π * sqrt (2 * f / 3)
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hsqrt : sqrt (2 * f / 3) = sqrt (6 * f) / 3 := by
    rw [show 2 * f / 3 = (6 * f) / 9 by ring, sqrt_div (by positivity : 0 ≤ 6 * f),
      show sqrt (9 : ℝ) = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  have hKc : K * c = 2 * A := by
    dsimp [K, c, A]
    rw [hsqrt]
    have hroot : 0 < sqrt (6 * f) := by positivity
    field_simp [hroot.ne']
    <;> ring
  have hcf : c ^ 2 * f = A := by
    dsimp [c, A]
    rw [div_pow, sq_sqrt (by positivity : 0 ≤ 6 * f)]
    field_simp
  let η := ε / (8 * K)
  let ρ := ε * c / 8
  let ζ := ε * c / 8
  let C := (1 + η) * c
  let a := ((r : ℝ) - 1) / 2
  let B := A * (1 + η) ^ 2
  let s (P : ℝ) := C * log P ^ a
  let W (P : ℝ) := (P / log P) / s P
  let Z (P : ℝ) := P / log P ^ (((r : ℝ) + 1) / 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hζ : 0 < ζ := hρ
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 < a := by
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    dsimp [a]
    linarith
  have hCa : C ^ 2 * f = B := by
    dsimp [C, B]
    rw [mul_pow, mul_assoc, hcf, mul_comm]
  have hnormalized : Tendsto (fun P => D P / (W P / s P)) atTop (𝓝 B) := by
    rw [← hCa]
    apply (hD.const_mul (C ^ 2)).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hP0 := zero_lt_one.trans hP
    have hL := log_pos hP
    have hLa := rpow_pos_of_pos hL a
    have hpow : log P ^ r = log P * log P ^ a * log P ^ a := by
      rw [← rpow_natCast, show (r : ℝ) = 1 + a + a by dsimp [a]; ring,
        rpow_add hL, rpow_add hL, rpow_one]
    dsimp [W, s]
    rw [hpow]
    field_simp
    <;> ring
  obtain ⟨U, m, hU, hm, hcost, hentropy⟩ := exists_uniform_rightEndpoint_grid hη hρ
  let mesh (i : ℕ) : ℝ := (i : ℝ) * (U / m)
  let t (i : Fin (m + 1)) : ℝ := mesh i
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hstep : 0 < U / (m : ℝ) := div_pos (zero_lt_one.trans_le hU) hm'
  have ht : StrictMono t := by
    intro i j hij
    have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast (show i.val < j.val from hij)
    exact mul_lt_mul_of_pos_right hij' hstep
  have ht0 : t 0 = 0 := by simp [t, mesh]
  let q (i : Fin m) : ℝ := sigmoid (-t i.succ)
  let δ (i : Fin m) : ℝ := t i.succ - t i.castSucc
  have hgridCost :
      2 * ∑ i : Fin m, t i.succ * (δ i * q i) =
        rightEndpointCost (fun i => (i : ℝ) * (U / m)) m := by
    simp only [t, δ, q, Fin.val_succ, Fin.val_castSucc, rightEndpointCost]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      mesh (j + 1) * ((mesh (j + 1) - mesh j) * sigmoid (-mesh (j + 1)))) m]
    congr 1
    apply sum_congr rfl
    intro i _
    change _ = (mesh (i + 1) - mesh i) * (mesh (i + 1) * sigmoid (-mesh (i + 1)))
    ring
  have hgridEntropy :
      2 * ∑ i : Fin m, δ i * binEntropy (q i) =
        rightEndpointEntropy (fun i => (i : ℝ) * (U / m)) m := by
    simp only [t, δ, q, Fin.val_succ, Fin.val_castSucc, rightEndpointEntropy]
    exact congrArg (fun x : ℝ => 2 * x) (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      (mesh (j + 1) - mesh j) * binEntropy (sigmoid (-mesh (j + 1)))) m)
  have hslack : 2 * ∑ i : Fin m, t i.succ * (δ i * q i) < B := by
    rw [hgridCost]
    apply hcost.trans_lt
    exact mul_lt_mul_of_pos_left (by nlinarith [sq_nonneg η]) hA
  have hd (i : Fin m) :
      Tendsto (fun P => ((donorBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (δ i)) := by
    simpa only [donorBin, s, W, δ, neg_sub_neg] using
      primeInterval_moving_log_power_capacity hC ha (neg_lt_neg (ht i.castSucc_lt_succ))
  have hrec (i : Fin m) :
      Tendsto (fun P => ((recipientBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (δ i)) :=
    primeInterval_moving_log_power_capacity hC ha (ht i.castSucc_lt_succ)
  have hs : Tendsto s atTop atTop :=
    ((tendsto_rpow_atTop ha).comp tendsto_log_atTop).const_mul_atTop hC
  have hnear (i : Fin m) : ∀ᶠ P in atTop, 3 / 4 < exp (-t i.succ / s P) := by
    have hexp : Tendsto (fun P => exp (-t i.succ / s P)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, exp_zero] using
        (continuous_exp.tendsto 0).comp (hs.const_div_atTop (-t i.succ))
    exact hexp.eventually_const_lt (by norm_num)
  have hdonors : ∀ᶠ P in atTop, ∀ i, donorBin t P (s P) i ⊆ base P := by
    filter_upwards [Filter.eventually_all.mpr hnear, hbase, hs.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with P hnearP hb hsP hP i p hp
    have hmem := mem_filter.mp (show p ∈ primeInterval
      (P * exp (-t i.succ / s P)) (P * exp (-t i.castSucc / s P)) from hp)
    have hend := mem_Ioc.mp hmem.1
    have ht_nonneg : 0 ≤ t i.castSucc := ht0 ▸ ht.monotone (Fin.zero_le _)
    refine hb.2.2.2 p hmem.2 ?_ ?_
    · have hlower : 3 * P / 4 < P * exp (-t i.succ / s P) := by
        calc
          3 * P / 4 = P * (3 / 4) := by ring
          _ < _ := mul_lt_mul_of_pos_left (hnearP i) hP
      exact hlower.trans (Nat.lt_of_floor_lt hend.1)
    · have hupper : P * exp (-t i.castSucc / s P) ≤ P := by
        conv_rhs => rw [← mul_one P]
        exact mul_le_mul_of_nonneg_left
          (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht_nonneg) hsP.le))
          hP.le
      exact ((Nat.le_floor_iff (mul_pos hP (exp_pos _)).le).mp hend.2).trans hupper
  have hexchange := log_power_grid_lower t ht ht0 q (fun i => sigmoid_pos _)
    (fun i => sigmoid_lt_one _) C a hC ha base D B ζ hζ hslack hd hrec hnormalized (by
      filter_upwards [hbase, hdonors] with P hb hdon
      exact ⟨hb.1, hdon, hb.2.2.1⟩)
  have hKC : K * C = 2 * A + ε * c / 8 := by
    dsimp [C, η]
    rw [mul_comm (1 + ε / (8 * K)) c, ← mul_assoc, hKc]
    calc
      2 * A * (1 + ε / (8 * K)) = 2 * A + (2 * A / K) * ε / 8 := by ring
      _ = _ := by rw [← hKc, mul_comm K c, mul_div_cancel_right₀ _ hK.ne']; ring
  have hcoef : (K - ε) * C ≤ 2 * ∑ i : Fin m, δ i * binEntropy (q i) - ζ := by
    rw [hgridEntropy, sub_mul, hKC]
    have hcC : c ≤ C := by dsimp [C]; nlinarith [mul_pos hη hc]
    have heC := mul_le_mul_of_nonneg_left hcC hε.le
    change 2 * A - ρ ≤ _ at hentropy
    dsimp only [ρ] at hentropy
    dsimp only [ζ]
    linarith only [hentropy, heC, mul_pos hε hc]
  filter_upwards [hexchange, hbase, eventually_gt_atTop (1 : ℝ)] with P he hb hP
  let tail := (Icc 1 ⌊exp P⌋₊).filter
    (fun n : ℕ => T P < (ArithmeticFunction.cardDistinctFactors n : ℝ))
  let h (i : Fin m) := ⌊q i *
    (min (donorBin t P (s P) i).card (recipientBin t P (s P) i).card : ℕ)⌋₊
  let outputs := pairedOutputs (base P) (donorBin t P (s P)) (recipientBin t P (s P)) h
  have hinclusion : outputs ⊆ tail := by
    intro n hn
    obtain ⟨hnpos, _, hω, hstrict⟩ := he.2.2.1 n hn
    refine mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hnpos, (Nat.le_floor_iff (exp_pos P).le).mpr hstrict.le⟩, ?_⟩
    simpa only [hω] using hb.2.1
  have hcard : outputs.card ≤ tail.card := card_le_card hinclusion
  have hpos : 0 < outputs.card := he.2.1
  have hlog := log_le_log (by exact_mod_cast hpos : (0 : ℝ) < outputs.card)
    (by exact_mod_cast hcard : (outputs.card : ℝ) ≤ tail.card)
  have hL := log_pos hP
  have hWP : 0 ≤ W P := by
    have hP0 := zero_lt_one.trans hP
    dsimp [W, s]
    positivity
  have hscale : Z P = C * W P := by
    dsimp [Z, W, s]
    rw [show ((r : ℝ) + 1) / 2 = 1 + a by dsimp [a]; ring, rpow_add hL, rpow_one]
    field_simp [hC.ne', (rpow_pos_of_pos hL a).ne']
  change 0 < tail.card ∧ (K - ε) * Z P ≤ log (tail.card : ℝ)
  refine ⟨hpos.trans_le hcard, ?_⟩
  calc
    (K - ε) * Z P = ((K - ε) * C) * W P := (congrArg ((K - ε) * ·) hscale).trans (mul_assoc _ _ _).symm
    _ ≤ (2 * ∑ i : Fin m, δ i * binEntropy (q i) - ζ) * W P :=
      mul_le_mul_of_nonneg_right hcoef hWP
    _ ≤ log (outputs.card : ℝ) := he.2.2.2
    _ ≤ log (tail.card : ℝ) := hlog

end D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
