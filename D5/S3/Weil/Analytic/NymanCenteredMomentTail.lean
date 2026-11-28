/- GID: D5/S3/Weil/Analytic/NymanCenteredMomentTail
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanCenteredMoment
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: Cubic logarithmic decay makes the weighted centered prime sum integrable on a tail. -/

import D5.S3.Weil.Analytic.MobiusLogFourth
import D5.S3.Weil.Analytic.NymanLogCorrectionEnvelope
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The absolute tail of the weighted centered prime dilation sum. -/

set_option autoImplicit false

noncomputable section

open Finset Filter MeasureTheory
open Set (Ioi Ioo)
open scoped ArithmeticFunction.Moebius

namespace NymanCenteredMomentTail

open NymanPrimeDilations
open NymanFixedRationalKernel (A_pos b b_lipschitz b_zero_left b_zero_off b_zero_right)
open MobiusCenteredHyperbola (mobiusPrefix)

private theorem prefix_eq_range (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (μ i : ℝ)) = mobiusPrefix (n : ℝ) := by
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp [mobiusPrefix]

/-- Abel summation on a finite interval with both endpoints outside the support. -/
private theorem shell_by_parts {x : ℝ} (hx : 0 < x) :
    shell x = -(∑ n ∈ Ico 0 (⌊B * x⌋₊ + 1),
      (b (((n + 1 : ℕ) : ℝ) / x) - b ((n : ℝ) / x)) * mobiusPrefix (n : ℝ)) := by
  let N : ℕ := ⌊B * x⌋₊ + 1
  let w (n : ℕ) : ℝ := b ((n : ℝ) / x)
  have hN : B * x ≤ (N : ℝ) := by
    dsimp [N]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (B * x)).le
  have hwN : w N = 0 := b_zero_right ((le_div_iff₀ hx).2 hN)
  have hsum : shell x = ∑ n ∈ Ico 0 (N + 1), w n • (μ n : ℝ) := by
    calc
      shell x = ∑ n ∈ Ioc 0 ⌊B * x⌋₊, w n • (μ n : ℝ) := by
        unfold shell
        apply Finset.sum_congr rfl
        intro n _
        simp only [w, smul_eq_mul]
        exact mul_comm _ _
      _ = _ := by
        apply Finset.sum_subset
        · intro n hn
          obtain ⟨_, htop⟩ := mem_Ioc.mp hn
          exact mem_Ico.mpr ⟨Nat.zero_le _, by dsimp [N]; omega⟩
        · intro n hn hn'
          by_cases h0 : n = 0
          · simp [h0]
          have htop := (mem_Ico.mp hn).2
          dsimp [N] at htop
          have hlast : n = N := by
            by_contra hne
            apply hn'
            refine mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, ?_⟩
            dsimp [N] at hne
            omega
          simp [hlast, hwN]
  change shell x = -(∑ n ∈ Ico 0 N, (w (n + 1) - w n) * mobiusPrefix (n : ℝ))
  rw [hsum, Finset.sum_Ico_by_parts w (fun n => (μ n : ℝ)) (Nat.succ_pos N)]
  rw [show N + 1 - 1 = N by omega]
  simp only [hwN, range_zero, sum_empty, smul_eq_mul, prefix_eq_range,
    zero_mul, mul_zero, sub_zero, zero_sub]

private theorem shell_log_fourth_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ≥ (4 : ℝ), |shell x| ≤ K * x / Real.log x ^ 4 := by
  obtain ⟨M, hM, hm⟩ := MobiusLogFourth.mobiusPrefix_fourth_log_bound
  obtain ⟨L, hL, hw⟩ := b_lipschitz
  have hB₀ : 0 ≤ B := pow_nonneg A_pos.le _
  refine ⟨16 * M * B * L * (B + 1), by positivity, fun x hx => ?_⟩
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx₁
  let N : ℕ := ⌊B * x⌋₊ + 1
  have hN : (N : ℝ) ≤ (B + 1) * x := by
    dsimp [N]
    push_cast
    linarith only [Nat.floor_le (mul_nonneg hB₀ hx₀.le), hx]
  have hpoint (n : ℕ) (hn : n ∈ Ico 0 N) :
      |(b (((n + 1 : ℕ) : ℝ) / x) - b ((n : ℝ) / x)) * mobiusPrefix (n : ℝ)| ≤
        16 * M * B * L / Real.log x ^ 4 := by
    by_cases hsmall : ((n + 1 : ℕ) : ℝ) ≤ x
    · have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hnsmall := hnle.trans hsmall
      rw [b_zero_left ((div_le_one hx₀).2 hsmall),
        b_zero_left ((div_le_one hx₀).2 hnsmall), sub_self, zero_mul, abs_zero]
      positivity
    have hnx : x / 2 ≤ (n : ℝ) := by
      push_cast at hsmall
      linarith
    have hn₁ : 1 < (n : ℝ) := by linarith
    have hnBx : (n : ℝ) ≤ B * x := by
      have hnat := (mem_Ico.mp hn).2
      dsimp [N] at hnat
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hnat)).trans
        (Nat.floor_le (mul_nonneg hB₀ hx₀.le))
    have hlogn : Real.log x / 2 ≤ Real.log (n : ℝ) := by
      have hnlog := Real.log_le_log (by positivity : 0 < x / 2) hnx
      rw [Real.log_div hx₀.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hnlog
      have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h4
      linarith
    have hMbound : |mobiusPrefix (n : ℝ)| ≤ (16 * M * B) * x / Real.log x ^ 4 := by
      calc
        _ ≤ M * (n : ℝ) / Real.log (n : ℝ) ^ 4 := hm n hn₁
        _ ≤ M * (n : ℝ) / (Real.log x / 2) ^ 4 :=
          div_le_div_of_nonneg_left (mul_nonneg hM (by positivity)) (pow_pos (by positivity) _)
            (pow_le_pow_left₀ (by positivity) hlogn 4)
        _ ≤ M * (B * x) / (Real.log x / 2) ^ 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnBx hM) (by positivity)
        _ = _ := by field_simp [hlog.ne']; ring
    have hstep : ((n + 1 : ℕ) : ℝ) / x - (n : ℝ) / x = 1 / x := by
      push_cast
      ring
    have hW : |b (((n + 1 : ℕ) : ℝ) / x) - b ((n : ℝ) / x)| ≤ L / x := by
      have h := hw (((n + 1 : ℕ) : ℝ) / x) ((n : ℝ) / x)
      rw [hstep, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / x)] at h
      simpa only [mul_one_div] using h
    rw [abs_mul]
    calc
      _ ≤ (L / x) * ((16 * M * B) * x / Real.log x ^ 4) :=
        mul_le_mul hW hMbound (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [hx₀.ne', hlog.ne']
  rw [shell_by_parts hx₀, abs_neg]
  change |∑ n ∈ Ico 0 N, (b (((n + 1 : ℕ) : ℝ) / x) - b ((n : ℝ) / x)) *
      mobiusPrefix (n : ℝ)| ≤ _
  calc
    _ ≤ ∑ _n ∈ Ico 0 N, 16 * M * B * L / Real.log x ^ 4 :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpoint)
    _ = (N : ℝ) * (16 * M * B * L / Real.log x ^ 4) := by simp [nsmul_eq_mul]
    _ ≤ ((B + 1) * x) * (16 * M * B * L / Real.log x ^ 4) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

private theorem shell_linear_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y > (0 : ℝ), |shell y| ≤ K * y := by
  obtain ⟨L, hL, hw⟩ := b_lipschitz
  have hB : 0 ≤ B := pow_nonneg A_pos.le _
  have hb (u : ℝ) : |b u| ≤ L := by
    by_cases hu : u ∈ Ioo (1 : ℝ) 2
    · have hu' := hw u 1
      rw [b_zero_left le_rfl, sub_zero, abs_of_nonneg (sub_nonneg.mpr hu.1.le)] at hu'
      exact hu'.trans (by nlinarith [mul_nonneg hL (sub_nonneg.mpr hu.2.le)])
    · simp [b_zero_off u hu, hL]
  refine ⟨L * B, by positivity, fun y hy => ?_⟩
  unfold shell
  calc
    _ ≤ ∑ _n ∈ Ioc 0 ⌊B * y⌋₊, L := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      refine Finset.sum_le_sum fun n _ => ?_
      rw [abs_mul]
      have hn : |(μ n : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      exact (mul_le_mul hn (hb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (⌊B * y⌋₊ : ℝ) * L := by simp [nsmul_eq_mul]
    _ ≤ (B * y) * L := mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hB hy.le)) hL
    _ = _ := by ring

private theorem past_half_envelope {K K₀ x : ℝ} (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀)
    (hfour : ∀ t ≥ (4 : ℝ), |shell t| ≤ K * t / Real.log t ^ 4)
    (hlin : ∀ t > (0 : ℝ), |shell t| ≤ K₀ * t)
    (hx : 16 ≤ x) (hsmall : Real.log x ^ 4 ≤ x ^ (1 / 4 : ℝ)) :
    ∀ t > (0 : ℝ), t ≤ x →
      |shell t| ≤ ((16 * K + K₀) * x ^ (1 / 2 : ℝ) / Real.log x ^ 4) *
        t ^ (1 / 2 : ℝ) := by
  intro t ht htx
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 < x := by linarith
  have hlog := Real.log_pos hx₁
  have hd : 0 < Real.log x ^ 4 := pow_pos hlog _
  have htroot : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have hroot : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx₀ _
  have htprod : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht]
    norm_num
  have htden : t / t ^ (1 / 2 : ℝ) = t ^ (1 / 2 : ℝ) := by
    exact (div_eq_iff htroot.ne').2 htprod.symm
  apply (div_le_iff₀ htroot).1
  by_cases hts : t ≤ x ^ (1 / 2 : ℝ)
  · have hp : (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = x ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hx₀.le]
      norm_num
    have htQ := Real.rpow_le_rpow ht.le hts (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [hp] at htQ
    have hQ : x ^ (1 / 4 : ℝ) ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ 4 := by
      have hprod : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx₀]
        norm_num
      exact (le_div_iff₀ hd).2
        ((mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hx₀.le _)).trans_eq hprod)
    calc
      |shell t| / t ^ (1 / 2 : ℝ) ≤ (K₀ * t) / t ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (hlin _ ht) htroot.le
      _ = K₀ * t ^ (1 / 2 : ℝ) := by rw [mul_div_assoc, htden]
      _ ≤ K₀ * (x ^ (1 / 2 : ℝ) / Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left (htQ.trans hQ) hK₀
      _ ≤ _ := by
        rw [mul_div_assoc (16 * K + K₀)]
        exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hroot.le hd.le)
  · have hts' : x ^ (1 / 2 : ℝ) ≤ t := le_of_not_ge hts
    have hx4 : 4 ≤ x ^ (1 / 2 : ℝ) := by
      have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
        rw [← Real.sqrt_eq_rpow]
        norm_num
      rw [← h16]
      exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
    have ht4 := hx4.trans hts'
    have hlogt := Real.log_le_log hroot hts'
    rw [Real.log_rpow hx₀] at hlogt
    have hpow : (Real.log x / 2) ^ 4 ≤ Real.log t ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) _ 4
      linarith
    have htr := Real.rpow_le_rpow ht.le htx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      |shell t| / t ^ (1 / 2 : ℝ) ≤ (K * t / Real.log t ^ 4) / t ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (hfour _ ht4) htroot.le
      _ = K * t ^ (1 / 2 : ℝ) / Real.log t ^ 4 := by
        rw [div_right_comm, mul_div_assoc, htden]
      _ ≤ K * t ^ (1 / 2 : ℝ) / (Real.log x / 2) ^ 4 :=
        div_le_div_of_nonneg_left (mul_nonneg hK htroot.le)
          (pow_pos (by positivity) _) hpow
      _ ≤ K * x ^ (1 / 2 : ℝ) / (Real.log x / 2) ^ 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htr hK) (by positivity)
      _ = (16 * K) * x ^ (1 / 2 : ℝ) / Real.log x ^ 4 := by
        field_simp [hlog.ne']
        ring
      _ ≤ _ := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₀) hroot.le) hd.le

set_option maxHeartbeats 500000 in
/-- The centered identity transports the unconditional Möbius prefix bound
to the weighted prime term used in the zero Mellin moment. -/
theorem centeredPrime_log_cube_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      |centeredPrimeDilations x| ≤ K * x / Real.log x ^ 3 := by
  obtain ⟨K, hK, hfour⟩ := shell_log_fourth_bound
  obtain ⟨K₀, hK₀, hlin⟩ := shell_linear_bound
  obtain ⟨D, hD, hpower⟩ := abs_higherPowerDilations_le_half_log_add
  let P := 16 * K + K₀
  let Q := 4 * NymanKernelConvolution.h + 16
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith [NymanKernelConvolution.h_pos]
  refine ⟨K + Q * P + (1 / 2 + D) * P, by positivity, ?_⟩
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := 1 / 4) 4
    (by norm_num)).eventuallyLE
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), hsmall] with x hx hlog₁ hsmall
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog₁
  have hsmall' : Real.log x ^ 4 ≤ x ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog.le _),
      abs_of_nonneg (Real.rpow_nonneg hx₀.le _)] using hsmall
  let E := P * x ^ (1 / 2 : ℝ) / Real.log x ^ 4
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henvelope := past_half_envelope hK hK₀ hfour hlin hx hsmall'
  have hEp : E * x ^ (1 / 2 : ℝ) = P * x / Real.log x ^ 4 := by
    have hp : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_add hx₀]
      norm_num
    dsimp [E]
    rw [div_mul_eq_mul_div₀, mul_assoc, hp]
  have hL := NymanLogCorrection.abs_logCorrection_le_envelope hx₀
    (show (1 / 2 : ℝ) ≤ 1 / 2 from le_rfl) hE henvelope
  change |logCorrection x| ≤ Q * E * x ^ (1 / 2 : ℝ) at hL
  rw [mul_assoc, hEp] at hL
  have hH := hpower x hx₁ (1 / 2) le_rfl E hE henvelope
  rw [hEp] at hH
  have hratio : ∀ A : ℝ, 0 ≤ A → A / Real.log x ^ 4 ≤ A / Real.log x ^ 3 := by
    intro A hA
    apply div_le_div_of_nonneg_left hA (pow_pos hlog _)
    have hh := mul_le_mul_of_nonneg_right hlog₁ (pow_nonneg hlog.le 3)
    rw [one_mul, ← pow_succ'] at hh
    exact hh
  have hL' : |logCorrection x| ≤ Q * P * x / Real.log x ^ 3 := by
    refine hL.trans ?_
    rw [← mul_div_assoc, ← mul_assoc]
    exact hratio _ (by positivity)
  have hH' : |higherPowerDilations x| ≤ (1 / 2 + D) * P * x / Real.log x ^ 3 := by
    have hh : Real.log x / 2 + D ≤ (1 / 2 + D) * Real.log x := by
      have h1 := mul_le_mul_of_nonneg_left hlog₁ hD
      linarith
    calc
      _ ≤ (P * x / Real.log x ^ 4) * (Real.log x / 2 + D) := hH
      _ ≤ (P * x / Real.log x ^ 4) * ((1 / 2 + D) * Real.log x) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [hlog.ne'] <;> ring
  have hs : |(1 - Real.log x) * shell x| ≤ K * x / Real.log x ^ 3 := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hlog₁)]
    calc
      _ ≤ Real.log x * (K * x / Real.log x ^ 4) :=
        mul_le_mul (by linarith) (hfour x (by linarith)) (abs_nonneg _) hlog.le
      _ = _ := by field_simp [hlog.ne'] <;> ring
  have hcent : centeredPrimeDilations x =
      (1 - Real.log x) * shell x - logCorrection x - higherPowerDilations x := by
    rw [← primeDilations_add_shell_eq_centered hx₁]
    calc
      _ = -(Real.log x * shell x + logCorrection x) + shell x - higherPowerDilations x := by
        rw [moebius_log_split hx₀]
        ring
      _ = _ := by ring
  rw [hcent]
  calc
    _ ≤ |(1 - Real.log x) * shell x| + |logCorrection x| + |higherPowerDilations x| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K * x / Real.log x ^ 3 + Q * P * x / Real.log x ^ 3 +
        (1 / 2 + D) * P * x / Real.log x ^ 3 := add_le_add (add_le_add hs hL') hH'
    _ = _ := by ring

/-- A measurable weighted centered prime term is absolutely integrable on a tail.
The compact-interval part is handled by the finite-dilation representation. -/
theorem integrable_centeredPrime_weighted_tail
    (hm : Measurable (fun x : ℝ => centeredPrimeDilations x / x ^ 2)) :
    ∃ T > (1 : ℝ), IntegrableOn (fun x : ℝ => centeredPrimeDilations x / x ^ 2) (Ioi T) := by
  obtain ⟨K, hK, hbound⟩ := centeredPrime_log_cube_bound
  obtain ⟨S, hS⟩ := eventually_atTop.mp (hbound.and
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)))
  let T := max S 2
  have hT : 1 < T := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  refine ⟨T, hT, ?_⟩
  have hDom : IntegrableOn (fun x : ℝ => K * (x⁻¹ / Real.log x ^ 2)) (Ioi T) :=
    (integrableOn_inv_div_log_sq_Ioi hT).const_mul K
  apply hDom.mono' hm.aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_Ioi).2
  apply Eventually.of_forall
  intro x hx
  have hxs : S ≤ x := (le_max_left _ _).trans hx.le
  obtain ⟨hb, hlog₁⟩ := hS x hxs
  have hx₀ : 0 < x := (zero_lt_one.trans hT).trans hx
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog₁
  have hpow : Real.log x ^ 2 ≤ Real.log x ^ 3 := by
    simpa only [one_mul, pow_succ'] using
      mul_le_mul_of_nonneg_right hlog₁ (pow_nonneg hlog.le 2)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg hx₀.le 2)]
  calc
    _ ≤ (K * x / Real.log x ^ 3) / x ^ 2 :=
      div_le_div_of_nonneg_right hb (pow_nonneg hx₀.le 2)
    _ ≤ (K * x / Real.log x ^ 2) / x ^ 2 :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (mul_nonneg hK hx₀.le) (pow_pos hlog _) hpow)
        (pow_nonneg hx₀.le 2)
    _ = _ := by field_simp [hx₀.ne', hlog.ne']

end NymanCenteredMomentTail
