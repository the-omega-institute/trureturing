/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveScalarFourth
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveScalarFourth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sieve moment hypotheses control fourth norms uniformly over interval lengths. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveFiniteProbability
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveIntervalGeometry
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizationAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform scalar fourth-norm estimates for finite sieve interval sums. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Each centered sieve variable is bounded by the reciprocal sieve density. -/
private theorem sieve_variable_abs_le (Q : ℕ+) : 1 ≤ sieveDensity Q ∧
    ∀ d : ℕ, ∀ x : ZMod (Q : ℕ), |sieveVariable Q d x| ≤ sieveDensity Q := by
  have hphi : (0 : ℝ) < Nat.totient (Q : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr Q.pos
  have hP : 1 ≤ sieveDensity Q := (one_le_div₀ hphi).mpr (by
    exact_mod_cast Nat.totient_le (Q : ℕ))
  refine ⟨hP, fun d x => ?_⟩
  unfold sieveVariable
  split_ifs <;> simp only [mul_one, mul_zero, zero_sub, abs_neg, abs_one]
  · exact abs_le.mpr ⟨by change -(sieveDensity Q) ≤ sieveDensity Q - 1; linarith, by change sieveDensity Q - 1 ≤ sieveDensity Q; linarith⟩
  · exact hP

/-- The fourth norm of an interval sum is at most its cardinality times the density. -/
private theorem sieve_interval_norm4_trivial (Q : ℕ+) (H a b : ℝ) :
    sieveNorm4 Q (sieveIntervalSum Q H a b) ≤ (points H a b).card * sieveDensity Q := by
  have hP := (sieve_variable_abs_le Q).1
  have hbound (x : ZMod (Q : ℕ)) :
      ‖sieveIntervalSum Q H a b x‖ ≤ (points H a b).card * sieveDensity Q := by
    change |∑ d ∈ points H a b, sieveVariable Q d x| ≤ _
    calc
      _ ≤ ∑ d ∈ points H a b, |sieveVariable Q d x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ points H a b, sieveDensity Q :=
        Finset.sum_le_sum (fun d _ => (sieve_variable_abs_le Q).2 d x)
      _ = _ := by simp
  have := sieve_probability Q
  rw [sieve_norm4_eq_lpNorm]
  calc
    _ ≤ lpNorm (fun _ : ZMod (Q : ℕ) => (points H a b).card * sieveDensity Q) 4 (sieveUniformMeasure Q) :=
      lpNorm_mono_real (sieve_memLp_four Q _) hbound
    _ = _ := by
      have hP0 : 0 ≤ sieveDensity Q := zero_le_one.trans hP
      simp [abs_of_nonneg hP0]

/-- The scalar finite-sieve hypothesis bounds fourth moments for every translated interval. -/
private theorem sieve_interval_fourth_moment (hMS : MSFinite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℕ+) (H a b : ℝ),
      let K : ℝ := (points H a b).card
      sieveExpectation Q (fun x => sieveIntervalSum Q H a b x ^ 4) ≤
        C * ((K * sieveDensity Q)^2 + K ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18) := by
  obtain ⟨C₂, C₄, hC₂, hC₄, h₂, h₄⟩ := hMS
  refine ⟨3 * C₂ ^ 2 + C₄, by positivity, ?_⟩
  intro Q H a b
  dsimp only
  let n := (points H a b).card
  by_cases hn : n = 0
  · have he : points H a b = ∅ := Finset.card_eq_zero.mp hn
    simp only [sieveIntervalSum, he, Finset.sum_empty, zero_pow (by norm_num : 4 ≠ 0),
      sieveExpectation, Finset.sum_const_zero, Finset.card_empty, Nat.cast_zero,
      zero_mul, zero_add, zero_div, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hv0 : 0 ≤ sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 2) := by
    unfold sieveExpectation
    positivity
  have hv := h₂ Q n hn1
  have hv2 := pow_le_pow_left₀ hv0 hv 2
  have hfour := (abs_le.mp (h₄ Q n hn1)).2
  rw [show sieveExpectation Q (fun x => sieveIntervalSum Q H a b x ^ 4) =
    sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 4) from sieve_interval_moment_prefix Q H a b 4]
  have hmain : sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 4) ≤
      3 * C₂ ^ 2 * ((n : ℝ) * sieveDensity Q) ^ 2 +
        C₄ * ((n : ℝ) ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18) := by
    nlinarith only [hv2, hfour]
  have herror : 0 ≤ (n : ℝ) ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18 := by positivity
  have hmain0 : 0 ≤ ((n : ℝ) * sieveDensity Q)^2 := sq_nonneg _
  change _ ≤ (3 * C₂ ^ 2 + C₄) *
    (((n : ℝ) * sieveDensity Q)^2 + (n : ℝ) ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18)
  nlinarith only [hmain, mul_nonneg hC₄ hmain0,
    mul_nonneg (show 0 ≤ 3 * C₂ ^ 2 by positivity) herror]

/-- Below the fourth-root threshold the pointwise bound gives the scalar error scale. -/
private theorem sieve_interval_norm4_small (B : ℝ) (_hB : 1 ≤ B) (H : ℝ) (hH : 2 ≤ H)
    (Q : ℕ+) (hP : sieveDensity Q ≤ B * Real.log H) (a b : ℝ)
    (hK : ((points H a b).card : ℝ) ≤ H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H)) :
    sieveNorm4 Q (sieveIntervalSum Q H a b) ≤ B * H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H) := by
  have hlog : 0 < Real.log H := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt (Real.log H) := Real.sqrt_pos.mpr hlog
  calc
    _ ≤ (points H a b).card * sieveDensity Q := sieve_interval_norm4_trivial Q H a b
    _ ≤ (H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H)) * (B * Real.log H) :=
      mul_le_mul hK hP (by linarith [(sieve_variable_abs_le Q).1]) (by positivity)
    _ = _ := by
      rw [div_mul_eq_mul_div, div_eq_iff hsqrt.ne']
      linear_combination -B * H ^ (1 / 4 : ℝ) * (Real.sq_sqrt hlog.le)

private theorem sieve_threshold_power_lower (H : ℝ) (hH : 0 < H)
    (hlog : 0 < Real.log H) (hbound : Real.log H ≤ H ^ (1 / 4 : ℝ)) :
    H ^ (1 / 8 : ℝ) ≤ H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H) := by
  have hsqrt : Real.sqrt (Real.log H) ≤ H ^ (1 / 8 : ℝ) := by
    apply (Real.sqrt_le_left (Real.rpow_nonneg hH.le _)).mpr
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    norm_num
    exact hbound
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hlog)).mpr
  calc
    _ ≤ H ^ (1 / 8 : ℝ) * H ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hH.le _)
    _ = H ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hH]; norm_num

/-- Above the fourth-root threshold the normalized scalar moment error is eventually at most one. -/
private theorem sieve_fourth_threshold_error (B : ℝ) (_hB : 1 ≤ B) :
    ∀ᶠ H : ℝ in atTop, ∀ K : ℝ,
      H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H) ≤ K →
      K ^ (-1 / 28 : ℝ) * (B * Real.log H)^18 / (Real.log H)^2 ≤ 1 := by
  have hloglim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun H : ℝ =>
      B^18 * ((Real.log H)^18 / H^(1 / 224 : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat, mul_zero] using
      ((isLittleO_log_rpow_rpow_atTop (18 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 224)).tendsto_div_nhds_zero.const_mul (B^18))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hloglim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with H hH hlog hlogbound hsmall
  have hH0 : 0 < H := zero_lt_one.trans hH
  have hlog0 : 0 < Real.log H := zero_lt_one.trans_le hlog
  have hbound : Real.log H ≤ H ^ (1 / 4 : ℝ) :=
    (div_le_one (Real.rpow_pos_of_pos hH0 _)).mp hlogbound
  intro K hK
  have hlow := (sieve_threshold_power_lower H hH0 hlog0 hbound).trans hK
  have hpow : K ^ (-1 / 28 : ℝ) ≤ H ^ (-1 / 224 : ℝ) := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hH0 (1 / 8 : ℝ))
      hlow (by norm_num : (-1 / 28 : ℝ) ≤ 0)
    rw [← Real.rpow_mul hH0.le] at hp
    norm_num at hp ⊢
    exact hp
  calc
    _ ≤ H ^ (-1 / 224 : ℝ) * (B * Real.log H)^18 / (Real.log H)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (by positivity)) (sq_nonneg _)
    _ ≤ H ^ (-1 / 224 : ℝ) * (B * Real.log H)^18 :=
      div_le_self (by positivity) (by nlinarith only [hlog])
    _ = B^18 * ((Real.log H)^18 / H^(1 / 224 : ℝ)) := by
      rw [show (-1 / 224 : ℝ) = -(1 / 224 : ℝ) by ring, Real.rpow_neg hH0.le, mul_pow]
      ring
    _ ≤ 1 := hsmall

/-- Above the fourth-root threshold the fourth norm has the square-root cardinality bound. -/
private theorem sieve_interval_norm4_large (hMS : MSFinite) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (Q : ℕ+), sieveDensity Q ≤ B * Real.log H → ∀ a b : ℝ,
      H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H) ≤ (points H a b).card →
      sieveNorm4 Q (sieveIntervalSum Q H a b) ≤ C * Real.sqrt ((points H a b).card * Real.log H) := by
  obtain ⟨C, hC, hmoment⟩ := sieve_interval_fourth_moment hMS
  let D := C * (B^2 + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + 1, by positivity, ?_⟩
  filter_upwards [sieve_fourth_threshold_error B hB, eventually_ge_atTop (2 : ℝ)]
    with H herror hH Q hP a b hK
  let K : ℝ := (points H a b).card
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log H := Real.log_pos (by linarith)
  have hK0 : 0 < K := (div_pos (Real.rpow_pos_of_pos hH0 _)
    (Real.sqrt_pos.mpr hL)).trans_le hK
  have hP0 : 0 ≤ sieveDensity Q := zero_le_one.trans (sieve_variable_abs_le Q).1
  have he : K ^ (-1 / 28 : ℝ) * (B * Real.log H)^18 ≤ (Real.log H)^2 :=
    (div_le_one (sq_pos_of_pos hL)).mp (herror K hK)
  have hid : K ^ (2 - 1 / 28 : ℝ) = K^2 * K ^ (-1 / 28 : ℝ) := by
    rw [show (2 - 1 / 28 : ℝ) = 2 + (-1 / 28) by ring, Real.rpow_add hK0,
      Real.rpow_two]
  have herr : K ^ (2 - 1 / 28 : ℝ) * sieveDensity Q^18 ≤ (K * Real.log H)^2 := by
    calc
      _ ≤ K ^ (2 - 1 / 28 : ℝ) * (B * Real.log H)^18 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP 18) (by positivity)
      _ = K^2 * (K ^ (-1 / 28 : ℝ) * (B * Real.log H)^18) := by rw [hid]; ring
      _ ≤ K^2 * (Real.log H)^2 := mul_le_mul_of_nonneg_left he (sq_nonneg K)
      _ = _ := by ring
  have hvar : (K * sieveDensity Q)^2 ≤ B^2 * (K * Real.log H)^2 := by
    have hp := pow_le_pow_left₀ hP0 hP 2
    nlinarith only [mul_le_mul_of_nonneg_left hp (sq_nonneg K)]
  have hfour : (sieveNorm4 Q (sieveIntervalSum Q H a b))^4 ≤ D * (K * Real.log H)^2 := by
    rw [sieve_norm4_fourth]
    simp only [Even.pow_abs (by decide : Even (4 : ℕ))]
    have hm := hmoment Q H a b
    change sieveExpectation Q (fun x => sieveIntervalSum Q H a b x ^ 4) ≤ D * (K * Real.log H)^2
    calc
      _ ≤ C * ((K * sieveDensity Q)^2 + K ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18) := hm
      _ ≤ C * (B^2 * (K * Real.log H)^2 + (K * Real.log H)^2) :=
        mul_le_mul_of_nonneg_left (add_le_add hvar herr) hC
      _ = _ := by dsimp [D]; ring
  have hDpow : D ≤ (D + 1)^4 :=
    (by linarith : D ≤ D + 1).trans (le_self_pow₀ (by linarith) (by norm_num))
  apply (pow_le_pow_iff_left₀ (sieve_norm4_nonneg Q _) (by positivity)
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  calc
    _ ≤ D * (K * Real.log H)^2 := hfour
    _ ≤ (D + 1)^4 * (K * Real.log H)^2 :=
      mul_le_mul_of_nonneg_right hDpow (sq_nonneg _)
    _ = ((D + 1) * Real.sqrt (K * Real.log H))^4 := by
      rw [mul_pow (D + 1) (Real.sqrt (K * Real.log H)) 4,
        (normalizer_powers K (Real.log H) hK0 hL).2.2.2]

private theorem sieve_card_sqrt_le (H a b : ℝ) (hH : 2 ≤ H)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt ((points H a b).card * Real.log H) ≤
      sieveScale H * Real.sqrt (b - a) + Real.sqrt (Real.log H) := by
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hcard := mul_le_mul_of_nonneg_right (sieve_interval_card_le H a b hH0 ha hab) hL
  have hA : (sieveScale H)^2 = H * Real.log H := Real.sq_sqrt (by positivity)
  have hs : (sieveScale H * Real.sqrt (b - a))^2 = H * Real.log H * (b - a) := by
    rw [mul_pow, hA, Real.sq_sqrt (sub_nonneg.mpr hab)]
  have hnonneg : 0 ≤ sieveScale H * Real.sqrt (b - a) := by unfold sieveScale; positivity
  apply (Real.sqrt_le_left (add_nonneg hnonneg (Real.sqrt_nonneg _))).mpr
  nlinarith only [hcard, hs, Real.sq_sqrt hL,
    mul_nonneg hnonneg (Real.sqrt_nonneg (Real.log H))]

/-- Scalar fourth norms are bounded by the interval square-root scale and the threshold error. -/
theorem sieve_interval_norm4_bound (hMS : MSFinite) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (Q : ℕ+), sieveDensity Q ≤ B * Real.log H → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      sieveNorm4 Q (sieveIntervalSum Q H a b) ≤ C *
        (sieveScale H * Real.sqrt (b - a) + H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H)) := by
  obtain ⟨C, hC, hlarge⟩ := sieve_interval_norm4_large hMS B hB
  let C' := max B (max 1 C)
  have hC' : 1 ≤ C' := (le_max_left 1 C).trans (le_max_right B (max 1 C))
  have hBC : B ≤ C' := le_max_left _ _
  have hCC : C ≤ C' := (le_max_right 1 C).trans (le_max_right B (max 1 C))
  refine ⟨C', hC', ?_⟩
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℝ)] with H hlargeH hH Q hP a b ha hab
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hA : 0 ≤ sieveScale H * Real.sqrt (b - a) := by unfold sieveScale; positivity
  have hroot : 1 ≤ H ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hsmallterm : Real.sqrt (Real.log H) ≤ H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hroot
  by_cases hK : H ^ (1 / 4 : ℝ) / Real.sqrt (Real.log H) ≤ (points H a b).card
  · calc
      _ ≤ C * Real.sqrt ((points H a b).card * Real.log H) := hlargeH Q hP a b hK
      _ ≤ C * (sieveScale H * Real.sqrt (b - a) + Real.sqrt (Real.log H)) :=
        mul_le_mul_of_nonneg_left (sieve_card_sqrt_le H a b hH ha hab) hC
      _ ≤ C' * (sieveScale H * Real.sqrt (b - a) + H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H)) :=
        mul_le_mul hCC (add_le_add le_rfl hsmallterm) (by positivity) (by linarith)
  · calc
      _ ≤ B * H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H) :=
        sieve_interval_norm4_small B hB H hH Q hP a b (le_of_not_ge hK)
      _ ≤ C' * (H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBC
          (mul_nonneg (Real.rpow_nonneg hH0.le _) (Real.sqrt_nonneg _))
      _ ≤ C' * (sieveScale H * Real.sqrt (b - a) + H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) (by linarith)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
