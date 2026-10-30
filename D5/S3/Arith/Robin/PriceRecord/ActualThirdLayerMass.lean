/- GID: D5/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualThirdLayerMass
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual full-record third-layer mass is uniformly negligible at root scale. -/

import D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import D5.S3.Arith.Robin.EulerLayerRootCorrection

/-! Finite third-layer mass and root-scale negligibility for the literal record integer. -/

namespace D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass

open Finset Filter Asymptotics
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity (layerPrime)
open D5.S3.Arith.Robin.EulerLayerRootCorrection (strict_inventory_third_layer_mass)
open scoped Topology

noncomputable section

/-- The complete actual mass above layer two has a finite bound at every
nonnegative-price full predecessor record, including an empty third layer. -/
theorem price_record_third_layer_mass_bound {m : ℕ} (hm : 2 ≤ m)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    0 ≤ strict_inventory_third_layer_mass m ∧
      strict_inventory_third_layer_mass m ≤
        (layerPrime m 3 : ℝ) * Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
  classical
  let S := m.primeFactors.filter (fun p => 3 ≤ m.factorization p)
  let B := Real.log (4 * (largestPrime m : ℝ) ^ 2)
  have hP : 2 ≤ largestPrime m := by
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
    exact (Nat.prime_of_mem_primeFactors hp).two_le.trans (Finset.le_sup (f := id) hp)
  have hPR : (2 : ℝ) ≤ (largestPrime m : ℝ) := by exact_mod_cast hP
  have hB : 0 ≤ B := Real.log_nonneg (by nlinarith)
  have hcard : S.card ≤ layerPrime m 3 := by
    have hsub : S ⊆ Finset.Icc 1 (layerPrime m 3) := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp hp).1).one_lt.le,
        (Finset.le_sup (f := id) hp).trans (le_max_right _ _)⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hterm (p : ℕ) (hp : p ∈ S) :
      ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p ≤ B := by
    have hpm := (Finset.mem_filter.mp hp).1
    have hprime := Nat.prime_of_mem_primeFactors hpm
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hpow : (p : ℝ) ^ m.factorization p < 4 * (largestPrime m : ℝ) ^ 2 := by
      exact_mod_cast PrimePowerEnvelope.price_record_prime_power_envelope hm hlambda hrecord
        p hprime (Nat.dvd_of_mem_primeFactors hpm)
    have hlogged := Real.log_lt_log (pow_pos (by exact_mod_cast hprime.pos) _) hpow
    have hsub : ((m.factorization p - 2 : ℕ) : ℝ) ≤ (m.factorization p : ℝ) :=
      by exact_mod_cast Nat.sub_le (m.factorization p) 2
    calc
      _ ≤ (m.factorization p : ℝ) * Real.log p := mul_le_mul_of_nonneg_right hsub hlog
      _ ≤ B := by simpa only [Real.log_pow] using hlogged.le
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt.le))
  · change (∑ p ∈ S, ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p) ≤ _
    calc
      _ ≤ (S.card : ℝ) * B := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul S
          (fun p => ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p) B hterm
      _ ≤ (layerPrime m 3 : ℝ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- The actual third-layer mass is uniformly negligible relative to the square
root of the largest prime, over every positive price and every full record. -/
theorem price_record_third_layer_mass_vanishing :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ T : ℝ, 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      strict_inventory_third_layer_mass m / Real.sqrt (largestPrime m : ℝ) < epsilon := by
  have hlog : Tendsto (fun P : ℝ => Real.log P / P ^ (1 / 6 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun P : ℝ => P ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hlimit : Tendsto (fun P : ℝ =>
      2 * P ^ (1 / 3 : ℝ) * Real.log (4 * P ^ 2) / Real.sqrt P) atTop (𝓝 0) := by
    have h := (hinv.const_mul (2 * Real.log 4)).add (hlog.const_mul 4)
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with P hP
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.sqrt_eq_rpow]
    have hpowers : P ^ (1 / 3 : ℝ) / P ^ (1 / 2 : ℝ) = P ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_sub hP]
      congr 1
      norm_num
    have hlogquot : Real.log P / P ^ (1 / 6 : ℝ) =
        Real.log P * P ^ (-(1 / 6 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hP.le]
    calc
      _ = 2 * Real.log 4 * (P ^ (1 / 3 : ℝ) / P ^ (1 / 2 : ℝ)) +
          4 * Real.log P * (P ^ (1 / 3 : ℝ) / P ^ (1 / 2 : ℝ)) := by
        rw [hpowers, hlogquot]
        ring
      _ = _ := by ring
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hlimit.eventually_lt_const hepsilon)
  obtain ⟨T3, hT3, hrigid⟩ := FixedLayerRigidity.price_record_fixed_layer_rigidity
    3 (by norm_num) 1 (by norm_num)
  refine ⟨max 1 (max T0 T3), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm lambda hlambda hrecord hT
  let P : ℝ := largestPrime m
  let R : ℝ := P ^ (1 / 3 : ℝ)
  have hP1 : 1 ≤ P := (le_max_left 1 (max T0 T3)).trans hT
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hP1
  have hR : 0 < R := Real.rpow_pos_of_pos hP _
  have hR3 : R ^ 3 = P := by
    simpa [R] using Real.rpow_inv_natCast_pow hP.le (by norm_num : (3 : ℕ) ≠ 0)
  have hT3P : T3 ≤ P := (le_max_right T0 T3).trans ((le_max_right 1 _).trans hT)
  have hcube : (layerPrime m 3 : ℝ) ^ 3 < 4 * P := by
    have h := (abs_lt.mp (hrigid m hm lambda hlambda hrecord hT3P)).2
    have hratio : (layerPrime m 3 : ℝ) ^ 3 / P < 4 := by norm_num at h ⊢; linarith
    exact (div_lt_iff₀ hP).mp hratio
  have hQ : (layerPrime m 3 : ℝ) ≤ 2 * R := by
    exact (lt_of_pow_lt_pow_left₀ 3 (by positivity : 0 ≤ 2 * R) (by
      nlinarith [hR3] : (layerPrime m 3 : ℝ) ^ 3 < (2 * R) ^ 3)).le
  have hmass := (price_record_third_layer_mass_bound hm hlambda.le hrecord).2
  have hB : 0 ≤ Real.log (4 * P ^ 2) := Real.log_nonneg (by nlinarith)
  have hupper : strict_inventory_third_layer_mass m ≤ 2 * R * Real.log (4 * P ^ 2) :=
    hmass.trans (mul_le_mul_of_nonneg_right hQ hB)
  exact (div_le_div_of_nonneg_right hupper (Real.sqrt_nonneg P)).trans_lt
    (hT0 P ((le_max_left T0 T3).trans ((le_max_right 1 _).trans hT)))

#print axioms price_record_third_layer_mass_bound
#print axioms price_record_third_layer_mass_vanishing

end

end D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
