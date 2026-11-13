/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-norm perturbations control finite sieve products and Wick pairings. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveFiniteProbability
import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FiniteProductMomentBounds

/-! Fourth-norm perturbations control products and Wick pairings of sieve variables. -/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

open D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FiniteProductMomentBounds

private theorem normalized_products (Q : ℕ+) (k : ℕ) (hk : 0 < k) (hk4 : k ≤ 4)
    (F : Fin k → ZMod (Q : ℕ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ i, sieveNorm4 Q (F i) ≤ K) :
    |sieveProductMoment Q F| ≤ K ^ k := by
  have : IsProbabilityMeasure (sieveUniformMeasure Q) := sieve_probability Q
  have hfourth (i : Fin k) :
      (∫ x, |F i x| ^ 4 ∂sieveUniformMeasure Q) ≤ K ^ 4 := by
    rw [sieve_expectation_integral, ← sieve_norm4_fourth Q (F i)]
    exact pow_le_pow_left₀ (sieve_norm4_nonneg Q (F i)) (hF i) 4
  have hprod := product_fourth_bound (μ := sieveUniformMeasure Q) hk hk4
      (f := F) (C := fun _ : Fin k => K ^ 4)
      (fun i => sieve_memLp_four Q (F i))
      (fun _ => by positivity) hfourth
  change |sieveExpectation Q (fun x => ∏ i, F i x)| ≤ K ^ k
  rw [← sieve_expectation_integral]
  calc
    |∫ (x : ZMod (Q : ℕ)), ∏ i, F i x ∂sieveUniformMeasure Q| ≤
        ∫ (x : ZMod (Q : ℕ)), |∏ i, F i x| ∂sieveUniformMeasure Q :=
      abs_integral_le_integral_abs
    _ ≤ ∏ i : Fin k, (K ^ 4) ^ (1 / 4 : ℝ) := hprod
    _ = K ^ k := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hroot : (K ^ 4) ^ (1 / 4 : ℝ) = K := by
        simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast hK (by norm_num : (4 : ℕ) ≠ 0)
      exact congrArg (fun z : ℝ => z ^ k) hroot

theorem sieve_product_moment_replacement (Q : ℕ+) (k : ℕ) (hk : 0 < k) (hk4 : k ≤ 4)
    (F G : Fin k → ZMod (Q : ℕ) → ℝ) (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hF : ∀ i, sieveNorm4 Q (F i) ≤ K) (hG : ∀ i, sieveNorm4 Q (G i) ≤ K)
    (hDfg : ∀ i, sieveNorm4 Q (fun x => F i x - G i x) ≤ D) :
    |sieveProductMoment Q F - sieveProductMoment Q G| ≤ (k : ℝ) * D * K ^ (k - 1) := by
  have : IsProbabilityMeasure (sieveUniformMeasure Q) := sieve_probability Q
  have hfourthF (i : Fin k) :
      (∫ x, |F i x| ^ 4 ∂sieveUniformMeasure Q) ≤ K ^ 4 := by
    rw [sieve_expectation_integral, ← sieve_norm4_fourth Q (F i)]
    exact pow_le_pow_left₀ (sieve_norm4_nonneg Q (F i)) (hF i) 4
  have hfourthG (i : Fin k) :
      (∫ x, |G i x| ^ 4 ∂sieveUniformMeasure Q) ≤ K ^ 4 := by
    rw [sieve_expectation_integral, ← sieve_norm4_fourth Q (G i)]
    exact pow_le_pow_left₀ (sieve_norm4_nonneg Q (G i)) (hG i) 4
  have hfourthD (i : Fin k) :
      (∫ x, |F i x - G i x| ^ 4 ∂sieveUniformMeasure Q) ≤ D ^ 4 := by
    rw [sieve_expectation_integral, ← sieve_norm4_fourth Q (fun x => F i x - G i x)]
    exact pow_le_pow_left₀ (sieve_norm4_nonneg Q (fun x => F i x - G i x)) (hDfg i) 4
  have hprod := product_fourth_difference_bound (μ := sieveUniformMeasure Q) hk hk4
      (f := F) (g := G) (K := K ^ 4) (D := D ^ 4) (by positivity) (by positivity)
      (fun i => ⟨sieve_memLp_four Q (F i), sieve_memLp_four Q (G i)⟩)
      hfourthF hfourthG hfourthD
  have hIF : Integrable (fun x => ∏ i, F i x) (sieveUniformMeasure Q) := by
    apply product_integrable hk
    intro i
    exact (sieve_memLp_four Q (F i)).mono_exponent (by exact_mod_cast hk4)
  have hIG : Integrable (fun x => ∏ i, G i x) (sieveUniformMeasure Q) := by
    apply product_integrable hk
    intro i
    exact (sieve_memLp_four Q (G i)).mono_exponent (by exact_mod_cast hk4)
  change |sieveExpectation Q (fun x => ∏ i, F i x) - sieveExpectation Q (fun x => ∏ i, G i x)| ≤
    (k : ℝ) * D * K ^ (k - 1)
  rw [← sieve_expectation_integral, ← sieve_expectation_integral,
    ← integral_sub hIF hIG]
  calc
    |∫ (x : ZMod (Q : ℕ)), (∏ i, F i x) - ∏ i, G i x ∂sieveUniformMeasure Q| ≤
        ∫ (x : ZMod (Q : ℕ)), |(∏ i, F i x) - ∏ i, G i x| ∂sieveUniformMeasure Q :=
      abs_integral_le_integral_abs
    _ ≤ (k : ℝ) * (D ^ 4) ^ (1 / 4 : ℝ) *
        (K ^ 4) ^ (((k : ℝ) - 1) / 4) := hprod
    _ = (k : ℝ) * D * K ^ (k - 1) := by
      have hDroot : (D ^ 4) ^ (1 / 4 : ℝ) = D := by
        simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast hD (by norm_num : (4 : ℕ) ≠ 0)
      have hKpow : (K ^ 4) ^ (((k : ℝ) - 1) / 4) = K ^ (k - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
        rw [← Real.rpow_natCast]
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne')]
        congr 1
        ring
      rw [hDroot, hKpow]

theorem sieve_wick_pairing_replacement (Q : ℕ+)
    (F G : Fin 4 → ZMod (Q : ℕ) → ℝ) (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hF : ∀ i, sieveNorm4 Q (F i) ≤ K) (hG : ∀ i, sieveNorm4 Q (G i) ≤ K)
    (hDfg : ∀ i, sieveNorm4 Q (fun x => F i x - G i x) ≤ D) :
    |sieveWickPairing Q F - sieveWickPairing Q G| ≤ 12 * D * K ^ 3 := by
  have pair_size (family : Fin 2 → ZMod (Q : ℕ) → ℝ)
      (hA : ∀ i, sieveNorm4 Q (family i) ≤ K) : |sieveProductMoment Q family| ≤ K ^ 2 := by
    exact normalized_products Q 2 (by norm_num) (by norm_num) family K hK hA
  have pair_diff (family B : Fin 2 → ZMod (Q : ℕ) → ℝ)
      (hA : ∀ i, sieveNorm4 Q (family i) ≤ K) (hB : ∀ i, sieveNorm4 Q (B i) ≤ K)
      (hAB : ∀ i, sieveNorm4 Q (fun x => family i x - B i x) ≤ D) :
      |sieveProductMoment Q family - sieveProductMoment Q B| ≤ 2 * D * K := by
    simpa using sieve_product_moment_replacement Q 2 (by norm_num) (by norm_num)
      family B K D hK hD hA hB hAB
  have hmul (u u' v v' : ℝ)
      (hu : |u - u'| ≤ 2 * D * K) (hv : |v - v'| ≤ 2 * D * K)
      (hv' : |v| ≤ K ^ 2) (hu' : |u'| ≤ K ^ 2) :
      |u * v - u' * v'| ≤ 4 * D * K ^ 3 := by
    calc
      |u * v - u' * v'| = |(u - u') * v + u' * (v - v')| := by
        congr 1
        ring
      _ ≤ |(u - u') * v| + |u' * (v - v')| := abs_add_le _ _
      _ = |u - u'| * |v| + |u'| * |v - v'| := by rw [abs_mul, abs_mul]
      _ ≤ (2 * D * K) * (K ^ 2) + (K ^ 2) * (2 * D * K) := by
        gcongr
      _ = 4 * D * K ^ 3 := by ring
  have h12 : |sieveProductMoment Q ![F 0, F 1] * sieveProductMoment Q ![F 2, F 3] -
      sieveProductMoment Q ![G 0, G 1] * sieveProductMoment Q ![G 2, G 3]| ≤ 4 * D * K ^ 3 := by
    exact hmul _ _ _ _
      (pair_diff ![F 0, F 1] ![G 0, G 1]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_diff ![F 2, F 3] ![G 2, G 3]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_size ![F 2, F 3] (by intro i; fin_cases i <;> simp [hF]))
      (pair_size ![G 0, G 1] (by intro i; fin_cases i <;> simp [hG]))
  have h13 : |sieveProductMoment Q ![F 0, F 2] * sieveProductMoment Q ![F 1, F 3] -
      sieveProductMoment Q ![G 0, G 2] * sieveProductMoment Q ![G 1, G 3]| ≤ 4 * D * K ^ 3 := by
    exact hmul _ _ _ _
      (pair_diff ![F 0, F 2] ![G 0, G 2]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_diff ![F 1, F 3] ![G 1, G 3]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_size ![F 1, F 3] (by intro i; fin_cases i <;> simp [hF]))
      (pair_size ![G 0, G 2] (by intro i; fin_cases i <;> simp [hG]))
  have h14 : |sieveProductMoment Q ![F 0, F 3] * sieveProductMoment Q ![F 1, F 2] -
      sieveProductMoment Q ![G 0, G 3] * sieveProductMoment Q ![G 1, G 2]| ≤ 4 * D * K ^ 3 := by
    exact hmul _ _ _ _
      (pair_diff ![F 0, F 3] ![G 0, G 3]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_diff ![F 1, F 2] ![G 1, G 2]
        (by intro i; fin_cases i <;> simp [hF])
        (by intro i; fin_cases i <;> simp [hG])
        (by intro i; fin_cases i <;> simp [hDfg]))
      (pair_size ![F 1, F 2] (by intro i; fin_cases i <;> simp [hF]))
      (pair_size ![G 0, G 3] (by intro i; fin_cases i <;> simp [hG]))
  rw [sieveWickPairing, sieveWickPairing]
  calc
    _ = |(sieveProductMoment Q ![F 0, F 1] * sieveProductMoment Q ![F 2, F 3] -
        sieveProductMoment Q ![G 0, G 1] * sieveProductMoment Q ![G 2, G 3]) +
      ((sieveProductMoment Q ![F 0, F 2] * sieveProductMoment Q ![F 1, F 3] -
        sieveProductMoment Q ![G 0, G 2] * sieveProductMoment Q ![G 1, G 3]) +
      (sieveProductMoment Q ![F 0, F 3] * sieveProductMoment Q ![F 1, F 2] -
        sieveProductMoment Q ![G 0, G 3] * sieveProductMoment Q ![G 1, G 2]))| := by
      congr 1
      ring
    _ ≤ |sieveProductMoment Q ![F 0, F 1] * sieveProductMoment Q ![F 2, F 3] -
          sieveProductMoment Q ![G 0, G 1] * sieveProductMoment Q ![G 2, G 3]| +
        |(sieveProductMoment Q ![F 0, F 2] * sieveProductMoment Q ![F 1, F 3] -
          sieveProductMoment Q ![G 0, G 2] * sieveProductMoment Q ![G 1, G 3]) +
        (sieveProductMoment Q ![F 0, F 3] * sieveProductMoment Q ![F 1, F 2] -
          sieveProductMoment Q ![G 0, G 3] * sieveProductMoment Q ![G 1, G 2])| := abs_add_le _ _
    _ ≤ |sieveProductMoment Q ![F 0, F 1] * sieveProductMoment Q ![F 2, F 3] -
          sieveProductMoment Q ![G 0, G 1] * sieveProductMoment Q ![G 2, G 3]| +
        |sieveProductMoment Q ![F 0, F 2] * sieveProductMoment Q ![F 1, F 3] -
          sieveProductMoment Q ![G 0, G 2] * sieveProductMoment Q ![G 1, G 3]| +
        |sieveProductMoment Q ![F 0, F 3] * sieveProductMoment Q ![F 1, F 2] -
          sieveProductMoment Q ![G 0, G 3] * sieveProductMoment Q ![G 1, G 2]| := by
      simpa only [add_assoc] using
        (add_le_add_right (abs_add_le
          (sieveProductMoment Q ![F 0, F 2] * sieveProductMoment Q ![F 1, F 3] -
            sieveProductMoment Q ![G 0, G 2] * sieveProductMoment Q ![G 1, G 3])
          (sieveProductMoment Q ![F 0, F 3] * sieveProductMoment Q ![F 1, F 2] -
            sieveProductMoment Q ![G 0, G 3] * sieveProductMoment Q ![G 1, G 2]))
          |sieveProductMoment Q ![F 0, F 1] * sieveProductMoment Q ![F 2, F 3] -
            sieveProductMoment Q ![G 0, G 1] * sieveProductMoment Q ![G 2, G 3]|)
    _ ≤ 12 * D * K ^ 3 := by nlinarith [h12, h13, h14]


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
