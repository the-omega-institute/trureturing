/- GID: D5/S3/Arith/PrimitiveRoot/SieveThresholdUnconditional
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SieveThresholdUnconditional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_large_prime; premises=D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower,D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five,D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six
   digest: Sieve parameters for a linear principal term without a zeta hypothesis. -/
import D5.S3.Arith.PrimitiveRoot.SieveThresholdExact

/-! A principal term of size 23p/50 suffices above five million. -/

namespace D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
open scoped BigOperators
open CharacterSieve CharacterExpansion SieveThreshold

private lemma log_margin_mono {x y B : ℝ} (hx : Real.exp 2 ≤ x) (hxy : x ≤ y)
    (hB : 0 ≤ B) (h : B * Real.log x < Real.sqrt x) :
    B * Real.log y < Real.sqrt y := by
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hb := (div_lt_one (Real.sqrt_pos.mpr hx0)).mpr h
  have hm := mul_le_mul_of_nonneg_left
    (Real.log_div_sqrt_antitoneOn hx (hx.trans hxy) hxy) hB
  apply (div_lt_one (Real.sqrt_pos.mpr hy0)).mp
  rw [mul_div_assoc] at hb ⊢
  exact hm.trans_lt hb

private lemma small_margin {x A : ℝ} (hx : 5000000 ≤ x) (hA : A ≤ 4417 / 100) :
    (330916 / 102465 : ℝ) * A * Real.log x < Real.sqrt x := by
  have hlog : Real.log (5000000 : ℝ) < 31 / 2 := by
    have hb := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 5000000 / 2 ^ 22 by norm_num)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow] at hb
    norm_num only [Nat.cast_ofNat] at hb
    linarith [Real.log_two_lt_d9]
  have hs : (2236 : ℝ) < Real.sqrt 5000000 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hm : (330916 / 102465 : ℝ) * (4417 / 100) * Real.log x <
      Real.sqrt x := by
    apply log_margin_mono (exp_two_le (by norm_num)) hx (by norm_num)
    linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by norm_num)) hl).trans_lt hm

private lemma eight_margin :
    (330916 / 102465 : ℝ) * (7 + 20 / (610847 / 1616615)) *
      Real.log 9699690 < Real.sqrt 9699690 := by
  have hlog : Real.log (9699690 : ℝ) < 160903 / 10000 := by
    have hle : Real.log (9699690 : ℝ) ≤
        Real.log (2 ^ 23 * (259243 / 250000 : ℝ) ^ 4) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow] at hle
    norm_num only [Nat.cast_ofNat] at hle
    have hr := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 259243 / 250000 by norm_num)
    linarith [Real.log_two_lt_d9]
  have hs : (15572 / 5 : ℝ) < Real.sqrt 9699690 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

private lemma scale_margin {x A : ℝ} (hx : 16 ≤ x) (hA : 0 ≤ A)
    (h : (330916 / 102465 : ℝ) * A * Real.log x < Real.sqrt x) :
    (330916 / 102465 : ℝ) * (2 * A) * Real.log (16 * x) <
      Real.sqrt (16 * x) := by
  have hx0 : 0 < x := by linarith
  have hl : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hm := mul_nonneg hA (sub_nonneg.mpr hl)
  rw [Real.log_mul (by norm_num) hx0.ne', Real.sqrt_mul (by norm_num)]
  norm_num only [show Real.sqrt 16 = 4 from by norm_num]
  nlinarith

private lemma many_margin (m : ℕ) :
    (330916 / 102465 : ℝ) * ((184 / 3) * 2 ^ (m + 1)) *
      Real.log (9699690 * 16 ^ (m + 1)) <
        Real.sqrt (9699690 * 16 ^ (m + 1)) := by
  induction m with
  | zero =>
    norm_num only [zero_add, pow_one]
    have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 9699690 * 16)
      (show (9699690 : ℝ) * 16 < 2 ^ 28 by norm_num)
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hs : (12000 : ℝ) < Real.sqrt (155195040 : ℝ) :=
      (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    nlinarith [Real.log_two_lt_d9]
  | succ m ih =>
    have hx : (16 : ℝ) ≤ 9699690 * 16 ^ (m + 1) := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := m + 1)
      nlinarith
    have hX : (9699690 : ℝ) * 16 ^ (m + 1 + 1) =
        16 * (9699690 * 16 ^ (m + 1)) := by ring
    have hA : (184 / 3 : ℝ) * 2 ^ (m + 1 + 1) =
        2 * ((184 / 3) * 2 ^ (m + 1)) := by ring
    rw [hX, hA]
    exact scale_margin hx (by positivity) ih

private lemma signed_linear_margin {x d K A : ℝ} (hx : 0 < x) (hd : 0 < d)
    (hK : K ≤ d * A)
    (h : (330916 / 102465 : ℝ) * A * Real.log x < Real.sqrt x)
    (hl : 0 ≤ Real.log x) :
    K * ((165458 / 111375 : ℝ) * Real.sqrt x * Real.log x) <
      d * ((23 / 50 : ℝ) * x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hstep : (165458 / 111375 : ℝ) * A * Real.log x <
      (23 / 50 : ℝ) * Real.sqrt x := by linarith
  calc
    _ ≤ (d * A) * ((165458 / 111375 : ℝ) * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (d * Real.sqrt x) * ((165458 / 111375 : ℝ) * A * Real.log x) := by ring
    _ < (d * Real.sqrt x) * ((23 / 50 : ℝ) * Real.sqrt x) :=
      mul_lt_mul_of_pos_left hstep (mul_pos hd hs)
    _ = _ := by nlinarith [Real.sq_sqrt hx.le]

/-- The support construction is feasible with the sharp character coefficient and 23p/50. -/
theorem covering_linear (x : ℕ) (hx : 5000000 ≤ x) :
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ x - 1 → q ∣ e ∨ q ∈ T) ∧
      0 < delta (sievePrimes x e T) ∧
      errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) *
        ((165458 / 111375 : ℝ) * Real.sqrt x * Real.log x) <
      delta (sievePrimes x e T) * ((23 / 50 : ℝ) * x) := by
  have hxR : (5000000 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hl : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by linarith)
  apply covering_parameters x (by omega)
  · intro d K hd hK
    exact signed_linear_margin hx0 hd hK (small_margin hxR le_rfl) hl
  · intro m hX d K hd hK
    have hd' : (3 / 8 : ℝ) < d := by linarith
    cases m with
    | zero =>
      norm_num only [pow_zero, mul_one] at hX
      have hA : K ≤ d * (7 + 20 / (610847 / 1616615)) := by
        norm_num only [zero_add, pow_succ, pow_zero] at hK
        nlinarith
      apply signed_linear_margin hx0 (by linarith) hA _ hl
      exact log_margin_mono (exp_two_le (by norm_num)) hX (by norm_num) eight_margin
    | succ m =>
      have hA : K ≤ d * ((184 / 3) * 2 ^ (m + 1)) := by
        rw [hK, pow_add]
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        have hm := mul_nonneg (sub_nonneg.mpr hd'.le)
          (show (0 : ℝ) ≤ 2 ^ (m + 1) by positivity)
        nlinarith
      apply signed_linear_margin hx0 (by linarith) hA _ hl
      apply log_margin_mono _ hX (by positivity) (many_margin m)
      apply (exp_two_le (x := 5000000) (by norm_num)).trans
      have := one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := m + 1)
      nlinarith

/-- A linear unconditional principal input replaces the former RH-dependent lower bound. -/
theorem exists_prime_primitiveRoot (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤
        (165458 / 111375 : ℝ) * Real.sqrt p * Real.log p)
    (hmain : (23 / 50 : ℝ) * p ≤ (smoothedCharacterSum p 1).re) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  apply SieveThresholdExact.exists_prime_primitiveRoot_of_covering p _ hM
  obtain ⟨e, T, he, hc, hδ, hm⟩ := covering_linear p hp
  exact ⟨e, T, he, hc, hm.trans_le (mul_le_mul_of_nonneg_left hmain hδ.le)⟩

#print axioms exists_prime_primitiveRoot
end D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
