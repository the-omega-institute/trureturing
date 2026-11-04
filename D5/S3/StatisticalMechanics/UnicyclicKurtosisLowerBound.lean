/- GID: D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp unicyclic current kurtosis lower bound is approached by one slow rate. -/

import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import D5.S3.Analytic.Interpolation.HermiteMomentBounds

/-! The fourth-to-second current cumulant ratio for positive unidirectional cycle rates.
The finite-cycle inequality is strict; the optimal constant is an asymptotic value. -/

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound

/-- The fourth scaled current cumulant divided by the second scaled current cumulant. -/
def kurtosis {n : ℕ} (k : Fin n → ℝ) : ℝ :=
  15 * powerSum n 2 (fun i => (k i)⁻¹) ^ 2 /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 4 -
    20 * powerSum n 3 (fun i => (k i)⁻¹) /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 3 +
    6 * powerSum n 4 (fun i => (k i)⁻¹) /
      (powerSum n 1 (fun i => (k i)⁻¹) ^ 2 * powerSum n 2 (fun i => (k i)⁻¹))

/-- The sharp lower bound, approached as the number of states tends to infinity. -/
def lowerBound : ℝ := -(1 + Real.sqrt 5) / 10

/-- Strict finite-cycle lower bound and greatest lower bound over all positive cycles. -/
def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    lowerBound < kurtosis k) ∧
  IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = kurtosis k} lowerBound

lemma normalized {n : ℕ} (k : Fin n → ℝ) :
    kurtosis k =
      15 * powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ^ 2 -
      20 * powerSum n 3 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) +
      6 * powerSum n 4 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) /
        powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) := by
  delta kurtosis powerSum
  simp only [div_pow, ← Finset.sum_div, pow_one]
  generalize (∑ i, (k i)⁻¹) = r
  generalize (∑ i, (k i)⁻¹ ^ 2) = a
  generalize (∑ i, (k i)⁻¹ ^ 3) = b
  generalize (∑ i, (k i)⁻¹ ^ 4) = c
  by_cases h : r = 0
  · simp [h]
  by_cases h2 : a = 0
  · simp [h2]; ring
  field_simp (disch := positivity)

lemma moments {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    0 < powerSum n 2 x ∧ 0 ≤ powerSum n 3 x ∧
      powerSum n 3 x ^ 2 ≤ powerSum n 2 x * powerSum n 4 x ∧
      powerSum n 4 x < powerSum n 2 x ^ 2 := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  have hp : 0 < ∑ l, x l ^ 2 :=
    Finset.sum_pos' (fun l _ => sq_nonneg (x l))
      ⟨i, Finset.mem_univ i, sq_pos_of_pos (hx i)⟩
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun l => x l ^ 2)
  have hpow (l : Fin n) : x l * x l ^ 2 = x l ^ 3 := (pow_succ' (x l) 2).symm
  have hpow2 (l : Fin n) : (x l ^ 2) ^ 2 = x l ^ 4 := (pow_mul (x l) 2 2).symm
  simp only [hpow, hpow2] at hcauchy
  have hstrict : (∑ l, x l ^ 4) < (∑ l, x l ^ 2) ^ 2 := by
    simpa only [← pow_mul] using
      D5.S3.Analytic.Interpolation.HermiteMomentBounds.sum_sq_lt_sq_sum hn
        (fun l => x l ^ 2) (fun l => sq_pos_of_pos (hx l))
  exact ⟨hp, Finset.sum_nonneg (fun l _ => le_of_lt (pow_pos (hx l) 3)),
    hcauchy, hstrict⟩

private lemma polynomial_lower_bound (u : ℝ) (hu : 0 ≤ u) :
    lowerBound ≤ 15 * u ^ 4 - 20 * u ^ 3 + 6 * u ^ 2 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hcoef : 0 ≤ 3 * Real.sqrt 5 - 5 := by
    apply sub_nonneg.mpr
    simpa only [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp
        (Real.le_sqrt_of_sq_le (by norm_num : (5 / 3 : ℝ) ^ 2 ≤ 5))
  have hconst : 0 ≤ (Real.sqrt 5 - 1) / 2 :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_sqrt.mpr (by norm_num))) (by norm_num)
  have hid : 15 * u ^ 4 - 20 * u ^ 3 + 6 * u ^ 2 - lowerBound =
      (u - (5 + Real.sqrt 5) / 10) ^ 2 *
        (15 * u ^ 2 + (3 * Real.sqrt 5 - 5) * u + (Real.sqrt 5 - 1) / 2) := by
    dsimp [lowerBound]
    ring_nf
    nlinarith [hs, congrArg (fun z : ℝ => z * Real.sqrt 5) hs]
  have hnonneg : 0 ≤ (u - (5 + Real.sqrt 5) / 10) ^ 2 *
      (15 * u ^ 2 + (3 * Real.sqrt 5 - 5) * u + (Real.sqrt 5 - 1) / 2) := by
    positivity
  linarith

private lemma moment_lower_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hbc : b ^ 2 ≤ a * c) (hc : c < a ^ 2) :
    lowerBound < 15 * a ^ 2 - 20 * b + 6 * c / a := by
  let t := b / a
  have hat : a * t = b := mul_div_cancel₀ b ha.ne'
  have hat2 : a ^ 2 * t ^ 2 = b ^ 2 := by rw [← mul_pow, hat]
  have ht : 0 ≤ t := div_nonneg hb ha.le
  have hts : t ^ 2 < a := by
    have h := mul_lt_mul_of_pos_left hc ha
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos ha)).mp
    nlinarith [hbc]
  have hcs : a * t ^ 2 ≤ c := by
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith [hbc]
  have he : 15 * a ^ 2 - 20 * a * t + 6 * t ^ 2 ≤
      15 * a ^ 2 - 20 * b + 6 * c / a := by
    have hdiv : t ^ 2 ≤ c / a := (le_div_iff₀ ha).mpr (by nlinarith [hcs])
    rw [mul_div_assoc]
    nlinarith
  by_cases ht23 : t ≤ 2 / 3
  · have hsq : t ^ 2 ≤ 4 / 9 := by
      convert pow_le_pow_left₀ ht ht23 2 using 1; norm_num
    have hbound : -(8 / 27 : ℝ) ≤ 15 * a ^ 2 - 20 * a * t + 6 * t ^ 2 := by
      nlinarith [sq_nonneg (3 * a - 2 * t)]
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (5 : ℝ)
    have hlt : lowerBound < -(8 / 27 : ℝ) := by dsimp [lowerBound]; nlinarith
    linarith
  · have hfactor : 0 < 15 * (a + t ^ 2) - 20 * t := by
      have h3t : 0 ≤ 3 * t - 2 := by linarith
      have : 0 ≤ t * (3 * t - 2) := mul_nonneg ht h3t
      nlinarith
    have hprod := mul_pos (sub_pos.mpr hts) hfactor
    have hf := polynomial_lower_bound t ht
    nlinarith

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < kurtosis k := by
  have hs : 0 < powerSum n 1 (fun i => (k i)⁻¹) := by
    let i : Fin n := ⟨0, by omega⟩
    exact Finset.sum_pos' (fun j _ => (pow_pos (inv_pos.mpr (hk j)) 1).le)
      ⟨i, Finset.mem_univ i, pow_pos (inv_pos.mpr (hk i)) 1⟩
  rw [normalized]
  obtain ⟨ha, hb, hbc, hc⟩ := moments hn
    (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹))
    (fun i => div_pos (inv_pos.mpr (hk i)) hs)
  exact moment_lower_bound _ _ _ ha hb hbc hc

private def sourceParameter : ℝ := (3 - Real.sqrt 5) / 2

private def sourceRates (m : ℕ) : Fin (m + 2) → ℝ :=
  fun i => if i = 0 then sourceParameter / (m + 2 : ℕ) else 1

private lemma source_rates_positive (m : ℕ) : ∀ i, 0 < sourceRates m i := by
  have ha : 0 < sourceParameter :=
    div_pos (sub_pos.mpr ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).mpr
      (by norm_num))) (by norm_num)
  intro i
  rw [sourceRates]
  split_ifs <;> positivity

private def approximation (a t : ℝ) : ℝ :=
  15 * (1 + a ^ 2 * (t - t ^ 2)) ^ 2 / (1 + a - a * t) ^ 4 -
    20 * (1 + a ^ 3 * (t ^ 2 - t ^ 3)) / (1 + a - a * t) ^ 3 +
    6 * (1 + a ^ 4 * (t ^ 3 - t ^ 4)) /
      ((1 + a - a * t) ^ 2 * (1 + a ^ 2 * (t - t ^ 2)))

private lemma source_kurtosis (m : ℕ) :
    kurtosis (sourceRates m) = approximation sourceParameter (1 / (m + 2 : ℕ)) := by
  have ha : 0 < sourceParameter := by
    have h := source_rates_positive 0 0
    simp only [sourceRates, ↓reduceIte] at h
    exact (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp h
  have hn : 0 < (m : ℝ) + 2 := by positivity
  have hs (j : ℕ) : powerSum (m + 2) j (fun i => (sourceRates m i)⁻¹) =
      (((m : ℝ) + 2) / sourceParameter) ^ j + ((m : ℝ) + 1) := by
    simp only [powerSum, sourceRates, Nat.cast_add, Nat.cast_ofNat, inv_pow, ite_pow,
      one_pow, Fin.sum_univ_succ, ↓reduceIte, Fin.succ_ne_zero, inv_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one, mul_one, add_left_inj]
    rw [← inv_pow, inv_div]
  delta kurtosis approximation
  simp only [hs, Nat.cast_add, Nat.cast_ofNat]
  have h1 : 0 < ((m : ℝ) + 2) / sourceParameter + ((m : ℝ) + 1) := by positivity
  have h2 : 0 < (((m : ℝ) + 2) / sourceParameter) ^ 2 + ((m : ℝ) + 1) := by
    positivity
  have ht : 0 < 1 / ((m : ℝ) + 2) := by positivity
  have ht1 : 1 / ((m : ℝ) + 2) ≤ 1 := by
    simpa only [one_div] using
      inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ m + 2 by omega))
  have hd : 0 < 1 + sourceParameter - sourceParameter * (1 / ((m : ℝ) + 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left ht1 ha.le]
  have hv : 0 < 1 + sourceParameter ^ 2 *
      (1 / ((m : ℝ) + 2) - (1 / ((m : ℝ) + 2)) ^ 2) := by
    have : 0 ≤ 1 / ((m : ℝ) + 2) - (1 / ((m : ℝ) + 2)) ^ 2 := by
      apply sub_nonneg.mpr
      simpa only [pow_two] using mul_le_of_le_one_right ht.le ht1
    positivity
  have hd1 : 0 < ((m : ℝ) + 2) * (1 + sourceParameter) - sourceParameter := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) ha.le]
  have hm1 : 0 < (m : ℝ) + 2 - 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hv1 : 0 < ((m : ℝ) + 2) ^ 2 + sourceParameter ^ 2 * ((m : ℝ) + 2 - 1) := by
    positivity
  field_simp (disch := positivity)
  field_simp (disch := positivity)
  ring

private lemma source_limit :
    Tendsto (fun m : ℕ => kurtosis (sourceRates m)) atTop (nhds lowerBound) := by
  have ha : 0 < sourceParameter := by
    have h := source_rates_positive 0 0
    simp only [sourceRates, ↓reduceIte] at h
    exact (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp h
  have hc : ContinuousAt (approximation sourceParameter) 0 := by
    unfold approximation
    fun_prop (disch := (norm_num; positivity))
  have hz : Tendsto (fun m : ℕ => 1 / ((m + 2 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
  have he : approximation sourceParameter 0 = lowerBound := by
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hs3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
      rw [pow_succ, hs]
    have hs4 : Real.sqrt 5 ^ 4 = 25 := by
      calc
        _ = (Real.sqrt 5 ^ 2) ^ 2 := pow_mul _ 2 2
        _ = _ := by rw [hs]; norm_num
    have hs5 : Real.sqrt 5 ^ 5 = 25 * Real.sqrt 5 := by
      rw [pow_succ, hs4]
    rw [approximation]
    norm_num
    field_simp (disch := positivity)
    dsimp [sourceParameter, lowerBound]
    ring_nf
    nlinarith only [hs, hs3, hs4, hs5]
  simpa only [Function.comp_def, ← source_kurtosis, he] using hc.tendsto.comp hz

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = kurtosis k} lowerBound := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨n, hn, k, hk, rfl⟩
    exact (strict_lower_bound n hn k hk).le
  · intro b hb
    apply ge_of_tendsto' source_limit
    intro m
    exact hb ⟨m + 2, by omega, sourceRates m, source_rates_positive m, rfl⟩

/-- Ptaszyński's sharp lower bound, with strictness for every finite positive cycle. -/
theorem result : claim := ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
