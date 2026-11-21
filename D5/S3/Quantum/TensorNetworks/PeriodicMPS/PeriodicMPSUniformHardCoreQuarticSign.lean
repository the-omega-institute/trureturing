/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreQuarticSign
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreQuarticSign
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Basic.Real.Sign]
   utility: none
   digest: Fibonacci bounds and Cassini's identity give the parity sign and nonvanishing of the quartic coefficient at every length at least seven. -/
import Mathlib.Basic.Real.Sign
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sign of the uniform hard-core quartic closed form

The definitions below give the Fibonacci specialization of formulas (23), (27), (28)
and (29) from the witness calculation. The coefficient identity for the transfer
calculation is a separate result.
-/

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreQuarticSign

noncomputable section

def F (n : ℕ) : ℝ := Nat.fib n
def G (n : ℕ) : ℝ := Nat.fib (n - 1)
def Z (n : ℕ) : ℝ := F n + 2 * G n

def delta (n : ℕ) : ℝ := F n ^ 2 - F n * G n - G n ^ 2
def A (n : ℕ) : ℝ := 4 * F n ^ 2 - 5 * F n * G n - 3 * G n ^ 2
def D (n : ℕ) : ℝ := 2 * (n : ℝ) * F n * delta n + Z n * (5 * G n ^ 2 - 2 * F n ^ 2)
def P (n : ℕ) : ℝ :=
  5 * G n ^ 2 * ((2 * (n : ℝ) + 20) * F n - (3 * (n : ℝ) + 34) * G n) +
    delta n * ((12 * (n : ℝ) - 32) * F n - (21 * (n : ℝ) - 10) * G n)

def quarticDenominator (n : ℕ) : ℝ := (F n - 2 * G n) * Z n * A n ^ 2 * D n

/-- The closed form in (27). -/
def quartic (n : ℕ) : ℝ :=
  (8 * F n * (3 * F n - 5 * G n) * delta n *
    (2 * F n ^ 2 - 4 * F n * G n + G n ^ 2) * P n) / quarticDenominator n

private theorem fib_six : Nat.fib 6 = 8 := by decide
private theorem fib_seven : Nat.fib 7 = 13 := by decide

private theorem F_succ {n : ℕ} (hn : 0 < n) : F (n + 1) = G n + F n := by
  unfold F G
  have h := Nat.fib_add_one (n := n) (Nat.ne_of_gt hn)
  exact_mod_cast h

private theorem G_succ (n : ℕ) : G (n + 1) = F n := by
  simp [G, F]

private theorem F_pos {n : ℕ} (hn : 7 ≤ n) : 0 < F n := by
  unfold F
  exact_mod_cast Nat.fib_pos.mpr (show 0 < n by omega)

theorem G_pos {n : ℕ} (hn : 7 ≤ n) : 0 < G n := by
  unfold G
  exact_mod_cast Nat.fib_pos.mpr (show 0 < n - 1 by omega)

/-- Cassini's identity in terms of the consecutive pair at length n. -/
theorem delta_eq {n : ℕ} (hn : 7 ≤ n) : delta n = (-1 : ℝ) ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [delta, F, G, fib_six, fib_seven]
  | succ n hn ih =>
    have hstep : delta (n + 1) = -delta n := by
      unfold delta
      rw [F_succ (by omega), G_succ]
      ring
    rw [hstep, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

private theorem delta_eq_one_or_neg_one {n : ℕ} (hn : 7 ≤ n) :
    delta n = 1 ∨ delta n = -1 := by
  rw [delta_eq hn]
  exact neg_one_pow_eq_or ℝ _

private theorem delta_le_one {n : ℕ} (hn : 7 ≤ n) : delta n ≤ 1 := by
  rcases delta_eq_one_or_neg_one hn with h | h <;> norm_num [h]

/-- The cross-multiplied bounds of (30). -/
theorem fib_bounds {n : ℕ} (hn : 7 ≤ n) :
    21 * G n ≤ 13 * F n ∧ 8 * F n ≤ 13 * G n ∧ 8 * (n : ℝ) ≤ G n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [F, G, fib_six, fib_seven]
  | succ n hn ih =>
    obtain ⟨hLower, hUpper, hGrowth⟩ := ih
    have hg := G_pos hn
    rw [F_succ (by omega), G_succ, Nat.cast_add, Nat.cast_one]
    refine ⟨by linarith, by linarith, ?_⟩
    have hThree : 3 * G n ≤ 2 * F n := by linarith
    have hSquare := mul_self_le_mul_self (show 0 ≤ 3 * G n by positivity) hThree
    have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hSquare, hGrowth, hn']

private theorem quadratic_upper {n : ℕ} (hn : 7 ≤ n) :
    2 * F n ^ 2 - 4 * F n * G n + G n ^ 2 ≤ -(7 / 32) * G n ^ 2 := by
  obtain ⟨hLower, hUpper, _⟩ := fib_bounds hn
  have hg := G_pos hn
  have hproduct := mul_nonneg (sub_nonneg.mpr hUpper)
    (show 0 ≤ 8 * F n - 3 * G n by linarith)
  nlinarith only [hproduct]

private theorem A_upper {n : ℕ} (hn : 7 ≤ n) : A n ≤ -(9 / 16) * G n ^ 2 := by
  have hUpper := (fib_bounds hn).2.1
  have hf := F_pos hn
  have hg := G_pos hn
  have hproduct := mul_nonneg (sub_nonneg.mpr hUpper)
    (show 0 ≤ 8 * F n + 3 * G n by positivity)
  unfold A
  nlinarith only [hproduct]

private theorem D_upper {n : ℕ} (hn : 7 ≤ n) :
    D n ≤ -(103 / 500) * (n : ℝ) * G n := by
  obtain ⟨hLower, hUpper, hGrowth⟩ := fib_bounds hn
  have hf := F_pos hn
  have hg := G_pos hn
  have hn' : (0 : ℝ) ≤ n := by positivity
  have hRatio : 8 * G n ≤ 5 * F n := by linarith
  have hSquare : (3 / 25) * G n ^ 2 ≤ 2 * F n ^ 2 - 5 * G n ^ 2 := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hRatio)
      (show 0 ≤ 5 * F n + 8 * G n by positivity)
    nlinarith only [hproduct]
  have hCubic : (54 / 125) * G n ^ 3 ≤ Z n * (2 * F n ^ 2 - 5 * G n ^ 2) := calc
    _ = ((18 / 5) * G n) * ((3 / 25) * G n ^ 2) := by ring
    _ ≤ _ := mul_le_mul (by unfold Z; linarith) hSquare (by positivity)
      (by unfold Z; positivity)
  have hDeltaTerm : 2 * (n : ℝ) * F n * delta n ≤ (13 / 4) * (n : ℝ) * G n := calc
    _ ≤ 2 * (n : ℝ) * F n * 1 := mul_le_mul_of_nonneg_left (delta_le_one hn) (by positivity)
    _ ≤ _ := by
      have hproduct := mul_nonneg (sub_nonneg.mpr hUpper) hn'
      nlinarith only [hproduct]
  have hGrowthTerm := mul_le_mul_of_nonneg_right hGrowth hg.le
  unfold D
  nlinarith only [hDeltaTerm, hCubic, hGrowthTerm]

theorem P_seven : P 7 = 220 := by
  norm_num [P, delta, F, G, fib_six, fib_seven]

theorem P_pos {n : ℕ} (hn : 7 ≤ n) : 0 < P n := by
  by_cases hSeven : n = 7
  · rw [hSeven, P_seven]
    norm_num
  have hn8 : 8 ≤ n := by omega
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hg := G_pos hn
  have hg13 : (13 : ℝ) ≤ G n := by
    unfold G
    have hfib := Nat.fib_mono (show 7 ≤ n - 1 by omega)
    rw [fib_seven] at hfib
    exact_mod_cast hfib
  obtain ⟨hLower, hUpper, _⟩ := fib_bounds hn
  let first : ℝ := (2 * (n : ℝ) + 20) * F n - (3 * (n : ℝ) + 34) * G n
  let second : ℝ := (12 * (n : ℝ) - 32) * F n - (21 * (n : ℝ) - 10) * G n
  have hFirst : (3 * (n : ℝ) - 22) * G n ≤ 13 * first := by
    dsimp [first]
    have hproduct := mul_nonneg (sub_nonneg.mpr hLower)
      (show 0 ≤ 2 * (n : ℝ) + 20 by positivity)
    nlinarith only [hproduct]
  have hSecondLower : (-21 * (n : ℝ) - 542) * G n ≤ 13 * second := by
    dsimp [second]
    have hproduct := mul_nonneg (sub_nonneg.mpr hLower)
      (show 0 ≤ 12 * (n : ℝ) - 32 by linarith)
    nlinarith only [hproduct]
  have hSecondNonpos : second ≤ 0 := by
    dsimp [second]
    have hproduct := mul_nonneg (sub_nonneg.mpr hUpper)
      (show 0 ≤ 12 * (n : ℝ) - 32 by linarith)
    have hsum := mul_nonneg (show 0 ≤ 12 * (n : ℝ) + 336 by positivity) hg.le
    nlinarith only [hproduct, hsum]
  -- The second bracket is nonpositive, so δ ≤ 1 gives a lower bound for its term.
  have hSecondTerm : second ≤ delta n * second := by
    simpa only [one_mul] using mul_le_mul_of_nonpos_right (delta_le_one hn) hSecondNonpos
  have hFirstTerm := mul_le_mul_of_nonneg_left hFirst (show 0 ≤ 5 * G n ^ 2 by positivity)
  have hSecondTermScaled := mul_le_mul_of_nonneg_left hSecondTerm (show (0 : ℝ) ≤ 13 by norm_num)
  have hSquare : (169 : ℝ) ≤ G n ^ 2 := by
    nlinarith only [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 13) hg13]
  have hWeighted := mul_le_mul_of_nonneg_right hSquare
    (mul_nonneg (show 0 ≤ 3 * (n : ℝ) - 22 by linarith) hg.le)
  have hFinal := mul_pos (show 0 < 2514 * (n : ℝ) - 19132 by linarith) hg
  change 0 < 5 * G n ^ 2 * first + delta n * second
  nlinarith only [hFirstTerm, hSecondLower, hSecondTermScaled, hWeighted, hFinal]

/-- Signs of the factors of the denominator in (27). -/
theorem denominator_factors {n : ℕ} (hn : 7 ≤ n) :
    F n - 2 * G n < 0 ∧ 0 < Z n ∧ A n < 0 ∧ D n < 0 := by
  have hf := F_pos hn
  have hg := G_pos hn
  have hUpper := (fib_bounds hn).2.1
  have hgSq := pow_pos hg 2
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hng := mul_pos hn' hg
  exact ⟨by linarith, by unfold Z; positivity, by linarith [A_upper hn],
    by nlinarith only [D_upper hn, hng]⟩

theorem quartic_denominator_pos {n : ℕ} (hn : 7 ≤ n) : 0 < quarticDenominator n := by
  obtain ⟨hDifference, hZ, hA, hD⟩ := denominator_factors hn
  have hASq := pow_pos (neg_pos.mpr hA) 2
  rw [neg_sq] at hASq
  unfold quarticDenominator
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hDifference hZ)
    hASq) hD

theorem quartic_denominator_ne_zero {n : ℕ} (hn : 7 ≤ n) : quarticDenominator n ≠ 0 :=
  ne_of_gt (quartic_denominator_pos hn)

private theorem quartic_eq_delta_mul (n : ℕ) :
    quartic n = delta n *
      ((8 * F n * (3 * F n - 5 * G n) *
        (2 * F n ^ 2 - 4 * F n * G n + G n ^ 2) * P n) / quarticDenominator n) := by
  rw [mul_div_assoc]
  unfold quartic
  ring

/-- For every length at least seven, (27) has strict alternating sign. -/
theorem quartic_sign {n : ℕ} (hn : 7 ≤ n) : Real.sign (quartic n) = (-1 : ℝ) ^ (n - 1) := by
  have hf := F_pos hn
  have hg := G_pos hn
  have hUpper := (fib_bounds hn).2.1
  have hLinear : 3 * F n - 5 * G n < 0 := by linarith
  have hQuadratic : 2 * F n ^ 2 - 4 * F n * G n + G n ^ 2 < 0 := by
    have hgSq := pow_pos hg 2
    linarith [quadratic_upper hn]
  have hMagnitude : 0 < (8 * F n * (3 * F n - 5 * G n) *
      (2 * F n ^ 2 - 4 * F n * G n + G n ^ 2) * P n) / quarticDenominator n := by
    apply div_pos _ (quartic_denominator_pos hn)
    exact mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by positivity) hLinear)
      hQuadratic) (P_pos hn)
  rw [← delta_eq hn, quartic_eq_delta_mul]
  rcases delta_eq_one_or_neg_one hn with h | h
  · rw [h, one_mul, Real.sign_of_pos hMagnitude]
  · rw [h, neg_one_mul, Real.sign_of_neg (neg_lt_zero.mpr hMagnitude)]

theorem quartic_ne_zero {n : ℕ} (hn : 7 ≤ n) : quartic n ≠ 0 := by
  intro h
  have hsign := quartic_sign hn
  rw [h, Real.sign_zero] at hsign
  exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hsign.symm

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreQuarticSign
