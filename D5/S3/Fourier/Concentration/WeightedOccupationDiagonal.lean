/- GID: D5/S3/Fourier/Concentration/WeightedOccupationDiagonal
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/WeightedOccupationDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive coefficient extraction bounds the weighted multinomial occupation diagonal. -/

import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

/-! A product bound for equal occupation counts in the high-order Fourier moment. -/

set_option autoImplicit false

open Finset Real
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

namespace D5.S3.Fourier.Concentration.WeightedOccupationDiagonal

/-- An exponential majorant for the series with squared reciprocal factorial coefficients. -/
noncomputable def diagonalEnvelope (x : ℝ) : ℝ := 2 * exp (x / 2) - 1

private theorem factorial_succ_lower (n : ℕ) : 2 ^ n ≤ n.succ.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ]
    calc
      2 ^ n * 2 ≤ n.succ.factorial * 2 := Nat.mul_le_mul_right _ ih
      _ = 2 * n.succ.factorial := Nat.mul_comm _ _
      _ ≤ n.succ.succ * n.succ.factorial := Nat.mul_le_mul_right _ (by omega)

private theorem local_bound (x : ℝ) (hx : 0 ≤ x) (p : ℕ) :
    (∑ n ∈ range (p + 1), x ^ n / (n.factorial : ℝ) ^ 2) ≤
      2 * exp (x / 2) - 1 := by
  have hterm (n : ℕ) :
      x ^ (n + 1) / ((n + 1).factorial : ℝ) ^ 2 ≤
        2 * ((x / 2) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
    have hfac : 0 < ((n + 1).factorial : ℝ) := by positivity
    have htwo : (2 : ℝ) ^ n ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast factorial_succ_lower n
    have hxpow : 0 ≤ x ^ (n + 1) := pow_nonneg hx _
    calc
      x ^ (n + 1) / ((n + 1).factorial : ℝ) ^ 2 =
          x ^ (n + 1) / ((n + 1).factorial : ℝ) / ((n + 1).factorial : ℝ) := by
        rw [pow_two, div_div]
      _ ≤ x ^ (n + 1) / ((n + 1).factorial : ℝ) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (div_nonneg hxpow hfac.le) (by positivity) htwo
      _ = 2 * ((x / 2) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
        rw [div_pow, pow_succ (2 : ℝ) n]
        have : (2 : ℝ) ^ n ≠ 0 := by positivity
        field_simp
  have hexp := Real.sum_le_exp_of_nonneg (show 0 ≤ x / 2 by positivity) (p + 1)
  rw [Finset.sum_range_succ'] at hexp ⊢
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one] at hexp ⊢
  have h := Finset.sum_le_sum (s := range p) fun n _ => hterm n
  rw [← mul_sum] at h
  linarith

private noncomputable def coefficient (w s : ℝ) (n : ℕ) : ℝ :=
  (s * w ^ 2) ^ n / (n.factorial : ℝ) ^ 2

private theorem weighted_monomial {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (s : ℝ) (p : ℕ) {m : J → ℕ} (hm : m ∈ piAntidiag univ p) :
    s ^ p * monomialWeight w m ^ 2 =
      (p.factorial : ℝ) ^ 2 * ∏ j, coefficient (w j) s (m j) := by
  have hsum := (mem_piAntidiag.mp hm).1
  have hspec : (∏ j, ((m j).factorial : ℝ)) * (Nat.multinomial univ m : ℝ) =
      (p.factorial : ℝ) := by
    have h := Nat.multinomial_spec univ m
    rw [hsum] at h
    exact_mod_cast h
  have hfac : (∏ j, ((m j).factorial : ℝ)) ≠ 0 := by positivity
  have hmult : (Nat.multinomial univ m : ℝ) =
      (p.factorial : ℝ) / ∏ j, ((m j).factorial : ℝ) :=
    (eq_div_iff hfac).2 (by rw [mul_comm, hspec])
  have hs : (∏ j, s ^ m j) = s ^ p := by
    rw [prod_pow_eq_pow_sum, hsum]
  unfold monomialWeight coefficient
  simp_rw [mul_pow, ← pow_mul, Nat.mul_comm 2]
  rw [prod_div_distrib, prod_mul_distrib, hs, hmult]
  simp_rw [pow_mul]
  rw [Finset.prod_pow, Finset.prod_pow]
  ring

/-- Bound one homogeneous degree in the product of nonnegative coordinate series. -/
theorem scaled_diagonal_le_product {J : Type*} [Fintype J] [DecidableEq J] (w : J → ℝ) (p : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    let envelope := diagonalEnvelope
    s ^ p * diagonal w p ≤
      (p.factorial : ℝ) ^ 2 * ∏ j, envelope (s * w j ^ 2) := by
  dsimp only
  classical
  unfold diagonal
  rw [mul_sum]
  have hnormalize :
      (∑ m ∈ piAntidiag univ p, s ^ p * monomialWeight w m ^ 2) =
        ∑ m ∈ piAntidiag univ p, (p.factorial : ℝ) ^ 2 *
          ∏ j, coefficient (w j) s (m j) :=
    sum_congr rfl fun _ hm => weighted_monomial w s p hm
  rw [hnormalize]
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ m ∈ Fintype.piFinset (fun _ : J => range (p + 1)),
        ∏ j, coefficient (w j) s (m j) := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => ?_)
      · intro m hm
        apply Fintype.mem_piFinset.mpr
        intro j
        rw [mem_range, Nat.lt_succ_iff, ← (mem_piAntidiag.mp hm).1]
        exact single_le_sum (fun i _ => Nat.zero_le (m i)) (mem_univ j)
      · exact prod_nonneg fun j _ => by unfold coefficient; positivity
    _ = ∏ j, ∑ n ∈ range (p + 1), coefficient (w j) s n :=
      (prod_univ_sum _ _).symm
    _ ≤ _ := by
      apply prod_le_prod₀
      · intro j _
        unfold coefficient
        positivity
      · intro j _
        exact local_bound _ (mul_nonneg hs (sq_nonneg _)) p

end D5.S3.Fourier.Concentration.WeightedOccupationDiagonal
