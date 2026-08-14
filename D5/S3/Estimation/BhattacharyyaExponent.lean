/- GID: D5/S3/Estimation/BhattacharyyaExponent
   generality: G
   mirror-B: D5/B/S3/Estimation/BhattacharyyaExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bhattacharyya n-fold testing floors and their sample-complexity inversion. -/

/- Library-search audit trail (2026-08-12):
   * Mathlib searches covered Bhattacharyya, Hellinger, Chernoff, testing-error bounds,
     square-root monotonicity, logarithm monotonicity, and powers. No probability-theory
     Bhattacharyya/Chernoff exponent or square-root complementary-affinity inequality was found.
     The elementary step uses the existing `Real.sqrt_one_add_le`; `Real.log_le_log_iff`,
     `Real.log_pow`, and `Real.log_inv` support the inversion.
   * A repository search below `D5` found the frozen two-factor
     `bhattacharyya_product_multiplicative`, but no n-fold Bhattacharyya theorem, error exponent,
     or Bhattacharyya sample-complexity statement. The imported `IidSpace`/`iidPower` encoding is
     consumed directly.
-/

import D5.S3.TotalVariation.BhattacharyyaProduct
import D5.S3.Estimation.LeCam
import D5.S3.DivergenceSupport.PowerAdditivity
import D5.S3.RenyiDivergence.PowerAdditivity

/-!
# The Bhattacharyya error exponent

For an arbitrary two-point test, Le Cam's floor and the frozen total-variation/Bhattacharyya
comparison give the sharp floor `1 - sqrt (1 - rho^2)`, and the elementary corollary `rho^2 / 2`.
The n-fold multiplicativity induction is the genuine proof work in this file: its successor is
exactly the frozen binary product theorem, while the zero-copy case is the one-point `PUnit`
calculation. The testing floor and exponent are then short compositions; the logarithmic inversion
is the only place where a sign condition matters, because `log rho < 0` reverses division.

Thus no arbitrary test beats the floor
`(bhattacharyya p q) ^ (2*n) / 2`: the error can decay at most exponentially in the number of
observations, at rate `2 * log (1 / rho)`. If a test has error at most `eps`, the primary product
form is the side-condition-free `rho ^ (2*n) ≤ 2*eps`; the solved form requires `0 < rho < 1`,
`0 < eps`, and `2*eps ≤ 1`, and is
`n ≥ log (2*eps) / (2*log rho)`, equivalently
`n ≥ log (1/(2*eps)) / (2*log (1/rho))`. At `rho = 1` the laws are identical, so no finite
number of observations can force a target error below the zero-copy floor.
-/

namespace D5.S3.Estimation.BhattacharyyaExponent

open D5.S3.RenyiDivergence
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker
open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.Estimation.LeCam

open Classical in
/-- Bhattacharyya affinity is multiplicative for every finite i.i.d. power.

The binary theorem needs only `0 ≤ p i * q i`. That product-radicand hypothesis propagates at a
successor because `iidPower p n z` and `iidPower q n z` are products of the marginals; the
induction itself only needs the propagated nonnegativity of the *product* of the two powers.
-/
theorem bhattacharyya_iidPower_multiplicative {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (hpq : ∀ i, 0 ≤ p i * q i) :
    bhattacharyya (iidPower p n) (iidPower q n) = (bhattacharyya p q) ^ n := by
  classical
  induction n with
  | zero =>
      rw [bhattacharyya]
      calc
        _ = Real.sqrt
            (iidPower p 0 PUnit.unit * iidPower q 0 PUnit.unit) :=
          Fintype.sum_eq_single PUnit.unit fun z hz =>
            (hz (Subsingleton.elim z PUnit.unit)).elim
        _ = _ := by norm_num [iidPower]
  | succ n ih =>
      change bhattacharyya
          (fun z : ι × IidSpace ι n => p z.1 * iidPower p n z.2)
          (fun z : ι × IidSpace ι n => q z.1 * iidPower q n z.2) =
        (bhattacharyya p q) ^ (n + 1)
      rw [bhattacharyya_product_multiplicative p q (iidPower p n) (iidPower q n) hpq]
      rw [ih, pow_succ']

open Classical in
/-- Sharp Bhattacharyya floor for the total error of every two-point test on one copy. -/
theorem testing_error_bhattacharyya_sharp {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    1 - Real.sqrt (1 - bhattacharyya p q ^ 2) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  have htv_sq := total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  have htv_nonneg : 0 ≤ totalVariation p q := total_variation_nonneg p q
  have hbc_nonneg : 0 ≤ bhattacharyya p q := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hbc_le_one := bhattacharyya_le_one p q hp hq
  have hrad_nonneg : 0 ≤ 1 - bhattacharyya p q ^ 2 := by
    nlinarith
  have htv : totalVariation p q ≤ Real.sqrt (1 - bhattacharyya p q ^ 2) := by
    apply (Real.le_sqrt htv_nonneg hrad_nonneg).2
    exact htv_sq
  calc
    1 - Real.sqrt (1 - bhattacharyya p q ^ 2) ≤ 1 - totalVariation p q :=
      sub_le_sub_left htv 1
    _ ≤ (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i :=
      le_cam_two_point_sum p q A (hp.2.trans hq.2.symm) hq.2

open Classical in
/-- The elementary corollary `rho^2/2` of the sharp Bhattacharyya testing floor. -/
theorem testing_error_bhattacharyya_quadratic {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    bhattacharyya p q ^ 2 / 2 ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  have hsharp := testing_error_bhattacharyya_sharp p q A hp hq
  have hbc_nonneg : 0 ≤ bhattacharyya p q := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hbc := bhattacharyya_le_one p q hp hq
  have hineq := Real.sqrt_one_add_le (x := -(bhattacharyya p q ^ 2))
    (by nlinarith [hbc, hbc_nonneg])
  have hroot : Real.sqrt (1 - bhattacharyya p q ^ 2) ≤
      1 - bhattacharyya p q ^ 2 / 2 := by
    calc
      Real.sqrt (1 - bhattacharyya p q ^ 2) =
          Real.sqrt (1 + -(bhattacharyya p q ^ 2)) := by congr 1
      _ ≤ 1 + -(bhattacharyya p q ^ 2) / 2 := hineq
      _ = 1 - bhattacharyya p q ^ 2 / 2 := by ring
  linarith

open Classical in
/-- The n-observation Bhattacharyya error exponent for every arbitrary test event. -/
theorem iid_testing_error_bhattacharyya {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    bhattacharyya p q ^ (2 * n) / 2 ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  have hprod := bhattacharyya_iidPower_multiplicative p q n
    (fun i => mul_nonneg (hp.1 i) (hq.1 i))
  have hquad := testing_error_bhattacharyya_quadratic
    (iidPower p n) (iidPower q n) A
    ⟨iid_power_nonneg p hp.1 n, iid_power_sum_one p hp.2 n⟩
    ⟨iid_power_nonneg q hq.1 n, iid_power_sum_one q hq.2 n⟩
  rw [hprod] at hquad
  rw [← pow_mul] at hquad
  simpa [Nat.mul_comm] using hquad

open Classical in
/-- Primary side-condition-free sample-complexity product form. -/
theorem bhattacharyya_sample_complexity_product {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (eps : ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (herror : (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ eps) :
    bhattacharyya p q ^ (2 * n) ≤ 2 * eps := by
  have h := iid_testing_error_bhattacharyya p q n A hp hq
  linarith

open Classical in
/-- Solved sample-complexity form; `log rho < 0` is used to reverse the division inequality. -/
theorem bhattacharyya_sample_complexity_log {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (eps : ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hrho_pos : 0 < bhattacharyya p q) (hrho_lt_one : bhattacharyya p q < 1)
    (heps_pos : 0 < eps) (_heps_half : 2 * eps ≤ 1)
    (herror : (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ eps) :
    Real.log (2 * eps) / (2 * Real.log (bhattacharyya p q)) ≤ n := by
  have hprod := bhattacharyya_sample_complexity_product p q n A eps hp hq herror
  have hrho_pow_pos : 0 < bhattacharyya p q ^ (2 * n) := pow_pos hrho_pos _
  have hlog := (Real.log_le_log_iff hrho_pow_pos (by nlinarith [heps_pos])).2 hprod
  rw [Real.log_pow] at hlog
  have hlog_rho : Real.log (bhattacharyya p q) < 0 := Real.log_neg hrho_pos hrho_lt_one
  norm_num [Nat.cast_mul] at hlog
  apply (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num) hlog_rho)).2
  ring_nf at hlog ⊢
  nlinarith

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    1 - Real.sqrt (1 - bhattacharyya p q ^ 2) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact testing_error_bhattacharyya_sharp p q A hp hq

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    bhattacharyya p q ^ 2 / 2 ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact testing_error_bhattacharyya_quadratic p q A hp hq

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    bhattacharyya p q ^ (2 * n) / 2 ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact iid_testing_error_bhattacharyya p q n A hp hq

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (eps : ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (herror : (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ eps) :
    bhattacharyya p q ^ (2 * n) ≤ 2 * eps := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact bhattacharyya_sample_complexity_product p q n A eps hp hq herror

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (eps : ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hrho_pos : 0 < bhattacharyya p q) (hrho_lt_one : bhattacharyya p q < 1)
    (heps_pos : 0 < eps) (_heps_half : 2 * eps ≤ 1)
    (herror : (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ eps) :
    Real.log (2 * eps) / (2 * Real.log (bhattacharyya p q)) ≤ n := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact bhattacharyya_sample_complexity_log p q n A eps hp hq hrho_pos hrho_lt_one
    heps_pos _heps_half herror

example : (0.9 : ℝ) = 9 / 10 ∧ (0.01 : ℝ) = 1 / 100 ∧
    (18.565 : ℝ) = 3713 / 200 := by
  norm_num

example : (2 * (1 / 2 : ℝ)) = 1 ∧ (0 : ℕ) ≤ 0 := by
  norm_num

#print axioms bhattacharyya_iidPower_multiplicative
#print axioms testing_error_bhattacharyya_sharp
#print axioms testing_error_bhattacharyya_quadratic
#print axioms iid_testing_error_bhattacharyya
#print axioms bhattacharyya_sample_complexity_product
#print axioms bhattacharyya_sample_complexity_log

end D5.S3.Estimation.BhattacharyyaExponent
