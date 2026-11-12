/- GID: D5/S3/Combinatorics/CatalanPowerHankel/BarryA188475
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/BarryA188475
   mirror-E: none(waiver:exact-symbolic-determinant)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Adjugate]
   utility: none
   digest: The recurrence-defined original Barry shifted Hankel determinant through monic orthogonality and finite Gram cofactors. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Polynomial
open Finset
namespace BarryA188475

def q : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => 2 * q (n + 2) + 2 * q (n + 1) +
      ∑ k ∈ range n, (catalan (k + 1) : ℚ) * q (n + 1 - k)
termination_by n => n
decreasing_by all_goals omega

private abbrev C : PowerSeries ℚ := P13CatalanLagrangeBridge.catalanUnit
private def F : PowerSeries ℚ := PowerSeries.mk q
private def T : PowerSeries ℚ := C ^ 2
private def M : PowerSeries ℚ := 1 + 2 * F

private theorem tail_eq : T * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 * T) = 1 := by
  have hc := P13CatalanLagrangeBridge.catalanUnit_equation
  have hx : PowerSeries.X * C ^ 2 = C - 1 := by
    linear_combination hc
  dsimp [T]
  calc
    C ^ 2 * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 * C ^ 2) =
        C ^ 2 - 2 * (PowerSeries.X * C ^ 2) - (PowerSeries.X * C ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hx]; ring

private theorem tail_coeff (n : ℕ) : PowerSeries.coeff n T = (catalan (n + 1) : ℚ) := by
  have hc := congrArg (PowerSeries.coeff (n + 1))
    P13CatalanLagrangeBridge.catalanUnit_equation
  simpa [T, PowerSeries.coeff_succ_mul_X, C, P13CatalanLagrangeBridge.catalanUnit]
    using hc

private theorem convolution_coeff (n : ℕ) : PowerSeries.coeff n (T * F) =
    ∑ k ∈ range (n + 1), (catalan (k + 1) : ℚ) * q (n - k) := by
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [tail_coeff, F]

private theorem source_eq : F = PowerSeries.X ^ 2 + 2 * PowerSeries.X * F +
    2 * PowerSeries.X ^ 2 * F + PowerSeries.X ^ 2 * (T * F) := by
  ext n
  have base0 : q 0 = 0 := by simp [q]
  have base1 : q 1 = 0 := by simp [q]
  have base2 : q 2 = 1 := by simp [q]
  have conv0 : PowerSeries.coeff 0 (T * F) = 0 := by
    simp [convolution_coeff, q]
  have coeffF (k : ℕ) : PowerSeries.coeff k F = q k := by simp [F]
  have linear (k : ℕ) : PowerSeries.coeff k (2 * PowerSeries.X * F) =
      2 * PowerSeries.coeff k (PowerSeries.X * F) := by
    rw [mul_assoc, PowerSeries.coeff_ofNat_mul]
  have quadratic (k : ℕ) : PowerSeries.coeff k (2 * PowerSeries.X ^ 2 * F) =
      2 * PowerSeries.coeff k (PowerSeries.X ^ 2 * F) := by
    rw [mul_assoc, PowerSeries.coeff_ofNat_mul]
  rcases n with _ | _ | _ | n
  · simp [F, q]
  · simp [map_add, linear, quadratic, PowerSeries.coeff_X_pow_mul', coeffF, q]
  · simp [map_add, linear, quadratic, PowerSeries.coeff_X_pow_mul', coeffF, q, conv0]
  · simp only [map_add, linear, quadratic, coeffF]
    rw [show n + 1 + 1 + 1 = n + 3 by omega]
    rw [PowerSeries.coeff_X_pow, if_neg (by omega : n + 3 ≠ 2)]
    rw [show n + 3 = (n + 2) + 1 by omega, PowerSeries.coeff_succ_X_mul]
    rw [show n + 2 + 1 = (n + 1) + 2 by omega,
      PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_X_pow_mul, convolution_coeff]
    rw [sum_range_succ, sum_range_succ]
    simp [coeffF, q, Nat.add_sub_cancel, base0, base1]

private theorem source_denominator : F *
    (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 2 * T) =
    PowerSeries.X ^ 2 := by
  linear_combination source_eq

private theorem root_eq : M * (1 - 2 * PowerSeries.X ^ 2 * T) = 1 := by
  have ht := tail_eq
  have hs := source_denominator
  dsimp [M]
  linear_combination 2 * T * hs - 2 * F * ht



private def beta (n : ℕ) : ℚ := if n = 0 then 2 else 1

private def P : ℕ → ℚ[X]
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => (Polynomial.X - Polynomial.C 2) * P (n + 1) - Polynomial.C (beta n) * P n

private def A : ℕ → ℚ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (1 - Polynomial.C 2 * Polynomial.X) * A (n + 1) -
      Polynomial.C (beta n) * Polynomial.X ^ 2 * A n

private def Q : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => (1 - Polynomial.C 2 * Polynomial.X) * Q (n + 1) -
      Polynomial.C (beta n) * Polynomial.X ^ 2 * Q n

private def E (n : ℕ) : PowerSeries ℚ := M * (A n : PowerSeries ℚ) - (Q n : PowerSeries ℚ)

private theorem error_recurrence (n : ℕ) : E (n + 2) =
    (1 - 2 * PowerSeries.X) * E (n + 1) -
      PowerSeries.C (beta n) * PowerSeries.X ^ 2 * E n := by
  have htwo : ((2 : ℚ[X]) : PowerSeries ℚ) = 2 := by
    simpa only [map_ofNat] using (Polynomial.coe_C (R := ℚ) 2)
  simp only [E, A, Q, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_pow, Polynomial.coe_C, htwo, map_ofNat]
  ring

private theorem error_one : E 1 = 2 * PowerSeries.X ^ 2 * T * M := by
  have hm := root_eq
  simp only [E, A, Q, Polynomial.coe_one, mul_one]
  linear_combination hm

private theorem error_step (n : ℕ) : E (n + 2) = PowerSeries.X ^ 2 * T * E (n + 1) := by
  induction n with
  | zero =>
    rw [error_recurrence, error_one]
    have hb0 : beta 0 = 2 := by simp [beta]
    rw [hb0]
    simp only [E, A, Q, Polynomial.coe_one, Polynomial.coe_zero,
      mul_one, sub_zero, map_ofNat]
    linear_combination 2 * PowerSeries.X ^ 2 * M * tail_eq
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 1) + 2 by omega, error_recurrence]
    have hb : beta (n + 1) = 1 := by simp [beta]
    rw [hb, map_one, one_mul, show n + 1 + 1 = n + 2 by omega, ih]
    linear_combination PowerSeries.X ^ 2 * E (n + 1) * tail_eq

private theorem error_exact (n : ℕ) : E (n + 1) =
    PowerSeries.X ^ (2 * (n + 1)) * (2 * T ^ (n + 1) * M) := by
  induction n with
  | zero =>
    norm_num only [Nat.zero_add, Nat.reduceMul, pow_one]
    rw [error_one]
    ring
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, error_step, ih]
    rw [show 2 * (n + 1 + 1) = 2 + 2 * (n + 1) by omega, pow_add, pow_succ]
    ring

private theorem error_low (n k : ℕ) (hk : k < 2 * (n + 1)) :
    PowerSeries.coeff k (E (n + 1)) = 0 := by
  rw [error_exact, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem error_lead (n : ℕ) : PowerSeries.coeff (2 * (n + 1)) (E (n + 1)) = 2 := by
  rw [error_exact, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have ht0 : PowerSeries.constantCoeff T = 1 := by
    simp only [T, map_pow, P13CatalanLagrangeBridge.catalanUnit_constantCoeff, one_pow]
  have hm0 : PowerSeries.constantCoeff M = 1 := by simp [M, F, q]
  norm_num [map_ofNat, ht0, hm0]


private theorem polynomial_monic (n : ℕ) : (P n).IsMonicOfDegree n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [P]
  | one => simpa [P] using (Polynomial.isMonicOfDegree_X (R := ℚ))
  | more n hn hn1 =>
    rw [P]
    have hm := (Polynomial.isMonicOfDegree_X_sub_one (2 : ℚ)).mul hn1
    have hl : (Polynomial.C (beta n) * P n).natDegree < 1 + (n + 1) := by
      refine Polynomial.natDegree_mul_le.trans_lt ?_
      simp only [Polynomial.natDegree_C, zero_add, hn.natDegree_eq]
      omega
    simpa only [show 1 + (n + 1) = n + 2 by omega] using hm.sub hl

private theorem reversed_polynomial (n : ℕ) : A n = Polynomial.reflect n (P n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [A, P]
  | one => simp [A, P, Polynomial.reflect_one_X]
  | more n hn hn1 =>
    have hlinear : Polynomial.reflect (n + 2) ((Polynomial.X - Polynomial.C 2) * P (n + 1)) =
        (1 - Polynomial.C 2 * Polynomial.X) * Polynomial.reflect (n + 1) (P (n + 1)) := by
      have hm := Polynomial.reflect_mul (Polynomial.X - Polynomial.C 2 : ℚ[X]) (P (n + 1))
        (F := 1) (G := n + 1) (by compute_degree!)
        (polynomial_monic (n + 1)).natDegree_eq.le
      simpa [Polynomial.reflect_sub, Polynomial.reflect_one_X,
        Polynomial.reflect_C, pow_one,
        show 1 + (n + 1) = n + 2 by omega] using hm
    have hsmall : Polynomial.reflect (n + 2) (Polynomial.C (beta n) * P n) =
        Polynomial.C (beta n) * Polynomial.X ^ 2 * Polynomial.reflect n (P n) := by
      have hm := Polynomial.reflect_mul (Polynomial.C (beta n)) (P n)
        (F := 2) (G := n) (by simp) (polynomial_monic n).natDegree_eq.le
      simpa [Polynomial.reflect_C, Nat.add_comm] using hm
    rw [A, P, Polynomial.reflect_sub, hlinear, hsmall, ← hn, ← hn1]

private def B : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun n =>
  (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (PowerSeries.coeff n M)

private theorem moment_pair (f : ℚ[X]) (N : ℕ) (hf : f.natDegree ≤ N) :
    B f = PowerSeries.coeff N (M * (Polynomial.reflect N f : PowerSeries ℚ)) := by
  change (f.sum fun n c => c * PowerSeries.coeff n M) = _
  rw [f.sum_over_range' (fun _ => by simp) (N + 1) (by omega)]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simpa [Finset.mem_range] using hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_reflect,
    ← Polynomial.revAt_le hkN, Polynomial.revAt_invol]
  ring


private theorem numerator_degree (n : ℕ) : n = 0 ∨ (Q n).natDegree < n := by
  induction n using Nat.twoStepInduction with
  | zero => exact Or.inl rfl
  | one => right; simp [Q]
  | more n hn hn1 =>
    right
    by_cases hn0 : n = 0
    · subst n
      norm_num [Q, beta]
      compute_degree!
    · have hqn := hn.resolve_left hn0
      have hqn1 := hn1.resolve_left (by omega : n + 1 ≠ 0)
      rw [Q]
      refine (Polynomial.natDegree_sub_le _ _).trans_lt ?_
      apply max_lt
      · refine Polynomial.natDegree_mul_le.trans_lt ?_
        have hl : (1 - Polynomial.C 2 * Polynomial.X : ℚ[X]).natDegree ≤ 1 := by compute_degree!
        omega
      · refine Polynomial.natDegree_mul_le.trans_lt ?_
        have hl : (Polynomial.C (beta n) * Polynomial.X ^ 2 : ℚ[X]).natDegree ≤ 2 := by
          refine Polynomial.natDegree_mul_le.trans ?_
          simp
        omega

private theorem reflect_monomial (n k : ℕ) :
    Polynomial.reflect (n + k) (Polynomial.X ^ k * P n) = A n := by
  have hm := Polynomial.reflect_mul (Polynomial.X ^ k : ℚ[X]) (P n)
    (F := k) (G := n) (by simp) (polynomial_monic n).natDegree_eq.le
  rw [Polynomial.reflect_monomial] at hm
  have hr : Polynomial.revAt k k = 0 := by rw [Polynomial.revAt_le le_rfl]; simp
  rw [hr, pow_zero, one_mul] at hm
  simpa only [Nat.add_comm k n, reversed_polynomial] using hm

private theorem monomial_orthogonality (n k : ℕ) (hk : k ≤ n) :
    B (Polynomial.X ^ k * P n) =
      if k = n then (if n = 0 then 1 else 2) else 0 := by
  cases n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp only [pow_zero, P, one_mul, ite_true]
    rw [moment_pair 1 0 (by simp)]
    simp [Polynomial.reflect_one, M, F, q]
  | succ n =>
    have hdegree : (Polynomial.X ^ k * P (n + 1)).natDegree ≤ n + 1 + k := by
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [(polynomial_monic (n + 1)).natDegree_eq]
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
      omega
    rw [moment_pair _ (n + 1 + k) hdegree, reflect_monomial]
    have hdef : M * (A (n + 1) : PowerSeries ℚ) =
        E (n + 1) + (Q (n + 1) : PowerSeries ℚ) := by simp [E]
    have hq : PowerSeries.coeff (n + 1 + k) (Q (n + 1) : PowerSeries ℚ) = 0 := by
      rw [Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le ((numerator_degree (n + 1)).resolve_left (by omega)) (by omega))
    rw [hdef, map_add, hq, add_zero]
    by_cases heq : k = n + 1
    · subst k
      simpa only [ite_true, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
        show n + 1 + (n + 1) = 2 * (n + 1) by omega] using error_lead n
    · rw [if_neg heq]
      exact error_low n (n + 1 + k) (by omega)


private theorem polynomial_orthogonality (i j : ℕ) : B (P i * P j) =
    if i = j then (if i = 0 then 1 else 2) else 0 := by
  have expand (f g : ℚ[X]) (N : ℕ) (hf : f.natDegree < N) :
      B (f * g) = ∑ k ∈ range N, f.coeff k * B (Polynomial.X ^ k * g) := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
    rw [Finset.sum_mul, map_sum]
    apply sum_congr rfl
    intro k _
    rw [show Polynomial.C (f.coeff k) * Polynomial.X ^ k * g =
      f.coeff k • (Polynomial.X ^ k * g) by
        rw [← Polynomial.smul_eq_C_mul, smul_mul_assoc], map_smul]
    rfl
  wlog hij : i ≤ j generalizing i j
  · rw [mul_comm, this j i (by omega)]
    simp only [if_neg (by omega : j ≠ i), if_neg (by omega : i ≠ j)]
  by_cases heq : i = j
  · subst j
    rw [if_pos rfl, expand (P i) (P i) (i + 1)
      (by rw [(polynomial_monic i).natDegree_eq]; omega), sum_range_succ]
    have hz : ∑ k ∈ range i, (P i).coeff k * B (Polynomial.X ^ k * P i) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hki : k < i := mem_range.mp hk
      rw [monomial_orthogonality i k (by omega), if_neg (by omega), mul_zero]
    rw [hz, zero_add, monomial_orthogonality i i le_rfl, if_pos rfl]
    have hc : (P i).coeff i = 1 := (Polynomial.isMonicOfDegree_iff (P i) i).mp (polynomial_monic i) |>.2
    rw [hc, one_mul]
  · rw [if_neg heq, expand (P i) (P j) (i + 1)
      (by rw [(polynomial_monic i).natDegree_eq]; omega)]
    apply sum_eq_zero
    intro k hk
    have hki : k < i + 1 := mem_range.mp hk
    rw [monomial_orthogonality j k (by omega), if_neg (by omega), mul_zero]




private def gram (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => PowerSeries.coeff (i.val + j.val) M

private def basisMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => (P j.val).coeff i.val

private def norm (i : ℕ) : ℚ := if i = 0 then 1 else 2

private theorem basis_det (N : ℕ) : (basisMatrix N).det = 1 := by
  have hu : (basisMatrix N).IsUpperTriangular := by
    intro i j h
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [(polynomial_monic j.val).natDegree_eq]; exact h)
  rw [Matrix.det_of_isUpperTriangular hu]
  apply prod_eq_one
  intro i _
  exact (Polynomial.isMonicOfDegree_iff (P i.val) i.val).mp (polynomial_monic i.val) |>.2

private theorem B_monomial (k : ℕ) : B (Polynomial.X ^ k) = PowerSeries.coeff k M := by
  simp [B, Polynomial.X_pow_eq_monomial]

private theorem pair_expansion (f g : ℚ[X]) (N : ℕ)
    (hf : f.natDegree < N) (hg : g.natDegree < N) :
    B (f * g) = ∑ i ∈ range N, ∑ j ∈ range N,
      f.coeff i * PowerSeries.coeff (i + j) M * g.coeff j := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf, g.as_sum_range_C_mul_X_pow' hg]
  rw [Finset.sum_mul, map_sum]
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum, map_sum]
  apply sum_congr rfl
  intro j _
  have hp : Polynomial.C (f.coeff i) * Polynomial.X ^ i *
      (Polynomial.C (g.coeff j) * Polynomial.X ^ j) =
      (f.coeff i * g.coeff j) • (Polynomial.X ^ (i + j)) := by
    rw [Polynomial.smul_eq_C_mul, map_mul, pow_add]
    ring
  rw [hp, map_smul, B_monomial]
  change (f.coeff i * g.coeff j) * _ = _
  ring

private theorem gram_congruence (N : ℕ) :
    (basisMatrix N).transpose * gram N * basisMatrix N =
      Matrix.diagonal (fun i : Fin N => norm i.val) := by
  ext i j
  rw [Matrix.diagonal_apply]
  change (∑ k : Fin N, (∑ l : Fin N,
    (P i.val).coeff l.val * PowerSeries.coeff (l.val + k.val) M) *
      (P j.val).coeff k.val) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun l => ∑ k : Fin N,
    (P i.val).coeff l * PowerSeries.coeff (l + k.val) M * (P j.val).coeff k.val) N]
  have inner (l : ℕ) := Fin.sum_univ_eq_sum_range (fun k =>
    (P i.val).coeff l * PowerSeries.coeff (l + k) M * (P j.val).coeff k) N
  simp_rw [inner]
  rw [← pair_expansion (P i.val) (P j.val) N
    (by rw [(polynomial_monic i.val).natDegree_eq]; exact i.isLt)
    (by rw [(polynomial_monic j.val).natDegree_eq]; exact j.isLt)]
  rw [polynomial_orthogonality]
  by_cases h : i = j
  · subst j; simp [Matrix.diagonal_apply, norm]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [Matrix.diagonal_apply, h, hv]



private theorem adjugate_congruence (N : ℕ) :
    (gram N).adjugate = basisMatrix N *
      (Matrix.diagonal (fun i : Fin N => norm i.val)).adjugate *
      (basisMatrix N).transpose := by
  rw [← gram_congruence, Matrix.adjugate_mul_distrib,
    Matrix.adjugate_mul_distrib]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_adjugate, basis_det, one_smul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transpose,
    basis_det, one_smul, Matrix.mul_one]

private theorem norm_det (N : ℕ) :
    (Matrix.diagonal (fun i : Fin (N + 1) => norm i.val)).det = 2 ^ N := by
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp [norm]

private theorem norm_adjugate (N : ℕ) :
    (Matrix.diagonal (fun i : Fin (N + 1) => norm i.val)).adjugate =
      Matrix.diagonal (fun i : Fin (N + 1) => 2 ^ N / norm i.val) := by
  rw [Matrix.adjugate_diagonal]
  congr 1
  funext i
  have h := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin (N + 1))))
    (f := fun j => norm j.val) (Finset.mem_univ i)
  have hd : (∏ j : Fin (N + 1), norm j.val) = 2 ^ N := by
    simpa only [Matrix.det_diagonal] using norm_det N
  rw [hd] at h
  exact (eq_div_iff (by simp [norm]; split_ifs <;> norm_num)).mpr h

private theorem constant_polynomial (n : ℕ) :
    (P (n + 1)).coeff 0 = 2 * (-1 : ℚ) ^ n * n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [P]
  | one => norm_num [P, beta]
  | more n hn hn1 =>
    have hrec : (P (n + 2 + 1)).coeff 0 =
        -2 * (P (n + 1 + 1)).coeff 0 - (P (n + 1)).coeff 0 := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, P]
      simp [Polynomial.coeff_mul, beta]
    rw [hrec, hn, hn1]
    push_cast
    rw [pow_succ, pow_succ]
    ring

private theorem constant_square (n : ℕ) : (P (n + 1)).coeff 0 ^ 2 = 4 * (n : ℚ) ^ 2 := by
  rw [constant_polynomial]
  have hs : ((-1 : ℚ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, mul_pow, hs]
  norm_num



def hankel (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => q (i.val + j.val + 2)

private theorem gram_minor (N : ℕ) :
    (gram (N + 1)).submatrix (0 : Fin (N + 1)).succAbove
      (0 : Fin (N + 1)).succAbove = (2 : ℚ) • hankel N := by
  ext i j
  simp [gram, hankel, M, F, PowerSeries.coeff_ofNat_mul, Matrix.smul_apply,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem cofactor_value (N : ℕ) :
    (gram (N + 1)).adjugate 0 0 =
      2 ^ N * (1 + 2 * ∑ k ∈ range N, (k : ℚ) ^ 2) := by
  rw [adjugate_congruence, norm_adjugate, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  change (∑ i : Fin (N + 1), (P i.val).coeff 0 *
    (2 ^ N / norm i.val) * (P i.val).coeff 0) = _
  rw [Fin.sum_univ_succ]
  have term (i : Fin N) : (P i.succ.val).coeff 0 *
      (2 ^ N / norm i.succ.val) * (P i.succ.val).coeff 0 =
      2 ^ N * (2 * (i.val : ℚ) ^ 2) := by
    have hs := constant_square i.val
    simp only [Fin.val_succ, norm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false]
    calc
      _ = (2 ^ N / 2) * ((P (i.val + 1)).coeff 0 ^ 2) := by ring
      _ = _ := by rw [hs]; ring
  simp_rw [term]
  rw [Fin.sum_univ_eq_sum_range (fun k => (2 : ℚ) ^ N * (2 * (k : ℚ) ^ 2)) N,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Fin.val_zero, P, Polynomial.coeff_one, ite_true, norm, div_one, one_mul, mul_one]
  ring

private theorem determinant_sum (N : ℕ) :
    (hankel N).det = 1 + 2 * ∑ k ∈ range N, (k : ℚ) ^ 2 := by
  have hc := Matrix.adjugate_fin_succ_eq_det_submatrix
    (gram (N + 1)) (0 : Fin (N + 1)) (0 : Fin (N + 1))
  rw [gram_minor, Matrix.det_smul] at hc
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fintype.card_fin] at hc
  rw [cofactor_value] at hc
  exact mul_left_cancel₀ (pow_ne_zero N (by norm_num : (2 : ℚ) ≠ 0)) hc.symm

theorem result (n : ℕ) :
    (hankel (n + 1)).det = 1 + 2 * ∑ k ∈ range (n + 1), (k : ℚ) ^ 2 ∧
    (hankel (n + 1)).det = (2 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 + n + 3) / 3 := by
  have hs := determinant_sum (n + 1)
  refine ⟨hs, ?_⟩
  rw [hs]
  have sumsq (m : ℕ) : (∑ k ∈ range (m + 1), (k : ℚ) ^ 2) =
      (m : ℚ) * (m + 1) * (2 * m + 1) / 6 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  rw [sumsq]
  ring

#print axioms result
end BarryA188475
