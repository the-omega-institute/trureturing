/- GID: D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Newton connection coefficients and their transform for complex monic annihilators. -/

import D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
import Mathlib.Algebra.Polynomial.Sequence

open Finset Polynomial
open D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform (pair pair_monomial pair_scalar)

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform

/-- The monic Newton polynomials, including coincident nodes. -/
noncomputable def newton (a b : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => newton a b n * (X - C (a + b * n))

noncomputable def connectionRow (alpha b a : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => (X + C (a - alpha * n)) * connectionRow alpha b a n +
      C b * (X * derivative (connectionRow alpha b a n))

/-- The all-parameter Hsu--Shiue coefficients in the monic polynomial convention. -/
noncomputable def S (alpha b a : ℂ) (n m : ℕ) : ℂ :=
  (connectionRow alpha b a n).coeff m

private theorem s_zero (alpha b a : ℂ) (m : ℕ) :
    S alpha b a 0 m = if m = 0 then 1 else 0 := by
  simp [S, connectionRow, coeff_one]

private theorem s_succ_zero (alpha b a : ℂ) (n : ℕ) :
    S alpha b a (n + 1) 0 = (a - alpha * n) * S alpha b a n 0 := by
  simp [S, connectionRow, add_mul, mul_coeff_zero]

private theorem s_succ_succ (alpha b a : ℂ) (n m : ℕ) :
    S alpha b a (n + 1) (m + 1) = S alpha b a n m +
      (a + b * (m + 1) - alpha * n) * S alpha b a n (m + 1) := by
  simp only [S, connectionRow, add_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    coeff_derivative]
  ring

private theorem s_above (alpha b a : ℂ) (n m : ℕ) (h : n < m) :
    S alpha b a n m = 0 := by
  induction n generalizing m with
  | zero => simp [s_zero, ne_of_gt h]
  | succ n ih =>
      cases m with
      | zero => omega
      | succ m => rw [s_succ_succ, ih m (by omega), ih (m + 1) (by omega)]; ring

/-- The factorial-weighted connection row. -/
noncomputable def G (alpha b a : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => (C (a - alpha * n) + X) * G alpha b a n +
      X * (C b + X) * derivative (G alpha b a n)

private theorem g_coeff (alpha b a : ℂ) (n m : ℕ) :
    (G alpha b a n).coeff m = (Nat.factorial m : ℂ) * S alpha b a n m := by
  induction n generalizing m with
  | zero => cases m <;> simp [G, s_zero, coeff_one]
  | succ n ih =>
      have step : G alpha b a (n + 1) =
          C (a - alpha * n) * G alpha b a n + X * G alpha b a n +
          C b * (X * derivative (G alpha b a n)) +
          X * (X * derivative (G alpha b a n)) := by rw [G]; ring
      rw [step]
      cases m with
      | zero => simp [coeff_add, mul_coeff_zero, ih, s_succ_zero]
      | succ m =>
          cases m with
          | zero =>
              simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative,
                mul_coeff_zero, ih, s_succ_succ, Nat.factorial_succ,
                Nat.factorial_zero, Nat.cast_zero, Nat.cast_one,
                zero_add, mul_one, one_mul, coeff_X_zero]
              ring
          | succ m =>
              simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, ih,
                s_succ_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              ring

private theorem g_degree (alpha b a : ℂ) (n : ℕ) :
    (G alpha b a n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [g_coeff, s_above alpha b a n m hm, mul_zero]

private theorem g_expansion (alpha b a : ℂ) (n : ℕ) :
    G alpha b a n = ∑ m ∈ range (n + 1),
      C ((Nat.factorial m : ℂ) * S alpha b a n m) * X ^ m := by
  simpa only [g_coeff] using (G alpha b a n).as_sum_range_C_mul_X_pow'
    (show (G alpha b a n).natDegree < n + 1 by have := g_degree alpha b a n; omega)

/-- Polynomial reflection for the genuine three-parameter connection family. -/
theorem reflection (alpha b a : ℂ) (n : ℕ) :
    (G alpha b a n).comp (-C b - X) =
      C ((-1 : ℂ) ^ n) * G (-alpha) b (b - a) n := by
  induction n with
  | zero => simp [G]
  | succ n ih =>
      have di := congrArg derivative ih
      simp only [derivative_comp, derivative_sub, derivative_neg, derivative_C,
        derivative_X, derivative_C_mul] at di
      have di' : (derivative (G alpha b a n)).comp (-C b - X) =
          -(C ((-1 : ℂ) ^ n) * derivative (G (-alpha) b (b - a) n)) := by
        linear_combination -di
      rw [G, add_comp, mul_comp, mul_comp, mul_comp]
      simp only [add_comp, C_comp, X_comp, ih, di']
      rw [G, pow_succ, C_mul]
      simp only [C_1, map_sub, map_mul, map_neg]
      ring

private noncomputable def newtonMap (a b : ℂ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  Polynomial.lsum fun j =>
    { toFun := fun z => z • newton a b j
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }

private theorem newtonMap_monomial (a b z : ℂ) (j : ℕ) :
    newtonMap a b (C z * X ^ j) = z • newton a b j := by
  rw [C_mul_X_pow_eq_monomial]
  change (monomial j z).sum (fun k w => w • newton a b k) = _
  simp

private theorem newtonMap_step (a b t : ℂ) (f : Polynomial ℂ) :
    newtonMap a b ((X + C (a - t)) * f + C b * (X * derivative f)) =
      (X - C t) * newtonMap a b f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simpa only [mul_add, derivative_add, map_add, add_mul, add_assoc,
        add_left_comm, add_comm] using congrArg₂ (· + ·) hf hg
  | monomial j z =>
      rw [← C_mul_X_pow_eq_monomial]
      have ex : (X + C (a - t)) * (C z * X ^ j) +
          C b * (X * derivative (C z * X ^ j)) =
          C z * X ^ (j + 1) + C ((a + b * j - t) * z) * X ^ j := by
        have dx : X * derivative (C z * X ^ j) = C (z * j) * X ^ j := by
          cases j with
          | zero => simp
          | succ j =>
              rw [derivative_C_mul, derivative_X_pow_succ]
              simp only [C_mul, Nat.cast_add, Nat.cast_one, pow_succ]
              ring
        rw [dx]
        simp only [C_mul, C_sub, C_add, pow_succ]
        ring
      rw [ex, map_add, newtonMap_monomial, newtonMap_monomial, newtonMap_monomial,
        newton, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
      simp only [C_mul, C_sub, C_add]
      ring

private theorem transport_row (alpha b a : ℂ) (n : ℕ) :
    newtonMap a b (connectionRow alpha b a n) = newton 0 alpha n := by
  induction n with
  | zero => simpa [connectionRow, newton] using newtonMap_monomial a b 1 0
  | succ n ih =>
      rw [connectionRow, newtonMap_step, ih, newton]
      simp only [zero_add]
      ring

/-- Literal finite Newton expansion; no node separation is assumed. -/
theorem connection (alpha b a : ℂ) (n : ℕ) :
    newton 0 alpha n = ∑ m ∈ range (n + 1),
      C (S alpha b a n m) * newton a b m := by
  have transport := transport_row alpha b a n
  have degree : (connectionRow alpha b a n).natDegree < n + 1 := by
    have h : (connectionRow alpha b a n).natDegree ≤ n := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      exact s_above alpha b a n m hm
    omega
  rw [(connectionRow alpha b a n).as_sum_range_C_mul_X_pow' degree, map_sum] at transport
  simpa only [newtonMap_monomial, S, smul_eq_C_mul] using transport.symm

/-- Coefficients of the monic Newton products in the power basis. -/
noncomputable def R (a b : ℂ) (n k : ℕ) : ℂ := (newton a b n).coeff k

/-- Power-to-Newton coefficients. -/
noncomputable def T (a b : ℂ) (n k : ℕ) : ℂ := S 0 b a n k

private theorem newton_zero_zero (n : ℕ) : newton 0 0 n = X ^ n := by
  induction n with
  | zero => simp [newton]
  | succ n ih => simp [newton, ih, pow_succ]

private theorem newton_degree (a b : ℂ) (n : ℕ) : (newton a b n).degree = n := by
  induction n with
  | zero => simp [newton]
  | succ n ih =>
      rw [newton, degree_mul, ih, degree_X_sub_C]
      simp

private noncomputable def newtonSequence (a b : ℂ) : Polynomial.Sequence ℂ where
  elems' := newton a b
  degree_eq' := newton_degree a b

private theorem newtonMap_injective (a b : ℂ) : Function.Injective (newtonMap a b) := by
  have hi := (newtonSequence a b).linearIndependent.finsuppLinearCombination_injective
  have he (f : Polynomial ℂ) :
      Finsupp.linearCombination ℂ (newtonSequence a b) f.toFinsupp.coeff = newtonMap a b f := by
    rfl
  intro f g h
  have hf : f.toFinsupp.coeff = g.toFinsupp.coeff := hi (by simpa only [he] using h)
  apply Polynomial.ext
  intro k
  exact congrArg (fun v : ℕ →₀ ℂ => v k) hf

private noncomputable def inverseMap (a b : ℂ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  Polynomial.lsum fun j =>
    { toFun := fun z => z • connectionRow 0 b a j
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }

private theorem inverseMap_monomial (a b z : ℂ) (j : ℕ) :
    inverseMap a b (C z * X ^ j) = z • connectionRow 0 b a j := by
  rw [C_mul_X_pow_eq_monomial]
  change (monomial j z).sum (fun k w => w • connectionRow 0 b a k) = _
  simp

private theorem inverseMap_left (a b : ℂ) (f : Polynomial ℂ) :
    newtonMap a b (inverseMap a b f) = f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial j z =>
      rw [← C_mul_X_pow_eq_monomial, inverseMap_monomial, map_smul, transport_row,
        newton_zero_zero, smul_eq_C_mul]

private theorem inverseMap_right (a b : ℂ) (f : Polynomial ℂ) :
    inverseMap a b (newtonMap a b f) = f := by
  apply newtonMap_injective a b
  rw [inverseMap_left]

private theorem inverseMap_coeff (a b : ℂ) (f : Polynomial ℂ) (n k : ℕ)
    (h : f.natDegree < n + 1) :
    (inverseMap a b f).coeff k =
      ∑ j ∈ range (n + 1), f.coeff j * T a b j k := by
  nth_rw 1 [f.as_sum_range_C_mul_X_pow' h]
  rw [map_sum, finsetSum_coeff]
  apply sum_congr rfl
  intro j hj
  rw [inverseMap_monomial, coeff_smul]
  rfl

/-- Both finite triangular inverses and the two-basis coefficient factorization. -/
theorem basis_change (alpha b a : ℂ) (n k : ℕ) :
    (∑ j ∈ range (n + 1), T a b n j * R a b j k) = (X ^ n : Polynomial ℂ).coeff k ∧
    (∑ j ∈ range (n + 1), R a b n j * T a b j k) = (X ^ n : Polynomial ℂ).coeff k ∧
    S alpha b a n k = ∑ j ∈ range (n + 1), R 0 alpha n j * T a b j k := by
  have ndeg (x y : ℂ) : (newton x y n).natDegree < n + 1 := by
    rw [natDegree_eq_of_degree_eq_some (newton_degree x y n)]
    omega
  constructor
  · have h := congrArg (fun f : Polynomial ℂ => f.coeff k) (connection 0 b a n)
    rw [newton_zero_zero, finsetSum_coeff] at h
    simpa only [coeff_C_mul, R, T] using h.symm
  constructor
  · have h := inverseMap_right a b (X ^ n)
    have hm : newtonMap a b (X ^ n) = newton a b n := by
      simpa using newtonMap_monomial a b 1 n
    rw [hm] at h
    have hc := congrArg (fun f : Polynomial ℂ => f.coeff k) h
    rw [inverseMap_coeff a b _ n k (ndeg a b)] at hc
    exact hc
  · have h : inverseMap a b (newton 0 alpha n) = connectionRow alpha b a n := by
      apply newtonMap_injective a b
      rw [inverseMap_left, transport_row]
    have hc := congrArg (fun f : Polynomial ℂ => f.coeff k) h
    rw [inverseMap_coeff a b _ n k (ndeg 0 alpha)] at hc
    exact hc.symm

private theorem homogeneous_reflection (alpha b a : ℂ) (n : ℕ) :
    (∑ m ∈ range (n + 1),
      MvPolynomial.C ((Nat.factorial m : ℂ) * S alpha b a n m) *
        (-MvPolynomial.C b * MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m *
        MvPolynomial.X 1 ^ (n - m)) =
    MvPolynomial.C ((-1 : ℂ) ^ n) * ∑ m ∈ range (n + 1),
      MvPolynomial.C ((Nat.factorial m : ℂ) * S (-alpha) b (b - a) n m) *
        MvPolynomial.X (0 : Fin 2) ^ m * MvPolynomial.X 1 ^ (n - m) := by
  have degree_one : (-C b - X : Polynomial ℂ).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have degree_pow (m : ℕ) : ((-C b - X : Polynomial ℂ) ^ m).natDegree ≤ m := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left m degree_one)
  have hp : ∀ m : ℕ, homogenize ((-C b - X : Polynomial ℂ) ^ m) m =
      (-MvPolynomial.C b * MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, homogenize_mul _ _ (degree_pow m) degree_one, ih]
        simp [homogenize_sub, homogenize_neg, homogenize_C, homogenize_X, pow_succ]
  have padded (m : ℕ) (hm : m ≤ n) : homogenize ((-C b - X : Polynomial ℂ) ^ m) n =
      (-MvPolynomial.C b * MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m *
        MvPolynomial.X 1 ^ (n - m) := by
    have h := homogenize_mul ((-C b - X : Polynomial ℂ) ^ m) 1
      (degree_pow m) (show (1 : Polynomial ℂ).natDegree ≤ n - m by simp)
    simpa [Nat.add_sub_of_le hm, hp] using h
  have r := reflection alpha b a n
  rw [g_expansion, g_expansion] at r
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp] at r
  have hr := congrArg (fun f : Polynomial ℂ => homogenize f n) r
  simp only [homogenize_finsetSum, homogenize_C_mul] at hr
  convert hr using 1
  · apply sum_congr rfl
    intro m hm
    rw [padded m (by simpa using mem_range.mp hm)]
    ring
  · congr 1
    apply sum_congr rfl
    intro m hm
    rw [homogenize_X_pow (by simpa using mem_range.mp hm)]
    ring

private theorem pair_shift (u : ℕ → ℂ) (c k : ℕ) (f : Polynomial ℂ) :
    pair u c (X ^ k * f) = pair u (k + c) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [mul_add, map_add, hf, hg]
  | monomial j z =>
      rw [← C_mul_X_pow_eq_monomial]
      have h : X ^ k * (C z * X ^ j) = C z * X ^ (k + j) := by rw [pow_add]; ring
      rw [h, pair_monomial, pair_monomial]
      congr 2
      omega

private theorem annihilation (d : ℕ) (q : ℂ) (A : Polynomial ℂ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + d) = q * u n +
      ∑ j ∈ A.support, A.coeff j * u (n + j)) (c : ℕ) (f : Polynomial ℂ) :
    pair u c ((X ^ d - C q - A) * f) = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [mul_add, map_add, hf, hg, add_zero]
  | monomial k z =>
      rw [← C_mul_X_pow_eq_monomial]
      have ex : (X ^ d - C q - A) * (C z * X ^ k) =
          C z * X ^ (k + d) - C (q * z) * X ^ k - C z * (X ^ k * A) := by
        simp only [pow_add, C_mul]; ring
      rw [ex, map_sub, map_sub, pair_monomial, pair_monomial, pair_scalar, pair_shift]
      have hpair : pair u (k + c) A = ∑ j ∈ A.support, A.coeff j * u (k + c + j) := by
        change (∑ j ∈ A.support, A.coeff j * u (j + (k + c))) = _
        apply sum_congr rfl
        intro j hj
        congr 2
        omega
      rw [hpair, show k + d + c = k + c + d by omega, hu]
      ring

/-- The full finite transform for an actual complex sequence with a monic annihilator. -/
theorem result (d : ℕ) (q : ℂ) (A : Polynomial ℂ) (alpha b a : ℂ)
    (ell c : ℕ) (u : ℕ → ℂ) (_hd : 1 ≤ d)
    (_hdegree : A.degree < (d : WithBot ℕ)) (_hzero : A.eval 0 = 0)
    (hu : ∀ n : ℕ, u (n + d) = q * u n +
      ∑ j ∈ A.support, A.coeff j * u (n + j)) :
    (∑ m ∈ range (ell + 1),
      (-1 : ℂ) ^ m * (Nat.factorial m : ℂ) * b ^ m * S alpha b a ell m *
        q ^ (ell - m) * u (d * m + c)) =
    (-1 : ℂ) ^ ell * ∑ m ∈ range (ell + 1),
      (Nat.factorial m : ℂ) * b ^ m * S (-alpha) b (b - a) ell m *
        q ^ (ell - m) * pair u c (A ^ m) := by
  let P : Polynomial ℂ := C q + A
  have power_pair (m : ℕ) : pair u c (P ^ m) = u (d * m + c) := by
    have hdiv : (X ^ d - C q - A : Polynomial ℂ) ∣ (X ^ d) ^ m - P ^ m := by
      have h := sub_dvd_pow_sub_pow (X ^ d : Polynomial ℂ) P m
      have hf : (X ^ d : Polynomial ℂ) - P = X ^ d - C q - A := by dsimp [P]; ring
      rwa [hf] at h
    obtain ⟨f, hf⟩ := hdiv
    have hz := annihilation d q A u hu c f
    rw [← hf, map_sub] at hz
    have he : pair u c ((X ^ d) ^ m) = u (d * m + c) := by
      rw [← pow_mul]
      simpa using pair_monomial u c (d * m) 1
    rw [he] at hz
    exact (sub_eq_zero.mp hz).symm
  have poly := congrArg
    (MvPolynomial.eval₂Hom (C : ℂ →+* Polynomial ℂ) ![C b * A, C q])
    (homogeneous_reflection alpha b a ell)
  simp only [map_sum, map_mul, map_pow, map_sub, map_neg,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one] at poly
  simp only [← C_mul, ← C_pow, ← C_neg] at poly
  have lp (m : ℕ) (z : ℂ) :
      pair u c (C z * (C (-b * q) - C b * A) ^ m * C (q ^ (ell - m))) =
        (-1 : ℂ) ^ m * z * b ^ m * q ^ (ell - m) * u (d * m + c) := by
    have hx : (C (-b * q) - C b * A : Polynomial ℂ) = C (-b) * P := by
      dsimp [P]; simp only [C_neg, C_mul]; ring
    rw [hx, mul_pow]
    have hp : C z * (C (-b) ^ m * P ^ m) * C (q ^ (ell - m)) =
        C ((-1 : ℂ) ^ m * z * b ^ m * q ^ (ell - m)) * P ^ m := by
      rw [neg_pow]
      simp only [C_mul, C_pow, C_neg, C_1]
      ring
    rw [hp, pair_scalar, power_pair]
  have rp (m : ℕ) (z : ℂ) :
      pair u c (C z * (C b * A) ^ m * C (q ^ (ell - m))) =
        z * b ^ m * q ^ (ell - m) * pair u c (A ^ m) := by
    have hp : C z * (C b * A) ^ m * C (q ^ (ell - m)) =
        C (z * b ^ m * q ^ (ell - m)) * A ^ m := by
      simp only [mul_pow, C_mul, C_pow]; ring
    rw [hp, pair_scalar]
  have paired := congrArg (pair u c) poly
  simp only [map_sum, pair_scalar, lp, rp] at paired
  convert paired using 1
  · apply sum_congr rfl
    intro m hm
    ring
  · congr 1
    apply sum_congr rfl
    intro m hm
    ring

end D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
