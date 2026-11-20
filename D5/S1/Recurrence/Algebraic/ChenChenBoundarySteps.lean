/- GID: D5/S1/Recurrence/Algebraic/ChenChenBoundarySteps
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenBoundarySteps
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Row polynomials of the step-m triangle at m = -1, -2, 0 and nonreal roots at m = -3. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#9, all clauses except
  real-rootedness for m > 0)
escape_witness: rowPoly_succ, the polynomial form R_{n+1} = (1 + (m(n-1)+1)X) R_n +
  m X (1 - X) R_n' of the step-m recursion (coefficient comparison against padded_rec), and the
  inductions step_minus_one, step_minus_two and step_zero that close the factorizations
  R_{-1,2q} = R_{-2,2q} = (1-y)^(2q-2)(1+y), R_{-1,2q+1} = (1-y)^(2q-2)(1+y^2),
  R_{-2,2q+1} = (1-y)^(2q), R_{0,n} = (1+y)^(n-1) through that recursion; at m = -3 the
  factorization R_{-3,6} = (1+y)(y^4+16y^3+246y^2+16y+1) and positivity of the quartic on the
  real line force a nonreal root.
proof_shape:
  rowPoly, R, claim: definitions; consumers: the theorems below.
  coeff_rowPoly, eval_rowPoly: bind-only helpers (finite-sum coefficient and evaluation
    bookkeeping); consumers: rowPoly_succ, rowPoly_one, rowPoly_two and result.
  rowPoly_succ: content; consumers: the step theorems.
  der_one_sub_pow: bind-only helper (derivative_pow and ring); consumers: step_minus_one,
    step_minus_two.
  rowPoly_one, rowPoly_two: bind-only helpers (boundary values of Source); consumers: the step
    theorems.
  step_minus_one, step_minus_two, step_zero, step_minus_three_six: content; consumer: result.
  norm_of_root_one_sub, norm_of_root_plus, norm_of_root_sq: bind-only helpers (roots of the
    factors lie on the unit circle); consumer: result.
  quartic_pos: content (sum-of-squares bound); consumer: result.
  result: content only through the step theorems; the nonreal root uses Complex.exists_root.
Direct frozen dependencies:
  D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums (Source, P, padded_rec)
    sha256:babe59678caa4efa35d42893011defa557b4e926070bb618982cee210a4d67c0
Not covered: the clause that every root of R_{m,n} is simple and negative for real m > 0
  (an interlacing argument) is not part of this module.
Search record (§3.1): no D5 declaration states row-polynomial factorizations of the step-m
  triangle; Mathlib has no Eulerian-type row polynomial at these parameters.
-/

import D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.ComputeDegree

/-! # Row polynomials of the step-`m` Eulerian triangle at boundary steps

For `R_{m,n}(y) = ∑_{k=1}^{n} T(n,k) y^(k-1)` and `q ≥ 1`:
`R_{-1,2q} = R_{-2,2q} = (1-y)^(2q-2)(1+y)`, `R_{-1,2q+1} = (1-y)^(2q-2)(1+y^2)`,
`R_{-2,2q+1} = (1-y)^(2q)`; hence every root of `R_{-1,n}` and `R_{-2,n}` lies on the unit circle
and the largest root modulus is `1` for `n ≥ 2`. Also `R_{0,n} = (1+y)^(n-1)`, and `R_{-3,6}` has a
nonreal root. The proofs pass through the polynomial form of the recursion,
`R_{n+1} = (1 + (m(n-1)+1)y) R_n + m y (1-y) R_n'`.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenBoundarySteps

open Finset Polynomial D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

/-- The row polynomial `∑ T(n,k) X^(k-1)` over `ℂ`. -/
noncomputable def rowPoly (T : ℕ → ℕ → ℝ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), C ((P T n (k + 1) : ℝ) : ℂ) * X ^ k

private theorem coeff_rowPoly (T : ℕ → ℕ → ℝ) (n j : ℕ) :
    (rowPoly T n).coeff j = (P T n (j + 1) : ℂ) := by
  unfold rowPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hj : j < n + 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'
  · rw [Finset.sum_eq_zero]
    · simp [P, show ¬ j + 1 ≤ n by omega]
    · intro b hb; have := Finset.mem_range.mp hb; simp [show j ≠ b by omega]



/-- Polynomial form of the step-`m` recursion:
`R_{n+1} = (1 + (m(n-1)+1)X) R_n + m X (1-X) R_n'`. -/
theorem rowPoly_succ {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) {n : ℕ} (hn : 1 ≤ n) :
    rowPoly T (n + 1) = rowPoly T n + C ((m * ((n : ℝ) - 1) + 1 : ℝ) : ℂ) * (rowPoly T n * X) +
      C (m : ℂ) * (derivative (rowPoly T n) * X) -
      C (m : ℂ) * (derivative (rowPoly T n) * X ^ 2) := by
  ext j
  rw [show rowPoly T n * X = rowPoly T n * X ^ 1 by rw [pow_one],
    show derivative (rowPoly T n) * X = derivative (rowPoly T n) * X ^ 1 by rw [pow_one]]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_X_pow', coeff_derivative,
    coeff_rowPoly]
  rw [padded_rec h (n := n + 1) (k := j + 1) (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  rcases j with _ | _ | j
  · simp [P]
  · simp; ring
  · simp only [show 1 ≤ j + 2 by omega, show 2 ≤ j + 2 by omega, ite_true,
      show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega]
    push_cast; ring


private theorem der_one_sub_pow (k : ℕ) :
    derivative ((1 - X : ℂ[X]) ^ k) * (1 - X) = -(k : ℂ[X]) * (1 - X) ^ k := by
  rcases k with _ | k
  · simp
  · rw [derivative_pow]; simp; ring

private theorem rowPoly_one {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) : rowPoly T 1 = 1 := by
  ext j; rw [coeff_rowPoly]
  rcases j with _ | j
  · simp [P, (h.1 1 le_rfl).1]
  · simp only [P, show ¬ j + 2 ≤ 1 by omega, and_false, ite_false, Complex.ofReal_zero]
    rw [coeff_one]; simp

private theorem rowPoly_two {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) : rowPoly T 2 = 1 + X := by
  ext j; rw [coeff_rowPoly]
  rcases j with _ | _ | j
  · simp [P, (h.1 2 (by norm_num)).1]
  · simp [P, (h.1 2 (by norm_num)).2, coeff_one]
  · simp [P, show ¬ j + 3 ≤ 2 by omega, coeff_one, coeff_X]

private theorem step_minus_one {T : ℕ → ℕ → ℝ} (h : Source (-1) T) (p : ℕ) :
    rowPoly T (2 * p + 2) = (1 - X) ^ (2 * p) * (1 + X) ∧
      rowPoly T (2 * p + 3) = (1 - X) ^ (2 * p) * (1 + X ^ 2) := by
  have odd_of_even : ∀ p, rowPoly T (2 * p + 2) = (1 - X) ^ (2 * p) * (1 + X) →
      rowPoly T (2 * p + 3) = (1 - X) ^ (2 * p) * (1 + X ^ 2) := by
    intro p hp
    rw [show 2 * p + 3 = (2 * p + 2) + 1 by ring, rowPoly_succ h (by omega), hp]
    simp only [derivative_mul, derivative_add, derivative_one, derivative_X]
    have hd := der_one_sub_pow (2 * p)
    push_cast at hd ⊢
    simp only [map_add, map_mul, map_neg, map_one, map_sub, map_natCast, map_ofNat]
    linear_combination (-X * (1 + X)) * hd
  induction p with
  | zero =>
    have h2 := rowPoly_two h
    exact ⟨by simpa using h2, odd_of_even 0 (by simpa using h2)⟩
  | succ p ih =>
    have he : rowPoly T (2 * (p + 1) + 2) = (1 - X) ^ (2 * (p + 1)) * (1 + X) := by
      rw [show 2 * (p + 1) + 2 = (2 * p + 3) + 1 by ring, rowPoly_succ h (by omega), ih.2]
      simp only [derivative_mul, derivative_add, derivative_one, derivative_X_pow]
      have hd := der_one_sub_pow (2 * p)
      push_cast at hd ⊢
      simp only [map_add, map_mul, map_neg, map_one, map_sub, map_natCast, map_ofNat]
      linear_combination (-X * (1 + X ^ 2)) * hd
    exact ⟨he, odd_of_even (p + 1) he⟩


private theorem step_minus_two {T : ℕ → ℕ → ℝ} (h : Source (-2) T) (p : ℕ) :
    rowPoly T (2 * p + 2) = (1 - X) ^ (2 * p) * (1 + X) ∧
      rowPoly T (2 * p + 3) = (1 - X) ^ (2 * p + 2) := by
  have odd_of_even : ∀ p, rowPoly T (2 * p + 2) = (1 - X) ^ (2 * p) * (1 + X) →
      rowPoly T (2 * p + 3) = (1 - X) ^ (2 * p + 2) := by
    intro p hp
    rw [show 2 * p + 3 = (2 * p + 2) + 1 by ring, rowPoly_succ h (by omega), hp]
    simp only [derivative_mul, derivative_add, derivative_one, derivative_X]
    have hd := der_one_sub_pow (2 * p)
    push_cast at hd ⊢
    simp only [map_add, map_mul, map_neg, map_one, map_sub, map_natCast, map_ofNat]
    linear_combination (-2 * X * (1 + X)) * hd
  induction p with
  | zero =>
    have h2 := rowPoly_two h
    exact ⟨by simpa using h2, odd_of_even 0 (by simpa using h2)⟩
  | succ p ih =>
    have he : rowPoly T (2 * (p + 1) + 2) = (1 - X) ^ (2 * (p + 1)) * (1 + X) := by
      rw [show 2 * (p + 1) + 2 = (2 * p + 3) + 1 by ring, rowPoly_succ h (by omega), ih.2]
      have hd := der_one_sub_pow (2 * p + 2)
      push_cast at hd ⊢
      simp only [map_add, map_mul, map_neg, map_one, map_sub, map_natCast, map_ofNat]
      linear_combination (-2 * X) * hd
    exact ⟨he, odd_of_even (p + 1) he⟩

private theorem step_zero {T : ℕ → ℕ → ℝ} (h : Source 0 T) (n : ℕ) :
    rowPoly T (n + 1) = (1 + X) ^ n := by
  induction n with
  | zero => simpa using rowPoly_one h
  | succ n ih =>
    rw [rowPoly_succ h (by omega), ih]
    simp; ring

private theorem step_minus_three_six {T : ℕ → ℕ → ℝ} (h : Source (-3) T) :
    rowPoly T 6 = (1 + X) * (X ^ 4 + 16 * X ^ 3 + 246 * X ^ 2 + 16 * X + 1) := by
  have r2 := rowPoly_two h
  have r3 : rowPoly T 3 = 1 - 4 * X + X ^ 2 := by
    rw [rowPoly_succ h (n := 2) (by norm_num), r2]
    simp [derivative_pow]; push_cast; simp only [map_ofNat]; ring
  have r4 : rowPoly T 4 = (1 + X) ^ 3 := by
    rw [rowPoly_succ h (n := 3) (by norm_num), r3]
    simp [derivative_pow]; push_cast; simp only [map_ofNat]; ring
  have r5 : rowPoly T 5 = (1 + X) ^ 2 * (X ^ 2 - 16 * X + 1) := by
    rw [rowPoly_succ h (n := 4) (by norm_num), r4]
    simp [derivative_pow]; push_cast; simp only [map_ofNat]; ring
  rw [rowPoly_succ h (n := 5) (by norm_num), r5]
  simp [derivative_pow]; push_cast; simp only [map_ofNat]; ring


/-- The row polynomial `R_{m,n}(y) = ∑_{k=1}^{n} T(n,k) y^(k-1)`. -/
noncomputable def R (T : ℕ → ℕ → ℝ) (n : ℕ) (y : ℂ) : ℂ := ∑ k ∈ Icc 1 n, (T n k : ℂ) * y ^ (k - 1)

private theorem eval_rowPoly (T : ℕ → ℕ → ℝ) (n : ℕ) (y : ℂ) : (rowPoly T n).eval y = R T n y := by
  unfold rowPoly R
  rw [eval_finsetSum, Finset.sum_range_succ,
    show Icc 1 n = Ico 1 (n + 1) from rfl, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [show P T n (n + 1) = 0 by simp [P], Complex.ofReal_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := Finset.mem_range.mp hk
  simp [P, add_comm 1 k, show k + 1 ≤ n by omega]

/-- Boundary steps `m = -1, -2, 0` and the nonreal roots of row six at `m = -3`. -/
def claim : Prop :=
  (∀ T, Source (-1) T → ∀ q, 1 ≤ q → ∀ y : ℂ,
      R T (2 * q) y = (1 - y) ^ (2 * q - 2) * (1 + y) ∧
      R T (2 * q + 1) y = (1 - y) ^ (2 * q - 2) * (1 + y ^ 2)) ∧
  (∀ T, Source (-2) T → ∀ q, 1 ≤ q → ∀ y : ℂ,
      R T (2 * q) y = (1 - y) ^ (2 * q - 2) * (1 + y) ∧
      R T (2 * q + 1) y = (1 - y) ^ (2 * q)) ∧
  (∀ T, (Source (-1) T ∨ Source (-2) T) → ∀ n, 2 ≤ n →
      (∃ z : ℂ, R T n z = 0 ∧ ‖z‖ = 1) ∧ ∀ z : ℂ, R T n z = 0 → ‖z‖ = 1) ∧
  (∀ T, Source 0 T → ∀ n, 1 ≤ n → ∀ y : ℂ, R T n y = (1 + y) ^ (n - 1)) ∧
  (∀ T, Source (-3) T → ∃ z : ℂ, R T 6 z = 0 ∧ z.im ≠ 0)


private theorem norm_of_root_one_sub {a : ℕ} {z : ℂ} (hz : (1 - z) ^ a = 0) : ‖z‖ = 1 := by
  have : z = 1 := by have := pow_eq_zero_iff'.mp hz; linear_combination -this.1
  simp [this]

private theorem norm_of_root_plus {a : ℕ} {z : ℂ} (hz : (1 - z) ^ a * (1 + z) = 0) : ‖z‖ = 1 := by
  rcases mul_eq_zero.mp hz with h | h
  · exact norm_of_root_one_sub h
  · have : z = -1 := by linear_combination h
    simp [this]

private theorem norm_of_root_sq {a : ℕ} {z : ℂ} (hz : (1 - z) ^ a * (1 + z ^ 2) = 0) : ‖z‖ = 1 := by
  rcases mul_eq_zero.mp hz with h | h
  · exact norm_of_root_one_sub h
  · have h2 : ‖z‖ ^ 2 = 1 := by
      rw [← norm_pow, show z ^ 2 = -1 by linear_combination h]; simp
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]

private theorem quartic_pos (x : ℝ) : 0 < x ^ 4 + 16 * x ^ 3 + 246 * x ^ 2 + 16 * x + 1 := by
  nlinarith [sq_nonneg (x ^ 2 + 8 * x), sq_nonneg (x + 2 / 91), sq_nonneg x]

/-- The boundary-step factorizations, unit root moduli, the case `m = 0`, and nonreal roots of
row six at `m = -3`. -/
theorem result : claim := by
  have hm1 : ∀ T, Source (-1) T → ∀ q, 1 ≤ q → ∀ y : ℂ,
      R T (2 * q) y = (1 - y) ^ (2 * q - 2) * (1 + y) ∧
      R T (2 * q + 1) y = (1 - y) ^ (2 * q - 2) * (1 + y ^ 2) := by
    intro T h q hq y
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    obtain ⟨he, ho⟩ := step_minus_one h p
    rw [← eval_rowPoly, ← eval_rowPoly, show 2 * (p + 1) = 2 * p + 2 by ring,
      show 2 * p + 2 + 1 = 2 * p + 3 by ring, he, ho, show 2 * p + 2 - 2 = 2 * p by omega]
    simp
  have hm2 : ∀ T, Source (-2) T → ∀ q, 1 ≤ q → ∀ y : ℂ,
      R T (2 * q) y = (1 - y) ^ (2 * q - 2) * (1 + y) ∧
      R T (2 * q + 1) y = (1 - y) ^ (2 * q) := by
    intro T h q hq y
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    obtain ⟨he, ho⟩ := step_minus_two h p
    rw [← eval_rowPoly, ← eval_rowPoly, show 2 * (p + 1) = 2 * p + 2 by ring,
      show 2 * p + 2 + 1 = 2 * p + 3 by ring, he, ho, show 2 * p + 2 - 2 = 2 * p by omega]
    simp
  refine ⟨hm1, hm2, ?_, ?_, ?_⟩
  · intro T hT n hn
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hq : 1 ≤ q := by omega
      have key : ∀ z, R T (2 * q) z = (1 - z) ^ (2 * q - 2) * (1 + z) := by
        intro z; rcases hT with h | h
        · exact (hm1 T h q hq z).1
        · exact (hm2 T h q hq z).1
      refine ⟨⟨-1, by rw [key]; ring, by simp⟩, fun z hz => norm_of_root_plus (by rwa [← key])⟩
    · have hq : 1 ≤ q := by omega
      rcases hT with h | h
      · have key := fun z => (hm1 T h q hq z).2
        refine ⟨⟨Complex.I, by rw [key]; simp, by simp⟩,
          fun z hz => norm_of_root_sq (by rwa [← key])⟩
      · have key := fun z => (hm2 T h q hq z).2
        refine ⟨⟨1, by rw [key]; simp; omega, by simp⟩,
          fun z hz => norm_of_root_one_sub (by rwa [← key])⟩
  · intro T h n hn y
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [← eval_rowPoly, step_zero h k]
    simp
  · intro T h
    set g : ℂ[X] := X ^ 4 + 16 * X ^ 3 + 246 * X ^ 2 + 16 * X + 1 with hg
    have hdeg4 : degree g = 4 := by
      rw [hg]; compute_degree!
    have hdeg : 0 < degree g := by rw [hdeg4]; norm_num
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    refine ⟨z, ?_, ?_⟩
    · rw [← eval_rowPoly, step_minus_three_six h, eval_mul]
      simp only [IsRoot.def] at hz
      rw [← hg, hz, mul_zero]
    · intro him
      have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      simp only [IsRoot.def, hg, eval_add, eval_mul, eval_pow, eval_X, eval_one,
        eval_ofNat] at hz
      rw [hzre] at hz
      have := quartic_pos z.re
      have hc : ((z.re ^ 4 + 16 * z.re ^ 3 + 246 * z.re ^ 2 + 16 * z.re + 1 : ℝ) : ℂ) = 0 := by
        push_cast; linear_combination hz
      exact absurd (Complex.ofReal_eq_zero.mp hc) this.ne'

end D5.S1.Recurrence.Algebraic.ChenChenBoundarySteps
