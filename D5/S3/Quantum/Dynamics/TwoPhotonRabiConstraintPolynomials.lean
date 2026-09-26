/- GID: D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: For the two-photon asymmetric quantum Rabi model (arXiv:2609.00750v1, Conjecture 4.5), the constraint polynomial P_N at the critical coupling x = 1 is the product of (y + 2n(2n + 2rho - 1)), and for x > 1 and bias eps >= 0 all its coefficients are positive. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: part (a) is produced by the closed
  form `closedForm` of every intermediate polynomial in the basis of partial products, whose
  coefficient recurrence `cstep` reduces to a polynomial identity valid for rho in {0, 1}; part (b)
  by the tridiagonal determinant recursion `detJac` (first-row expansion reused from the frozen
  `det_sparse_front`), the positive definiteness of the Jacobi matrix at x = 1 obtained from
  part (a) (`jacOnePosDef`), and the splitting J(x) = sqrt x J(1) + D with a nonnegative
  diagonal D (`hsplit`, `hDnn`)
admission_basis: open-problem-resolution (issue #10148)
Direct frozen dependencies: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.det_sparse_front
-/

import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.Polynomial.Vieta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials

open Polynomial
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (det_sparse_front)

/-!
Reyes-Bustos and Wakayama, *Two-photon quantum Rabi models – Spectral degeneracy and
symmetries*, arXiv:2609.00750v1, §4. Definition 4.1 gives the polynomials
`P_k^{(N,ρ,ε)}(x, y)` by `P_0 = 1`, `P_1 = y + 2x(4N + 2ρ + 2ε - 1) - 4(1 + ε)` and
`P_k = (y + 2xk(4N + 2ρ - 2k + 2ε + 1) - 4k(k + ε)) P_{k-1}
  - 4k(k - 1)(2(N - k + 1) + ρ)(2(N - k + 1) + ρ - 1) x P_{k-2}`;
Conjecture 4.5 states `P_N^{(N,ρ,ε)}(1, y) = ∏_{n=1}^{N} (y + 2n(2n + 2ρ - 1))` and that for
`x > 1` the polynomial `P_N^{(N,ρ,ε)}(x, y)` has positive coefficients. Here `ρ ∈ {0, 1}` is
the parity, `x = (2g)^2`, `y = Δ^2` and `ε` is the bias; the second statement is read for
`ε ≥ 0` (issue #10148), since for `ε = -2`, `N = 1`, `ρ = 0` one has `P_1 = y - 2x + 4`.
-/

/-- Definition 4.1 of arXiv:2609.00750v1: `P_k^{(N,ρ,ε)}(x, y)` as a polynomial in `y`. -/
noncomputable def constraintPoly (N : ℕ) (ρ ε x : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + C (2 * x * (4 * N + 2 * ρ + 2 * ε - 1) - 4 * (1 + ε))
  | k + 2 => (X + C (2 * x * ((k : ℝ) + 2) * (4 * N + 2 * ρ - 2 * ((k : ℝ) + 2) + 2 * ε + 1)
        - 4 * ((k : ℝ) + 2) * (((k : ℝ) + 2) + ε))) * constraintPoly N ρ ε x (k + 1)
      - C (4 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ)
        * (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ - 1) * x) * constraintPoly N ρ ε x k

/-- Conjecture 4.5 of arXiv:2609.00750v1, the first statement for every bias `ε`, and the second
(positive coefficients, and therefore no positive roots in `y`) for `ε ≥ 0`. -/
def claim : Prop :=
  ∀ (N : ℕ) (ρ : ℝ), (ρ = 0 ∨ ρ = 1) →
    (∀ ε : ℝ, constraintPoly N ρ ε 1 N =
      ∏ n ∈ Finset.Icc 1 N, (X + C (2 * (n : ℝ) * (2 * n + 2 * ρ - 1)))) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ x : ℝ, 1 < x →
      (∀ i ≤ N, 0 < (constraintPoly N ρ ε x N).coeff i) ∧
        ∀ y : ℝ, 0 < y → (constraintPoly N ρ ε x N).eval y ≠ 0)

/-- The eigenvalue `2n(2n + 2ρ - 1)` of the critical tridiagonal matrix. -/
private noncomputable def lam (ρ : ℝ) (n : ℕ) : ℝ := 2 * n * (2 * n + 2 * ρ - 1)

/-- The partial product `∏_{n=1}^{i} (y + λ_n)`. -/
private noncomputable def qpoly (ρ : ℝ) (i : ℕ) : ℝ[X] :=
  ∏ n ∈ Finset.Icc 1 i, (X + C (lam ρ n))

/-- The coefficient `C(i+j, i) 4^j ∏_{l<j} (N - i - 1 - l) ∏_{l<j} (i + j + 1 - l)`. -/
private noncomputable def gco (N i j : ℕ) : ℝ :=
  ((i + j).choose i : ℝ) * 4 ^ j * (∏ l ∈ Finset.range j, ((N : ℝ) - i - 1 - l)) *
    (∏ l ∈ Finset.range j, ((i : ℝ) + j + 1 - l))

/-- The coefficient of the partial product of length `i` in `P_k^{(N,ρ,ε)}(1, y)`. -/
private noncomputable def coef (N k i : ℕ) : ℝ := if i ≤ k then gco N i (k - i) else 0

/-- The diagonal entry `2xk(4N + 2ρ - 2k + 2ε + 1) - 4k(k + ε)` of the recursion. -/
private noncomputable def dg (N : ℕ) (ρ ε x : ℝ) (k : ℕ) : ℝ :=
  2 * x * k * (4 * N + 2 * ρ - 2 * k + 2 * ε + 1) - 4 * k * (k + ε)

/-- The coupling `4k(k - 1)(2(N - k + 1) + ρ)(2(N - k + 1) + ρ - 1)` without the factor `x`. -/
private noncomputable def bb (N : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  4 * k * ((k : ℝ) - 1) * (2 * ((N : ℝ) - k + 1) + ρ) * (2 * ((N : ℝ) - k + 1) + ρ - 1)

/-- The symmetric tridiagonal matrix whose row `i` carries the index `m - i` of the recursion. -/
private noncomputable def jac (N : ℕ) (ρ ε x : ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if i = j then dg N ρ ε x (m - i) else
    if (i : ℕ) + 1 = j then Real.sqrt (bb N ρ (m - i) * x) else
    if (j : ℕ) + 1 = i then Real.sqrt (bb N ρ (m - j) * x) else 0

/-- Part (a): in the basis of partial products `Q_i = ∏_{n ≤ i} (y + λ_n)` the polynomial
`P_k^{(N,ρ,ε)}(1, y)` has the coefficients `coef N k i`, which vanish at `k = N` except for
`i = N`. Part (b): `P_N^{(N,ρ,ε)}(x, y) = det(y + J(x))` for the symmetric tridiagonal matrix
`J(x)` with diagonal `d_k(x)` and off-diagonal `√(b_k x)`; `J(x) = √x J(1) + D` with `D` a
nonnegative diagonal matrix for `x ≥ 1`, `ε ≥ 0`, and `J(1)` is positive definite since its
eigenvalues are the roots `λ_n > 0` from part (a). Hence `J(x)` is positive definite, and the
coefficients of `∏ (y + μ_i)` over its eigenvalues `μ_i > 0` are positive. -/
theorem result : claim := by
  intro N ρ hρ
  have hρ0 : 0 ≤ ρ := by rcases hρ with rfl | rfl <;> norm_num
  have gstep : ∀ i j : ℕ,
      gco N i (j + 2) = (if i = 0 then 0 else gco N (i - 1) (j + 2)) +
        (2 * ((i + j : ℕ) + 2 : ℝ) * (4 * N + 2 * ρ - 4 * ((i + j : ℕ) + 2 : ℝ) + 1) -
          lam ρ (i + 1)) *
          gco N i (j + 1) -
        4 * ((i + j : ℕ) + 2 : ℝ) * ((i + j : ℕ) + 1 : ℝ) *
          (2 * ((N : ℝ) - ((i + j : ℕ) + 2) + 1) + ρ) *
          (2 * ((N : ℝ) - ((i + j : ℕ) + 2) + 1) + ρ - 1) * gco N i j := by
    intro i j
    have hA1 : ∏ l ∈ Finset.range (j + 1), ((N : ℝ) - i - 1 - l) =
        (∏ l ∈ Finset.range j, ((N : ℝ) - i - 1 - l)) * ((N : ℝ) - i - 1 - j) := by
      rw [Finset.prod_range_succ]
    have hA2 : ∏ l ∈ Finset.range (j + 2), ((N : ℝ) - i - 1 - l) =
        (∏ l ∈ Finset.range j, ((N : ℝ) - i - 1 - l)) * ((N : ℝ) - i - 1 - j) *
          ((N : ℝ) - i - 1 - (j + 1)) := by
      rw [Finset.prod_range_succ, hA1]; push_cast; ring
    have shift : ∀ (s : ℝ) (m : ℕ), ∏ l ∈ Finset.range (m + 1), (s - l) =
        s * ∏ l ∈ Finset.range m, ((s - 1) - l) := by
      intro s m
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun l _ => ?_
        push_cast; ring
    have hB1 : ∏ l ∈ Finset.range (j + 1), ((i : ℝ) + (j + 1 : ℕ) + 1 - l) =
        ((i : ℝ) + j + 2) * ∏ l ∈ Finset.range j, ((i : ℝ) + j + 1 - l) := by
      rw [shift]
      push_cast
      congr 1
      · ring
      · refine Finset.prod_congr rfl fun l _ => ?_
        ring
    have hB2 : ∏ l ∈ Finset.range (j + 2), ((i : ℝ) + (j + 2 : ℕ) + 1 - l) =
        ((i : ℝ) + j + 3) * ((i : ℝ) + j + 2) *
          ∏ l ∈ Finset.range j, ((i : ℝ) + j + 1 - l) := by
      rw [shift, shift, ← mul_assoc]
      push_cast
      congr 1
      · ring
      · refine Finset.prod_congr rfl fun l _ => ?_
        ring
    have hC1 :
        ((i + (j + 1)).choose i : ℝ) * (j + 1) = ((i + j).choose i : ℝ) * (i + j + 1) := by
      have := Nat.choose_mul_succ_eq (i + j) i
      rw [show i + j + 1 - i = j + 1 by omega, show i + j + 1 = i + (j + 1) by ring] at this
      exact_mod_cast this.symm
    have hC2 : ((i + (j + 2)).choose i : ℝ) * (j + 2) =
        ((i + (j + 1)).choose i : ℝ) * (i + j + 2) := by
      have := Nat.choose_mul_succ_eq (i + (j + 1)) i
      rw [show i + (j + 1) + 1 - i = j + 2 by omega,
        show i + (j + 1) + 1 = i + (j + 2) by ring] at this
      exact_mod_cast this.symm
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hj2 : ((j : ℝ) + 2) ≠ 0 := by positivity
    have eC1 :
        ((i + (j + 1)).choose i : ℝ) = ((i + j).choose i : ℝ) * (i + j + 1) / (j + 1) := by
      rw [eq_div_iff hj1, hC1]
    have eC2 : ((i + (j + 2)).choose i : ℝ) =
        ((i + (j + 1)).choose i : ℝ) * (i + j + 2) / (j + 2) := by
      rw [eq_div_iff hj2, hC2]
    have hρ2 : ρ * ρ = ρ := by rcases hρ with rfl | rfl <;> norm_num
    cases i with
    | zero =>
      simp only [gco]
      rw [hA2, hA1, hB2, hB1, eC2, eC1]
      unfold lam
      push_cast
      field_simp
      rcases hρ with rfl | rfl <;> ring
    | succ i =>
      have hA3 : ∏ l ∈ Finset.range (j + 2), ((N : ℝ) - ((i + 1 - 1 : ℕ) : ℝ) - 1 - l) =
          ((N : ℝ) - ((i + 1 : ℕ) : ℝ)) *
            ((∏ l ∈ Finset.range j, ((N : ℝ) - ((i + 1 : ℕ) : ℝ) - 1 - l)) *
              ((N : ℝ) - ((i + 1 : ℕ) : ℝ) - 1 - j)) := by
        rw [shift, ← hA1]
        push_cast
        congr 1
        · ring
        · refine Finset.prod_congr rfl fun l _ => ?_
          ring
      have hB3 :
          ∏ l ∈ Finset.range (j + 2), (((i + 1 - 1 : ℕ) : ℝ) + (j + 2 : ℕ) + 1 - l) =
          ((i : ℝ) + 1 + j + 2) *
            ((∏ l ∈ Finset.range j, (((i + 1 : ℕ) : ℝ) + j + 1 - l)) *
            ((i : ℝ) + 1 + 1)) := by
        rw [shift, Finset.prod_range_succ]
        push_cast
        congr 1
        · ring
        · congr 1
          · refine Finset.prod_congr rfl fun l _ => ?_
            ring
          · ring
      have hC3 : (((i + 1 - 1) + (j + 2)).choose (i + 1 - 1) : ℝ) * (j + 2) =
          ((i + 1 + (j + 1)).choose (i + 1) : ℝ) * (i + 1) := by
        have h1 := Nat.choose_mul_succ_eq (i + j + 1) i
        have h2 := Nat.add_one_mul_choose_eq (i + j + 1) i
        rw [show i + 1 - 1 = i by omega, show i + (j + 2) = i + j + 1 + 1 by ring,
          show i + 1 + (j + 1) = i + j + 1 + 1 by ring]
        rw [show i + j + 1 + 1 - i = j + 2 by omega] at h1
        have h1' :
            ((i + j + 1).choose i : ℝ) * (i + j + 1 + 1) =
              ((i + j + 1 + 1).choose i : ℝ) * (j + 2) := by
          exact_mod_cast h1
        have h2' : ((i + j + 1 + 1) : ℝ) * ((i + j + 1).choose i : ℝ) =
            ((i + j + 1 + 1).choose (i + 1) : ℝ) * (i + 1) := by
          exact_mod_cast h2
        linear_combination -h1' + h2'
      have eC3 : (((i + 1 - 1) + (j + 2)).choose (i + 1 - 1) : ℝ) =
          ((i + 1 + (j + 1)).choose (i + 1) : ℝ) * (i + 1) / (j + 2) := by
        rw [eq_div_iff hj2, hC3]
      simp only [gco, if_neg (Nat.succ_ne_zero i)]
      rw [hA2, hA1, hB2, hB1, eC3, hA3, hB3, eC2, eC1]
      unfold lam
      push_cast
      field_simp
      rcases hρ with rfl | rfl <;> ring
  have cstep : ∀ k i : ℕ, k + 2 ≤ N →
      coef N (k + 2) i = (if i = 0 then 0 else coef N (k + 1) (i - 1)) +
        (2 * ((k : ℝ) + 2) * (4 * N + 2 * ρ - 4 * ((k : ℝ) + 2) + 1) - lam ρ (i + 1)) *
          coef N (k + 1) i -
        4 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ) *
          (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ - 1) * coef N k i := by
    intro k i hk
    rcases lt_trichotomy i (k + 1) with hi | hi | hi
    · obtain ⟨j, rfl⟩ : ∃ j, k = i + j := ⟨k - i, by omega⟩
      have e2 : coef N (i + j + 2) i = gco N i (j + 2) := by
        rw [coef, if_pos (by omega), show i + j + 2 - i = j + 2 by omega]
      have e1 : coef N (i + j + 1) i = gco N i (j + 1) := by
        rw [coef, if_pos (by omega), show i + j + 1 - i = j + 1 by omega]
      have e0 : coef N (i + j) i = gco N i j := by
        rw [coef, if_pos (by omega), show i + j - i = j by omega]
      have em : (if i = 0 then 0 else coef N (i + j + 1) (i - 1)) =
          (if i = 0 then 0 else gco N (i - 1) (j + 2)) := by
        split_ifs with h
        · rfl
        · rw [coef, if_pos (by omega), show i + j + 1 - (i - 1) = j + 2 by omega]
      rw [e2, e1, e0, em]
      exact gstep i j
    · subst hi
      have e2 :
          coef N (k + 2) (k + 1) = 4 * ((k : ℝ) + 2) * ((N : ℝ) - k - 2) * ((k : ℝ) + 3) := by
        rw [coef, if_pos (by omega), show k + 2 - (k + 1) = 1 by omega]
        simp only [gco, Finset.prod_range_one, show k + 1 + 1 = k + 2 by ring]
        rw [Nat.choose_succ_self_right]
        push_cast; ring
      have e1 : coef N (k + 1) k = 4 * ((k : ℝ) + 1) * ((N : ℝ) - k - 1) * ((k : ℝ) + 2) := by
        rw [coef, if_pos (by omega), show k + 1 - k = 1 by omega]
        simp only [gco, Finset.prod_range_one]
        rw [Nat.choose_succ_self_right]
        push_cast; ring
      have e11 : coef N (k + 1) (k + 1) = 1 := by
        rw [coef, if_pos le_rfl, Nat.sub_self]; simp [gco]
      have e01 : coef N k (k + 1) = 0 := by rw [coef, if_neg (by omega)]
      rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, e2, e1, e11, e01]
      unfold lam
      push_cast; ring
    · rcases Nat.lt_or_ge i (k + 3) with h3 | h3
      · obtain rfl : i = k + 2 := by omega
        have e22 : coef N (k + 2) (k + 2) = 1 := by
          rw [coef, if_pos le_rfl, Nat.sub_self]; simp [gco]
        have e11 : coef N (k + 1) (k + 1) = 1 := by
          rw [coef, if_pos le_rfl, Nat.sub_self]; simp [gco]
        have e12 : coef N (k + 1) (k + 2) = 0 := by rw [coef, if_neg (by omega)]
        have e02 : coef N k (k + 2) = 0 := by rw [coef, if_neg (by omega)]
        rw [if_neg (by omega), show k + 2 - 1 = k + 1 by omega, e22, e11, e12, e02]
        ring
      · have z2 : coef N (k + 2) i = 0 := by rw [coef, if_neg (by omega)]
        have z1 : coef N (k + 1) i = 0 := by rw [coef, if_neg (by omega)]
        have z0 : coef N k i = 0 := by rw [coef, if_neg (by omega)]
        have zm : coef N (k + 1) (i - 1) = 0 := by rw [coef, if_neg (by omega)]
        rw [if_neg (by omega), z2, z1, z0, zm]
        ring
  have closedForm : ∀ ε : ℝ, ∀ k, k ≤ N → constraintPoly N ρ ε 1 k =
      ∑ i ∈ Finset.range (N + 1), C (coef N k i) * qpoly ρ i := by
    intro ε
    have hQ : ∀ i, qpoly ρ (i + 1) = qpoly ρ i * (X + C (lam ρ (i + 1))) := by
      intro i
      rw [qpoly, qpoly, Finset.prod_Icc_succ_top (by omega)]
    have trunc : ∀ k, k ≤ N → ∑ i ∈ Finset.range (N + 1), C (coef N k i) * qpoly ρ i =
        ∑ i ∈ Finset.range (k + 1), C (coef N k i) * qpoly ρ i := by
      intro k hk
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hni => ?_
      rw [Finset.mem_range] at hni
      rw [coef, if_neg (by omega), map_zero, zero_mul]
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      match k, ih, hk with
      | 0, _, _ =>
        rw [trunc 0 (by omega), Finset.sum_range_one, coef, if_pos le_rfl]
        simp [constraintPoly, gco, qpoly]
      | 1, _, hk =>
        rw [trunc 1 hk, Finset.sum_range_succ, Finset.sum_range_one, coef, if_pos (by omega),
          coef, if_pos le_rfl]
        simp only [gco, constraintPoly, Nat.sub_self, Nat.sub_zero, Finset.prod_range_one,
          Finset.range_zero, Finset.prod_empty, pow_zero, pow_one, Nat.choose_self,
          Nat.choose_zero_right]
        rw [qpoly, qpoly, Finset.Icc_self, Finset.prod_singleton]
        simp only [Finset.Icc_eq_empty_of_lt (show 1 > 0 by omega), Finset.prod_empty]
        unfold lam
        simp only [map_add, map_sub, map_mul, map_one, map_natCast, map_ofNat]
        push_cast
        ring
      | k + 2, ih, hk =>
        have ih1 := ih (k + 1) (by omega) (by omega)
        have ih0 := ih k (by omega) (by omega)
        set a : ℝ := 2 * ((k : ℝ) + 2) * (4 * N + 2 * ρ - 4 * ((k : ℝ) + 2) + 1) with ha
        set b : ℝ := 4 * ((k : ℝ) + 2) * ((k : ℝ) + 1) *
          (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ) *
          (2 * ((N : ℝ) - ((k : ℝ) + 2) + 1) + ρ - 1) with hb
        have hP : constraintPoly N ρ ε 1 (k + 2) =
            (X + C a) * constraintPoly N ρ ε 1 (k + 1) - C b * constraintPoly N ρ ε 1 k := by
          rw [constraintPoly]
          congr 3
          · rw [ha]; ring_nf
          · rw [hb]; ring_nf
        have key : ∑ i ∈ Finset.range (N + 1), C (coef N (k + 1) i) * qpoly ρ (i + 1) =
            ∑ i ∈ Finset.range (N + 1),
              C (if i = 0 then 0 else coef N (k + 1) (i - 1)) * qpoly ρ i := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ' _ N]
          have hz : coef N (k + 1) N = 0 := by rw [coef, if_neg (by omega)]
          rw [hz, map_zero, zero_mul, add_zero, if_pos rfl, map_zero, zero_mul, add_zero]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
        rw [hP, ih1, ih0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        calc ∑ i ∈ Finset.range (N + 1),
              ((X + C a) * (C (coef N (k + 1) i) * qpoly ρ i) -
                C b * (C (coef N k i) * qpoly ρ i))
            = ∑ i ∈ Finset.range (N + 1), (C (coef N (k + 1) i) * qpoly ρ (i + 1) +
                (C ((a - lam ρ (i + 1)) * coef N (k + 1) i) * qpoly ρ i -
                  C (b * coef N k i) * qpoly ρ i)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hQ]
              simp only [map_mul, map_sub]
              ring
          _ = ∑ i ∈ Finset.range (N + 1), C (coef N (k + 1) i) * qpoly ρ (i + 1) +
                ∑ i ∈ Finset.range (N + 1),
                  (C ((a - lam ρ (i + 1)) * coef N (k + 1) i) * qpoly ρ i -
                  C (b * coef N k i) * qpoly ρ i) := Finset.sum_add_distrib
          _ = ∑ i ∈ Finset.range (N + 1),
                C (if i = 0 then 0 else coef N (k + 1) (i - 1)) * qpoly ρ i +
                ∑ i ∈ Finset.range (N + 1),
                  (C ((a - lam ρ (i + 1)) * coef N (k + 1) i) * qpoly ρ i -
                  C (b * coef N k i) * qpoly ρ i) := by rw [key]
          _ = ∑ i ∈ Finset.range (N + 1), C (coef N (k + 2) i) * qpoly ρ i := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [cstep k i hk, ← ha, ← hb, map_sub, map_add]
              ring
  have partA : ∀ ε : ℝ, constraintPoly N ρ ε 1 N =
      ∏ n ∈ Finset.Icc 1 N, (X + C (2 * (n : ℝ) * (2 * n + 2 * ρ - 1))) := by
    intro ε
    rw [closedForm ε N le_rfl, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun i hi => ?_), zero_add, coef, if_pos le_rfl, Nat.sub_self]
    · simp [gco, qpoly, lam]
    · rw [Finset.mem_range] at hi
      have : ∏ l ∈ Finset.range (N - i), ((N : ℝ) - i - 1 - l) = 0 := by
        apply Finset.prod_eq_zero (i := N - i - 1) (Finset.mem_range.mpr (by omega))
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
      rw [coef, if_pos (by omega), gco, this, mul_zero, zero_mul, map_zero, zero_mul]
  have detJac : ∀ ε x : ℝ, 0 ≤ x → ∀ m, m ≤ N → ∀ t : ℝ,
      (t • (1 : Matrix (Fin m) (Fin m) ℝ) + jac N ρ ε x m).det =
        (constraintPoly N ρ ε x m).eval t := by
    intro ε x hx m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm t
      match m, ih, hm with
      | 0, _, _ => simp [constraintPoly]
      | 1, _, _ =>
        rw [Matrix.det_unique]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, jac, Matrix.of_apply,
          if_true, smul_eq_mul, mul_one, constraintPoly, eval_add, eval_X, eval_C, dg,
          Fin.default_eq_zero, Fin.val_zero, Nat.sub_zero]
        push_cast
        ring
      | k + 2, ih, hm =>
        rw [det_sparse_front _ ?_ ?_]
        · have s1 :
              (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) + jac N ρ ε x (k + 2)).submatrix
                Fin.succ Fin.succ =
              t • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) + jac N ρ ε x (k + 1) := by
            ext i j
            simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, jac,
              Matrix.of_apply, Fin.succ_inj, Fin.val_succ, Matrix.one_apply]
            have e1 : k + 2 - ((i : ℕ) + 1) = k + 1 - i := by omega
            have e2 : k + 2 - ((j : ℕ) + 1) = k + 1 - j := by omega
            rw [e1, e2]
            simp only [add_left_inj]
          have s2 :
              (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) + jac N ρ ε x (k + 2)).submatrix
                (fun i : Fin k => i.succ.succ) (fun j : Fin k => j.succ.succ) =
              t • (1 : Matrix (Fin k) (Fin k) ℝ) + jac N ρ ε x k := by
            ext i j
            simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, jac,
              Matrix.of_apply, Fin.succ_inj, Fin.val_succ, Matrix.one_apply]
            have e1 : k + 2 - ((i : ℕ) + 1 + 1) = k - i := by omega
            have e2 : k + 2 - ((j : ℕ) + 1 + 1) = k - j := by omega
            rw [e1, e2]
            simp only [add_left_inj]
          rw [s1, s2, ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
          have hbb : 0 ≤ bb N ρ (k + 2) * x := by
            apply mul_nonneg _ hx
            unfold bb
            have hN : (k : ℝ) + 2 ≤ N := by exact_mod_cast hm
            push_cast
            have h1 : 0 ≤ 2 * ((N : ℝ) - (k + 2) + 1) + ρ - 1 := by linarith
            have h2 : 0 ≤ 2 * ((N : ℝ) - (k + 2) + 1) + ρ := by linarith
            have h3 : 0 ≤ ((k : ℝ) + 2) - 1 := by linarith
            positivity
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, jac, Matrix.of_apply]
          simp only [Fin.val_zero, Fin.val_one, zero_add, Nat.sub_zero,
            show (0 : Fin (k + 2)) ≠ 1 from by simp, show (1 : Fin (k + 2)) ≠ 0 from by simp,
            if_true, if_false, smul_eq_mul, mul_one, mul_zero, zero_add]
          rw [if_neg (by norm_num : (1 : ℕ) + 1 ≠ 0), Real.mul_self_sqrt hbb, constraintPoly]
          simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
          unfold dg bb
          push_cast
          ring
        · intro j
          have hne : (0 : Fin (k + 2)) ≠ j.succ.succ := (Fin.succ_ne_zero _).symm
          simp [jac, Matrix.one_apply_ne hne, hne]
        · intro i
          simp [jac, Fin.succ_ne_zero]
  have hermProd : ∀ (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (t : ℝ),
      (t • (1 : Matrix (Fin N) (Fin N) ℝ) + A).det = ∏ i, (t + hA.eigenvalues i) := by
    intro A hA t
    have h1 := Matrix.eval_charpoly A (-t)
    rw [hA.charpoly_eq] at h1
    have h2 : Matrix.scalar (Fin N) (-t) - A = -(t • (1 : Matrix (Fin N) (Fin N) ℝ) + A) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply]
      split_ifs <;> ring
    rw [h2, Matrix.det_neg, eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id, Fintype.card_fin] at h1
    have h3 : ∏ i, (-t - hA.eigenvalues i) = (-1) ^ N * ∏ i, (t + hA.eigenvalues i) := by
      rw [show (-1 : ℝ) ^ N = (-1) ^ (Finset.univ : Finset (Fin N)).card by simp,
        ← Finset.prod_neg]
      refine Finset.prod_congr rfl fun i _ => ?_
      ring
    rw [h3] at h1
    have h4 : ((-1 : ℝ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_left_cancel₀ h4 h1).symm
  have jacHerm : ∀ (ε x : ℝ) (m : ℕ), (jac N ρ ε x m).IsHermitian := by
    intro ε x m
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [jac, Matrix.of_apply, star_trivial]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg (Ne.symm hij), if_neg hij]
      by_cases h1 : (j : ℕ) + 1 = i
      · rw [if_pos h1, if_neg (by omega), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : (i : ℕ) + 1 = j
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h1, if_neg h2]
  have polyEq : ∀ ε x : ℝ, 0 ≤ x →
      constraintPoly N ρ ε x N = ∏ i, (X + C ((jacHerm ε x N).eigenvalues i)) := by
    intro ε x hx
    apply Polynomial.funext
    intro t
    rw [← detJac ε x hx N le_rfl t, hermProd _ (jacHerm ε x N) t, eval_prod]
    simp only [eval_add, eval_X, eval_C]
  have jacOnePosDef : ∀ ε : ℝ, (jac N ρ ε 1 N).PosDef := by
    intro ε
    have hA := jacHerm ε 1 N
    rw [hA.posDef_iff_eigenvalues_pos]
    intro i
    have e := (polyEq ε 1 zero_le_one).symm.trans (partA ε)
    have h0 := congrArg (eval (-(hA.eigenvalues i))) e
    rw [eval_prod, eval_prod] at h0
    simp only [eval_add, eval_X, eval_C] at h0
    have hl : ∏ j, (-(hA.eigenvalues i) + hA.eigenvalues j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
    rw [hl] at h0
    obtain ⟨n, hn, hz⟩ := Finset.prod_eq_zero_iff.mp h0.symm
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have : hA.eigenvalues i = 2 * (n : ℝ) * (2 * n + 2 * ρ - 1) := by linarith
    rw [this]
    have : (0 : ℝ) < 2 * n + 2 * ρ - 1 := by linarith
    positivity
  refine ⟨partA, fun ε hε x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  set s := Real.sqrt x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hx.le
  set D : Fin N → ℝ := fun i => dg N ρ ε x (N - i) - s * dg N ρ ε 1 (N - i) with hD
  have hsplit : jac N ρ ε x N = s • jac N ρ ε 1 N + Matrix.diagonal D := by
    ext i j
    simp only [jac, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      smul_eq_mul, hD]
    by_cases hij : i = j
    · subst hij; simp only [if_true]; ring
    · simp only [if_neg hij, add_zero]
      split_ifs
      · rw [Real.sqrt_mul' _ hx0, mul_one, mul_comm]
      · rw [Real.sqrt_mul' _ hx0, mul_one, mul_comm]
      · ring
  have hDnn : 0 ≤ D := by
    intro i
    simp only [hD, Pi.zero_apply]
    have hk : ((N - (i : ℕ) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N i
    have hk0 : (0 : ℝ) ≤ ((N - (i : ℕ) : ℕ) : ℝ) := Nat.cast_nonneg _
    set k : ℝ := ((N - (i : ℕ) : ℕ) : ℝ)
    have e : dg N ρ ε x (N - i) - s * dg N ρ ε 1 (N - i) =
        2 * k * (s - 1) * ((4 * N + 2 * ρ - 2 * k + 2 * ε + 1) * s + 2 * (k + ε)) := by
      unfold dg; rw [← hs2]; ring
    rw [e]
    have hc : 0 ≤ 4 * (N : ℝ) + 2 * ρ - 2 * k + 2 * ε + 1 := by linarith
    have h1 : 0 ≤ s - 1 := by linarith
    have h2 : 0 ≤ (4 * N + 2 * ρ - 2 * k + 2 * ε + 1) * s + 2 * (k + ε) := by positivity
    positivity
  have hPD : (jac N ρ ε x N).PosDef := by
    rw [hsplit]
    exact ((jacOnePosDef ε).smul (by linarith : (0 : ℝ) < s)).add_posSemidef
      (Matrix.PosSemidef.diagonal hDnn)
  refine ⟨fun i hi => ?_, fun y hy => ?_⟩
  · rw [polyEq ε x hx0]
    rw [Finset.prod_X_add_C_coeff _ _ (by simpa using hi)]
    refine Finset.sum_pos (fun t _ => Finset.prod_pos fun j _ => ?_) ?_
    · exact hPD.eigenvalues_pos j
    · exact Finset.powersetCard_nonempty.mpr (Nat.sub_le _ _)
  · rw [polyEq ε x hx0, eval_prod]
    refine (Finset.prod_pos fun j _ => ?_).ne'
    rw [eval_add, eval_X, eval_C]
    linarith [hPD.eigenvalues_pos j]

#print axioms claim
#print axioms result

end D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
