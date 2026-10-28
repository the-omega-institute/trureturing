/- GID: D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraPolynomialRuns
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rational bivariate polynomials count the actual positive run-length vectors. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraRunCompositions
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Polynomial weights for simultaneous positive run lengths on the two axes. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraPolynomialRuns
open MiuraRunCompositions
open scoped BigOperators
open MvPolynomial

/-- The shifted falling product in one of the two physical dimension variables. -/
noncomputable def falling (axis : Fin 2) (u k : ℕ) : MvPolynomial (Fin 2) ℚ :=
  ∏ t ∈ Finset.range k, (X axis - C ((u + 1 + t : ℕ) : ℚ))

private theorem falling_succ (axis : Fin 2) (u k : ℕ) :
    falling axis u (k + 1) = falling axis u k * (X axis - C ((u + 1 + k : ℕ) : ℚ)) := by
  simp only [falling, Finset.prod_range_succ]

private theorem eval_falling (v : Fin 2 → ℚ) (axis : Fin 2) (u k : ℕ) :
    eval v (falling axis u k) =
      (descPochhammer ℚ k).eval (v axis - ((u + 1 : ℕ) : ℚ)) := by
  induction k with
  | zero => simp [falling]
  | succ k ih =>
    rw [falling_succ, eval_mul, eval_sub, eval_X, eval_C, ih,
      descPochhammer_succ_eval]
    push_cast
    ring

private theorem falling_degree_le (axis : Fin 2) (u k : ℕ) :
    (falling axis u k).totalDegree ≤ k := by
  induction k with
  | zero => simp [falling]
  | succ k ih =>
    rw [falling_succ]
    have hf : (X axis - C ((u + 1 + k : ℕ) : ℚ)).totalDegree ≤ 1 := by
      simpa only [totalDegree_X] using totalDegree_sub_C_le (X axis) ((u + 1 + k : ℕ) : ℚ)
    exact (totalDegree_mul _ _).trans (by omega)

/-- One occupied-axis count and one positive-run count determine a rational weight. -/
noncomputable def runPolynomial (axis : Fin 2) (u r : ℕ) : MvPolynomial (Fin 2) ℚ :=
  falling axis u (r - 1) * C ((Nat.factorial (r - 1) : ℚ)⁻¹)

private theorem run_degree_le (axis : Fin 2) (u r : ℕ) :
    (runPolynomial axis u r).totalDegree ≤ r - 1 := by
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, Nat.add_zero] using (falling_degree_le axis u (r - 1))

private theorem eval_run (v : Fin 2 → ℚ) (axis : Fin 2) (u r M : ℕ)
    (hval : v axis = (M : ℚ)) (hr : 1 ≤ r) (hM : u + r ≤ M) :
    eval v (runPolynomial axis u r) = (Nat.card (PositiveLengths (M - u) r) : ℚ) := by
  rw [runPolynomial, eval_mul, eval_C, eval_falling, hval,
    positive_lengths_card (M - u) r hr (by omega)]
  have hcast : (M : ℚ) - ((u + 1 : ℕ) : ℚ) = ((M - u - 1 : ℕ) : ℚ) := by
    have hle : u + 1 ≤ M := by omega
    rw [show M - u - 1 = M - (u + 1) by omega, Nat.cast_sub hle]
  rw [hcast]
  simpa only [div_eq_mul_inv] using
    (Nat.cast_choose_eq_descPochhammer_div ℚ (M - u - 1) (r - 1)).symm

/-- The two axes are represented by distinct variables of the same polynomial. -/
noncomputable def jointRunPolynomial (u v r s : ℕ) : MvPolynomial (Fin 2) ℚ :=
  runPolynomial 0 u r * runPolynomial 1 v s

/-- The actual Cartesian product of positive vectors has this exact polynomial value. -/
theorem joint_run_polynomial_eval (u v r s m n : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hm : u + r ≤ m) (hn : v + s ≤ n) :
    eval (fun i : Fin 2 => if i = 0 then (m : ℚ) else (n : ℚ))
        (jointRunPolynomial u v r s) =
      (Nat.card (PositiveLengths (m - u) r × PositiveLengths (n - v) s) : ℚ) := by
  rw [jointRunPolynomial, eval_mul,
    eval_run _ 0 u r m (by simp) hr hm,
    eval_run _ 1 v s n (by norm_num) hs hn,
    Nat.card_prod, Nat.cast_mul]

/-- The total degree uses the sum of both actual run-vector exponents. -/
theorem joint_run_polynomial_degree_le (u v r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (jointRunPolynomial u v r s).totalDegree ≤ r + s - 2 := by
  have h0 := run_degree_le 0 u r
  have h1 := run_degree_le 1 v s
  exact (totalDegree_mul _ _).trans (by omega)

end D5.S3.Combinatorics.Geometry.MiuraPolynomialRuns
