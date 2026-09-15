/- GID: D5/S3/Observer/Monodromy/ExteriorSquareContraction
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/ExteriorSquareContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partial contraction recovers a natural operator and detects rank-one nilpotence from its exterior-square square. -/

import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic

/-!
# Partial contractions of the genuine second additive compound

Bivectors are represented by skew-symmetric coefficient matrices. The actual
induced derivation is B |-> X B + B X^t. No exterior operator is supplied as a
free table. Contractions of its first and second powers are computed from matrix
multiplication. In dimensions with n-2 and n-4 nonzero, a trace-zero operator
whose second additive compound squares to zero is itself square-zero and has
an explicit outer-product factorization.

This is a concrete additive-compound result. The companion primitive module
transfers its hypotheses from the actual primitive subspace. It does not
establish that a geometric local system has an exterior-square lift.
Prior art: Ofir--Margaliot, arXiv:2401.02100, compound/Kronecker formulas;
Dey--Ofir--Grussler, arXiv:2605.27682, multiplicative compound inversion.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.ExteriorSquareContraction

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- Coefficient matrix of the actual bivector e_i wedge e_j. -/
def wedgeUnit (i j : I) : Matrix I I K :=
  Matrix.single i j 1 - Matrix.single j i 1

/-- The natural action on bivector coefficients, extended linearly to all matrices. -/
def action (X : Matrix I I K) : Matrix I I K →ₗ[K] Matrix I I K where
  toFun B := X * B + B * X.transpose
  map_add' B C := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c B := by
    simp [Matrix.mul_smul, Matrix.smul_mul, smul_add]

@[simp] theorem action_apply (X B : Matrix I I K) :
    action X B = X * B + B * X.transpose := rfl

theorem wedgeUnit_skew (i j : I) :
    (wedgeUnit (K := K) i j).transpose = -wedgeUnit i j := by
  simp only [wedgeUnit, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]

private theorem left_wedge_entry (A : Matrix I I K) (k l i j : I) :
    (A * wedgeUnit k l) i j =
      (if j = l then A i k else 0) - (if j = k then A i l else 0) := by
  classical
  simp [wedgeUnit, Matrix.mul_sub, Matrix.mul_apply, Matrix.single]

private theorem right_wedge_entry (A : Matrix I I K) (k l i j : I) :
    (wedgeUnit k l * A.transpose) i j =
      (if i = k then A j l else 0) - (if i = l then A j k else 0) := by
  classical
  simp [wedgeUnit, Matrix.sub_mul, Matrix.mul_apply, Matrix.single,
    Matrix.transpose_apply]

private theorem sandwich_wedge_entry (X : Matrix I I K) (k l i j : I) :
    (X * wedgeUnit k l * X.transpose) i j = X i k * X j l - X i l * X j k := by
  classical
  simp [Matrix.mul_apply, left_wedge_entry, Matrix.transpose_apply,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

theorem action_wedge_entry (X : Matrix I I K) (k l i j : I) :
    action X (wedgeUnit k l) i j =
      (if j = l then X i k else 0) - (if j = k then X i l else 0) +
      (if i = k then X j l else 0) - (if i = l then X j k else 0) := by
  rw [action_apply]
  simp only [Matrix.add_apply, left_wedge_entry, right_wedge_entry]
  ring

/-- Explicit left inverse on trace-zero natural operators, before primitive projection. -/
theorem first_contraction (X : Matrix I I K) (i k : I) :
    (∑ j, action X (wedgeUnit k j) i j) =
      ((Fintype.card I : K) - 2) * X i k +
        (if i = k then Matrix.trace X else 0) := by
  classical
  simp_rw [action_wedge_entry]
  by_cases h : i = k
  · subst k
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Matrix.trace, Matrix.diag_apply, nsmul_eq_mul]
    <;> ring
  · simp [h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Matrix.trace, Matrix.diag_apply, nsmul_eq_mul]
    <;> ring

/-- The square of the actual derivation, not a definition of a nilpotence label. -/
theorem action_square_expansion (X B : Matrix I I K) :
    action X (action X B) = (X * X) * B +
      (2 : K) • (X * B * X.transpose) + B * (X * X).transpose := by
  simp only [action_apply, Matrix.transpose_mul, two_smul]
  noncomm_ring

theorem action_square_wedge_entry (X : Matrix I I K) (k l i j : I) :
    action X (action X (wedgeUnit k l)) i j =
      (if j = l then (X * X) i k else 0) -
      (if j = k then (X * X) i l else 0) +
      2 * (X i k * X j l - X i l * X j k) +
      (if i = k then (X * X) j l else 0) -
      (if i = l then (X * X) j k else 0) := by
  rw [action_square_expansion]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    left_wedge_entry, right_wedge_entry, sandwich_wedge_entry]
  ring

/-- The partial contraction of the square detects X^2 with coefficient n-4. -/
theorem second_contraction (X : Matrix I I K) (i k : I) :
    (∑ j, action X (action X (wedgeUnit k j)) i j) =
      ((Fintype.card I : K) - 4) * (X * X) i k +
      2 * Matrix.trace X * X i k +
      (if i = k then Matrix.trace (X * X) else 0) := by
  classical
  simp_rw [action_square_wedge_entry]
  have hprod : (∑ j, X i j * X j k) = (X * X) i k := rfl
  have htrace : (∑ j, X i k * X j j) = X i k * Matrix.trace X := by
    simp [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  by_cases h : i = k
  · subst k
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hprod, htrace, Matrix.trace, Matrix.diag_apply, nsmul_eq_mul]
    <;> ring
  · simp [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hprod, htrace, Matrix.trace, Matrix.diag_apply, nsmul_eq_mul]
    <;> ring

/-- Quadratic exterior nilpotence forces actual natural nilpotence and every
2-by-2 minor to vanish. In particular natural rank one is not an input. -/
theorem square_zero_and_minors (X : Matrix I I K)
    (htrace : Matrix.trace X = 0) (h2 : (2 : K) ≠ 0)
    (hn2 : (Fintype.card I : K) - 2 ≠ 0)
    (hn4 : (Fintype.card I : K) - 4 ≠ 0)
    (hquad : ∀ k l, action X (action X (wedgeUnit k l)) = 0) :
    X * X = 0 ∧
      ∀ i j k l, X i k * X j l = X i l * X j k := by
  have hc (i k : I) :
      ((Fintype.card I : K) - 4) * (X * X) i k +
        (if i = k then Matrix.trace (X * X) else 0) = 0 := by
    have h := second_contraction X i k
    simp only [hquad, Matrix.zero_apply, Finset.sum_const_zero, htrace,
      mul_zero, zero_mul, add_zero] at h
    exact h.symm
  have hsum : (∑ i, (((Fintype.card I : K) - 4) * (X * X) i i +
      Matrix.trace (X * X))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simpa using hc i i
  have ht2 : Matrix.trace (X * X) = 0 := by
    have he : (2 * ((Fintype.card I : K) - 2)) * Matrix.trace (X * X) = 0 := by
      calc
        _ = ∑ i, (((Fintype.card I : K) - 4) * (X * X) i i +
            Matrix.trace (X * X)) := by
          simp [Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.trace,
            Matrix.diag_apply, nsmul_eq_mul]
          <;> ring
        _ = 0 := hsum
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero h2 hn2)
  have hXX : X * X = 0 := by
    ext i k
    have h := hc i k
    simp only [ht2, ite_self, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hn4
  refine ⟨hXX, ?_⟩
  intro i j k l
  have h := congrArg (fun M : Matrix I I K => M i j) (hquad k l)
  rw [action_square_wedge_entry, hXX] at h
  simp only [Matrix.zero_apply, ite_self, sub_self, zero_add, add_zero, sub_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2)

/-- A nonzero pivot explicitly recovers the rank-one factorization and its
nilpotent scalar contraction. No rank or Jordan-form classification is assumed. -/
theorem pivot_factorization (X : Matrix I I K)
    (hXX : X * X = 0)
    (hminor : ∀ i j k l, X i k * X j l = X i l * X j k)
    (p q : I) (hpq : X p q ≠ 0) :
    (∀ i j, X i j = X i q * (X p j / X p q)) ∧
      (∑ j, (X p j / X p q) * X j q) = 0 := by
  constructor
  · intro i j
    have h := hminor i p j q
    have h' : X i j = (X i q * X p j) / X p q := (eq_div_iff hpq).mpr h
    simpa [mul_div_assoc] using h'
  · calc
      (∑ j, (X p j / X p q) * X j q) =
          (∑ j, X p j * X j q) / X p q := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (X * X) p q / X p q := rfl
      _ = 0 := by rw [hXX]; simp

/-- Complete outer-product output, including the zero operator. -/
theorem exterior_square_zero_rank_one (X : Matrix I I K)
    (htrace : Matrix.trace X = 0) (h2 : (2 : K) ≠ 0)
    (hn2 : (Fintype.card I : K) - 2 ≠ 0)
    (hn4 : (Fintype.card I : K) - 4 ≠ 0)
    (hquad : ∀ k l, action X (action X (wedgeUnit k l)) = 0) :
    X * X = 0 ∧ ∃ u v : I → K,
      (∀ i j, X i j = u i * v j) ∧ (∑ j, v j * u j) = 0 := by
  obtain ⟨hXX, hminor⟩ := square_zero_and_minors X htrace h2 hn2 hn4 hquad
  refine ⟨hXX, ?_⟩
  by_cases hzero : X = 0
  · refine ⟨0, 0, ?_, ?_⟩ <;> simp [hzero]
  · have hpivot : ∃ p q, X p q ≠ 0 := by
      by_contra h
      push_neg at h
      apply hzero
      ext i j
      exact h i j
    obtain ⟨p, q, hpq⟩ := hpivot
    exact ⟨fun i => X i q, fun j => X p j / X p q,
      pivot_factorization X hXX hminor p q hpq⟩

#print axioms first_contraction
#print axioms second_contraction
#print axioms exterior_square_zero_rank_one

end D5.S3.Observer.Monodromy.ExteriorSquareContraction
