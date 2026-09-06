/- GID: D5/S3/Weil/ThirdOrderCumulantMatrix
   generality: G
   mirror-B: D5/B/S3/Weil/ThirdOrderCumulantMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-order cumulants give a positive matrix whose determinant is the reversed cubic. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/- Library-search audit trail (2026-09-06):
   * Repository searches for `K_3`, `K3`, `chi_4`, `chi_6`, `P_3`, cubic
     discriminants, principal minors, and positive definite matrices found no
     matching cumulant matrix. `D5.S3.Weil.ZetaLinear.Sylvester` concerns
     inertia subspaces, while `NewtonHankelRealRootCriterion` concerns a
     different Hankel real-root test; neither proves this bridge.
   * Pinned Mathlib searches found the exact reusable primitives
     `Matrix.det_fin_three`, `Matrix.eval_charpoly`,
     `Matrix.mem_spectrum_iff_isRoot_charpoly`,
     `Matrix.IsHermitian.posDef_iff_eigenvalues_pos`, and `Real.sq_sqrt`.
     No packaged three-by-three Sylvester criterion or this `K3` construction
     was found.
   * Searches across the pinned non-Mathlib Lean packages found no matching
     declaration. NyxID/Tavily searches for Lean Sylvester criteria and a
     tridiagonal cubic-discriminant theorem returned only general mathematical
     references, not a Lean implementation. No admissible third-party exact
     hit was found.
   * The remaining finite determinant computations and the bridge from the
     typed cubic root condition to matrix positivity are proved locally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial

namespace D5.S3.Weil.ThirdOrderCumulantMatrix

/-- The second, fourth, and sixth cumulants used by the third-order model. -/
structure ThirdOrderCumulants where
  chi2 : Real
  chi4 : Real
  chi6 : Real

/-- The positive fourth-order scale `u = -chi4`. -/
def u (c : ThirdOrderCumulants) : Real := -c.chi4

/-- The center of the cubic model. -/
def mu (c : ThirdOrderCumulants) : Real := c.chi2 / 6

/-- The normalized sixth-order displacement. -/
def r (c : ThirdOrderCumulants) : Real := c.chi6 / (60 * u c)

/-- The first squared off-diagonal coefficient. -/
def b1 (c : ThirdOrderCumulants) : Real := u c / 54

/-- The second squared off-diagonal coefficient. -/
def b2 (c : ThirdOrderCumulants) : Real := u c / 108 - r c ^ 2

/-- The strict discriminant inequalities stated for the third-order model. -/
def CubicDiscriminantCondition (c : ThirdOrderCumulants) : Prop :=
  0 < u c ∧ 3 * c.chi6 ^ 2 < 100 * u c ^ 3

/-- The centered characteristic cubic from the third-order cumulants. -/
def q3 (c : ThirdOrderCumulants) : Real[X] :=
  (X - C (mu c)) ^ 3 - C (u c / 36) * (X - C (mu c)) -
    C (c.chi6 / 3240)

/-- The root condition supplied by the preceding cubic analysis: every root
of `q3` is strictly positive. -/
def HasPositiveCubicRoots (c : ThirdOrderCumulants) : Prop :=
  ∀ x : Real, (q3 c).IsRoot x → 0 < x

/-- The coefficient-wise reversal of `q3`, written with positive powers. -/
def p3 (c : ThirdOrderCumulants) : Real[X] :=
  1 + C (3 * mu c) * X + C (3 * mu c ^ 2 - u c / 36) * X ^ 2 +
    C (mu c ^ 3 - u c * mu c / 36 + c.chi6 / 3240) * X ^ 3

/-- Formula (24), as an explicit real symmetric matrix. -/
def k3Matrix (c : ThirdOrderCumulants) : Matrix (Fin 3) (Fin 3) Real :=
  !![mu c, Real.sqrt (b1 c), 0;
     Real.sqrt (b1 c), mu c + r c, Real.sqrt (b2 c);
     0, Real.sqrt (b2 c), mu c - r c]

private def finOneToThree (i : Fin 1) : Fin 3 :=
  ⟨i.1, by omega⟩

private def finTwoToThree (i : Fin 2) : Fin 3 :=
  ⟨i.1, by omega⟩

/-- The upper-left one-by-one principal minor. -/
def leadingPrincipalMinorOne (A : Matrix (Fin 3) (Fin 3) Real) : Real :=
  Matrix.det (A.submatrix finOneToThree finOneToThree)

/-- The upper-left two-by-two principal minor. -/
def leadingPrincipalMinorTwo (A : Matrix (Fin 3) (Fin 3) Real) : Real :=
  Matrix.det (A.submatrix finTwoToThree finTwoToThree)

private theorem discriminant_coefficients_pos (c : ThirdOrderCumulants)
    (hdisc : CubicDiscriminantCondition c) :
    0 < b1 c ∧ 0 < b2 c := by
  have hu : 0 < u c := hdisc.1
  have hune : u c ≠ 0 := ne_of_gt hu
  constructor
  · simp only [b1]
    positivity
  · simp only [b2, r]
    rw [div_pow]
    have hu2 : 0 < u c ^ 2 := sq_pos_of_pos hu
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < (60 * u c) ^ 2)).2
    rw [show (60 * u c) ^ 2 = 3600 * u c ^ 2 by ring]
    nlinarith [hdisc.2]

private theorem k3_isHermitian (c : ThirdOrderCumulants) :
    (k3Matrix c).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k3Matrix]

/-- Under the strict discriminant inequality, formula (24) has exactly the
centered cubic `q3` as its characteristic polynomial. -/
theorem k3_charpoly_eq_q3 (c : ThirdOrderCumulants)
    (hdisc : CubicDiscriminantCondition c) :
    (k3Matrix c).charpoly = q3 c := by
  rcases discriminant_coefficients_pos c hdisc with ⟨hb1, hb2⟩
  have hune : u c ≠ 0 := ne_of_gt hdisc.1
  have hb1sq : Real.sqrt (b1 c) ^ 2 = b1 c := Real.sq_sqrt hb1.le
  have hb2sq : Real.sqrt (b2 c) ^ 2 = b2 c := Real.sq_sqrt hb2.le
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  simp only [q3, eval_sub, eval_pow, eval_X, eval_C, eval_mul]
  rw [Matrix.det_fin_three]
  simp [k3Matrix, Matrix.scalar_apply]
  ring_nf
  rw [hb1sq, hb2sq]
  unfold b1 b2 r
  field_simp [hune]
  ring

/-- The preregistered escape witness. The discriminant condition makes the
off-diagonal coefficients real and nonzero; the root condition, transported
through the computed characteristic polynomial, makes every Hermitian
eigenvalue positive. The same certificate records all three leading
Sylvester minors. -/
theorem K3_posdef_from_cubic_discriminant (c : ThirdOrderCumulants)
    (hdisc : CubicDiscriminantCondition c)
    (hroots : HasPositiveCubicRoots c) :
    0 < leadingPrincipalMinorOne (k3Matrix c) ∧
      0 < leadingPrincipalMinorTwo (k3Matrix c) ∧
      0 < Matrix.det (k3Matrix c) ∧
      (k3Matrix c).PosDef := by
  have hherm : (k3Matrix c).IsHermitian := k3_isHermitian c
  have hpos : (k3Matrix c).PosDef :=
    hherm.posDef_iff_eigenvalues_pos.mpr fun i ↦ by
      apply hroots (hherm.eigenvalues i)
      rw [← k3_charpoly_eq_q3 c hdisc]
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp
        (hherm.eigenvalues_mem_spectrum_real i)
  have hinj1 : Function.Injective finOneToThree := by
    intro i j hij
    apply Fin.ext
    simpa [finOneToThree] using congrArg (fun x : Fin 3 => x.1) hij
  have hinj2 : Function.Injective finTwoToThree := by
    intro i j hij
    apply Fin.ext
    simpa [finTwoToThree] using congrArg (fun x : Fin 3 => x.1) hij
  refine ⟨?_, ?_, hpos.det_pos, hpos⟩
  · exact (hpos.submatrix hinj1).det_pos
  · exact (hpos.submatrix hinj2).det_pos

/-- Reversing the centered cubic gives the determinant of `I + v K3`. -/
theorem k3_determinant_reversal (c : ThirdOrderCumulants)
    (hdisc : CubicDiscriminantCondition c) (v : Real) :
    Matrix.det (1 + v • k3Matrix c) = (p3 c).eval v := by
  rcases discriminant_coefficients_pos c hdisc with ⟨hb1, hb2⟩
  have hune : u c ≠ 0 := ne_of_gt hdisc.1
  have hb1sq : Real.sqrt (b1 c) ^ 2 = b1 c := Real.sq_sqrt hb1.le
  have hb2sq : Real.sqrt (b2 c) ^ 2 = b2 c := Real.sq_sqrt hb2.le
  rw [Matrix.det_fin_three]
  simp only [p3, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_pow]
  simp [k3Matrix]
  ring_nf
  rw [hb1sq, hb2sq]
  unfold b1 b2 r
  field_simp [hune]
  ring

/-- The third-order slice: the typed root condition produces the positive
matrix in formula (24), and its centered characteristic cubic reverses to
`det (I + v K3) = P3(v)`. -/
theorem third_order_cumulant_positive_matrix_reversal
    (c : ThirdOrderCumulants)
    (hdisc : CubicDiscriminantCondition c)
    (hroots : HasPositiveCubicRoots c) (v : Real) :
    (k3Matrix c).PosDef ∧
      Matrix.det (1 + v • k3Matrix c) = (p3 c).eval v := by
  have hK3 := K3_posdef_from_cubic_discriminant c hdisc hroots
  exact ⟨hK3.2.2.2, k3_determinant_reversal c hdisc v⟩

#print axioms k3_charpoly_eq_q3
#print axioms K3_posdef_from_cubic_discriminant
#print axioms k3_determinant_reversal
#print axioms third_order_cumulant_positive_matrix_reversal

end D5.S3.Weil.ThirdOrderCumulantMatrix
