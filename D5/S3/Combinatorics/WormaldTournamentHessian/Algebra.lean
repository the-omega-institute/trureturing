/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Algebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Algebra
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow, mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement, mathlib/module/Mathlib.LinearAlgebra.Matrix.Gershgorin, mathlib/module/Mathlib.NumberTheory.Zsqrtd.GaussianInt]
   utility: none
   digest: Determinant squares, difference minors, and mixed inverse variations. -/

/-
admission_basis: escape-witness
Utility is none: arbitrary finite-dimensional identities and complex C2 local
solutions, not finite certificates. Direct frozen D5 dependencies: none.
Live content: alpha_second_single and alpha_second_const.
Judgments use the bypass test; binding and normalization do not create content.

name | proof_shape | escape_witness | consumers | frozen deps
skewDiag | bind-only | none | shiftedDetNeZero, shiftedDetPureImaginary | frozen deps: none
  Unfold subtraction and transpose; diagonal cancellation is normalization.
skewNormLe | bind-only | none | shiftedDetNeZero | frozen deps: none
  Unfold Boolean entries and normalize the four cases.
shiftedDetNeZero | bind-only | none | algebraicRatioRational, shiftedNegativeDetNeZero | frozen deps: none
  Instantiate Mathlib strict diagonal dominance; normalize the bounded row sum and diagonal.
shiftedDetPureImaginary | bind-only | none | imaginaryShiftIntegral | frozen deps: none
  Transpose/conjugate determinant laws and odd-sign arithmetic; no new nonnormalizing fact.
imaginaryShiftIntegral | bind-only | none | algebraicRatioRational | frozen deps: none
  Use the Gaussian-integer determinant and map_det; the purely imaginary projection normalizes.
algebraicRatioRational | bind-only | none | algebraicSquareIdentity | frozen deps: none
  Instantiate integral casts and nonzero quotients; denominator integrality comes from the consumed helper.
algebraicSquareIdentity | bind-only | none | regularAlgebraicSquare | frozen deps: none
  Determinant multiplicativity and transpose laws plus normalized quadratic factorizations and the rational quotient.
regularAlgebraicSquare | bind-only | none | result | frozen deps: none
  Instantiate algebraicSquareIdentity with regularOdd; both expanded inputs are bind-only.
bridgeU | bind-only (definition) | none | bridgeU_det, bridgeU_congr | frozen deps: none
  Explicit change-of-basis matrix definition; no proved assertion.
bridgeU_det | bind-only | none | bridge_det | frozen deps: none
  Instantiate the existing block determinant formula; normalize the one-dimensional Schur complement.
bridgeH | bind-only (definition) | none | bridgeU_congr, bridge_det | frozen deps: none
  Difference-minor matrix definition; no proved assertion.
bridgeU_entry_left | bind-only | none | bridgeU_congr | frozen deps: none
  Unfold the block matrix and normalize its entries.
bridgeU_entry_right | bind-only | none | bridgeU_congr | frozen deps: none
  Unfold the block matrix and normalize its final column.
bridgeU_congr | bind-only | none | bridge_det | frozen deps: none
  Multiply the explicit block matrices and normalize their entries using the given row/column sums.
bridge_det | bind-only | none | differenceMinor_det | frozen deps: none
  Apply determinant multiplicativity and block determinant laws to bridgeU_congr; cancel the nonzero dimension factor.
skew_resolvent_det | bind-only | none | skew_difference_det | frozen deps: none
  Normalize the two resolvent products and apply inverse cancellation plus determinant multiplicativity; no new analytic content.
bridgeFinEquiv | bind-only (definition) | none | differenceMinor_det | frozen deps: none
  Composition of existing finite index equivalences; no proved assertion.
differenceMinor_det | bind-only | none | skew_difference_det | frozen deps: none
  Transport bridge_det along the explicit finite equivalence and normalize the indices.
inverse_row_sum | bind-only | none | inverse_col_sum, resolvent_row_col_sum, calH_closedForm | frozen deps: none
  Instantiate existing inverse action on a constant-vector eigenrelation and normalize the row sums.
inverse_col_sum | bind-only | none | resolvent_row_col_sum, calH_closedForm | frozen deps: none
  Instantiate inverse_row_sum on the transpose and normalize.
resolvent_row_col_sum | bind-only | none | skew_difference_det | frozen deps: none
  Substitute inverse_row_sum/inverse_col_sum into the finite sums and normalize.
skew_difference_det | bind-only | none | calH_closedForm | frozen deps: none
  Combine the consumed difference-minor and resolvent determinant formulas; the remaining sign and scalar arithmetic normalize.
diagonalCLM | bind-only (definition) | none | inverseQDeriv, inverseQ_hasFDerivAt | frozen deps: none
  Linear/continuous packaging of Matrix.diagonal; no proved assertion.
sumEntriesCLM | bind-only (definition) | none | alpha_hasFDerivAt, alpha_fderiv_single | frozen deps: none
  Linear/continuous packaging of the sum of all entries; no proved assertion.
matrixInverse_hasFDerivAt | bind-only | none | inverse_hasFDerivAt | frozen deps: none
  Direct hasFDerivAt_ringInverse instantiation after rewriting matrix inverse to ringInverse.
inverseQ | bind-only (definition) | none | alpha, inverseQ_hasFDerivAt | frozen deps: none
  Auxiliary diagonal-minus-skew resolvent definition; no proved assertion.
alpha | bind-only (definition) | none | alpha_hasFDerivAt, calH_closedForm | frozen deps: none
  Auxiliary inverse-entry-sum definition; no proved assertion.
inverseQDeriv | bind-only (definition) | none | inverseQ_hasFDerivAt, inverseQDeriv_single | frozen deps: none
  Explicit derivative continuous linear map definition; no proved assertion.
inverseQ_hasFDerivAt | bind-only | none | inverse_hasFDerivAt | frozen deps: none
  Instantiate inverse-coordinate, Pi, diagonal and constant-subtraction derivative rules.
inverse_hasFDerivAt | bind-only | none | alpha_hasFDerivAt, inverse_fderiv_single, row_fderiv_single, col_fderiv_single, alpha_fderiv_single, alpha_second_single | frozen deps: none
  Direct composition of matrixInverse_hasFDerivAt and inverseQ_hasFDerivAt.
alpha_hasFDerivAt | bind-only | none | alpha_fderiv_single | frozen deps: none
  Direct composition with sumEntriesCLM.
inverseQ_contDiffAt | bind-only | none | inverse_contDiffAt, alpha_second_single | frozen deps: none
  Instantiate coordinatewise inverse, Pi and linear-map smoothness rules.
inverse_contDiffAt | bind-only | none | alpha_contDiffAt | frozen deps: none
  Instantiate contDiffAt_ringInverse and compose with inverseQ_contDiffAt.
alpha_contDiffAt | bind-only | none | calH_closedForm | frozen deps: none
  Direct smooth composition with sumEntriesCLM.
inverseQDeriv_single | bind-only | none | inverse_fderiv_single | frozen deps: none
  Unfold the explicit diagonal continuous linear map and normalize single-coordinate entries.
inverse_fderiv_single | bind-only | none | row_fderiv_single, col_fderiv_single, alpha_fderiv_single | frozen deps: none
  Instantiate the inverse derivative on one coordinate and normalize the diagonal matrix product to an outer product.
rowSumCLM | bind-only (definition) | none | row_fderiv_single, alpha_second_single | frozen deps: none
  Linear/continuous packaging of a row sum; no proved assertion.
colSumCLM | bind-only (definition) | none | col_fderiv_single, alpha_second_single | frozen deps: none
  Linear/continuous packaging of a column sum; no proved assertion.
row_fderiv_single | bind-only | none | alpha_second_single | frozen deps: none
  Apply rowSumCLM to inverse_fderiv_single and normalize the finite sum.
col_fderiv_single | bind-only | none | alpha_second_single | frozen deps: none
  Apply colSumCLM to inverse_fderiv_single and normalize the finite sum.
alpha_fderiv_single | bind-only | none | alpha_second_single, alpha_first_const | frozen deps: none
  Apply sumEntriesCLM to inverse_fderiv_single and normalize the product of row/column sums; no repeated inverse-derivative proof.
inverse_square_hasDerivAt | bind-only | none | alpha_second_single | frozen deps: none
  Instantiate inverse, power and scalar-multiple derivative rules; scalar normalization.
alpha_second_single | content | local heq and hh: neighbourhood first-derivative germ and its coupled-product derivative | alpha_second_const | frozen deps: none
  Own step: establish the first-derivative identity on an invertible neighbourhood and differentiate its coupled coefficient/row/column factors to obtain the full mixed inverse-entry second variation. A pointwise first-derivative value alone does not supply this germ or mixed derivative.
alpha_first_const | bind-only | none | calH_closedForm | frozen deps: none
  Substitute the constant-point row and column sums in alpha_fderiv_single; scalar normalization.
alpha_second_const | content | alpha_second_single: live inverse-entry mixed second variation | calH_closedForm | frozen deps: none
  Propagation: substitute row/column sums in the live alpha_second_single mixed-derivative relation; scalar normalization does not bypass that relation.
-/

module

public import D5.S3.Combinatorics.WormaldTournamentHessian.Defs

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # Regular tournament Hessians: algebra -/

public section

open scoped Topology ContDiff Matrix Matrix.Norms.Operator
open Matrix Filter
open D5.S3.Combinatorics.WormaldTournamentHessian.Defs

namespace D5.S3.Combinatorics.WormaldTournamentHessian.Algebra

private theorem skewDiag {d : ℕ} (A : Fin d → Fin d → Bool) (i : Fin d) :
    skewAdjacency A i i = 0 := by simp [skewAdjacency]

private theorem skewNormLe {d : ℕ} (A : Fin d → Fin d → Bool) (i j : Fin d) :
    ‖(skewAdjacency A i j : ℂ)‖ ≤ 1 := by
  simp only [skewAdjacency, Matrix.sub_apply, Matrix.transpose_apply, adjacency]
  split <;> split <;> norm_num

theorem shiftedDetNeZero {d : ℕ} (A : Fin d → Fin d → Bool) (c : ℂ)
    (hc : ‖c‖ = d) :
    ((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i,
      ‖((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1) i j‖) ≤ (d - 1 : ℕ) := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using
          skewNormLe A i j
      _ = _ := by simp
  have hdiag : ((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1) i i = c := by
    simp [skewDiag]
  rw [hdiag, hc]
  have hd : 0 < d := Fin.pos i
  exact lt_of_le_of_lt hsum (by exact_mod_cast Nat.sub_lt hd (by omega : 0 < 1))

private theorem shiftedDetPureImaginary {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : Odd d) :
    (((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det).re = 0 := by
  let M := (skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1
  have hstar : M.conjTranspose = -M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.conjTranspose_apply, skewDiag]
    · simp [M, Matrix.conjTranspose_apply, skewAdjacency, adjacency,
        hij, Ne.symm hij]
  have heq : star M.det = -M.det := by
    rw [← Matrix.det_conjTranspose, hstar, Matrix.det_neg]
    simp only [Fintype.card_fin, hd.neg_one_pow, neg_one_mul]
  have hr := congrArg Complex.re heq
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  linarith

private theorem imaginaryShiftIntegral {d : ℕ} (A : Fin d → Fin d → Bool) (hd : Odd d) :
    ∃ b : ℤ, ((skewAdjacency A).map (Int.castRingHom ℂ) +
      (Complex.I * d) • 1).det = (b : ℂ) * Complex.I := by
  let Z : Matrix (Fin d) (Fin d) GaussianInt := fun i j =>
    ⟨skewAdjacency A i j, if i = j then (d : ℤ) else 0⟩
  have hm : Z.map GaussianInt.toComplex =
      (skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1 := by
    ext i j
    change GaussianInt.toComplex ⟨skewAdjacency A i j,
      if i = j then (d : ℤ) else 0⟩ = _
    by_cases hij : i = j
    · simp [GaussianInt.toComplex_def', hij, Matrix.smul_apply]
      ring
    · simp [GaussianInt.toComplex_def', hij, Matrix.smul_apply]
  have hdet : (Z.det : ℂ) =
      ((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det := by
    rw [RingHom.map_det]
    change (Z.map GaussianInt.toComplex).det = _
    rw [hm]
  have hr := shiftedDetPureImaginary A hd
  rw [← hdet] at hr
  have hre : Z.det.re = 0 := by
    have hr' : (Z.det.re : ℝ) = 0 := (GaussianInt.intCast_re Z.det).trans hr
    exact_mod_cast hr'
  refine ⟨Z.det.im, ?_⟩
  rw [← hdet, GaussianInt.toComplex_def, hre]
  simp

private theorem algebraicRatioRational {d : ℕ} (A : Fin d → Fin d → Bool) (hd : Odd d) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ)).det /
        (((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det /
          Complex.I)) = (q : ℂ) := by
  obtain ⟨b, hb⟩ := imaginaryShiftIntegral A hd
  have hI : ‖Complex.I * (d : ℂ)‖ = (d : ℝ) := by simp
  have hD : ‖(d : ℂ)‖ = (d : ℝ) := by simp
  have hb0 : b ≠ 0 := by
    intro h
    have := shiftedDetNeZero A (Complex.I * d) hI
    exact this (by simpa only [h, Int.cast_zero, zero_mul] using hb)
  let a : ℤ := ((d : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ) + skewAdjacency A).det
  have ha : (a : ℂ) = ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (skewAdjacency A).map (Int.castRingHom ℂ)).det := by
    dsimp [a]
    rw [Int.cast_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, Matrix.natCast_apply, hij]
  have ha0 : a ≠ 0 := by
    intro h
    have hn := shiftedDetNeZero A (d : ℂ) hD
    rw [add_comm] at hn
    rw [← ha, h, Int.cast_zero] at hn
    exact hn rfl
  refine ⟨(a : ℚ) / b, div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hb0), ?_⟩
  rw [← ha, hb]
  push_cast
  rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]

private theorem algebraicSquareIdentity {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : Odd d) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det) = (q : ℂ)^2 := by
  let S := (skewAdjacency A).map (Int.castRingHom ℂ)
  have hst : S.transpose = -S := by
    ext i j
    simp [S, skewAdjacency, adjacency]
  have hreal : ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - S).det =
      ((d : ℂ) • 1 + S).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, hst, sub_neg_eq_add]
  have himag : (S - (Complex.I * d) • 1).det =
      -(S + (Complex.I * d) • 1).det := by
    have heq : S - (Complex.I * d) • 1 = -(S + (Complex.I * d) • 1).transpose := by
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hst]
      abel
    rw [heq, Matrix.det_neg, Matrix.det_transpose]
    simp [hd.neg_one_pow]
  have hm : ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + S) *
      ((d : ℂ) • 1 - S) = (d : ℂ)^2 • 1 - S*S := by
    simp [add_mul, mul_sub, smul_smul, pow_two]
    abel
  have hp : (S + (Complex.I * d) • 1) * (S - (Complex.I * d) • 1) =
      (d : ℂ)^2 • 1 + S*S := by
    simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      smul_smul]
    have hc : (Complex.I * (d : ℂ)) * (Complex.I * d) = -(d : ℂ)^2 := by
      calc
        _ = Complex.I^2 * (d : ℂ)^2 := by ring
        _ = _ := by simp
    rw [hc, neg_smul]
    abel
  have hnum : ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) - S*S).det =
      (((d : ℂ) • 1 + S).det)^2 := by
    rw [← hm, Matrix.det_mul, hreal, pow_two]
  have hden : ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) + S*S).det =
      ((S + (Complex.I*d) • 1).det / Complex.I)^2 := by
    rw [← hp, Matrix.det_mul, himag, div_pow, Complex.I_sq]
    ring
  obtain ⟨q, hq, heq⟩ := algebraicRatioRational A hd
  refine ⟨q, hq, ?_⟩
  change ((d : ℂ)^2 • 1 - S*S).det / ((d : ℂ)^2 • 1 + S*S).det = _
  rw [hnum, hden, ← div_pow]
  exact congrArg (fun x : ℂ => x^2) heq

theorem regularAlgebraicSquare {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det) = (q : ℂ)^2 :=
  algebraicSquareIdentity A (regularOdd A hd hA)


open Matrix
open scoped Matrix

section
variable {m : Type*} [Fintype m] [DecidableEq m]

private noncomputable def bridgeU : Matrix (Sum m Unit) (Sum m Unit) ℂ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => -1) 1

private lemma bridgeU_det : (bridgeU (m := m)).det = (Fintype.card m : ℂ) + 1 := by
  unfold bridgeU
  rw [Matrix.det_fromBlocks_one₁₁, Matrix.det_unique]
  simp [Matrix.mul_apply] <;> ring

private noncomputable def bridgeH (T : Matrix (Sum m Unit) (Sum m Unit) ℂ) : Matrix m m ℂ :=
  fun j k => T (.inl j) (.inl k) - T (.inl j) (.inr ()) - T (.inr ()) (.inl k) + T (.inr ()) (.inr ())

private lemma bridgeU_entry_left (i : Sum m Unit) (j : m) :
    bridgeU i (.inl j) = (if i = .inl j then 1 else 0) - (if i = .inr () then 1 else 0) := by
  cases i <;> simp [bridgeU, Matrix.fromBlocks, Matrix.one_apply]

private lemma bridgeU_entry_right (i : Sum m Unit) : bridgeU (m := m) i (.inr ()) = 1 := by
  cases i <;> simp [bridgeU, Matrix.fromBlocks]

private lemma bridgeU_congr (T : Matrix (Sum m Unit) (Sum m Unit) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (bridgeU (m := m)).transpose * T * bridgeU =
      Matrix.fromBlocks (bridgeH T) 0 0 (Matrix.of fun (_ _ : Unit) => -((Fintype.card m : ℂ) + 1)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        bridgeU, Matrix.fromBlocks, Matrix.one_apply, bridgeH,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    | inr j =>
      cases j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, mul_one]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow]
      simp [bridgeU_entry_left, Fintype.sum_sum_type, Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, one_mul,
        hcol, bridgeU_entry_left, mul_sub, Finset.sum_sub_distrib, Fintype.sum_sum_type]
      simp [Matrix.fromBlocks]
    | inr j =>
      cases j
      simp [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, hcol,
        Matrix.fromBlocks, Fintype.card_sum]

private lemma bridge_det (T : Matrix (Sum m Unit) (Sum m Unit) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (bridgeH T).det = -((Fintype.card m : ℂ) + 1) * T.det := by
  have hd := congrArg Matrix.det (bridgeU_congr T hrow hcol)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, bridgeU_det,
    Matrix.det_fromBlocks_zero₂₁] at hd
  rw [Matrix.det_unique (Matrix.of fun (_ _ : Unit) => -((Fintype.card m : ℂ) + 1))] at hd
  simp only [Matrix.of_apply] at hd
  have hn : (Fintype.card m : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < (Fintype.card m : ℝ) + 1 := by positivity
    exact_mod_cast ne_of_gt h
  have heq : ((Fintype.card m : ℂ) + 1) *
      ((bridgeH T).det + ((Fintype.card m : ℂ) + 1) * T.det) = 0 := by
    linear_combination hd
  have := (mul_eq_zero.mp heq).resolve_left hn
  linear_combination this
end

section Skew
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma skew_resolvent_det (S : Matrix n n ℂ) (c : ℂ)
    (hS : S.transpose = -S) (hn : Odd (Fintype.card n))
    (hq : (c • (1 : Matrix n n ℂ) - S).det ≠ 0) :
    (1 - c • ((c • (1 : Matrix n n ℂ) - S)⁻¹ +
      ((c • (1 : Matrix n n ℂ) - S)⁻¹).transpose)).det =
      -(c^2 • (1 : Matrix n n ℂ) + S*S).det /
        (c^2 • (1 : Matrix n n ℂ) - S*S).det := by
  let Q : Matrix n n ℂ := c • 1 - S
  let P : Matrix n n ℂ := c • 1 + S
  have hQT : Q.transpose = P := by
    simp [Q, P, Matrix.transpose_sub, Matrix.transpose_smul, hS]
  have hq' : Q.det ≠ 0 := hq
  have hp : P.det ≠ 0 := by rw [← hQT, Matrix.det_transpose]; exact hq'
  have hqp : Q*P = c^2 • 1 - S*S := by
    simp [Q, P, sub_mul, mul_add, smul_add, smul_sub, smul_smul, pow_two] <;> abel
  have hpq : P*Q = c^2 • 1 - S*S := by
    simp [Q, P, add_mul, mul_sub, smul_smul, pow_two]
    abel
  have hqi : Q⁻¹ * (Q*P) = P :=
    Matrix.nonsing_inv_mul_cancel_left Q P (isUnit_iff_ne_zero.mpr hq')
  have hpi : P⁻¹ * (Q*P) = Q := by
    rw [show Q*P=P*Q from hqp.trans hpq.symm]
    exact Matrix.nonsing_inv_mul_cancel_left P Q (isUnit_iff_ne_zero.mpr hp)
  have hid : (1 - c • (Q⁻¹ + P⁻¹)) * (Q*P) = -(c^2 • 1 + S*S) := by
    calc
      _ = Q*P - c • (Q⁻¹*(Q*P) + P⁻¹*(Q*P)) := by
        simp [sub_mul, Matrix.smul_mul, add_mul]
      _ = Q*P - c • (P+Q) := by rw [hqi,hpi]
      _ = _ := by
        rw [hqp]
        simp [Q, P, smul_add, smul_sub, smul_smul, pow_two]
        abel
  have hd : (c^2 • (1 : Matrix n n ℂ) - S*S).det ≠ 0 := by
    rw [← hqp, Matrix.det_mul]
    exact mul_ne_zero hq' hp
  rw [Matrix.transpose_nonsing_inv, hQT]
  change (1-c • (Q⁻¹+P⁻¹)).det = _
  apply (eq_div_iff hd).mpr
  have hh := congrArg Matrix.det hid
  rw [Matrix.det_mul, hqp, Matrix.det_neg] at hh
  simpa [hn.neg_one_pow] using hh
end Skew

section Fin
private noncomputable def bridgeFinEquiv (n : ℕ) : (Fin n ⊕ Unit) ≃ Fin (n+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

private lemma differenceMinor_det (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (Matrix.of fun j k : Fin n =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det =
      -((n : ℂ)+1) * T.det := by
  let e := bridgeFinEquiv n
  let T' := T.submatrix e e
  have hr : ∀ i, ∑ j, T' i j = -1 := by
    intro i
    exact (e.sum_comp (fun j => T (e i) j)).trans (hrow (e i))
  have hc : ∀ j, ∑ i, T' i j = -1 := by
    intro j
    exact (e.sum_comp (fun i => T i (e j))).trans (hcol (e j))
  have h := bridge_det T' hr hc
  rw [Matrix.det_submatrix_equiv_self] at h
  have hh : bridgeH T' = (Matrix.of fun j k : Fin n =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)) := by
    rfl
  rw [hh] at h
  simpa using h
end Fin

section RowSum
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma inverse_row_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ i, ∑ j, Q i j = c) :
    ∀ i, ∑ j, Q⁻¹ i j = c⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet Q (isUnit_iff_ne_zero.mpr hQ)
  have hu : (fun _ : n => (1 : ℂ)) = Q *ᵥ (fun _ => c⁻¹) := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hr, hc]
  have hv := Matrix.inv_mulVec_eq_vec hu
  intro i
  simpa [Matrix.mulVec, dotProduct] using congrFun hv i

lemma inverse_col_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ j, ∑ i, Q i j = c) :
    ∀ j, ∑ i, Q⁻¹ i j = c⁻¹ := by
  have hv := inverse_row_sum Q.transpose c hc (by simpa using hQ) hr
  simpa [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply] using hv

private lemma resolvent_row_col_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ i, ∑ j, Q i j = c) (hcol : ∀ j, ∑ i, Q i j = c) :
    (∀ i, ∑ j, (1-c • (Q⁻¹+(Q⁻¹).transpose)) i j = -1) ∧
    (∀ j, ∑ i, (1-c • (Q⁻¹+(Q⁻¹).transpose)) i j = -1) := by
  have hri := inverse_row_sum Q c hc hQ hr
  have hci := inverse_col_sum Q c hc hQ hcol
  constructor
  · intro i
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Matrix.transpose_apply, Matrix.one_apply, hri, hci, hc, mul_add]
  · intro j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Matrix.transpose_apply, Matrix.one_apply, hri, hci, hc, mul_add]
end RowSum

lemma skew_difference_det (n : ℕ) (S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (c : ℂ) (hc : c ≠ 0) (hS : S.transpose = -S) (hn : Odd (n+1))
    (hq : (c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S).det ≠ 0)
    (hr : ∀ i, ∑ j, S i j = 0) :
    let T := 1-c • ((c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S)⁻¹ +
      ((c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S)⁻¹).transpose)
    (Matrix.of fun j k : Fin n => T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
      T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det =
      ((n : ℂ)+1) * (c^2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) + S*S).det /
        (c^2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S*S).det := by
  let Q := c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S
  let T := 1-c • (Q⁻¹ + (Q⁻¹).transpose)
  have hcol : ∀ j, ∑ i, S i j = 0 := by
    intro j
    calc
      _ = ∑ i, -S j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M j i) hS
      _ = -(∑ i, S j i) := Finset.sum_neg_distrib (fun i => S j i)
      _ = 0 := neg_eq_zero.mpr (hr j)
  have hqr : ∀ i, ∑ j, Q i j = c := by
    intro i
    simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hr]
  have hqc : ∀ j, ∑ i, Q i j = c := by
    intro j
    simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hcol]
  have hsum := resolvent_row_col_sum Q c hc hq hqr hqc
  have hdet := differenceMinor_det n T hsum.1 hsum.2
  have hid := skew_resolvent_det S c hS (by simpa using hn) hq
  change (Matrix.of fun j k : Fin n => T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
      T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det = _
  rw [hdet]
  change -((n : ℂ)+1) * (1-c • (Q⁻¹+(Q⁻¹).transpose)).det = _
  rw [hid]
  ring

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology ContDiff

section
variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  ({ toFun := Matrix.diagonal
     map_add' := by intro u v; exact (Matrix.diagonal_add u v).symm
     map_smul' := by intro c u; exact Matrix.diagonal_smul c u } :
    (n → ℂ) →ₗ[ℂ] Matrix n n ℂ).toContinuousLinearMap

private noncomputable def sumEntriesCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ i, ∑ j, M i j
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private lemma matrixInverse_hasFDerivAt (Q : Matrix n n ℂ) (hQ : Q.det ≠ 0) :
    HasFDerivAt (fun M : Matrix n n ℂ => M⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) Q⁻¹ Q⁻¹) Q := by
  rw [show (fun M : Matrix n n ℂ => M⁻¹) = Ring.inverse from
    funext fun M => Matrix.nonsing_inv_eq_ringInverse M]
  exact hasFDerivAt_ringInverse (𝕜 := ℂ)
    (Matrix.nonsingInvUnit Q (isUnit_iff_ne_zero.mpr hQ))

@[expose]
noncomputable def inverseQ (S : Matrix n n ℂ) (y : n → ℂ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => 2 / y i) - S
@[expose]
noncomputable def alpha (S : Matrix n n ℂ) (y : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((inverseQ S y)⁻¹) i j

private noncomputable def inverseQDeriv (y : n → ℂ) :
    (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  diagonalCLM ∘L ContinuousLinearMap.pi (fun i =>
    (-(2 : ℂ) / (y i)^2) • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ))

private lemma inverseQ_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) :
    HasFDerivAt (inverseQ S) (inverseQDeriv y) y := by
  have hscalar : HasFDerivAt (fun y : n → ℂ => fun i => 2 / y i)
      (ContinuousLinearMap.pi (fun i =>
        (-(2 : ℂ) / (y i)^2) • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ))) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    convert (((hasDerivAt_inv (hy i)).comp_hasFDerivAt y ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ)).hasFDerivAt).const_mul 2) using 1
    · ext y; simp [div_eq_mul_inv]
    · ext t; simp [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  exact ((diagonalCLM (n := n)).hasFDerivAt.comp y hscalar).sub_const S

private lemma inverse_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    HasFDerivAt (fun y => (inverseQ S y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
        (inverseQ S y)⁻¹ (inverseQ S y)⁻¹) ∘L inverseQDeriv y) y :=
  (matrixInverse_hasFDerivAt (inverseQ S y) hQ).comp y (inverseQ_hasFDerivAt S y hy)

private lemma alpha_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    HasFDerivAt (alpha S)
      (sumEntriesCLM ∘L ((-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
        (inverseQ S y)⁻¹ (inverseQ S y)⁻¹) ∘L inverseQDeriv y)) y := by
  change HasFDerivAt ((sumEntriesCLM (n := n)) ∘ (fun u => (inverseQ S u)⁻¹)) _ y
  exact (sumEntriesCLM (n := n)).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
private lemma inverseQ_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ) (hy : ∀ i, y i ≠ 0) :
    ContDiffAt ℂ 2 (inverseQ S) y := by
  have hs : ContDiffAt ℂ 2 (fun y : n → ℂ => fun i => 2 / y i) y := by
    apply contDiffAt_pi.mpr
    intro i
    have hi : ContDiffAt ℂ 2 (fun u : n → ℂ => (u i)⁻¹) y :=
      (contDiffAt_apply ℂ (fun _ : n => ℂ) i y).inv (hy i)
    have hm : ContDiffAt ℂ 2 (fun u : n → ℂ => (2 : ℂ) * (u i)⁻¹) y :=
      contDiffAt_const.mul hi
    simpa [div_eq_mul_inv] using hm
  exact ((diagonalCLM (n := n)).contDiff.contDiffAt.comp y hs).sub contDiffAt_const

private lemma inverse_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    ContDiffAt ℂ 2 (fun y => (inverseQ S y)⁻¹) y := by
  have h := (contDiffAt_ringInverse ℂ
    (Matrix.nonsingInvUnit (inverseQ S y) (isUnit_iff_ne_zero.mpr hQ))).comp y
      (inverseQ_contDiffAt S y hy)
  rw [show (fun u => (inverseQ S u)⁻¹) = Ring.inverse ∘ inverseQ S from
    funext fun u => Matrix.nonsing_inv_eq_ringInverse (inverseQ S u)]
  exact h

lemma alpha_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    ContDiffAt ℂ 2 (alpha S) y := by
  change ContDiffAt ℂ 2 ((sumEntriesCLM (n := n)) ∘ (fun u => (inverseQ S u)⁻¹)) y
  exact (sumEntriesCLM (n := n)).contDiff.contDiffAt.comp y (inverse_contDiffAt S y hy hQ)

private lemma inverseQDeriv_single (y : n → ℂ) (j : n) :
    inverseQDeriv y (Pi.single j 1) =
      (-(2 : ℂ) / (y j)^2) • Matrix.diagonal (Pi.single j 1) := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst j; simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, Pi.single_apply]
    · simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, Pi.single_apply,
        hij, Ne.symm hij]
  · simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, hik]

private lemma inverse_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j : n) :
    fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single j 1) =
      (2 / (y j)^2) • Matrix.of (fun i k =>
        ((inverseQ S y)⁻¹) i j * ((inverseQ S y)⁻¹) j k) := by
  rw [(inverse_hasFDerivAt S y hy hQ).fderiv]
  let V := (inverseQ S y)⁻¹
  change -(V * inverseQDeriv y (Pi.single j 1) * V) =
    (2 / (y j)^2) • Matrix.of (fun i k => V i j * V j k)
  rw [inverseQDeriv_single]
  ext i k
  simp [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.single_apply, Matrix.neg_apply]
  ring

private noncomputable def rowSumCLM (j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ k, M j k
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
private noncomputable def colSumCLM (j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ k, M k j
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private lemma row_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun y => ∑ l, ((inverseQ S y)⁻¹) j l) y (Pi.single k 1) =
      (2 / (y k)^2) * ((inverseQ S y)⁻¹) j k *
        (∑ l, ((inverseQ S y)⁻¹) k l) := by
  have hd := (rowSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) j l) _ y at hd
  rw [hd.fderiv]
  rw [← (inverse_hasFDerivAt S y hy hQ).fderiv]
  change rowSumCLM j (fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single k 1)) = _
  rw [inverse_fderiv_single S y hy hQ k]
  simp [rowSumCLM, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

private lemma col_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun y => ∑ l, ((inverseQ S y)⁻¹) l j) y (Pi.single k 1) =
      (2 / (y k)^2) * ((inverseQ S y)⁻¹) k j *
        (∑ l, ((inverseQ S y)⁻¹) l k) := by
  have hd := (colSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) l j) _ y at hd
  rw [hd.fderiv]
  rw [← (inverse_hasFDerivAt S y hy hQ).fderiv]
  change colSumCLM j (fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single k 1)) = _
  rw [inverse_fderiv_single S y hy hQ k]
  simp [colSumCLM, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma alpha_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j : n) :
    fderiv ℂ (alpha S) y (Pi.single j 1) =
      (2 / (y j)^2) * (∑ k, ((inverseQ S y)⁻¹) j k) *
        (∑ i, ((inverseQ S y)⁻¹) i j) := by
  rw [(alpha_hasFDerivAt S y hy hQ).fderiv]
  rw [← (inverse_hasFDerivAt S y hy hQ).fderiv]
  change sumEntriesCLM (fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single j 1)) = _
  rw [inverse_fderiv_single S y hy hQ j]
  change (∑ i, ∑ k, ((2 / (y j)^2) • Matrix.of (fun i k =>
    ((inverseQ S y)⁻¹) i j * ((inverseQ S y)⁻¹) j k)) i k) = _
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma inverse_square_hasDerivAt (t : ℂ) (ht : t ≠ 0) :
    HasDerivAt (fun t : ℂ => 2 / t^2) (-(4 : ℂ) / t^3) t := by
  have hd := (((hasDerivAt_id t).inv ht).pow 2).const_mul (2 : ℂ)
  convert hd using 1
  · ext u
    simp [div_eq_mul_inv]
  · dsimp
    field_simp [ht] <;> ring

private lemma alpha_second_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) y (Pi.single k 1) =
      (-(4 : ℂ) / (y j)^3) * (if k = j then 1 else 0) *
        (∑ l, ((inverseQ S y)⁻¹) j l) * (∑ l, ((inverseQ S y)⁻¹) l j) +
      (4 / ((y j)^2 * (y k)^2)) *
        (((inverseQ S y)⁻¹) j k * (∑ l, ((inverseQ S y)⁻¹) k l) *
          (∑ l, ((inverseQ S y)⁻¹) l j) +
        ((inverseQ S y)⁻¹) k j * (∑ l, ((inverseQ S y)⁻¹) j l) *
          (∑ l, ((inverseQ S y)⁻¹) l k)) := by
  have hys : ∀ᶠ u in 𝓝 y, ∀ i, u i ≠ 0 :=
    Filter.eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually_ne (hy i)
  have hdet : ContinuousAt (fun u => (inverseQ S u).det) y :=
    (show Continuous (Matrix.det : Matrix n n ℂ → ℂ) from continuous_id.matrix_det).continuousAt.comp
      (inverseQ_contDiffAt S y hy).continuousAt
  have heq : (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) =ᶠ[𝓝 y]
      (fun u => (2 / (u j)^2) * (∑ l, ((inverseQ S u)⁻¹) j l) *
        (∑ l, ((inverseQ S u)⁻¹) l j)) := by
    filter_upwards [hys, hdet.eventually_ne hQ] with u hu hqu
    exact alpha_fderiv_single S u hu hqu j
  have hcoef := (inverse_square_hasDerivAt (y j) (hy j)).comp_hasFDerivAt y
    ((ContinuousLinearMap.proj j : (n → ℂ) →L[ℂ] ℂ)).hasFDerivAt
  change HasFDerivAt (fun u : n → ℂ => 2 / (u j)^2) _ y at hcoef
  have hrow := (rowSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  have hcol := (colSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) j l) _ y at hrow
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) l j) _ y at hcol
  have hh := ((hcoef.mul hrow).mul hcol).congr_of_eventuallyEq heq
  rw [hh.fderiv]
  have hr := row_fderiv_single S y hy hQ j k
  have hc := col_fderiv_single S y hy hQ j k
  rw [hrow.fderiv] at hr
  rw [hcol.fderiv] at hc
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.one_apply] at *
  rw [hr, hc]
  dsimp [rowSumCLM, colSumCLM]
  by_cases hjk : j = k
  · subst k
    simp <;> ring
  · simp [hjk, Ne.symm hjk] <;> ring

lemma alpha_first_const (S : Matrix n n ℂ) (b : ℂ) (hb : b ≠ 0)
    (hQ : (inverseQ S (fun _ => b)).det ≠ 0)
    (hr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2)
    (hc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2) (j : n) :
    fderiv ℂ (alpha S) (fun _ => b) (Pi.single j 1) = 1 / 2 := by
  rw [alpha_fderiv_single S (fun _ => b) (fun _ => hb) hQ j, hr, hc]
  field_simp <;> ring

lemma alpha_second_const (S : Matrix n n ℂ) (b : ℂ) (hb : b ≠ 0)
    (hQ : (inverseQ S (fun _ => b)).det ≠ 0)
    (hr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2)
    (hc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2) (j k : n) :
    fderiv ℂ (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) (fun _ => b) (Pi.single k 1) =
      (b^2)⁻¹ * (((inverseQ S (fun _ => b))⁻¹) j k +
        ((inverseQ S (fun _ => b))⁻¹) k j) - (if j = k then b⁻¹ else 0) := by
  rw [alpha_second_single S (fun _ => b) (fun _ => hb) hQ j k]
  simp_rw [hr, hc]
  by_cases hjk : j = k
  · subst k
    simp only [ite_true]
    field_simp <;> ring
  · simp only [hjk, Ne.symm hjk, ite_false, mul_zero, zero_mul, zero_add, sub_zero]
    field_simp <;> ring

end

end D5.S3.Combinatorics.WormaldTournamentHessian.Algebra
