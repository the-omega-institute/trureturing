import D5.S3.Analytic.PetzStripFiniteSeries
import D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Basic.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mixed-spectral triangular divergence for finite density matrices

The divergence uses the denominator of the Sylvester map `X ↦ AX + XB`.
The mixed coordinates range over both full eigenbases, including the kernels.
The variational maximizer takes value zero on pairs of zero eigenvalues.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Filter
open CStarMatrix (ofMatrix)
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_eq_max_re_tr_U exists_svd_sqrt_eigenvalues)
open PetzExponentialBoundaryEvaluation (petzWeight)

namespace D5.S3.Quantum.Recovery.PetzTriangularOrbit

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem posSemidef (A : DensityState n) : (ofMatrix.symm A.1).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm A.nonnegative)

/-- Eigenvalues of the actual density matrix, with zeros retained. -/
def eigenvalue (A : DensityState n) : n → ℝ :=
  (posSemidef A).1.eigenvalues

/-- The unitary whose columns are eigenvectors of the actual density matrix. -/
def eigenbasis (A : DensityState n) : Matrix.unitaryGroup n ℂ :=
  (posSemidef A).1.eigenvectorUnitary

private theorem eigenvalue_nonneg (A : DensityState n) (i : n) : 0 ≤ eigenvalue A i :=
  (posSemidef A).eigenvalues_nonneg i

private theorem sum_eigenvalue (A : DensityState n) : ∑ i, eigenvalue A i = 1 := by
  have htrace : (ofMatrix.symm A.1).trace = 1 := A.trace_eq_one
  have h := congrArg Complex.re (posSemidef A).1.trace_eq_sum_eigenvalues
  simpa only [htrace, Complex.one_re, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, eigenvalue]
    using h.symm

private theorem adjoint_mul_unitary (U : Matrix.unitaryGroup n ℂ) : U.valᴴ * U.val = 1 :=
  U.prop.1

private theorem unitary_mul_adjoint (U : Matrix.unitaryGroup n ℂ) : U.val * U.valᴴ = 1 :=
  U.prop.2

/-- Matrix of `X` in the left basis `U` and right basis `V`. -/
def coordinates (U V : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  U.valᴴ * (X * V.val)

private theorem coordinates_sub (U V : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    coordinates U V (X - Y) = coordinates U V X - coordinates U V Y := by
  simp only [coordinates, Matrix.sub_mul, Matrix.mul_sub]

private theorem coordinates_add (U V : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    coordinates U V (X + Y) = coordinates U V X + coordinates U V Y := by
  simp only [coordinates, Matrix.add_mul, Matrix.mul_add]

/-- Real Hilbert–Schmidt pairing expressed in the original matrix coordinates. -/
def tracePair (X Y : Matrix n n ℂ) : ℝ :=
  ((Xᴴ * Y).trace).re

private theorem tracePair_sum (X Y : Matrix n n ℂ) :
    tracePair X Y = ∑ ij : n × n, (star (X ij.1 ij.2) * Y ij.1 ij.2).re := by
  simp only [tracePair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Complex.re_sum, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem tracePair_coordinates (U V : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    tracePair (coordinates U V X) (coordinates U V Y) = tracePair X Y := by
  have h (Z : Matrix n n ℂ) : U.val * (U.valᴴ * Z) = Z := by
    rw [← Matrix.mul_assoc, unitary_mul_adjoint, Matrix.one_mul]
  have heq : (coordinates U V X)ᴴ * coordinates U V Y =
      V.valᴴ * (Xᴴ * Y) * V.val := by
    simp only [coordinates, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, h]
  unfold tracePair
  rw [heq, Matrix.trace_mul_cycle, unitary_mul_adjoint, Matrix.one_mul]

private theorem tracePair_self (X : Matrix n n ℂ) :
    tracePair X X = ∑ ij : n × n, ‖X ij.1 ij.2‖ ^ 2 := by
  rw [tracePair_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- Squared Hilbert–Schmidt norm on finite matrices. -/
def hsSq (X : Matrix n n ℂ) : ℝ := tracePair X X

theorem hsSq_eq_sum (X : Matrix n n ℂ) :
    hsSq X = ∑ ij : n × n, ‖X ij.1 ij.2‖ ^ 2 :=
  tracePair_self X

theorem hsSq_coordinates (U V : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    hsSq (coordinates U V X) = hsSq X :=
  tracePair_coordinates U V X X

/-- A real function applied on the spectrum of a density matrix. -/
def spectral (A : DensityState n) (f : ℝ → ℝ) : Matrix n n ℂ :=
  (eigenbasis A).val *
    (Matrix.diagonal (fun i => (f (eigenvalue A i) : ℂ)) * (eigenbasis A).valᴴ)

private theorem spectral_id (A : DensityState n) : spectral A id = (ofMatrix.symm A.1) := by
  simpa only [spectral, eigenvalue, eigenbasis, id_eq, Function.comp_def,
    Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.mul_assoc, RCLike.ofReal_eq_complex_ofReal]
    using (posSemidef A).1.spectral_theorem.symm

private theorem coordinates_spectral_mul (A B : DensityState n) (f : ℝ → ℝ)
    (X : Matrix n n ℂ) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) (spectral A f * X) i j =
      (f (eigenvalue A i) : ℂ) * coordinates (eigenbasis A) (eigenbasis B) X i j := by
  have h (Z : Matrix n n ℂ) :
      (eigenbasis A).valᴴ * ((eigenbasis A).val * Z) = Z := by
    rw [← Matrix.mul_assoc, adjoint_mul_unitary, Matrix.one_mul]
  have heq : coordinates (eigenbasis A) (eigenbasis B) (spectral A f * X) =
      Matrix.diagonal (fun k => (f (eigenvalue A k) : ℂ)) *
        coordinates (eigenbasis A) (eigenbasis B) X := by
    simp only [coordinates, spectral, Matrix.mul_assoc, h]
  rw [heq, Matrix.diagonal_mul]

private theorem coordinates_mul_spectral (A B : DensityState n) (f : ℝ → ℝ)
    (X : Matrix n n ℂ) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) (X * spectral B f) i j =
      coordinates (eigenbasis A) (eigenbasis B) X i j * (f (eigenvalue B j) : ℂ) := by
  have heq : coordinates (eigenbasis A) (eigenbasis B) (X * spectral B f) =
      coordinates (eigenbasis A) (eigenbasis B) X *
        Matrix.diagonal (fun k => (f (eigenvalue B k) : ℂ)) := by
    simp only [coordinates, spectral, Matrix.mul_assoc, adjoint_mul_unitary, Matrix.mul_one]
  rw [heq, Matrix.mul_diagonal]

/-- The mixed coordinates of the identity give the eigenbasis overlaps. -/
def overlap (A B : DensityState n) (i j : n) : ℂ :=
  coordinates (eigenbasis A) (eigenbasis B) 1 i j

/-- The eigenvalue of `X ↦ AX + XB` on a mixed coordinate. -/
def weight (A B : DensityState n) (i j : n) : ℝ :=
  eigenvalue A i + eigenvalue B j

private theorem weight_nonneg (A B : DensityState n) (i j : n) : 0 ≤ weight A B i j :=
  add_nonneg (eigenvalue_nonneg A i) (eigenvalue_nonneg B j)

private theorem eigenvalues_eq_zero_of_weight_eq_zero (A B : DensityState n) {i j : n}
    (h : weight A B i j = 0) : eigenvalue A i = 0 ∧ eigenvalue B j = 0 := by
  unfold weight at h
  have ha := eigenvalue_nonneg A i
  have hb := eigenvalue_nonneg B j
  constructor <;> linarith

private theorem coordinates_spectral_sub (A B : DensityState n) (f g : ℝ → ℝ) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) (spectral A f - spectral B g) i j =
      ((f (eigenvalue A i) - g (eigenvalue B j) : ℝ) : ℂ) * overlap A B i j := by
  have hA := coordinates_spectral_mul A B f 1 i j
  have hB := coordinates_mul_spectral A B g 1 i j
  rw [Matrix.mul_one] at hA
  rw [Matrix.one_mul] at hB
  rw [coordinates_sub, Matrix.sub_apply, hA, hB, Complex.ofReal_sub]
  unfold overlap
  ring

private theorem coordinates_difference (A B : DensityState n) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) i j =
      ((eigenvalue A i - eigenvalue B j : ℝ) : ℂ) * overlap A B i j := by
  simpa only [spectral_id, id_eq] using coordinates_spectral_sub A B id id i j

theorem coordinates_difference_zero (A B : DensityState n) {i j : n}
    (h : weight A B i j = 0) :
    coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) i j = 0 := by
  obtain ⟨ha, hb⟩ := eigenvalues_eq_zero_of_weight_eq_zero A B h
  simp [coordinates_difference, ha, hb]

private theorem normSq_scaled (r : ℝ) (z : ℂ) :
    Complex.normSq ((r : ℂ) * z) = r ^ 2 * Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, pow_two]

/-- Petz's mixed-spectral triangular divergence. At `aᵢ + bⱼ = 0`, both
eigenvalues are zero and the summand has its continuous value zero. -/
def triangular (A B : DensityState n) : ℝ :=
  ∑ ij : n × n, (eigenvalue A ij.1 - eigenvalue B ij.2) ^ 2 *
    Complex.normSq (overlap A B ij.1 ij.2) / weight A B ij.1 ij.2

theorem triangular_eq_coordinates (A B : DensityState n) :
    triangular A B = ∑ ij : n × n,
      Complex.normSq (coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) ij.1 ij.2) /
        weight A B ij.1 ij.2 := by
  simp only [triangular, coordinates_difference, normSq_scaled]

theorem triangular_nonneg (A B : DensityState n) : 0 ≤ triangular A B := by
  rw [triangular_eq_coordinates]
  exact Finset.sum_nonneg fun ij _ =>
    div_nonneg (Complex.normSq_nonneg _) (weight_nonneg A B ij.1 ij.2)

private theorem coordinates_sylvester (A B : DensityState n) (X : Matrix n n ℂ) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) * X + X * (ofMatrix.symm B.1)) i j =
      (weight A B i j : ℂ) * coordinates (eigenbasis A) (eigenbasis B) X i j := by
  have hA := coordinates_spectral_mul A B id X i j
  have hB := coordinates_mul_spectral A B id X i j
  simp only [spectral_id, id_eq] at hA hB
  rw [coordinates_add, Matrix.add_apply, hA, hB, weight, Complex.ofReal_add]
  ring

/-- The variational objective on the original matrices. -/
def objective (A B : DensityState n) (X : Matrix n n ℂ) : ℝ :=
  2 * tracePair X ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) - tracePair X ((ofMatrix.symm A.1) * X + X * (ofMatrix.symm B.1))

theorem objective_eq_traces (A B : DensityState n) (X : Matrix n n ℂ) :
    objective A B X = 2 * ((Xᴴ * ((ofMatrix.symm A.1) - (ofMatrix.symm B.1))).trace).re -
      ((Xᴴ * (ofMatrix.symm A.1) * X).trace).re - ((Xᴴ * X * (ofMatrix.symm B.1)).trace).re := by
  simp only [objective, tracePair, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    Matrix.mul_assoc]
  ring

private theorem objective_eq_sum (A B : DensityState n) (X : Matrix n n ℂ) :
    objective A B X = ∑ ij : n × n,
      (2 * (star (coordinates (eigenbasis A) (eigenbasis B) X ij.1 ij.2) *
        coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) ij.1 ij.2).re -
        weight A B ij.1 ij.2 *
        Complex.normSq (coordinates (eigenbasis A) (eigenbasis B) X ij.1 ij.2)) := by
  unfold objective
  rw [← tracePair_coordinates (eigenbasis A) (eigenbasis B) X ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)),
    ← tracePair_coordinates (eigenbasis A) (eigenbasis B) X ((ofMatrix.symm A.1) * X + X * (ofMatrix.symm B.1))]
  simp only [tracePair_sum, coordinates_sylvester, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

private theorem complete_square {w : ℝ} (d x : ℂ)
    (hz : w = 0 → d = 0) :
    Complex.normSq d / w -
      (2 * (star x * d).re - w * Complex.normSq x) =
        w * Complex.normSq (x - d / (w : ℂ)) := by
  by_cases h : w = 0
  · simp [h, hz h]
  · simp only [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re,
      Complex.div_ofReal_im]
    field_simp [h] <;> ring

/-- An actual maximizing matrix. Division in a pair of zero eigenspaces returns zero. -/
def maximizer (A B : DensityState n) : Matrix n n ℂ :=
  (eigenbasis A).val *
    ((Matrix.of fun i j => coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) i j /
      (weight A B i j : ℂ)) * (eigenbasis B).valᴴ)

private theorem coordinates_maximizer (A B : DensityState n) (i j : n) :
    coordinates (eigenbasis A) (eigenbasis B) (maximizer A B) i j =
      coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) i j / (weight A B i j : ℂ) := by
  have hA (Z : Matrix n n ℂ) :
      (eigenbasis A).valᴴ * ((eigenbasis A).val * Z) = Z := by
    rw [← Matrix.mul_assoc, adjoint_mul_unitary, Matrix.one_mul]
  simp only [coordinates, maximizer, Matrix.mul_assoc, adjoint_mul_unitary, Matrix.mul_one, hA,
    Matrix.of_apply]

/-- Exact gap from the variational maximum, including the unconstrained
zero-weight coordinates. -/
theorem triangular_sub_objective (A B : DensityState n) (X : Matrix n n ℂ) :
    triangular A B - objective A B X = ∑ ij : n × n, weight A B ij.1 ij.2 *
      Complex.normSq (coordinates (eigenbasis A) (eigenbasis B) X ij.1 ij.2 -
        coordinates (eigenbasis A) (eigenbasis B) ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) ij.1 ij.2 /
          (weight A B ij.1 ij.2 : ℂ)) := by
  rw [triangular_eq_coordinates, objective_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  exact complete_square _ _ (coordinates_difference_zero A B)

theorem objective_le_triangular (A B : DensityState n) (X : Matrix n n ℂ) :
    objective A B X ≤ triangular A B := by
  apply sub_nonneg.mp
  rw [triangular_sub_objective]
  exact Finset.sum_nonneg fun ij _ =>
    mul_nonneg (weight_nonneg A B ij.1 ij.2) (Complex.normSq_nonneg _)

theorem objective_maximizer (A B : DensityState n) :
    objective A B (maximizer A B) = triangular A B := by
  apply le_antisymm (objective_le_triangular _ _ _)
  apply sub_nonpos.mp
  rw [triangular_sub_objective]
  simp only [coordinates_maximizer, sub_self, Complex.normSq_zero, mul_zero, Finset.sum_const_zero, le_refl]

/-- The supremum is attained over all complex matrices on the original carrier. -/
theorem triangular_isGreatest (A B : DensityState n) :
    IsGreatest (Set.range (objective A B)) (triangular A B) := by
  refine ⟨⟨maximizer A B, objective_maximizer A B⟩, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact objective_le_triangular A B X

private theorem sum_weighted_unitary (A B : DensityState n) (U : Matrix.unitaryGroup n ℂ) :
    (∑ ij : n × n, weight A B ij.1 ij.2 * Complex.normSq (U.val ij.1 ij.2)) = 2 := by
  have hr (i : n) : ∑ j, Complex.normSq (U.val i j) = 1 := by
    simp only [Complex.normSq_eq_norm_sq]
    exact Matrix.unitary_row_sum_norm_sq U.val (unitary_mul_adjoint U) i
  have hc (j : n) : ∑ i, Complex.normSq (U.val i j) = 1 := by
    simp only [Complex.normSq_eq_norm_sq]
    exact Matrix.unitary_col_sum_norm_sq U.val (adjoint_mul_unitary U) j
  simp only [Fintype.sum_prod_type, weight, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => eigenvalue B j * Complex.normSq (U.val i j))]
  simp only [← Finset.mul_sum, hr, hc, mul_one, sum_eigenvalue]
  norm_num

private theorem re_pair_sq_le (x y : ℂ) :
    (star x * y).re ^ 2 ≤ Complex.normSq x * Complex.normSq y := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (star x * y)) 2
  simpa only [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul,
    Complex.star_def, Complex.normSq_conj] using h

/-- Apply weighted Cauchy–Schwarz in mixed coordinates to the maximizing
unitary from the D5 trace-norm duality. The weight vanishes only where the
bound on the corresponding matrix entry has value zero. -/
private theorem traceNorm_sq_le_of_coordinates (A B : DensityState n) (Y : Matrix n n ℂ)
    (c : n × n → ℝ) (hc : ∀ ij, 0 ≤ c ij)
    (hY : ∀ ij : n × n, Complex.normSq
      (coordinates (eigenbasis A) (eigenbasis B) Y ij.1 ij.2) =
        weight A B ij.1 ij.2 * c ij) :
    traceNorm Y ^ 2 ≤ 2 * ∑ ij : n × n, c ij := by
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U Y).1
  let W : Matrix.unitaryGroup n ℂ := star (eigenbasis A) * (star U * eigenbasis B)
  have hW : W.val = coordinates (eigenbasis A) (eigenbasis B) U.valᴴ := rfl
  let r : n × n → ℝ := fun ij => (star (W.val ij.1 ij.2) *
    coordinates (eigenbasis A) (eigenbasis B) Y ij.1 ij.2).re
  have hsum : traceNorm Y = ∑ ij, r ij := by
    rw [← hU]
    have hpair : tracePair U.valᴴ Y = ((U.val * Y).trace).re := by
      rw [tracePair, Matrix.conjTranspose_conjTranspose]
    rw [← hpair]
    rw [← tracePair_coordinates (eigenbasis A) (eigenbasis B) U.valᴴ Y,
      tracePair_sum]
    simp only [r, hW]
  rw [hsum, mul_comm (2 : ℝ), ← sum_weighted_unitary A B W]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun ij _ => hc ij)
    (fun ij _ => mul_nonneg (weight_nonneg A B ij.1 ij.2) (Complex.normSq_nonneg _))
    (fun ij _ => ?_)
  calc
    r ij ^ 2 ≤ Complex.normSq (W.val ij.1 ij.2) *
        Complex.normSq (coordinates (eigenbasis A) (eigenbasis B) Y ij.1 ij.2) :=
      re_pair_sq_le _ _
    _ = _ := by rw [hY]; ring

/-- Full trace-norm control, with both states allowed to be singular. -/
theorem traceNorm_sub_sq_le_two_triangular (A B : DensityState n) :
    traceNorm ((ofMatrix.symm A.1) - (ofMatrix.symm B.1)) ^ 2 ≤ 2 * triangular A B := by
  rw [triangular_eq_coordinates]
  refine traceNorm_sq_le_of_coordinates A B _ _
    (fun ij => div_nonneg (Complex.normSq_nonneg _) (weight_nonneg A B ij.1 ij.2))
    (fun ij => ?_)
  by_cases hz : weight A B ij.1 ij.2 = 0
  · simp [hz, coordinates_difference_zero A B hz]
  · field_simp [hz]

/-- The mixed-spectral harmonic overlap. Its zero-weight summands are zero. -/
def harmonicOverlap (A B : DensityState n) : ℝ :=
  ∑ ij : n × n, (2 * eigenvalue A ij.1 * eigenvalue B ij.2 *
    Complex.normSq (overlap A B ij.1 ij.2)) / weight A B ij.1 ij.2

theorem triangular_eq_two_sub_harmonic (A B : DensityState n) :
    triangular A B = 2 * (1 - harmonicOverlap A B) := by
  have hmass :
      (∑ ij : n × n, weight A B ij.1 ij.2 * Complex.normSq (overlap A B ij.1 ij.2)) = 2 := by
    have hunit : (star (eigenbasis A) * eigenbasis B).val =
        (eigenbasis A).valᴴ * (eigenbasis B).val := rfl
    simpa only [overlap, coordinates, Matrix.one_mul, hunit] using
      sum_weighted_unitary A B (star (eigenbasis A) * eigenbasis B)
  unfold triangular harmonicOverlap
  rw [mul_sub, mul_one]
  nth_rw 1 [← hmass]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  by_cases hz : weight A B ij.1 ij.2 = 0
  · simp [hz]
  · field_simp [hz] <;> simp only [weight] <;> ring

private theorem spectral_eq_cfc (A : DensityState n) (f : ℝ → ℝ) :
    spectral A f = (posSemidef A).1.cfc f := by
  simp only [spectral, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.mul_assoc, eigenbasis, eigenvalue, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal]

private theorem spectral_sqrt (A : DensityState n) :
    spectral A Real.sqrt = CFC.sqrt (ofMatrix.symm A.1) := by
  rw [CFC.sqrt_eq_real_sqrt _ (posSemidef A).nonneg, cfcₙ_eq_cfc,
    Matrix.IsHermitian.cfc_eq (posSemidef A).1, spectral_eq_cfc]

/-- Root fidelity in the actual matrix trace norm. -/
def rootFidelity (A B : DensityState n) : ℝ :=
  traceNorm (CFC.sqrt (ofMatrix.symm A.1) * CFC.sqrt (ofMatrix.symm B.1))

/-- Weighted Cauchy–Schwarz in the two eigenbases bounds the actual root fidelity. -/
theorem rootFidelity_sq_le_harmonicOverlap (A B : DensityState n) :
    rootFidelity A B ^ 2 ≤ harmonicOverlap A B := by
  let c : n × n → ℝ := fun ij => eigenvalue A ij.1 * eigenvalue B ij.2 *
    Complex.normSq (overlap A B ij.1 ij.2) / weight A B ij.1 ij.2
  have hc (ij : n × n) : 0 ≤ c ij :=
    div_nonneg
      (mul_nonneg (mul_nonneg (eigenvalue_nonneg A _) (eigenvalue_nonneg B _))
        (Complex.normSq_nonneg _)) (weight_nonneg A B _ _)
  unfold rootFidelity
  rw [← spectral_sqrt A, ← spectral_sqrt B]
  have h := traceNorm_sq_le_of_coordinates A B (spectral A Real.sqrt * spectral B Real.sqrt) c hc
    (fun ij => by
      have hB := coordinates_mul_spectral A B Real.sqrt 1 ij.1 ij.2
      rw [Matrix.one_mul] at hB
      rw [coordinates_spectral_mul, hB,
        mul_comm (coordinates (eigenbasis A) (eigenbasis B) 1 ij.1 ij.2)
          (Real.sqrt (eigenvalue B ij.2) : ℂ),
        ← mul_assoc, ← Complex.ofReal_mul, normSq_scaled,
        mul_pow, Real.sq_sqrt (eigenvalue_nonneg A _), Real.sq_sqrt (eigenvalue_nonneg B _)]
      change _ = weight A B ij.1 ij.2 * c ij
      unfold c overlap
      by_cases hz : weight A B ij.1 ij.2 = 0
      · obtain ⟨ha, hb⟩ := eigenvalues_eq_zero_of_weight_eq_zero A B hz
        simp [ha, hb, hz]
      · field_simp [hz])
  have hsum : harmonicOverlap A B = 2 * ∑ ij : n × n, c ij := by
    rw [Finset.mul_sum]
    unfold harmonicOverlap
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp only [c, ← mul_div_assoc]
    ring
  exact h.trans_eq hsum.symm

theorem triangular_le_two_one_sub_rootFidelity_sq (A B : DensityState n) :
    triangular A B ≤ 2 * (1 - rootFidelity A B ^ 2) := by
  rw [triangular_eq_two_sub_harmonic]
  linarith [rootFidelity_sq_le_harmonicOverlap A B]

/-- The scalar spectral profile of the feature `√2 A exp(-s A)`. -/
def featureScalar (s a : ℝ) : ℝ := Real.sqrt 2 * a * Real.exp (-a * s)

/-- The matrix-valued feature on the original carrier. -/
def feature (A : DensityState n) (s : ℝ) : Matrix n n ℂ :=
  spectral A (featureScalar s)

private theorem featureScalar_mul (s a b : ℝ) :
    featureScalar s a * featureScalar s b = (2 * a * b) * Real.exp (-(a + b) * s) := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold featureScalar
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) * a * b *
        (Real.exp (-a * s) * Real.exp (-b * s)) := by ring
    _ = _ := by rw [h, ← Real.exp_add, show -a * s + -b * s = -(a + b) * s by ring]

private theorem integrate_featureScalar_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntegrableOn (fun s => featureScalar s a * featureScalar s b) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), featureScalar s a * featureScalar s b) =
        2 * a * b / (a + b) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, featureScalar]
  have hneg : -(a + b) < 0 := neg_lt_zero.mpr (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab))
  simp only [featureScalar_mul]
  refine ⟨(integrableOn_exp_mul_Ioi hneg 0).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hneg]
  rw [mul_zero, Real.exp_zero, div_neg_eq_neg_div, neg_div, neg_neg, ← mul_div_assoc, mul_one]

private theorem integrate_featureScalar_sq {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun s => featureScalar s a ^ 2) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), featureScalar s a ^ 2) = a := by
  have h := integrate_featureScalar_mul ha ha
  simp only [pow_two]
  refine ⟨h.1, h.2.trans ?_⟩
  by_cases hz : a = 0
  · simp [hz]
  · have hd : a + a ≠ 0 := by
      intro hzero
      apply hz
      linarith
    field_simp [hd] <;> ring

private theorem integrate_featureScalar_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntegrableOn (fun s => (featureScalar s a - featureScalar s b) ^ 2) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), (featureScalar s a - featureScalar s b) ^ 2) =
        (a - b) ^ 2 / (a + b) := by
  obtain ⟨hiA, hA⟩ := integrate_featureScalar_sq ha
  obtain ⟨hiB, hB⟩ := integrate_featureScalar_sq hb
  obtain ⟨hiAB, hAB⟩ := integrate_featureScalar_mul ha hb
  have hpoint (s : ℝ) : (featureScalar s a - featureScalar s b) ^ 2 =
      featureScalar s a ^ 2 + featureScalar s b ^ 2 -
        2 * (featureScalar s a * featureScalar s b) := by ring
  simp only [hpoint]
  refine ⟨(hiA.add hiB).sub (hiAB.const_mul 2), ?_⟩
  have hsub := integral_sub (hiA.add hiB) (hiAB.const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hiA hiB, integral_const_mul, hA, hB, hAB]
  by_cases hz : a + b = 0
  · rw [hz]
    simp
  · field_simp [hz] <;> ring

/-- The exact squared distance of the features integrated over positive times.
The proof integrates the scalar exponential on each full mixed coordinate. -/
theorem integral_feature_distance (A B : DensityState n) :
    IntegrableOn (fun s => hsSq (feature A s - feature B s)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), hsSq (feature A s - feature B s)) = triangular A B := by
  let c : n × n → ℝ := fun ij => Complex.normSq (overlap A B ij.1 ij.2)
  let f : n × n → ℝ → ℝ := fun ij s =>
    (featureScalar s (eigenvalue A ij.1) - featureScalar s (eigenvalue B ij.2)) ^ 2
  have h (ij : n × n) : IntegrableOn (f ij) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), f ij s) =
        (eigenvalue A ij.1 - eigenvalue B ij.2) ^ 2 / weight A B ij.1 ij.2 :=
    integrate_featureScalar_sub_sq (eigenvalue_nonneg A _) (eigenvalue_nonneg B _)
  have hpoint (s : ℝ) : hsSq (feature A s - feature B s) = ∑ ij, c ij * f ij s := by
    rw [← hsSq_coordinates (eigenbasis A) (eigenbasis B), hsSq_eq_sum]
    simp only [feature, coordinates_spectral_sub, ← Complex.normSq_eq_norm_sq, normSq_scaled]
    exact Finset.sum_congr rfl fun ij _ => mul_comm _ _
  have hterm (ij : n × n) : IntegrableOn (fun s => c ij * f ij s) (Set.Ioi 0) :=
    (h ij).1.const_mul _
  simp only [hpoint]
  refine ⟨integrable_finsetSum _ (fun ij _ => hterm ij), ?_⟩
  rw [integral_finsetSum _ (fun ij _ => hterm ij)]
  unfold triangular
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [integral_const_mul, (h ij).2]
  simp only [c, ← mul_div_assoc]
  ring

/-- The exact cosine-transform multiplier of the strip's upper weight. -/
def fourierFactor (ω : ℝ) : ℝ :=
  if ω = 0 then 1 else (ω / 2) / Real.sinh (ω / 2)

private theorem petzWeight_nonneg (t : ℝ) : 0 ≤ petzWeight t :=
  (div_pos Real.pi_pos (add_pos (Real.cosh_pos _) zero_lt_one)).le

private theorem continuous_petzWeight : Continuous petzWeight := by
  unfold petzWeight
  exact continuous_const.div (by fun_prop)
    (fun t => (add_pos (Real.cosh_pos (2 * Real.pi * t)) zero_lt_one).ne')

private theorem integrable_petzWeight_mul_bounded {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∀ t, |f t| ≤ 1) : Integrable (fun t => petzWeight t * f t) := by
  refine PetzStripFiniteSeries.integrable_petzWeight.mono'
    (continuous_petzWeight.mul hf).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_of_nonneg (petzWeight_nonneg t), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (petzWeight_nonneg t) (hb t)

private theorem integrable_petzWeight_cos (ω : ℝ) :
    Integrable (fun t => petzWeight t * Real.cos (ω * t)) :=
  integrable_petzWeight_mul_bounded (by fun_prop) (fun _ => Real.abs_cos_le_one _)

private theorem integrable_petzWeight_sin (ω : ℝ) :
    Integrable (fun t => petzWeight t * Real.sin (ω * t)) :=
  integrable_petzWeight_mul_bounded (by fun_prop) (fun _ => Real.abs_sin_le_one _)

private theorem integral_petzWeight_sin (ω : ℝ) :
    (∫ t, petzWeight t * Real.sin (ω * t)) = 0 := by
  let f : ℝ → ℝ := fun t => petzWeight t * Real.sin (ω * t)
  have hf (t : ℝ) : f (-t) = -f t := by
    simp only [f, petzWeight, mul_neg, Real.sin_neg, Real.cosh_neg]
  have hreflect : (∫ t, f (-t)) = ∫ t, f t :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding f
  simp only [hf, integral_neg] at hreflect
  change (∫ t, f t) = 0
  linarith only [hreflect]

theorem fourierFactor_nonneg (ω : ℝ) : 0 ≤ fourierFactor ω := by
  unfold fourierFactor
  split_ifs with hzero
  · norm_num
  · rcases lt_or_gt_of_ne hzero with h | h
    · have hh : ω / 2 < 0 := by linarith
      exact div_nonneg_of_nonpos hh.le (Real.sinh_neg_iff.mpr hh).le
    · have hh : 0 < ω / 2 := by linarith
      exact div_nonneg hh.le (Real.sinh_pos_iff.mpr hh).le

theorem fourierFactor_le_one (ω : ℝ) : fourierFactor ω ≤ 1 := by
  rw [← PetzStripFiniteSeries.integral_petzWeight, ←
    show (∫ t, petzWeight t * Real.cos (ω * t)) = fourierFactor ω from
      PetzStripFiniteSeries.integral_petzWeight_mul_cos ω]
  exact integral_mono (integrable_petzWeight_cos ω) PetzStripFiniteSeries.integrable_petzWeight
    (fun t => mul_le_of_le_one_right (petzWeight_nonneg t) (Real.cos_le_one _))

/-- The phase of one modular eigenvalue or one frequency difference. -/
def phase (ω t : ℝ) : ℂ := Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)

private theorem phase_normSq (ω t : ℝ) : Complex.normSq (phase ω t) = 1 := by
  rw [Complex.normSq_eq_norm_sq, phase, Complex.norm_exp_ofReal_mul_I, one_pow]

private theorem normSq_sub_le (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * (Complex.normSq a + Complex.normSq b) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg (a - b)) (norm_sub_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

/-- Exact reflection-averaged square for a complex orbit entry, including
the constant mode. -/
theorem integral_phase_distance (ω : ℝ) (a b : ℂ) :
    Integrable (fun t => petzWeight t * Complex.normSq (a - phase ω t * b)) ∧
      (∫ t, petzWeight t * Complex.normSq (a - phase ω t * b)) =
        fourierFactor ω * Complex.normSq (a - b) +
          (1 - fourierFactor ω) * (Complex.normSq a + Complex.normSq b) := by
  let c := a * conj b
  have hpoint (t : ℝ) : petzWeight t * Complex.normSq (a - phase ω t * b) =
      (Complex.normSq a + Complex.normSq b) * petzWeight t -
        ((2 * c.re) * (petzWeight t * Real.cos (ω * t)) +
          (2 * c.im) * (petzWeight t * Real.sin (ω * t))) := by
    have hc : a * conj (phase ω t * b) = c * conj (phase ω t) := by
      simp only [c, map_mul]
      ring
    rw [Complex.normSq_sub, Complex.normSq_mul, phase_normSq, one_mul, hc]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, phase,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hmass := PetzStripFiniteSeries.integrable_petzWeight.const_mul
    (Complex.normSq a + Complex.normSq b)
  have hcos := (integrable_petzWeight_cos ω).const_mul (2 * c.re)
  have hsin := (integrable_petzWeight_sin ω).const_mul (2 * c.im)
  simp only [hpoint]
  refine ⟨hmass.sub (hcos.add hsin), ?_⟩
  have hsub := integral_sub hmass (hcos.add hsin)
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hcos hsin]
  simp only [integral_const_mul, PetzStripFiniteSeries.integral_petzWeight,
    PetzStripFiniteSeries.integral_petzWeight_mul_cos, integral_petzWeight_sin,
    Complex.normSq_sub, fourierFactor, c]
  ring

theorem normSq_sub_le_twice_integral_phase_distance (ω : ℝ) (a b : ℂ) :
    Complex.normSq (a - b) ≤
      2 * ∫ t, petzWeight t * Complex.normSq (a - phase ω t * b) := by
  rw [(integral_phase_distance ω a b).2]
  have h₁ := mul_nonneg (fourierFactor_nonneg ω) (Complex.normSq_nonneg (a - b))
  have h₂ := mul_nonneg (sub_nonneg.mpr (fourierFactor_le_one ω))
    (sub_nonneg.mpr (normSq_sub_le a b))
  nlinarith only [h₁, h₂]

private def diagonalPhase (κ : n → ℝ) (t : ℝ) : Matrix.unitaryGroup n ℂ := by
  refine ⟨Matrix.diagonal (fun i => phase (κ i) t), Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change Matrix.diagonal (fun i => phase (κ i) t) *
    (Matrix.diagonal (fun i => phase (κ i) t))ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal']
  have h (i : n) : phase (κ i) t * star (phase (κ i) t) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, phase_normSq, Complex.ofReal_one]
  simpa only [Pi.star_apply, h] using
    (Matrix.diagonal_one : Matrix.diagonal (fun _ : n => (1 : ℂ)) = 1)

/-- Modular unitary in an arbitrary fixed basis. For a supported reference
matrix take `κ` to be its log-spectrum on the reference carrier. -/
def modularUnitary (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ) (t : ℝ) :
    Matrix.unitaryGroup n ℂ := U * diagonalPhase κ t * star U

/-- Unitary conjugation on matrices. -/
def conjugate (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  U.val * X * U.valᴴ

private theorem coordinates_modularOrbit (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ)
    (t : ℝ) (X : Matrix n n ℂ) (i j : n) :
    coordinates U U (conjugate (modularUnitary U κ t) X) i j =
      phase (κ i - κ j) t * coordinates U U X i j := by
  let P : Matrix n n ℂ := Matrix.diagonal (fun i => phase (κ i) t)
  have heq : (modularUnitary U κ t).val = U.val * P * U.valᴴ := rfl
  have hcancel (Z : Matrix n n ℂ) : U.valᴴ * (U.val * Z) = Z := by
    rw [← Matrix.mul_assoc, adjoint_mul_unitary, Matrix.one_mul]
  have hmatrix : coordinates U U (conjugate (modularUnitary U κ t) X) =
      P * coordinates U U X * Pᴴ := by
    simp only [coordinates, conjugate, heq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, adjoint_mul_unitary,
      Matrix.mul_one, hcancel]
  rw [hmatrix, show P = Matrix.diagonal (fun i => phase (κ i) t) from rfl,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hp : phase (κ i) t * star (phase (κ j) t) = phase (κ i - κ j) t := by
    simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hp]
  simp only [Pi.star_apply]
  ring

/-- The upper-strip average controls the original Hilbert–Schmidt distance. -/
theorem hsSq_le_twice_integral_modularOrbit (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ)
    (X Y : Matrix n n ℂ) :
    Integrable (fun t => petzWeight t * hsSq (X - conjugate (modularUnitary U κ t) Y)) ∧
      hsSq (X - Y) ≤
        2 * ∫ t, petzWeight t * hsSq (X - conjugate (modularUnitary U κ t) Y) := by
  let f : n × n → ℝ → ℝ := fun ij t => petzWeight t * Complex.normSq
    (coordinates U U X ij.1 ij.2 - phase (κ ij.1 - κ ij.2) t * coordinates U U Y ij.1 ij.2)
  have hf (ij : n × n) : Integrable (f ij) := (integral_phase_distance _ _ _).1
  have hpoint (t : ℝ) :
      petzWeight t * hsSq (X - conjugate (modularUnitary U κ t) Y) = ∑ ij, f ij t := by
    rw [← hsSq_coordinates U U, hsSq_eq_sum, Finset.mul_sum]
    simp only [f, ← Complex.normSq_eq_norm_sq, coordinates_sub, Matrix.sub_apply,
      coordinates_modularOrbit]
  simp only [hpoint]
  refine ⟨integrable_finsetSum _ (fun ij _ => hf ij), ?_⟩
  rw [integral_finsetSum _ (fun ij _ => hf ij), Finset.mul_sum,
    ← hsSq_coordinates U U, hsSq_eq_sum]
  simp only [← Complex.normSq_eq_norm_sq, coordinates_sub, Matrix.sub_apply]
  exact Finset.sum_le_sum fun ij _ =>
    normSq_sub_le_twice_integral_phase_distance (κ ij.1 - κ ij.2) _ _

/-- Conjugation of an actual density state, including states of deficient rank. -/
def conjugateState (U : Matrix.unitaryGroup n ℂ) (A : DensityState n) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (conjugate U (ofMatrix.symm A.1)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((posSemidef A).mul_mul_conjTranspose_same U.val).nonneg
  · change (conjugate U (ofMatrix.symm A.1)).trace = 1
    rw [conjugate, Matrix.trace_mul_cycle, adjoint_mul_unitary, Matrix.one_mul]
    exact A.trace_eq_one

private theorem feature_eq_cfc (A : DensityState n) (s : ℝ) :
    feature A s = cfc (featureScalar s) (ofMatrix.symm A.1) := by
  rw [feature, spectral_eq_cfc, (posSemidef A).1.cfc_eq]

theorem feature_conjugateState (U : Matrix.unitaryGroup n ℂ) (A : DensityState n) (s : ℝ) :
    feature (conjugateState U A) s = conjugate U (feature A s) := by
  rw [feature_eq_cfc, feature_eq_cfc]
  exact Matrix.cfc_conj_unitary (A := (ofMatrix.symm A.1)) (featureScalar s) U

private theorem hsSq_conjugate (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    hsSq (conjugate U X) = hsSq X := by
  simpa only [coordinates, conjugate, show (star U).val = U.valᴴ from rfl,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
    hsSq_coordinates (star U) (star U) X

private theorem hsSq_nonneg (X : Matrix n n ℂ) : 0 ≤ hsSq X := by
  rw [hsSq_eq_sum]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem hsSq_sub_le (X Y : Matrix n n ℂ) :
    hsSq (X - Y) ≤ 2 * (hsSq X + hsSq Y) := by
  simp only [hsSq_eq_sum, Matrix.sub_apply, ← Complex.normSq_eq_norm_sq,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun ij _ => normSq_sub_le (X ij.1 ij.2) (Y ij.1 ij.2)

private theorem hsSq_feature (A : DensityState n) (s : ℝ) :
    hsSq (feature A s) = ∑ i, featureScalar s (eigenvalue A i) ^ 2 := by
  let U := eigenbasis A
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (featureScalar s (eigenvalue A i) : ℂ))
  have h (Z : Matrix n n ℂ) : U.valᴴ * (U.val * Z) = Z := by
    rw [← Matrix.mul_assoc, adjoint_mul_unitary, Matrix.one_mul]
  have hcoord : coordinates U U (feature A s) = D := by
    change U.valᴴ * ((U.val * (D * U.valᴴ)) * U.val) = D
    simp only [Matrix.mul_assoc, adjoint_mul_unitary, Matrix.mul_one, h]
  rw [← hsSq_coordinates U U, hcoord, hsSq, tracePair]
  simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]

private theorem integrableOn_hsSq_feature (A : DensityState n) :
    IntegrableOn (fun s => hsSq (feature A s)) (Set.Ioi 0) := by
  simp only [hsSq_feature]
  exact integrable_finsetSum _ fun i _ => (integrate_featureScalar_sq (eigenvalue_nonneg A i)).1

private theorem continuous_diag {α : Type*} [TopologicalSpace α] (f : n → α → ℂ)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => Matrix.diagonal (fun i => f i x)) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i = j
  · simpa only [h, Matrix.diagonal_apply_eq] using hf j
  · simpa only [Matrix.diagonal_apply_ne _ h] using (continuous_const : Continuous (fun _ : α => (0 : ℂ)))

private theorem continuous_feature (A : DensityState n) : Continuous (feature A) := by
  unfold feature spectral
  refine continuous_const.mul ((continuous_diag _ fun i => ?_).mul continuous_const)
  unfold featureScalar
  fun_prop

private theorem continuous_conjugate_modular (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ)
    {α : Type*} [TopologicalSpace α] {t : α → ℝ} {X : α → Matrix n n ℂ}
    (ht : Continuous t) (hX : Continuous X) :
    Continuous (fun x => conjugate (modularUnitary U κ (t x)) (X x)) := by
  have hp (i : n) : Continuous (fun x => phase (κ i) (t x)) := by
    unfold phase
    fun_prop
  have hm : Continuous (fun x => (modularUnitary U κ (t x)).val) := by
    change Continuous (fun x => (U.val * Matrix.diagonal (fun i => phase (κ i) (t x))) * U.valᴴ)
    exact (continuous_const.mul (continuous_diag _ hp)).mul continuous_const
  exact (hm.mul hX).mul hm.matrix_conjTranspose

private theorem continuous_hsSq : Continuous (hsSq : Matrix n n ℂ → ℝ) := by
  simp only [show (hsSq : Matrix n n ℂ → ℝ) = fun X => ∑ ij : n × n, ‖X ij.1 ij.2‖ ^ 2
    from funext hsSq_eq_sum]
  exact continuous_finsetSum _ fun ij _ => ((continuous_id.matrix_elem ij.1 ij.2).norm).pow 2

/-- Projection inequality for the actual density orbit. The product
integrability is proved using a time-independent feature bound in the
modular variable. -/
theorem triangular_le_twice_integral_modularOrbit (A B : DensityState n)
    (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ) :
    Integrable (fun t => petzWeight t * triangular A (conjugateState (modularUnitary U κ t) B)) ∧
      triangular A B ≤
        2 * ∫ t, petzWeight t * triangular A (conjugateState (modularUnitary U κ t) B) := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioi 0)
  let F : ℝ × ℝ → ℝ := fun z =>
    petzWeight z.2 * hsSq (feature A z.1 - conjugate (modularUnitary U κ z.2) (feature B z.1))
  have hbound : Integrable (fun s => 2 * (hsSq (feature A s) + hsSq (feature B s))) μ :=
    ((integrableOn_hsSq_feature A).add (integrableOn_hsSq_feature B)).const_mul 2
  have hcont : Continuous F :=
    (continuous_petzWeight.comp continuous_snd).mul
      (continuous_hsSq.comp (((continuous_feature A).comp continuous_fst).sub
        (continuous_conjugate_modular U κ continuous_snd
          ((continuous_feature B).comp continuous_fst))))
  have hprod : Integrable F (μ.prod volume) := by
    refine (hbound.mul_prod PetzStripFiniteSeries.integrable_petzWeight).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    dsimp only [F]
    rw [Real.norm_of_nonneg (mul_nonneg (petzWeight_nonneg _) (hsSq_nonneg _))]
    rw [mul_comm (2 * (hsSq (feature A z.1) + hsSq (feature B z.1))) (petzWeight z.2)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [hsSq_conjugate] using
        hsSq_sub_le (feature A z.1) (conjugate (modularUnitary U κ z.2) (feature B z.1)))
      (petzWeight_nonneg _)
  have hright (t : ℝ) : (∫ s, F (s, t) ∂μ) =
      petzWeight t * triangular A (conjugateState (modularUnitary U κ t) B) := by
    simp only [F, ← feature_conjugateState, integral_const_mul, μ, (integral_feature_distance _ _).2]
  refine ⟨by simpa only [hright] using hprod.integral_prod_right, ?_⟩
  have hmono : (∫ s, hsSq (feature A s - feature B s) ∂μ) ≤
      ∫ s, 2 * (∫ t, F (s, t)) ∂μ := by
    refine integral_mono (integral_feature_distance A B).1
      (hprod.integral_prod_left.const_mul 2) ?_
    intro s
    exact (hsSq_le_twice_integral_modularOrbit U κ (feature A s) (feature B s)).2
  rw [integral_const_mul, integral_integral_swap (f := fun s t => F (s, t)) hprod] at hmono
  simpa only [μ, (integral_feature_distance A B).2, hright] using hmono

/-- A square amplitude admits a unitary polar extension even when it is
singular. This form uses the left Gram matrix on the recovered carrier. -/
private theorem exists_left_polar (G : Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ, G = CFC.sqrt (G * Gᴴ) * U.val := by
  obtain ⟨L, R, hG⟩ := exists_svd_sqrt_eigenvalues G
  let D : Matrix n n ℂ := Matrix.diagonal (fun i =>
    (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self G).eigenvalues i) : ℂ))
  have hG' : G = L.val * D * R.valᴴ := hG
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast Real.sqrt_nonneg ((Matrix.isHermitian_conjTranspose_mul_self G).eigenvalues i)
  let U : Matrix.unitaryGroup n ℂ := L * star R
  have hU : U.val = L.val * R.valᴴ := rfl
  let H := G * U.valᴴ
  have hH : H.PosSemidef := by
    have heq : H = L.val * D * L.valᴴ := by
      dsimp only [H]
      rw [hU, hG', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R.valᴴ R.val,
        adjoint_mul_unitary, Matrix.one_mul]
    rw [heq]
    exact hD.mul_mul_conjTranspose_same L.val
  have hh : H * H = G * Gᴴ := calc
    H * H = H * Hᴴ := by rw [hH.isHermitian.eq]
    _ = G * Gᴴ := by
      simp only [H, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, ← Matrix.mul_assoc U.valᴴ U.val, adjoint_mul_unitary, Matrix.one_mul]
  refine ⟨U, ?_⟩
  rw [CFC.sqrt_unique hh hH.nonneg]
  simp only [H, Matrix.mul_assoc, adjoint_mul_unitary, Matrix.mul_one]

/-- The physical upper-strip overlap is bounded by root fidelity whenever
its completed amplitude has the recovered state as its left Gram matrix. -/
theorem tracePair_sqrt_amplitude_le_rootFidelity (A B : DensityState n)
    (G : Matrix n n ℂ) (hG : G * Gᴴ = (ofMatrix.symm B.1)) :
    tracePair (CFC.sqrt (ofMatrix.symm A.1)) G ≤ rootFidelity A B := by
  obtain ⟨U, hpolar⟩ := exists_left_polar G
  have hroot : (CFC.sqrt (ofMatrix.symm A.1)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (ofMatrix.symm A.1))).isHermitian
  unfold tracePair rootFidelity
  rw [hpolar, hG, hroot.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hub := (traceNorm_eq_max_re_tr_U
    (CFC.sqrt (ofMatrix.symm A.1) * CFC.sqrt (ofMatrix.symm B.1))).2
  simp only [upperBounds, Set.mem_ofPred_eq] at hub
  exact hub ⟨U, rfl⟩

/-- Pointwise conversion of the linear upper-strip deficit. -/
theorem triangular_le_two_upperDeficit (A B : DensityState n) (G : Matrix n n ℂ)
    (hG : G * Gᴴ = (ofMatrix.symm B.1)) :
    triangular A B ≤ 2 * (2 * (1 - tracePair (CFC.sqrt (ofMatrix.symm A.1)) G)) := by
  have h₁ := triangular_le_two_one_sub_rootFidelity_sq A B
  have h₂ := tracePair_sqrt_amplitude_le_rootFidelity A B G hG
  nlinarith only [h₁, h₂, sq_nonneg (1 - rootFidelity A B)]

section SupportedStrip

open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (supported_relative_modular_model)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
  (deficit integral_supported_channel_strip lower_deficit_nonneg)
open PetzCothStripMode (lowerWeight)

variable [Nonempty n]
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- From the physical upper amplitude to the commuting-output coefficient
eight. The two pointwise equalities supply the completed amplitude on
the original carrier and identify its left Gram matrix and real overlap. -/
theorem traceNorm_sub_sq_le_eight_of_supported_upper_amplitude
    (Φ : QuantumChannel n m) (ρ σ τ : DensityState n) (support : SupportContained ρ σ)
    (U : Matrix.unitaryGroup n ℂ) (κ : n → ℝ) (G : ℝ → Matrix n n ℂ)
    (hGram : ∀ t, G t * (G t)ᴴ = ofMatrix.symm (conjugateState (modularUnitary U κ t) τ).1)
    (hOverlap : ∀ t, deficit (supported_relative_modular_model Φ ρ σ support).data (1 / 2) t =
      2 * (1 - tracePair (CFC.sqrt (ofMatrix.symm ρ.1)) (G t))) :
    traceNorm ((ofMatrix.symm ρ.1) - (ofMatrix.symm τ.1)) ^ 2 ≤
      8 * (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  let M := supported_relative_modular_model Φ ρ σ support
  obtain ⟨_, hu, heq⟩ := integral_supported_channel_strip Φ ρ σ support
  change Integrable (fun t => petzWeight t * deficit M.data (1 / 2) t) at hu
  change (∫ t, lowerWeight t * deficit M.data 0 t) +
    (∫ t, petzWeight t * deficit M.data (1 / 2) t) =
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) at heq
  have hl : 0 ≤ ∫ t, lowerWeight t * deficit M.data 0 t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _)))
      (lower_deficit_nonneg M t)
  obtain ⟨hi, hp⟩ := triangular_le_twice_integral_modularOrbit ρ τ U κ
  have hupper :
      (∫ t, petzWeight t * triangular ρ (conjugateState (modularUnitary U κ t) τ)) ≤
      2 * ∫ t, petzWeight t * deficit M.data (1 / 2) t := by
    rw [← integral_const_mul]
    refine integral_mono hi (hu.const_mul 2) ?_
    intro t
    dsimp only
    rw [mul_left_comm, hOverlap t]
    exact mul_le_mul_of_nonneg_left
      (triangular_le_two_upperDeficit ρ _ (G t) (hGram t)) (petzWeight_nonneg t)
  linarith only [traceNorm_sub_sq_le_two_triangular ρ τ, hp, hupper, heq, hl]

end SupportedStrip

end D5.S3.Quantum.Recovery.PetzTriangularOrbit
