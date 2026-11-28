/- GID: D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/DiracCliffordSpinors4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dirac matrices, Weyl projections, Lorentz covariance and Majorana reality. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.SL2CLorentzCover4D
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! The chiral Clifford matrices use the time-positive metric of the Pauli cover.
The finite matrix identities are checked over Gaussian integers before scalar extension. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate

namespace D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev Spinor := Fin 4 → ℂ

private abbrev ZMat4 := Matrix (Fin 4) (Fin 4) GaussianInt
private def imaginary : GaussianInt := ⟨0, 1⟩
private def complexify : ZMat4 →+* Mat4 := GaussianInt.toComplex.mapMatrix

private def gammaZ : Fin 4 → ZMat4 :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0],
    !![0, 0, 0, -imaginary; 0, 0, imaginary, 0;
       0, imaginary, 0, 0; -imaginary, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]]

def γ (μ : Fin 4) : Mat4 := complexify (gammaZ μ)

private def metricZ (μ ν : Fin 4) : GaussianInt :=
  if μ = ν then if μ = 0 then 1 else -1 else 0

/-- The metric has signature one positive and three negative. -/
def η (μ ν : Fin 4) : ℂ := (metricZ μ ν : ℂ)

private theorem complexify_smul (z : GaussianInt) (M : ZMat4) :
    complexify (z • M) = (z : ℂ) • complexify M := by
  ext i j
  exact map_mul GaussianInt.toComplex _ _

private theorem complexify_trace (M : ZMat4) :
    ((M.trace : GaussianInt) : ℂ) = (complexify M).trace :=
  map_sum GaussianInt.toComplex _ _

private theorem complexify_dagger (M : ZMat4) : complexify Mᴴ = (complexify M)ᴴ := by
  ext i j
  exact GaussianInt.toComplex_star _

private theorem complexify_transpose (M : ZMat4) : complexify Mᵀ = (complexify M)ᵀ := rfl

private theorem imaginary_cast : (imaginary : ℂ) = Complex.I := by
  simp [imaginary, GaussianInt.toComplex_def']

theorem clifford_anticommutator (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ = (2 * η μ ν) • (1 : Mat4) := by
  have h : ∀ a b, gammaZ a * gammaZ b + gammaZ b * gammaZ a =
      (2 * metricZ a b) • (1 : ZMat4) := by decide
  simpa only [map_add, map_mul, map_ofNat, complexify_smul, map_one, γ, η]
    using congrArg complexify (h μ ν)

theorem gamma_hermitian_conjugate (μ : Fin 4) : (γ μ)ᴴ = γ 0 * γ μ * γ 0 := by
  have h : ∀ a, (gammaZ a)ᴴ = gammaZ 0 * gammaZ a * gammaZ 0 := by decide
  simpa only [complexify_dagger, map_mul, γ] using congrArg complexify (h μ)

theorem gamma_trace_zero (μ : Fin 4) : (γ μ).trace = 0 := by
  have h : ∀ a, (gammaZ a).trace = 0 := by decide
  simpa only [complexify_trace, map_zero, γ] using congrArg GaussianInt.toComplex (h μ)

theorem gamma_two_trace (μ ν : Fin 4) : (γ μ * γ ν).trace = 4 * η μ ν := by
  have h : ∀ a b, (gammaZ a * gammaZ b).trace = 4 * metricZ a b := by decide
  simpa only [complexify_trace, map_mul, map_ofNat, γ, η]
    using congrArg GaussianInt.toComplex (h μ ν)

theorem gamma_four_trace (μ ν ρ σ : Fin 4) :
    (γ μ * γ ν * γ ρ * γ σ).trace =
      4 * (η μ ν * η ρ σ - η μ ρ * η ν σ + η μ σ * η ν ρ) := by
  have h : ∀ a b c d, (gammaZ a * gammaZ b * gammaZ c * gammaZ d).trace =
      4 * (metricZ a b * metricZ c d - metricZ a c * metricZ b d +
        metricZ a d * metricZ b c) := by decide
  simpa only [complexify_trace, map_mul, map_ofNat, map_sub, map_add, γ, η]
    using congrArg GaussianInt.toComplex (h μ ν ρ σ)

def slash (p : Spinor) : Mat4 := ∑ μ, p μ • γ μ

theorem feynman_slash_sq (p : Spinor) :
    slash p * slash p = (∑ μ, η μ μ * p μ ^ 2) • (1 : Mat4) := by
  have h : slash p * slash p = ∑ i, ∑ j, (p i * p j) • (γ i * γ j) := by
    rw [slash, Matrix.sum_mul]
    simp only [Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul, smul_smul]
    simp only [mul_comm (p _) (p _)]
  have h' : slash p * slash p = ∑ i, ∑ j, (p i * p j) • (γ j * γ i) := by
    rw [h, Finset.sum_comm]
    simp only [mul_comm (p _) (p _)]
  have hs : slash p * slash p + slash p * slash p =
      ∑ i, ∑ j, (p i * p j) • ((2 * η i j) • (1 : Mat4)) := by
    calc
      _ = _ := congrArg₂ (· + ·) h h'
      _ = _ := by simp only [← Finset.sum_add_distrib, ← smul_add, clifford_anticommutator]
  apply (smul_right_injective Mat4 (show (2 : ℂ) ≠ 0 by norm_num))
  change (2 : ℂ) • (slash p * slash p) = _
  rw [two_smul ℂ, hs]
  simp only [smul_smul, Finset.mul_sum, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hne
    simp [η, metricZ, Ne.symm hne]
  · simp

open SL2CLorentzCover4D in
theorem minkowski_slash_sq (p : V4) :
    slash (fun i => (p i : ℂ)) * slash (fun i => (p i : ℂ)) =
      (minkowskiNormSq p : ℂ) • (1 : Mat4) := by
  rw [feynman_slash_sq]
  congr 1
  norm_num [η, metricZ, minkowskiNormSq, Fin.sum_univ_four, GaussianInt.toComplex_neg,
    GaussianInt.toComplex_one]
  ring

private def gamma5Z : ZMat4 := imaginary • (gammaZ 0 * gammaZ 1 * gammaZ 2 * gammaZ 3)

def gamma5 : Mat4 := Complex.I • (γ 0 * γ 1 * γ 2 * γ 3)

private theorem complexify_gamma5 : complexify gamma5Z = gamma5 := by
  simp only [gamma5Z, gamma5, complexify_smul, map_mul, imaginary_cast, γ]

private theorem explicit_gammaZ5 :
    gamma5Z = diagonal ![-1, -1, 1, 1] := by decide

theorem gamma5_explicit : gamma5 = diagonal ![-1, -1, 1, 1] := by
  rw [← complexify_gamma5, explicit_gammaZ5]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexify, GaussianInt.toComplex_neg,
      GaussianInt.toComplex_one, GaussianInt.toComplex_zero]

theorem gamma5_sq : gamma5 * gamma5 = 1 := by
  have h : gamma5Z * gamma5Z = 1 := by decide
  simpa only [map_mul, map_one, complexify_gamma5] using congrArg complexify h

theorem gamma5_hermitian : gamma5ᴴ = gamma5 := by
  rw [gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem gamma5_trace_zero : gamma5.trace = 0 := by
  have h : gamma5Z.trace = 0 := by decide
  simpa only [complexify_trace, complexify_gamma5, map_zero]
    using congrArg GaussianInt.toComplex h

theorem gamma5_anticommutes (μ : Fin 4) : gamma5 * γ μ + γ μ * gamma5 = 0 := by
  have h : ∀ a, gamma5Z * gammaZ a + gammaZ a * gamma5Z = 0 := by decide
  simpa only [map_add, map_mul, map_zero, complexify_gamma5, γ] using congrArg complexify (h μ)

def PL : Mat4 := (1 / 2 : ℂ) • (1 - gamma5)
def PR : Mat4 := (1 / 2 : ℂ) • (1 + gamma5)

private theorem chiral_diagonals :
    PL = diagonal ![1, 1, 0, 0] ∧ PR = diagonal ![0, 0, 1, 1] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [PL, PR, gamma5_explicit, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

theorem chiral_projectors_spec :
    PL * PL = PL ∧ PR * PR = PR ∧ PL * PR = 0 ∧ PR * PL = 0 ∧
      PL + PR = 1 ∧ PLᴴ = PL ∧ PRᴴ = PR ∧
        ∀ μ, γ μ * PL = PR * γ μ := by
  rcases chiral_diagonals with ⟨hl, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [hr, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [hl, hr, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [hl, hr, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hl, hr]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hl, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hr, Matrix.conjTranspose_apply]
  · intro μ
    rw [PL, PR, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, sub_eq_add_neg,
      eq_neg_of_add_eq_zero_left (gamma5_anticommutes μ)]

/-- Ordered scalar, vector, tensor, axial and pseudoscalar indices. -/
private def basisZ : Fin 16 → ZMat4 :=
  ![1, gammaZ 0, gammaZ 1, gammaZ 2, gammaZ 3,
    imaginary • (gammaZ 0 * gammaZ 1), imaginary • (gammaZ 0 * gammaZ 2),
    imaginary • (gammaZ 0 * gammaZ 3), imaginary • (gammaZ 1 * gammaZ 2),
    imaginary • (gammaZ 1 * gammaZ 3), imaginary • (gammaZ 2 * gammaZ 3),
    gammaZ 0 * gamma5Z, gammaZ 1 * gamma5Z, gammaZ 2 * gamma5Z, gammaZ 3 * gamma5Z, gamma5Z]

def clifford16 (i : Fin 16) : Mat4 := complexify (basisZ i)

def gammaTensor (μ ν : Fin 4) : Mat4 :=
  (Complex.I / 2) • (γ μ * γ ν - γ ν * γ μ)

theorem clifford16_components :
    clifford16 = ![1, γ 0, γ 1, γ 2, γ 3, gammaTensor 0 1, gammaTensor 0 2,
      gammaTensor 0 3, gammaTensor 1 2, gammaTensor 1 3, gammaTensor 2 3,
      γ 0 * gamma5, γ 1 * gamma5, γ 2 * gamma5, γ 3 * gamma5, gamma5] := by
  have tensor (a b : Fin 4) (hab : a ≠ b) :
      complexify (imaginary • (gammaZ a * gammaZ b)) = gammaTensor a b := by
    have h := clifford_anticommutator a b
    simp only [η, metricZ, if_neg hab, GaussianInt.toComplex_zero, mul_zero, zero_smul] at h
    rw [gammaTensor, complexify_smul, imaginary_cast, map_mul, ← γ, ← γ,
      eq_neg_of_add_eq_zero_right h, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    congr 1
    ring
  funext i
  fin_cases i <;>
    simp [clifford16, basisZ, tensor, γ, complexify_gamma5]

theorem clifford16_trace_orthogonal (a b : Fin 16) :
    ((clifford16 a)ᴴ * clifford16 b).trace = if a = b then 4 else 0 := by
  have h : ∀ i j, ((basisZ i)ᴴ * basisZ j).trace = if i = j then 4 else 0 := by decide
  simpa only [complexify_trace, map_mul, map_ofNat, map_zero, complexify_dagger, clifford16,
    apply_ite GaussianInt.toComplex] using congrArg GaussianInt.toComplex (h a b)

theorem clifford16_linearIndependent : LinearIndependent ℂ clifford16 := by
  apply Fintype.linearIndependent_iff.mpr
  intro c h i
  have hz := congrArg (fun M : Mat4 => ((clifford16 i)ᴴ * M).trace) h
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    clifford16_trace_orthogonal, smul_eq_mul, mul_ite, mul_zero,
    Finset.mem_univ, ite_true, Matrix.trace_zero,
    Finset.sum_ite_eq] at hz
  exact (mul_eq_zero.mp hz).resolve_right (by norm_num)

noncomputable def clifford16_basis : Module.Basis (Fin 16) ℂ Mat4 :=
  basisOfLinearIndependentOfCardEqFinrank clifford16_linearIndependent
    (by simp [Module.finrank_matrix])

theorem clifford16_span_top : Submodule.span ℂ (Set.range clifford16) = ⊤ := by
  simpa [clifford16_basis] using clifford16_basis.span_eq

open SL2CLorentzCover4D (H2 SL2C V4 pauliHerm pauliHerm_lorentzVec
  lorentzOfSL2C lorentzOfSL2C_mulVec lorentzOfSL2C_mul lorentzOfSL2C_one
  lorentzOfSL2C_preserves_minkowski)

private abbrev blockOrder : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
private abbrev flatten := Matrix.reindexAlgEquiv ℂ ℂ blockOrder
private abbrev blocks (a b c d : H2) : Mat4 := flatten (fromBlocks a b c d)
private abbrev diagonalBlocks (a d : H2) : Mat4 := blocks a 0 0 d

private theorem blocks_entry (a b c d : H2) (i j : Fin 4) :
    blocks a b c d i j = fromBlocks a b c d (blockOrder.symm i) (blockOrder.symm j) := rfl

private theorem block_indices :
    blockOrder.symm 0 = Sum.inl 0 ∧ blockOrder.symm 1 = Sum.inl 1 ∧
    blockOrder.symm 2 = Sum.inr 0 ∧ blockOrder.symm 3 = Sum.inr 1 := by decide

private theorem blocks_dagger (a b c d : H2) :
    (blocks a b c d)ᴴ = blocks aᴴ cᴴ bᴴ dᴴ := by
  change flatten (fromBlocks a b c d)ᴴ = _
  rw [Matrix.fromBlocks_conjTranspose]

private theorem blocks_mul (a b c d e f g h : H2) :
    blocks a b c d * blocks e f g h =
      blocks (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h) := by
  rw [blocks, blocks, ← map_mul, Matrix.fromBlocks_multiply]

private theorem gamma0_blocks : γ 0 = blocks 0 1 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [γ, gammaZ, complexify, blocks_entry, block_indices.1, block_indices.2.1,
    block_indices.2.2.1, block_indices.2.2.2]

private theorem gamma5_blocks : gamma5 = diagonalBlocks (-1) 1 := by
  rw [gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBlocks, blocks_entry, block_indices.1, block_indices.2.1,
    block_indices.2.2.1, block_indices.2.2.2]

private abbrev mat (A : SL2C) : H2 := A
private abbrev rightBlock (A : SL2C) : H2 := (mat A⁻¹)ᴴ

private theorem mat_mul_inv (A : SL2C) : mat A * mat A⁻¹ = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem mat_inv_mul (A : SL2C) : mat A⁻¹ * mat A = 1 := by
  simpa using mat_mul_inv A⁻¹

/-- The left block is fundamental and the right block is inverse adjoint. -/
def bispinor (A : SL2C) : Mat4 := diagonalBlocks (mat A) (rightBlock A)

theorem bispinor_one : bispinor 1 = 1 := by
  simp [bispinor, rightBlock, Matrix.SpecialLinearGroup.coe_one, Matrix.fromBlocks_one]

theorem bispinor_mul (A B : SL2C) : bispinor (A * B) = bispinor A * bispinor B := by
  rw [bispinor, bispinor, bispinor]
  change blocks (mat (A * B)) 0 0 (rightBlock (A * B)) = _
  rw [blocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.mul_inv_rev,
    rightBlock, Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul]

theorem bispinor_det_one (A : SL2C) : (bispinor A).det = 1 := by
  rw [bispinor, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁]
  change (mat A).det * ((mat A⁻¹)ᴴ).det = 1
  rw [Matrix.det_conjTranspose, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe]
  simp

theorem bispinor_inverse (A : SL2C) : (bispinor A)⁻¹ = bispinor A⁻¹ := by
  have h : bispinor A * bispinor A⁻¹ = 1 := by
    rw [← bispinor_mul, mul_inv_cancel, bispinor_one]
  exact Matrix.inv_eq_right_inv h

theorem bispinor_gamma0_intertwine (A : SL2C) :
    (bispinor A)ᴴ * γ 0 * bispinor A = γ 0 := by
  have h : (mat A)ᴴ * rightBlock A = 1 := by
    rw [← Matrix.conjTranspose_mul, mat_inv_mul, Matrix.conjTranspose_one]
  rw [bispinor, gamma0_blocks]
  change (blocks (mat A) 0 0 (rightBlock A))ᴴ * blocks 0 1 1 0 *
    blocks (mat A) 0 0 (rightBlock A) = _
  rw [blocks_dagger, blocks_mul, blocks_mul]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, h, mat_inv_mul]

theorem bispinor_commutes_gamma5 (A : SL2C) : bispinor A * gamma5 = gamma5 * bispinor A := by
  simp [bispinor, gamma5_blocks, diagonalBlocks, blocks_mul]

private theorem slash_pauli (p : V4) :
    slash (fun i => (p i : ℂ)) = blocks 0 (pauliHerm p) (pauliHerm p).adjugate 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, γ, gammaZ, complexify, imaginary_cast, blocks_entry, block_indices.1, block_indices.2.1,
      block_indices.2.2.1, block_indices.2.2.2, pauliHerm,
      Matrix.adjugate_fin_two, Fin.sum_univ_four, Matrix.smul_apply,
      GaussianInt.toComplex_neg, GaussianInt.toComplex_zero, GaussianInt.toComplex_one] <;> ring

theorem bispinor_slash_covariance (A : SL2C) (p : V4) :
    bispinor A * slash (fun i => (p i : ℂ)) * bispinor A⁻¹ =
      slash (fun i => ((lorentzOfSL2C A *ᵥ p) i : ℂ)) := by
  have h (B : SL2C) : (mat B).adjugate = mat B⁻¹ :=
    (Matrix.SpecialLinearGroup.coe_inv B).symm
  have h' (B : SL2C) : ((mat B)ᴴ).adjugate = rightBlock B := by
    rw [← Matrix.adjugate_conjTranspose, h]
  simp only [slash_pauli, lorentzOfSL2C_mulVec, pauliHerm_lorentzVec, bispinor, diagonalBlocks,
    blocks_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.adjugate_mul_distrib,
    h', h, Matrix.mul_assoc]
  rw [rightBlock, inv_inv]

theorem bispinor_lorentz_covariance (A : SL2C) (μ : Fin 4) :
    (bispinor A)⁻¹ * γ μ * bispinor A =
      ∑ ν, (lorentzOfSL2C A⁻¹ ν μ : ℂ) • γ ν := by
  have h := bispinor_slash_covariance A⁻¹ (Pi.single μ 1)
  rw [bispinor_inverse]
  simpa [slash, Matrix.mulVec_single_one, Pi.single_apply,
    apply_ite Complex.ofReal, Finset.sum_ite_eq', Finset.sum_ite_eq] using h

/-- Lower the spacetime index with the time-positive metric. -/
def gammaLower (μ : Fin 4) : Mat4 := ((![1, -1, -1, -1] : V4) μ : ℂ) • γ μ

private theorem lorentz_inverse_entry (A : SL2C) (μ ν : Fin 4) :
    (![1, -1, -1, -1] : V4) μ * lorentzOfSL2C A⁻¹ ν μ =
      lorentzOfSL2C A μ ν * (![1, -1, -1, -1] : V4) ν := by
  have h := congrArg (fun L => L * lorentzOfSL2C A⁻¹) (lorentzOfSL2C_preserves_minkowski A)
  have hh : lorentzOfSL2C A * lorentzOfSL2C A⁻¹ = 1 := by
    rw [← lorentzOfSL2C_mul, mul_inv_cancel, lorentzOfSL2C_one]
  simp only [Matrix.mul_assoc, hh, Matrix.mul_one] at h
  have he := (congrArg (fun L : Matrix (Fin 4) (Fin 4) ℝ => L ν μ) h).symm
  simp only [SL2CLorentzCover4D.eta, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply] at he
  fin_cases μ <;> fin_cases ν <;> simp at he ⊢ <;> linarith

theorem bispinor_lorentz_covariance_lower (A : SL2C) (μ : Fin 4) :
    (bispinor A)⁻¹ * gammaLower μ * bispinor A =
      ∑ ν, (lorentzOfSL2C A μ ν : ℂ) • gammaLower ν := by
  simp only [gammaLower, Matrix.mul_smul, Matrix.smul_mul, bispinor_lorentz_covariance,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, lorentz_inverse_entry]

def diracAdjoint (ψ : Spinor) : Spinor := (fun i => conj (ψ i)) ᵥ* γ 0

def diracBilinear (M : Mat4) (ψ χ : Spinor) : ℂ := diracAdjoint ψ ⬝ᵥ (M *ᵥ χ)

private theorem dirac_adjoint_transform (A : SL2C) (ψ : Spinor) :
    diracAdjoint (bispinor A *ᵥ ψ) = diracAdjoint ψ ᵥ* (bispinor A)⁻¹ := by
  have h := congrArg (fun M => M * (bispinor A)⁻¹) (bispinor_gamma0_intertwine A)
  have h' : bispinor A * (bispinor A)⁻¹ = 1 := by
    rw [bispinor_inverse, ← bispinor_mul, mul_inv_cancel, bispinor_one]
  simp only [Matrix.mul_assoc, h', Matrix.mul_one] at h
  change star (bispinor A *ᵥ ψ) ᵥ* γ 0 = (star ψ ᵥ* γ 0) ᵥ* (bispinor A)⁻¹
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h]

private theorem bilinear_transform (A : SL2C) (M : Mat4) (ψ χ : Spinor) :
    diracBilinear M (bispinor A *ᵥ ψ) (bispinor A *ᵥ χ) =
      diracBilinear ((bispinor A)⁻¹ * M * bispinor A) ψ χ := by
  simp only [diracBilinear, dirac_adjoint_transform, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem bilinear_sum {ι : Type*} [Fintype ι] (w : ι → ℂ) (M : ι → Mat4)
    (ψ χ : Spinor) :
    diracBilinear (∑ i, w i • M i) ψ χ = ∑ i, w i * diracBilinear (M i) ψ χ := by
  simp [diracBilinear, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul]

theorem dirac_scalar_invariant (A : SL2C) (ψ χ : Spinor) :
    diracBilinear 1 (bispinor A *ᵥ ψ) (bispinor A *ᵥ χ) = diracBilinear 1 ψ χ := by
  rw [bilinear_transform, Matrix.mul_one, bispinor_inverse, ← bispinor_mul, inv_mul_cancel,
    bispinor_one]

theorem dirac_pseudoscalar_invariant (A : SL2C) (ψ χ : Spinor) :
    diracBilinear gamma5 (bispinor A *ᵥ ψ) (bispinor A *ᵥ χ) = diracBilinear gamma5 ψ χ := by
  rw [bilinear_transform, Matrix.mul_assoc, ← bispinor_commutes_gamma5, ← Matrix.mul_assoc,
    bispinor_inverse, ← bispinor_mul, inv_mul_cancel, bispinor_one, Matrix.one_mul]

theorem dirac_vector_covariant (A : SL2C) (ψ χ : Spinor) (μ : Fin 4) :
    diracBilinear (gammaLower μ) (bispinor A *ᵥ ψ) (bispinor A *ᵥ χ) =
      ∑ ν, (lorentzOfSL2C A μ ν : ℂ) * diracBilinear (gammaLower ν) ψ χ := by
  rw [bilinear_transform, bispinor_lorentz_covariance_lower, bilinear_sum]

theorem dirac_axial_vector_covariant (A : SL2C) (ψ χ : Spinor) (μ : Fin 4) :
    diracBilinear (gammaLower μ * gamma5) (bispinor A *ᵥ ψ) (bispinor A *ᵥ χ) =
      ∑ ν, (lorentzOfSL2C A μ ν : ℂ) * diracBilinear (gammaLower ν * gamma5) ψ χ := by
  have h : (bispinor A)⁻¹ * (gammaLower μ * gamma5) * bispinor A =
      ((bispinor A)⁻¹ * gammaLower μ * bispinor A) * gamma5 := by
    simp only [Matrix.mul_assoc, bispinor_commutes_gamma5]
  rw [bilinear_transform, h, bispinor_lorentz_covariance_lower, Matrix.sum_mul]
  simp only [Matrix.smul_mul, bilinear_sum]


private def chargeMatrixZ : ZMat4 := imaginary • (gammaZ 2 * gammaZ 0)

def chargeMatrix : Mat4 := Complex.I • (γ 2 * γ 0)

private theorem complexify_chargeMatrix : complexify chargeMatrixZ = chargeMatrix := by
  simp only [chargeMatrixZ, chargeMatrix, complexify_smul, imaginary_cast, map_mul, γ]

theorem chargeConj_unitary_antisymm :
    chargeMatrixᴴ * chargeMatrix = 1 ∧ chargeMatrixᵀ = -chargeMatrix ∧
      chargeMatrix * chargeMatrix = -1 := by
  have h : chargeMatrixZᴴ * chargeMatrixZ = 1 ∧ chargeMatrixZᵀ = -chargeMatrixZ ∧
      chargeMatrixZ * chargeMatrixZ = -1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [complexify_chargeMatrix, map_one, map_mul, complexify_dagger]
      using congrArg complexify h.1
  · simpa only [complexify_chargeMatrix, map_neg, complexify_transpose]
      using congrArg complexify h.2.1
  · simpa only [complexify_chargeMatrix, map_one, map_mul, map_neg]
      using congrArg complexify h.2.2

theorem chargeConj_gamma (μ : Fin 4) :
    chargeMatrix * γ μ * chargeMatrix⁻¹ = -(γ μ)ᵀ := by
  have h : ∀ a, chargeMatrixZ * gammaZ a = -(gammaZ a)ᵀ * chargeMatrixZ := by decide
  have hc := congrArg complexify (h μ)
  simp only [map_mul, map_neg, complexify_chargeMatrix, complexify_transpose] at hc
  change chargeMatrix * γ μ = -(γ μ)ᵀ * chargeMatrix at hc
  have hu := chargeConj_unitary_antisymm.1
  rw [Matrix.inv_eq_left_inv hu]
  have hi := mul_eq_one_comm.mp hu
  rw [hc, Matrix.mul_assoc, hi, Matrix.mul_one]

private def chargeFactorZ : ZMat4 := imaginary • gammaZ 2
private def chargeFactor : Mat4 := Complex.I • γ 2

private theorem complexify_chargeFactor : complexify chargeFactorZ = chargeFactor := by
  simp only [chargeFactorZ, chargeFactor, complexify_smul, imaginary_cast, γ]

private abbrev barMat {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := M.map (starRingEnd ℂ)

def chargeConj (ψ : Spinor) : Spinor := chargeFactor *ᵥ star ψ

theorem chargeConj_eq_diracAdjoint (ψ : Spinor) :
    chargeConj ψ = chargeMatrix *ᵥ diracAdjoint ψ := by
  have h : (gammaZ 0)ᵀ = gammaZ 0 ∧ gammaZ 0 * gammaZ 0 = 1 := by decide
  have ht : (γ 0)ᵀ = γ 0 := by
    simpa only [γ, complexify_transpose] using congrArg complexify h.1
  have hs : γ 0 * γ 0 = 1 := by
    simpa only [γ, map_mul, map_one] using congrArg complexify h.2
  change chargeFactor *ᵥ star ψ = chargeMatrix *ᵥ (star ψ ᵥ* γ 0)
  rw [← Matrix.mulVec_transpose, ht, Matrix.mulVec_mulVec]
  simp [chargeMatrix, chargeFactor, Matrix.mul_assoc, hs]

private theorem bar_mulVec {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    star (M *ᵥ v) = barMat M *ᵥ star v :=
  funext (RingHom.map_mulVec (starRingEnd ℂ) M v)

private theorem chargeFactor_real : barMat chargeFactor = chargeFactor := by
  have h : chargeFactorZ.map star = chargeFactorZ := by decide
  rw [← complexify_chargeFactor]
  calc
    _ = complexify (chargeFactorZ.map star) := by
      ext i j
      exact (GaussianInt.toComplex_star _).symm
    _ = _ := congrArg complexify h

theorem chargeConj_involutive (ψ : Spinor) : chargeConj (chargeConj ψ) = ψ := by
  have h : chargeFactorZ * chargeFactorZ = 1 := by decide
  have hc : chargeFactor * chargeFactor = 1 := by
    simpa only [complexify_chargeFactor, map_mul, map_one] using congrArg complexify h
  simp only [chargeConj, bar_mulVec, chargeFactor_real, star_star, Matrix.mulVec_mulVec,
    hc, Matrix.one_mulVec]

theorem chargeConj_flips_chirality (ψ : Spinor) :
    chargeConj (PL *ᵥ ψ) = PR *ᵥ chargeConj ψ := by
  have hb : barMat PL = PL := by
    rw [chiral_diagonals.1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hc : chargeFactor * PL = PR * chargeFactor := by
    rw [chiral_diagonals.1, chiral_diagonals.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, chargeFactor, γ, gammaZ, complexify]
  simp only [chargeConj, bar_mulVec, hb, Matrix.mulVec_mulVec, hc]

theorem no_majorana_weyl_4d (ψ : Spinor) (hc : chargeConj ψ = ψ) (hl : PL *ᵥ ψ = ψ) :
    ψ = 0 := by
  have hr := chargeConj_flips_chirality ψ
  rw [hl, hc] at hr
  have h := chiral_projectors_spec.2.2.1
  calc
    ψ = PL *ᵥ (PR *ᵥ ψ) := by rw [← hr, hl]
    _ = 0 := by rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

private def epsilon : H2 := !![0, 1; -1, 0]

private theorem chargeFactor_blocks : chargeFactor = blocks 0 epsilon (-epsilon) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chargeFactor, γ, gammaZ, complexify, imaginary_cast, blocks_entry, block_indices.1,
      block_indices.2.1, block_indices.2.2.1, block_indices.2.2.2, epsilon,
      GaussianInt.toComplex_neg, Complex.I_mul_I]

private theorem epsilon_intertwine (A : SL2C) :
    epsilon * barMat (mat A) = rightBlock A * epsilon := by
  change epsilon * barMat (A : H2) = ((A⁻¹ : SL2C) : H2)ᴴ * epsilon
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsilon, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

private theorem bar_blocks (a b c d : H2) :
    barMat (blocks a b c d) = blocks (barMat a) (barMat b) (barMat c) (barMat d) := by
  ext i j
  simp only [Matrix.map_apply, blocks_entry]
  cases blockOrder.symm i <;> cases blockOrder.symm j <;> rfl

theorem chargeConj_lorentz_equivariant (A : SL2C) (ψ : Spinor) :
    chargeConj (bispinor A *ᵥ ψ) = bispinor A *ᵥ chargeConj ψ := by
  have h : epsilon * barMat (rightBlock A) = mat A * epsilon := by
    change epsilon * barMat (((A⁻¹ : SL2C) : H2)ᴴ) = (A : H2) * epsilon
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [epsilon, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  simp only [chargeConj, bar_mulVec, Matrix.mulVec_mulVec, chargeFactor_blocks, bispinor,
    diagonalBlocks, bar_blocks, Matrix.map_zero, map_zero, blocks_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_zero,
    epsilon_intertwine, h]

end D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D
