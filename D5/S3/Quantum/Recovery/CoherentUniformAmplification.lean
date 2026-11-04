/- GID: D5/S3/Quantum/Recovery/CoherentUniformAmplification
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CoherentUniformAmplification
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: A scalar success Gram gives a uniform operator rotation on the whole source. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-! The same two reflections act on every source column. The standard
amplitude-amplification rotation is expressed as a rectangular operator
identity, rather than a reflection chosen from an unknown input vector.
The exact coin construction and its query bound are separate statements. -/

noncomputable section
open scoped Matrix Kronecker

namespace D5.S3.Quantum.Recovery.CoherentUniformAmplification

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {s l : Type*} [Fintype s] [DecidableEq s] [Fintype l] [DecidableEq l]

/-- The normalized successful source isometry. -/
def success (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ) : Matrix l s ℂ :=
  (Real.sqrt p : ℂ)⁻¹ • (P * U)

/-- The normalized failed source isometry, for success strictly below one. -/
def failure (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ) : Matrix l s ℂ :=
  (Real.sqrt (1 - p) : ℂ)⁻¹ • ((1 - P) * U)

/-- Reflection in the prepared source subspace, followed by a good-flag flip. -/
def iterate (U : Matrix l s ℂ) (P : Matrix l l ℂ) : Matrix l l ℂ :=
  (2 • (U * Uᴴ) - 1) * (1 - 2 • P)

private theorem rotation_power (Q : Matrix l l ℂ) (W B : Matrix l s ℂ) (θ : ℝ)
    (hW : Q * W = (Real.cos (2 * θ) : ℂ) • W - (Real.sin (2 * θ) : ℂ) • B)
    (hB : Q * B = (Real.sin (2 * θ) : ℂ) • W + (Real.cos (2 * θ) : ℂ) • B)
    (n : ℕ) :
    Q ^ n * ((Real.sin θ : ℂ) • W + (Real.cos θ : ℂ) • B) =
      (Real.sin ((2 * n + 1) * θ) : ℂ) • W +
      (Real.cos ((2 * n + 1) * θ) : ℂ) • B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, hW, hB]
    have ha : (2 * (↑(n + 1) : ℝ) + 1) * θ = (2 * n + 1) * θ + 2 * θ := by
      push_cast
      ring
    rw [ha, Real.sin_add, Real.cos_add]
    push_cast
    simp only [smul_add, smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

private theorem source_gram (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ)
    (hU : Uᴴ * U = 1) (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * U)ᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ)) :
    Uᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ) ∧
    ((1 - P) * U)ᴴ * ((1 - P) * U) = (1 - (p : ℂ)) • (1 : Matrix s s ℂ) ∧
    (P * U)ᴴ * ((1 - P) * U) = 0 := by
  have hg : Uᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ) := by
    simpa only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc P P, hPP] using hA
  refine ⟨hg, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hP, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P U, hPP, hg, hU]
    module
  · simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P U, hPP, sub_self, Matrix.mul_zero]

private theorem frame_rotation (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ)
    (hp : 0 < p) (hpl : p < 1) (hU : Uᴴ * U = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * U)ᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ)) :
    let θ := Real.arcsin (Real.sqrt p)
    let W := success U P p
    let B := failure U P p
    Wᴴ * W = 1 ∧ Bᴴ * B = 1 ∧ Wᴴ * B = 0 ∧
    U = (Real.sin θ : ℂ) • W + (Real.cos θ : ℂ) • B ∧
    iterate U P * W = (Real.cos (2 * θ) : ℂ) • W - (Real.sin (2 * θ) : ℂ) • B ∧
    iterate U P * B = (Real.sin (2 * θ) : ℂ) • W + (Real.cos (2 * θ) : ℂ) • B := by
  have hs : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  have ht : (Real.sqrt (1 - p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (sub_pos.2 hpl)).ne'
  have hs2 : (Real.sqrt p : ℂ) ^ 2 = p := by
    exact_mod_cast Real.sq_sqrt hp.le
  have ht2 : (Real.sqrt (1 - p) : ℂ) ^ 2 = 1 - (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_pos.2 hpl).le
  have hsin : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by positivity) ((Real.sqrt_le_one).2 hpl.le)
  have hcos : Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (1 - p) := by
    rw [Real.cos_arcsin, Real.sq_sqrt hp.le]
  obtain ⟨hg, hb, ho⟩ := source_gram U P p hU hP hPP hA
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [success, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hA, star_inv, Complex.star_def,
      Complex.conj_ofReal]
    have hc : (Real.sqrt p : ℂ)⁻¹ * (Real.sqrt p : ℂ)⁻¹ * (p : ℂ) = 1 := by
      rw [← hs2]
      field_simp
    rw [hc, one_smul]
  · simp only [failure, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hb, star_inv, Complex.star_def,
      Complex.conj_ofReal]
    have hc : (Real.sqrt (1-p) : ℂ)⁻¹ * (Real.sqrt (1-p) : ℂ)⁻¹ * (1-(p:ℂ)) = 1 := by
      rw [← ht2]
      field_simp
    rw [hc, one_smul]
  · simp [success, failure, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, ho]
  · rw [hsin, hcos]
    simp only [success, failure, smul_smul, mul_inv_cancel₀ hs, mul_inv_cancel₀ ht,
      one_smul, Matrix.sub_mul, Matrix.one_mul]
    module
  · rw [Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    simp only [success, failure, iterate, Matrix.mul_smul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P U, hPP, hg]
    simp only [Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    linear_combination (U i j * 2) * ht2 +
      ((P * U) i j * 2 - U i j * 2) * hs2
  · rw [Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    simp only [success, failure, iterate, Matrix.mul_smul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P U, hPP]
    simp only [sub_self, Matrix.mul_zero, smul_zero, sub_zero]
    rw [Matrix.mul_sub, hg, hU]
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    field_simp
    linear_combination (U i j * 2) * ht2 +
      ((P * U) i j * 2 - U i j * 2) * hs2

/-- The normalized success and failure operators are orthogonal isometries,
and every power of the same reflection product rotates the whole source.
The equality remains an operator equality after tensoring any reference matrix.
This establishes the uniform-rotation part of coherent amplification; it
does not assert the auxiliary-coin construction or a gate-count bound. -/
theorem uniform_operator_rotation
    (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (p : ℝ)
    (hJ : Jᴴ * J = 1) (hC : Cᴴ * C = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * (C * J))ᴴ * (P * (C * J)) = (p : ℂ) • (1 : Matrix s s ℂ))
    (hp : 0 < p) (hpl : p < 1) :
    let U := C * J
    let W := success U P p
    let B := failure U P p
    let θ := Real.arcsin (Real.sqrt p)
    Wᴴ * W = 1 ∧ Bᴴ * B = 1 ∧ Wᴴ * B = 0 ∧
    ∀ n : ℕ,
      iterate U P ^ n * U =
        (Real.sin ((2 * n + 1) * θ) : ℂ) • W +
        (Real.cos ((2 * n + 1) * θ) : ℂ) • B ∧
      ∀ (z : Type*) (R : Matrix z z ℂ),
        (iterate U P ^ n * U) ⊗ₖ R =
          (Real.sin ((2 * n + 1) * θ) : ℂ) • (W ⊗ₖ R) +
          (Real.cos ((2 * n + 1) * θ) : ℂ) • (B ⊗ₖ R) := by
  have hU : (C * J)ᴴ * (C * J) = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Cᴴ C J, hC, Matrix.one_mul, hJ]
  obtain ⟨hW, hB, hWB, hsplit, hrW, hrB⟩ :=
    frame_rotation (C * J) P p hp hpl hU hP hPP hA
  refine ⟨hW, hB, hWB, ?_⟩
  intro n
  have he := rotation_power (iterate (C * J) P)
    (success (C * J) P p) (failure (C * J) P p)
    (Real.arcsin (Real.sqrt p)) hrW hrB n
  rw [← hsplit] at he
  refine ⟨he, ?_⟩
  intro z R
  rw [he, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]

#print axioms uniform_operator_rotation

end D5.S3.Quantum.Recovery.CoherentUniformAmplification
