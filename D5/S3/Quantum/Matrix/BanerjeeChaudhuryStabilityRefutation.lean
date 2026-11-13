/- GID: D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.claim; result=D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.result; claim=D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.claim
   digest: A positive stochastic matrix and a positive semidefinite projection refute the proposed stability interval. -/

import D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.Star.Real

/-! Banerjee–Chaudhury, arXiv:2509.06715v1, Conjecture 1.1, with the
nonsymmetry convention of the preceding paragraph. The source is CC BY 4.0.
The definitions of the operators and stability are those of the source. -/

noncomputable section

open Matrix
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator

namespace D5.S3.Quantum.Matrix.BanerjeeChaudhuryStabilityRefutation

open AsynchronousIterationSpectralRadiusRefutation (radius)

/-- The real spectral radius of the entrywise complexification. -/
def rho {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := (radius A).toReal

/-- The first iteration operator. -/
def P {n : ℕ} (W B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) := W * (1 - t • B)

/-- The second iteration operator, used on its invertibility domain. -/
def R {n : ℕ} (W B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :=
  1 - W + (1 + t • B)⁻¹ * (2 • W - 1)

/-- Source hypotheses, with the positive left Perron vector normalized to sum one. -/
def Admissible {n : ℕ} (W B : Matrix (Fin n) (Fin n) ℝ) (pi : Fin n → ℝ) : Prop :=
  ¬ W.IsSymm ∧ W ∈ rowStochastic ℝ (Fin n) ∧ W.IsPrimitive ∧
  B ≠ 0 ∧ B.IsSymm ∧ B.PosSemidef ∧
  (∀ i, 0 < pi i) ∧ (∑ i, pi i) = 1 ∧ pi ᵥ* W = pi ∧
  (∀ i, (B *ᵥ 1) i ≤ rho B) ∧ 0 < dotProduct pi (B *ᵥ 1)

/-- Both operators are stable throughout the proposed interval, with a genuine inverse. -/
def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (W B : Matrix (Fin n) (Fin n) ℝ) (pi : Fin n → ℝ),
    Admissible W B pi → ∀ t : ℝ, 0 < t → t < 2 / rho B →
      IsUnit (1 + t • B) ∧ rho (P W B t) < 1 ∧ rho (R W B t) < 1

private theorem radius_max {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)),
      rho A = ‖z‖ ∧ radius A = ENNReal.ofReal ‖z‖ ∧
      ∀ w ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖w‖ ≤ ‖z‖ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional
    (𝕜 := ℂ) (A.map (algebraMap ℝ ℂ))
  obtain ⟨z, hz, he⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hs
  have hr : radius A = (‖z‖₊ : ℝ≥0∞) := he.symm
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · simp [rho, hr]
  · exact hr.trans (ENNReal.ofReal_coe_nnreal (p := ‖z‖₊)).symm
  · intro w hw
    have hle : (‖w‖₊ : ℝ≥0∞) ≤ radius A := by
      unfold radius
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun w (_ : w ∈ spectrum ℂ
        (A.map (algebraMap ℝ ℂ))) => (‖w‖₊ : ℝ≥0∞)) w hw
    rw [hr] at hle
    exact_mod_cast hle

private theorem norm_le_rho {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    {z : ℂ} (hz : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) : ‖z‖ ≤ rho A := by
  obtain ⟨w, _, hr, _, hb⟩ := radius_max hn A
  rw [hr]
  exact hb z hz

private def W : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 40 : ℝ) • !![37, 1, 1, 1; 1, 1, 1, 37; 1, 1, 1, 37; 37, 1, 1, 1]

private def B : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 3 : ℝ) • !![1, 1, 1, 0; 1, 1, 1, 0; 1, 1, 1, 0; 0, 0, 0, 3]

private def pi : Fin 4 → ℝ := ![176 / 200, 5 / 200, 5 / 200, 14 / 200]

private def x : Fin 4 → ℂ := ![28, -19, -19, 28]

private theorem B_idempotent : IsIdempotentElem (B.map (algebraMap ℝ ℂ)) := by
  change B.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) = B.map (algebraMap ℝ ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]

private theorem B_one : B *ᵥ (1 : Fin 4 → ℝ) = 1 := by
  ext i
  fin_cases i <;> norm_num [B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem B_radius : rho B = 1 := by
  have he : B.map (algebraMap ℝ ℂ) *ᵥ (1 : Fin 4 → ℂ) = (1 : ℂ) • 1 := by
    ext i
    fin_cases i <;> norm_num [B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hz : (1 : Fin 4 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hmem := D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
    _ 1 1 hz he
  have hlo := norm_le_rho (by norm_num) B hmem
  obtain ⟨z, hz, hr, _, _⟩ := radius_max (by norm_num) B
  have hs := B_idempotent.spectrum_subset ℂ hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> norm_num at hr hlo ⊢ <;> linarith

private theorem admissible : Admissible W B pi := by
  have hpos : ∀ i j, 0 < W i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [W]
  have hsym : B.IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.transpose_apply]
  have hgram : Bᴴ * B = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ⟨fun i j => (hpos i j).le, 1, by norm_num, by simpa using hpos⟩,
    ?_, hsym, hgram ▸ Matrix.posSemidef_conjTranspose_mul_self B, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hh := congrFun (congrFun h 0) 3
    norm_num [W, Matrix.transpose_apply] at hh
  · rw [Matrix.mem_rowStochastic]
    refine ⟨fun i j => (hpos i j).le, ?_⟩
    ext i
    fin_cases i <;> norm_num [W, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [B] at hh
  · intro i
    fin_cases i <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [pi, W, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · intro i
    rw [B_one, B_radius]
    norm_num
  · rw [B_one]
    norm_num [pi, dotProduct, Fin.sum_univ_succ]

private theorem unstable_eigenpair : x ≠ 0 ∧
    (P W B (9 / 5)).map (algebraMap ℝ ℂ) *ᵥ x = (27 / 25 : ℂ) • x := by
  constructor
  · intro h
    have hh := congrFun h 0
    norm_num [x] at hh
  · ext i
    fin_cases i <;>
      norm_num [P, W, B, x, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]

/-- The four-dimensional example violates the first stability conclusion. -/
theorem result : ¬ claim := by
  intro h
  let H : Matrix (Fin 4) (Fin 4) ℝ := 1 - (9 / 14 : ℝ) • B
  have hi : (1 + (9 / 5 : ℝ) • B) * H = 1 ∧
      H * (1 + (9 / 5 : ℝ) • B) = 1 := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [H, B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hunit : IsUnit (1 + (9 / 5 : ℝ) • B) := isUnit_iff_exists.mpr ⟨H, hi⟩
  have hinv : (1 + (9 / 5 : ℝ) • B)⁻¹ = H := Matrix.inv_eq_right_inv hi.1
  have hb := h 4 (by norm_num) W B pi admissible (9 / 5) (by norm_num)
    (by rw [B_radius]; norm_num)
  obtain ⟨hx, he⟩ := unstable_eigenpair
  have hz := D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
    _ (27 / 25) x hx he
  have hlo := norm_le_rho (by norm_num) (P W B (9 / 5)) hz
  have hlt := hb.2.1
  norm_num [norm_div] at hlo
  linarith

end D5.S3.Quantum.Matrix.BanerjeeChaudhuryStabilityRefutation
