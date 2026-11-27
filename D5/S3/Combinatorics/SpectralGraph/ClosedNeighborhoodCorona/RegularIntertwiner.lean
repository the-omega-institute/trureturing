/- GID: D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/RegularIntertwiner
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/RegularIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonal intertwiners fixing the constant vector of cospectral regular graphs. -/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import OmegaBuild.Commands
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Orthogonal intertwiners for regular adjacency matrices

The common row-sum eigenspace contains the normalized constant vector on both sides.
A reflection within that eigenspace aligns the two vectors after spectral conjugation.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Matrix Unitary
open scoped Matrix

namespace ClosedNeighborhoodCorona

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem spectralConjugacy {A B : Matrix V V ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hχ : A.charpoly = B.charpoly) :
    ∃ Q : Matrix.unitaryGroup V ℝ, conjStarAlgAut ℝ _ Q A = B := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hχ
  refine ⟨hB.eigenvectorUnitary * star hA.eigenvectorUnitary, ?_⟩
  rw [conjStarAlgAut_mul_apply, hA.conjStarAlgAut_star_eigenvectorUnitary, he,
    ← hB.spectral_theorem]

private theorem transpose_unitary (Q : Matrix.unitaryGroup V ℝ) :
    (Q : Matrix V V ℝ)ᵀ * Q = 1 ∧ (Q : Matrix V V ℝ) * (Q : Matrix V V ℝ)ᵀ = 1 := by
  simpa only [coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
      And.intro (coe_star_mul_self Q) (coe_mul_star_self Q)

private theorem conjugation_eq {A B : Matrix V V ℝ} {Q : Matrix.unitaryGroup V ℝ}
    (hQ : conjStarAlgAut ℝ _ Q A = B) :
    (Q : Matrix V V ℝ) * A * (Q : Matrix V V ℝ)ᵀ = B := by
  simpa only [conjStarAlgAut_apply, coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hQ

private theorem reflectionInEigenspace {B : Matrix V V ℝ} (hB : B.IsSymm)
    {r : ℝ} {x y : V → ℝ} (hx : B *ᵥ x = r • x) (hy : B *ᵥ y = r • y)
    (hNorm : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ R : Matrix V V ℝ, Rᵀ = R ∧ R * R = 1 ∧ R * B = B * R ∧ R *ᵥ x = y := by
  by_cases hxy : x = y
  · exact ⟨1, transpose_one, one_mul 1, by simp, by simpa only [one_mulVec] using hxy⟩
  let u := x - y
  let M := vecMulVec u u
  let s := u ⬝ᵥ u
  have hs : s ≠ 0 := fun h => hxy (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
  have hu : B *ᵥ u = r • u := by rw [show u = x - y from rfl, mulVec_sub, hx, hy, smul_sub]
  have hMcomm : M * B = B * M := by
    have hleft : u ᵥ* B = B *ᵥ u := by
      simpa only [hB.eq] using vecMul_transpose B u
    change vecMulVec u u * B = B * vecMulVec u u
    rw [vecMulVec_mul, mul_vecMulVec, hleft, hu, vecMulVec_smul, smul_vecMulVec]
  let P : Matrix V V ℝ := s⁻¹ • M
  have hM : M * M = s • M := by
    change vecMulVec u u * vecMulVec u u = s • vecMulVec u u
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hP : P * P = P := by
    change (s⁻¹ • M) * (s⁻¹ • M) = s⁻¹ • M
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul (s⁻¹) s,
      inv_mul_cancel₀ hs, one_smul]
  have hRatio : (2 : ℝ) * (u ⬝ᵥ x) = s := by
    have hComm := dotProduct_comm x y
    change 2 * ((x - y) ⬝ᵥ x) = (x - y) ⬝ᵥ (x - y)
    simp only [sub_dotProduct, dotProduct_sub, hNorm, hComm]
    ring
  refine ⟨1 - (2 : ℝ) • P, ?_, ?_, ?_, ?_⟩
  · simp [P, M, transpose_vecMulVec]
  · simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hP,
      ← mul_smul, show (2 : ℝ) * 2 = 2 + 2 by ring, add_smul]
    abel
  · simp only [sub_mul, mul_sub, one_mul, mul_one, P, Matrix.smul_mul, Matrix.mul_smul, hMcomm]
  · simp only [sub_mulVec, one_mulVec, smul_mulVec, P, M, vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
    rw [mul_comm (2 : ℝ) (s⁻¹), mul_assoc, hRatio, inv_mul_cancel₀ hs, one_smul]
    change x - (x - y) = y
    abel

public section

/-- Cospectral real symmetric matrices with a common row sum admit an orthogonal
intertwiner fixing the all-ones vector. -/
private theorem exists_orthogonal_intertwiner_of_row_sum {A B : Matrix V V ℝ} {r : ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hχ : A.charpoly = B.charpoly)
    (ha : A *ᵥ (1 : V → ℝ) = r • (1 : V → ℝ))
    (hb : B *ᵥ (1 : V → ℝ) = r • (1 : V → ℝ)) :
    ∃ U : Matrix V V ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      U * A = B * U ∧ U *ᵥ (1 : V → ℝ) = 1 := by
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      one_mulVec _⟩
  | inr h =>
    let := h
    obtain ⟨Q, hQ⟩ := spectralConjugacy
      (isHermitian_iff_isSymm.mpr hA) (isHermitian_iff_isSymm.mpr hB) hχ
    obtain ⟨hQtQ, hQQt⟩ := transpose_unitary Q
    let q : Matrix V V ℝ := Q
    have hq : q * A = B * q := by
      rw [← conjugation_eq hQ, Matrix.mul_assoc (q * A), hQtQ, mul_one]
    let c := (Real.sqrt (Fintype.card V : ℝ))⁻¹
    have hc : c ≠ 0 :=
      inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))
    let e : V → ℝ := c • (1 : V → ℝ)
    -- Regularity puts the entire spectral decomposition of e in the r-eigenspace.
    have heA : A *ᵥ e = r • e := by
      simp only [e, mulVec_smul, ha, smul_comm c r (1 : V → ℝ)]
    have heB : B *ᵥ e = r • e := by
      simp only [e, mulVec_smul, hb, smul_comm c r (1 : V → ℝ)]
    have hx : B *ᵥ (q *ᵥ e) = r • (q *ᵥ e) := by
      rw [mulVec_mulVec, ← hq, ← mulVec_mulVec, heA, mulVec_smul]
    have hNorm : (q *ᵥ e) ⬝ᵥ (q *ᵥ e) = e ⬝ᵥ e := by
      rw [dotProduct_mulVec, vecMul_mulVec, hQtQ, vecMul_one]
    obtain ⟨R, hRt, hRR, hRcomm, hRe⟩ := reflectionInEigenspace hB hx heB hNorm
    refine ⟨R * q, ?_, ?_, ?_, ?_⟩
    · rw [transpose_mul, hRt, Matrix.mul_assoc qᵀ, ← Matrix.mul_assoc R R, hRR,
        one_mul, hQtQ]
    · rw [transpose_mul, hRt, Matrix.mul_assoc R, ← Matrix.mul_assoc q, hQQt,
        one_mul, hRR]
    · rw [Matrix.mul_assoc, hq, ← Matrix.mul_assoc, hRcomm, Matrix.mul_assoc]
    · have hscaled : c • ((R * q) *ᵥ (1 : V → ℝ)) = c • (1 : V → ℝ) := by
        simpa only [e, mulVec_mulVec, mulVec_smul] using hRe
      exact smul_right_injective _ hc hscaled

/-- The shared characteristic polynomial forces the same regular degree on a nonempty
carrier, so the orthogonal intertwiner applies to separately regular simple graphs. -/
theorem exists_orthogonal_adjacency_intertwiner
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] {dG dH : ℕ}
    (hG : G.IsRegularOfDegree dG) (hH : H.IsRegularOfDegree dH)
    (hχ : (G.adjMatrix ℝ).charpoly = (H.adjMatrix ℝ).charpoly) :
    ∃ U : Matrix V V ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      U * G.adjMatrix ℝ = H.adjMatrix ℝ * U ∧ U *ᵥ (1 : V → ℝ) = 1 := by
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      one_mulVec _⟩
  | inr h =>
    let := h
    let A := G.adjMatrix ℝ
    let B := H.adjMatrix ℝ
    have hA : A.IsSymm := G.isSymm_adjMatrix
    have hB : B.IsSymm := H.isSymm_adjMatrix
    obtain ⟨Q, hQ⟩ := spectralConjugacy
      (isHermitian_iff_isSymm.mpr hA) (isHermitian_iff_isSymm.mpr hB) hχ
    let q : Matrix V V ℝ := Q
    have hsim : q * A * qᵀ = B := conjugation_eq hQ
    have horth : qᵀ * q = 1 := (transpose_unitary Q).1
    have htrace : (B * B).trace = (A * A).trace := calc
      (B * B).trace = (q * (A * A) * qᵀ).trace := by
        rw [← hsim]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc qᵀ q, horth, one_mul]
      _ = (A * A).trace := by rw [trace_mul_cycle, horth, one_mul]
    have hdegree : (Fintype.card V : ℝ) * dH = (Fintype.card V : ℝ) * dG := by
      simpa only [A, B, Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_mul_self_apply_self,
        hH.degree_eq, hG.degree_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        using htrace
    have hd : (dH : ℝ) = dG := mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hdegree
    apply exists_orthogonal_intertwiner_of_row_sum hA hB hχ (r := (dG : ℝ))
    · funext v
      change (G.adjMatrix ℝ *ᵥ Function.const V 1) v = (dG : ℝ) * 1
      exact SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hG
    · funext v
      change (H.adjMatrix ℝ *ᵥ Function.const V 1) v = (dG : ℝ) * 1
      rw [← hd]
      exact SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hH

end

end ClosedNeighborhoodCorona
