/- GID: D5/S3/Combinatorics/SpectralGraph/BonettoSignature
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BonettoSignature
   mirror-E: none(waiver:noncomputational-theorem)
   anchors: []
   utility: none
   digest: Signature is nonincreasing for a graph Laplacian plus positive adjacency weight. -/

import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Signature of a mixed graph matrix

Bonetto and Jardón Kojakhmetov, arXiv:2408.00487v1, Definitions 3, 7, 8
and Conjecture 1. The signature counts characteristic-polynomial roots
with algebraic multiplicity, excluding zero. The graph matrices are the
ordinary real adjacency and combinatorial Laplacian matrices.
-/

noncomputable section

open Matrix RHLinalg

namespace D5.S3.Combinatorics.SpectralGraph.BonettoSignature

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A disjoint spanning edge partition of the original simple graph. -/
def IsEdgePartition (F G H : SimpleGraph V) : Prop :=
  Disjoint G H ∧ G ⊔ H = F

/-- The real matrix `L_G + u A_H` of Definition 3. -/
def mixedMatrix (G H : SimpleGraph V) (u : ℝ) : Matrix V V ℝ := by
  classical
  exact G.lapMatrix ℝ + u • H.adjMatrix ℝ

/-- Positive roots minus negative roots of the characteristic polynomial,
counted with algebraic multiplicity in the integers. -/
def signature (Q : Matrix V V ℝ) : ℤ := by
  classical
  exact ((Q.charpoly.roots.filter (fun x => 0 < x)).card : ℤ) -
    ((Q.charpoly.roots.filter (fun x => x < 0)).card : ℤ)

private theorem mixedMatrix_isHermitian (G H : SimpleGraph V) (u : ℝ) :
    (mixedMatrix G H u).IsHermitian := by
  classical
  exact (G.isHermitian_lapMatrix ℝ).add
    ((H.isHermitian_adjMatrix ℝ).smul (by simp [IsSelfAdjoint]))

private theorem signature_eq_indices {Q : Matrix V V ℝ} (hQ : Q.IsHermitian) :
    signature Q = (posIndex hQ : ℤ) - (negIndex hQ : ℤ) := by
  classical
  simp [signature, posIndex, negIndex, hQ.roots_charpoly_eq_eigenvalues,
    Multiset.filter_map, Function.comp_def]

private theorem posIndex_le_of_form {A B : Matrix V V ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, 0 < hermForm A x → 0 < hermForm B x) :
    posIndex hA ≤ posIndex hB := by
  obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  rw [← hdim]
  exact finrank_le_posIndex_of_posDefOn hB (fun x hx hne => h x (hW x hx hne))

/-- Conjecture 1: on the entire positive parameter axis, the actual spectral
signature of the mixed graph matrix is nonincreasing. -/
theorem result (F G H : SimpleGraph V) (_partition : IsEdgePartition F G H)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    signature (mixedMatrix G H t) ≤ signature (mixedMatrix G H s) := by
  classical
  have ht : 0 < t := hs.trans_le hst
  have hscale (a : ℝ) (Q : Matrix V V ℝ) (x : V → ℝ) :
      hermForm (a • Q) x = a * hermForm Q x := by
    simp [hermForm, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hL (x : V → ℝ) : 0 ≤ hermForm (G.lapMatrix ℝ) x :=
    hermForm_nonneg_of_posSemidef (G.posSemidef_lapMatrix ℝ) x
  have hpos : posIndex (mixedMatrix_isHermitian G H t) ≤
      posIndex (mixedMatrix_isHermitian G H s) := by
    apply posIndex_le_of_form
    intro x hx
    have hid : mixedMatrix G H s =
        (s / t) • mixedMatrix G H t + (1 - s / t) • G.lapMatrix ℝ := by
      ext i j
      simp only [mixedMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp
      <;> ring
    rw [hid, hermForm_add, hscale, hscale]
    exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hs ht) hx)
      (mul_nonneg (sub_nonneg.mpr ((div_le_one ht).mpr hst)) (hL x))
  have hneg : negIndex (mixedMatrix_isHermitian G H s) ≤
      negIndex (mixedMatrix_isHermitian G H t) := by
    rw [← D5.S3.SpectralTopology.FiniteSpectralLocalizer.posIndex_neg_eq_negIndex,
      ← D5.S3.SpectralTopology.FiniteSpectralLocalizer.posIndex_neg_eq_negIndex]
    apply posIndex_le_of_form
    intro x hx
    have hid : -mixedMatrix G H t =
        (t / s) • (-mixedMatrix G H s) + (t / s - 1) • G.lapMatrix ℝ := by
      ext i j
      simp only [mixedMatrix, Matrix.neg_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      field_simp
      <;> ring
    rw [hid, hermForm_add, hscale, hscale]
    exact add_pos_of_pos_of_nonneg (mul_pos (div_pos ht hs) hx)
      (mul_nonneg (sub_nonneg.mpr ((one_le_div hs).mpr hst)) (hL x))
  rw [signature_eq_indices (mixedMatrix_isHermitian G H t),
    signature_eq_indices (mixedMatrix_isHermitian G H s)]
  exact sub_le_sub (Int.ofNat_le.mpr hpos) (Int.ofNat_le.mpr hneg)

end D5.S3.Combinatorics.SpectralGraph.BonettoSignature
