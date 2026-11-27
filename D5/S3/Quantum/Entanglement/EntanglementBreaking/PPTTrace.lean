/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Output partial transpose and trace separation of decomposable maps. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.ChoiCongruences
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Matrix.PartialTransposeTrace (partial_transpose_trace_duality)

/-- Decomposability as a sum of a completely positive and a completely copositive map. -/
def IsDecomposable {a b : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  ∃ P Q : MatrixMap (Fin a) (Fin b) ℂ, P.IsCompletelyPositive ∧
    ((Matrix.transposeLinearEquiv (Fin b) (Fin b) ℂ ℂ).toLinearMap.comp Q
      : MatrixMap (Fin a) (Fin b) ℂ).IsCompletelyPositive ∧ Φ = P + Q

theorem inputChoi_decomposition {a b : ℕ} {Φ : MatrixMap (Fin a) (Fin b) ℂ}
    (hΦ : IsDecomposable Φ) :
    ∃ P Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      P.PosSemidef ∧ Q.PosSemidef ∧ inputChoi Φ = P + partialTranspose Q := by
  obtain ⟨P, Q, hP, hQ, hΦ⟩ := hΦ
  let T := (Matrix.transposeLinearEquiv (Fin b) (Fin b) ℂ ℂ).toLinearMap
  have hinvolution : T.comp (T.comp Q) = Q := by
    ext X i j
    rfl
  have hΦ' : Φ = P + T.comp (T.comp Q) := by rw [hinvolution, hΦ]
  rw [hΦ']
  refine ⟨inputChoi P, inputChoi (T.comp Q),
    ((MatrixMap.choi_PSD_iff_CP_map P).mp hP).submatrix Prod.swap,
    ((MatrixMap.choi_PSD_iff_CP_map (T.comp Q)).mp hQ).submatrix Prod.swap, ?_⟩
  ext ⟨i, u⟩ ⟨j, v⟩
  rfl

private def partialTransposeLinear {A B : Type} :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun := partialTranspose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem partialTranspose_trace_pairing_of_psd {A B : Type} [Fintype A] [Fintype B]
    (Q R : Matrix (A × B) (A × B) ℂ) (hQ : Q.PosSemidef) :
    (partialTranspose Q * R).trace = (Q * partialTranspose R).trace := by
  obtain ⟨n, s, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hQ
  change (partialTransposeLinear (∑ i, vecMulVec (s i) (star (s i))) * R).trace = _
  rw [map_sum, Matrix.sum_mul, Matrix.sum_mul, trace_sum, trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (partialTranspose (vecMulVec (s i) (star (s i))) * R).trace = _
  rw [trace_mul_comm (partialTranspose (vecMulVec (s i) (star (s i)))) R]
  rw [← partial_transpose_trace_duality R (s i), Matrix.vecMulVec_mul, trace_vecMulVec,
    dotProduct_mulVec, dotProduct_comm]

/-- A negative trace pairing with a PPT matrix excludes CP plus co-CP. -/
theorem indecomposable_of_ppt_trace {a b : ℕ} {Φ : MatrixMap (Fin a) (Fin b) ℂ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hR : R.PosSemidef) (hΓ : (partialTranspose R).PosSemidef)
    (hneg : (inputChoi Φ * R).trace.re < 0) :
    ¬ IsDecomposable Φ := by
  intro hΦ
  obtain ⟨P, Q, hP, hQ, hW⟩ := inputChoi_decomposition hΦ
  rw [hW, Matrix.add_mul, trace_add, Complex.add_re,
    partialTranspose_trace_pairing_of_psd Q R hQ] at hneg
  exact (not_lt_of_ge (add_nonneg (RHLinalg.trace_mul_nonneg_of_posSemidef hP hR)
    (RHLinalg.trace_mul_nonneg_of_posSemidef hQ hΓ))) hneg

/-- Input-first Choi candidate in dimension d. -/
def choiCandidate {d : ℕ} (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 - (16 / (d : ℝ)) • H

/-- Unnormalized PPT test matrix. Normalization is unnecessary for the sign. -/
def pptTest {d : ℕ} (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 + (1 / (4 * (d : ℝ))) • H

theorem candidate_trace_bound {d : ℕ} (hd : 1 ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (htr : H.trace = 0) (henergy : (d : ℝ)^4 / 2 ≤ (H * H).trace.re) :
    (choiCandidate H * pptTest H).trace.re ≤ -(d : ℝ)^2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have htrace : (choiCandidate H * pptTest H).trace.re =
      (d : ℝ)^2 - (4 / (d : ℝ)^2) * (H * H).trace.re := by
    simp only [choiCandidate, pptTest, Matrix.sub_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      trace_sub, trace_add, trace_smul, trace_one, htr, smul_zero, sub_zero, zero_sub,
      Complex.add_re, Complex.neg_re, Complex.smul_re, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, smul_eq_mul]
    field_simp
    ring
  rw [htrace]
  have hbound := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ 4 / (d : ℝ)^2 by positivity)
  have hscale : 4 / (d : ℝ)^2 * ((d : ℝ)^4 / 2) = 2 * (d : ℝ)^2 := by
    field_simp
    ring
  rw [hscale] at hbound
  linarith

theorem candidate_indecomposable {d : ℕ} (hd : 1 ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (htr : H.trace = 0) (henergy : (d : ℝ)^4 / 2 ≤ (H * H).trace.re)
    (hR : (pptTest H).PosSemidef) (hΓ : (partialTranspose (pptTest H)).PosSemidef) :
    ¬ IsDecomposable (fromInputChoi (choiCandidate H)) := by
  apply indecomposable_of_ppt_trace (pptTest H) hR hΓ
  rw [inputChoi_fromInputChoi]
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  exact (candidate_trace_bound hd H htr henergy).trans_lt (neg_lt_zero.mpr (by positivity))

