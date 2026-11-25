/- GID: D5/S3/Quantum/Decoherence/LabelResetSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/LabelResetSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite matrix support under isometric padding, partial trace and prescribed pure marginals. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Matrix.PosDef

/-!
# Support geometry for finite label reset

Rectangular isometries insert a supported matrix into ambient coordinates.
A positive matrix inherits the support of its marginal, and a normalized
pure label marginal factors off from the joint matrix.
-/

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace LabelResetBandwidth

noncomputable section

variable {N I J D : Type*} [Fintype N] [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq N] [DecidableEq I] [DecidableEq J] [DecidableEq D]

/-- Insert a matrix into the ambient space using the columns of an isometry. -/
def pad (V : Matrix N I ℂ) (A : Matrix I I ℂ) : Matrix N N ℂ :=
  V * A * Vᴴ

omit [DecidableEq N] in
theorem compress_pad (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) : Vᴴ * pad V A * V = A := by
  calc
    Vᴴ * pad V A * V = (Vᴴ * V) * A * (Vᴴ * V) := by simp only [pad, Matrix.mul_assoc]
    _ = A := by simp [hV]

omit [DecidableEq N] in
theorem rank_pad (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) : (pad V A).rank = A.rank := by
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · calc
      A.rank = (Vᴴ * pad V A * V).rank := congrArg Matrix.rank (compress_pad V hV A).symm
      _ ≤ (pad V A).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

omit [DecidableEq N] [DecidableEq I] in
theorem pad_psd (V : Matrix N I ℂ) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (pad V A).PosSemidef := by
  simpa only [pad, conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Vᴴ

theorem padding_charpoly (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) :
    Polynomial.X ^ Fintype.card I * (pad V A).charpoly =
      Polynomial.X ^ Fintype.card N * A.charpoly := by
  simpa [pad, ← Matrix.mul_assoc, hV] using charpoly_mul_comm' (V * A) Vᴴ

omit [Fintype N] [DecidableEq N] [DecidableEq I] in
private theorem pad_hermitian (V : Matrix N I ℂ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (pad V A).IsHermitian := by
  change (pad V A)ᴴ = pad V A
  simp [pad, conjTranspose_mul, hA.eq, Matrix.mul_assoc]

theorem conj_eq_pad (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    conjStarAlgAut ℂ _ U A = pad (U : Matrix N N ℂ) A := by
  rw [conjStarAlgAut_apply, star_eq_conjTranspose, pad]

theorem rank_unitary_conj (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    (conjStarAlgAut ℂ _ U A).rank = A.rank := by
  rw [conj_eq_pad]
  exact rank_pad _ (by simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self U) A

/-- Matrices with the same Hermitian spectrum lie in the same unitary orbit. -/
theorem exists_unitary_of_charpoly_eq {A B : Matrix N N ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    ∃ U : unitary (Matrix N N ℂ), conjStarAlgAut ℂ _ U A = B := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h
  refine ⟨hB.eigenvectorUnitary * star hA.eigenvectorUnitary, ?_⟩
  rw [conjStarAlgAut_mul_apply, hA.conjStarAlgAut_star_eigenvectorUnitary, he,
    ← hB.spectral_theorem]

/-- Extend the isometry from the input columns to the specified output columns
to an ambient unitary. The equation fixes its action on every input column. -/
theorem exists_unitary_extension (V W : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    (hW : Wᴴ * W = 1) :
    ∃ U : unitary (Matrix N N ℂ), (U : Matrix N N ℂ) * V = W := by
  let P := pad V (1 : Matrix I I ℂ)
  let Q := pad W (1 : Matrix I I ℂ)
  have hc : P.charpoly = Q.charpoly := by
    apply mul_left_cancel₀ (pow_ne_zero (Fintype.card I) Polynomial.X_ne_zero)
    exact (padding_charpoly V hV 1).trans (padding_charpoly W hW 1).symm
  obtain ⟨U₀, hU₀⟩ := exists_unitary_of_charpoly_eq
    (pad_hermitian V isHermitian_one) (pad_hermitian W isHermitian_one) hc
  let T : Matrix N N ℂ := U₀
  have hT : Tᴴ * T = 1 := by
    simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self U₀
  have hPQ : T * P = Q * T := by
    rw [conj_eq_pad, pad] at hU₀
    calc
      T * P = T * P * (Tᴴ * T) := by rw [hT, Matrix.mul_one]
      _ = Q * T := by rw [← Matrix.mul_assoc, hU₀]
  have hP : P = V * Vᴴ := by simp [P, pad]
  have hQ : Q = W * Wᴴ := by simp [Q, pad]
  have hPh : Pᴴ = P := (pad_hermitian V isHermitian_one).eq
  have hPv : P * V = V := by rw [hP, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hPP : P * P = P := by
    calc
      P * P = (P * V) * Vᴴ := by rw [Matrix.mul_assoc, ← hP]
      _ = P := by rw [hPv, hP]
  have hWT : Wᴴ * T = Wᴴ * (T * P) := by
    rw [hPQ, ← Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hcross : Wᴴ * (T * (1 - P)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sub, ← hWT, sub_self]
  have hcross' : (T * (1 - P))ᴴ * W = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_zero, conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hcross
  let U : Matrix N N ℂ := W * Vᴴ + T * (1 - P)
  have hU : Uᴴ * U = 1 := by
    have hleft : (W * Vᴴ)ᴴ * (W * Vᴴ) = P := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, hP,
        Matrix.mul_assoc V, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul]
    have hright : (T * (1 - P))ᴴ * (T * (1 - P)) = 1 - P := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ, hT, Matrix.one_mul,
        conjTranspose_sub, conjTranspose_one, hPh]
      simp [Matrix.sub_mul, Matrix.mul_sub, hPP]
    simp only [U, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hleft, hright]
    rw [show (W * Vᴴ)ᴴ * (T * (1 - P)) = 0 by
          simp [conjTranspose_mul, Matrix.mul_assoc, hcross],
        show (T * (1 - P))ᴴ * (W * Vᴴ) = 0 by
          rw [← Matrix.mul_assoc, hcross', Matrix.zero_mul]]
    abel
  refine ⟨⟨U, ?_⟩, ?_⟩
  · exact Matrix.mem_unitaryGroup_iff'.mpr hU
  · change U * V = W
    calc
      U * V = W * (Vᴴ * V) + T * ((1 - P) * V) := by
        simp only [U, Matrix.add_mul, Matrix.mul_assoc]
      _ = W := by simp [hV, Matrix.sub_mul, hPv]

omit [Fintype N] [DecidableEq N] [DecidableEq I] in
/-- The partial trace is natural under a rectangular change of the retained coordinates. -/
theorem partialTrace_pad (V : Matrix N I ℂ) (A : Matrix (D × I) (D × I) ℂ) :
    partialTraceLeft (pad ((1 : Matrix D D ℂ) ⊗ₖ V) A) =
      pad V (partialTraceLeft A) := by
  have left (b c : D) (i : N) (j : I) :
      (((1 : Matrix D D ℂ) ⊗ₖ V) * A) (b, i) (c, j) =
        ∑ k : I, V i k * A (b, k) (c, j) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]
  have right (b : D) (i j : N) :
      (pad ((1 : Matrix D D ℂ) ⊗ₖ V) A) (b, i) (b, j) =
        ∑ k : I, (∑ l : I, V i l * A (b, l) (b, k)) * Vᴴ k j := by
    rw [pad, conjTranspose_kronecker, conjTranspose_one, Matrix.mul_apply]
    simp [Fintype.sum_prod_type, left, Matrix.one_apply, mul_ite]
  ext i j
  simp only [partialTraceLeft, right]
  simp only [pad, Matrix.mul_apply, partialTraceLeft, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

omit [Fintype I] [DecidableEq N] [DecidableEq I] in
private theorem mul_eq_zero_of_sandwich_zero {A : Matrix N N ℂ} (hA : A.PosSemidef)
    (C : Matrix N I ℂ) (h : Cᴴ * A * C = 0) : A * C = 0 := by
  ext i j
  have hd := congrArg (fun T : Matrix I I ℂ => T j j) h
  have hv : star (C.col j) ⬝ᵥ (A *ᵥ C.col j) = 0 := by
    rw [Matrix.mul_assoc] at hd
    simpa [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.col,
      conjTranspose_apply, Pi.star_apply] using hd
  have hz := congrFun (hA.dotProduct_mulVec_zero_iff.mp hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.col, dotProduct] using hz

/-- A positive state with retained marginal supported on the columns of V
has the corresponding joint support and can be recovered from its compression. -/
theorem supported_of_marginal (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    {A : Matrix (D × N) (D × N) ℂ} (hA : A.PosSemidef)
    {σ : Matrix I I ℂ} (hσ : partialTraceLeft A = pad V σ) :
    let K := (1 : Matrix D D ℂ) ⊗ₖ V
    A = pad K (Kᴴ * A * K) := by
  dsimp only
  let P := V * Vᴴ
  let L : Matrix N N ℂ := 1 - P
  let C := (1 : Matrix D D ℂ) ⊗ₖ L
  let K := (1 : Matrix D D ℂ) ⊗ₖ V
  have hCh : Cᴴ = C := by
    simp [C, L, P, conjTranspose_kronecker, conjTranspose_mul]
  have hpv : L * V = 0 := by simp [L, P, Matrix.sub_mul, Matrix.mul_assoc, hV]
  have hm : partialTraceLeft (pad C A) = 0 := by
    change partialTraceLeft (pad ((1 : Matrix D D ℂ) ⊗ₖ L) A) = 0
    rw [partialTrace_pad, hσ]
    simp [pad, ← Matrix.mul_assoc, hpv]
  have hz : Cᴴ * A * C = 0 := by
    apply (hA.conjTranspose_mul_mul_same C).trace_eq_zero_iff.mp
    rw [hCh, ← show pad C A = C * A * C from by simp [pad, hCh],
      ← trace_partialTraceLeft, hm, Matrix.trace_zero]
  have hr := mul_eq_zero_of_sandwich_zero hA C hz
  have hl : C * A = 0 := by
    simpa only [conjTranspose_mul, hA.isHermitian.eq, hCh, conjTranspose_zero]
      using congrArg Matrix.conjTranspose hr
  have hC : C = 1 - K * Kᴴ := by
    have hsub : (1 : Matrix D D ℂ) ⊗ₖ (1 - P) = 1 - (1 : Matrix D D ℂ) ⊗ₖ P := by
      ext ⟨b, i⟩ ⟨c, j⟩
      by_cases hbi : b = c <;> by_cases hij : i = j <;>
        simp [Prod.ext_iff, mul_sub, hbi, hij]
    simpa [C, L, P, K, conjTranspose_kronecker, ← mul_kronecker_mul] using hsub
  rw [hC, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hl
  rw [hC, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hr
  change A = pad K (Kᴴ * A * K)
  calc
    A = (K * Kᴴ) * A := hl
    _ = (K * Kᴴ) * (A * (K * Kᴴ)) := congrArg ((K * Kᴴ) * ·) hr
    _ = _ := by simp only [pad, Matrix.mul_assoc]


section PureMarginal

variable {X : Type*} [Fintype X]

/-- The projector for a prescribed normalized label vector. -/
def pure (w : X → ℂ) : Matrix X X ℂ := vecMulVec w (star w)

theorem trace_pure (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) : (pure w).trace = 1 := by
  change (∑ i, w i * star (w i)) = 1
  rw [← hw]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A pure label marginal factors from the rest of a positive joint state. -/
theorem pure_marginal_factors (w : X → ℂ) (hw : star w ⬝ᵥ w = 1)
    {A : Matrix (X × D) (X × D) ℂ} (hA : A.PosSemidef)
    (hwA : partialTraceRight A = pure w) :
    A = pure w ⊗ₖ partialTraceLeft A := by
  classical
  let F : Matrix X Unit ℂ := fun x _ => w x
  have hF : Fᴴ * F = 1 := by
    ext ⟨⟩ ⟨⟩
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    exact hw
  have hFp : pad F (1 : Matrix Unit Unit ℂ) = pure w := by
    rw [pad, Matrix.mul_one]
    ext i j
    rw [Matrix.mul_apply]
    rw [Fintype.sum_unique]
    rfl
  let S := A.submatrix (Equiv.prodComm D X) (Equiv.prodComm D X)
  have hS : partialTraceLeft S = pad F (1 : Matrix Unit Unit ℂ) := by
    rw [hFp]
    exact hwA
  let K := (1 : Matrix D D ℂ) ⊗ₖ F
  let Q := Kᴴ * S * K
  have hSQ : S = pad K Q :=
    supported_of_marginal F hF (hA.submatrix (Equiv.prodComm D X)) hS
  let Ω : Matrix D D ℂ := fun i j => Q (i, ()) (j, ())
  have hfac : A = pure w ⊗ₖ Ω := by
    have hK (i j : D) (x : X) (u : Unit) : K (i, x) (j, u) =
        (1 : Matrix D D ℂ) i j * w x := rfl
    have hleft (i j : D) (x : X) :
        (K * Q) (i, x) (j, ()) = w x * Ω i j := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp [hK, Ω, Matrix.one_apply, ite_mul]
    have hright (i j : D) (x y : X) :
        (pad K Q) (i, x) (j, y) = pure w x y * Ω i j := by
      rw [pad, Matrix.mul_apply, Fintype.sum_prod_type]
      simp [hleft, hK, pure, conjTranspose_apply, Matrix.one_apply,
        apply_ite (star : ℂ → ℂ), mul_ite, ite_mul, vecMulVec_apply, Pi.star_apply,
        mul_right_comm]
    ext ⟨x, i⟩ ⟨y, j⟩
    exact (congrArg (fun T : Matrix (D × X) (D × X) ℂ => T (i, x) (j, y)) hSQ).trans
      (hright i j x y)
  have hΩ : partialTraceLeft A = Ω := by
    rw [hfac]
    change partialTraceLeft (Matrix.kronecker (pure w) Ω) = Ω
    rw [partialTraceLeft_kronecker, trace_pure w hw, one_smul]
  rw [hΩ, ← hfac]

end PureMarginal

omit [Fintype N] [DecidableEq N] [DecidableEq I] [DecidableEq J] in
theorem pad_comp (V : Matrix N I ℂ) (W : Matrix I J ℂ) (A : Matrix J J ℂ) :
    pad V (pad W A) = pad (V * W) A := by
  simp only [pad, conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype J] [DecidableEq N] in
theorem isometry_comp (V : Matrix N I ℂ) (W : Matrix I J ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    (V * W)ᴴ * (V * W) = 1 := by
  calc
    (V * W)ᴴ * (V * W) = Wᴴ * (Vᴴ * V) * W := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by simp [hV, hW]

omit [Fintype I] [DecidableEq N] in
theorem bathEmbedding_isometry (V : Matrix N I ℂ)
    (hV : Vᴴ * V = 1) :
    (((1 : Matrix D D ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix D D ℂ) ⊗ₖ V)) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul, hV, one_kronecker_one]

omit [DecidableEq N] in
theorem trace_pad (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) : (pad V A).trace = A.trace := by
  rw [pad, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

omit [DecidableEq N] in
theorem range_pad (V : Matrix N I ℂ) (hV : Vᴴ * V = 1)
    {A : Matrix I I ℂ} (hA : A.PosDef) :
    LinearMap.range (pad V A).mulVecLin = LinearMap.range V.mulVecLin := by
  have hs : LinearMap.range Vᴴ.mulVecLin = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨V *ᵥ x, ?_⟩
    change Vᴴ *ᵥ (V *ᵥ x) = x
    rw [mulVec_mulVec, hV, one_mulVec]
  have ht : LinearMap.range A.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (mulVec_surjective_iff_isUnit.mpr hA.isUnit)
  unfold pad
  rw [mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs,
    mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ ht]


end

end LabelResetBandwidth
