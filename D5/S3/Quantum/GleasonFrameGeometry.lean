/- GID: D5/S3/Quantum/GleasonFrameGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/GleasonFrameGeometry
   mirror-E: none(waiver:finite-dimensional-algebraic-proof)
   anchors: []
   utility: none -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/notes/gleason1957measures.md. Authors: Zayn Blore.
Adapted from zblore/csd-lean4 at 07e2273b0180e69b4cb8f84e9d2200faa19fe07d.
Imports, source grouping and exact-supplier applications use the receiving Mathlib pin.
Retire this transplant when the receiving pinned Mathlib supplies equivalent declarations.
-/

module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace Gleason
section Gram
variable {𝕜 : Type*} [RCLike 𝕜] {N k : ℕ}
def colMatrix (e : Fin k → EuclideanSpace 𝕜 (Fin N)) : Matrix (Fin N) (Fin k) 𝕜 :=
  Matrix.of fun a i => e i a
omit [RCLike 𝕜] in
@[simp] lemma colMatrix_apply (e : Fin k → EuclideanSpace 𝕜 (Fin N)) (a : Fin N) (i : Fin k) :
    colMatrix e a i = e i a := rfl
lemma conjTranspose_mul_colMatrix_apply (e : Fin k → EuclideanSpace 𝕜 (Fin N)) (i j : Fin k) :
    ((colMatrix e)ᴴ * colMatrix e) i j = ⟪e i, e j⟫_𝕜 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colMatrix_apply, PiLp.inner_apply,
    RCLike.inner_apply', RCLike.star_def]
lemma conjTranspose_mul_colMatrix_of_orthonormal {e : Fin k → EuclideanSpace 𝕜 (Fin N)}
    (he : Orthonormal 𝕜 e) : (colMatrix e)ᴴ * colMatrix e = 1 := by
  ext i j
  rw [conjTranspose_mul_colMatrix_apply, orthonormal_iff_ite.mp he, Matrix.one_apply]
lemma colMatrix_mul_conjTranspose_of_orthonormalBasis
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N))) :
    colMatrix b * (colMatrix b)ᴴ = 1 :=
  mul_eq_one_comm.mp (conjTranspose_mul_colMatrix_of_orthonormal b.orthonormal)
lemma sum_vecMulVec_eq_colMatrix_mul (e : Fin k → EuclideanSpace 𝕜 (Fin N)) :
    ∑ i, vecMulVec (⇑(e i)) (star ⇑(e i)) = colMatrix e * (colMatrix e)ᴴ := by
  ext a c
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
end Gram
variable {N : ℕ}
def rankOne (v : EuclideanSpace ℂ (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  vecMulVec (⇑v) (star ⇑v)
lemma rankOne_posSemidef (v : EuclideanSpace ℂ (Fin N)) : (rankOne v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (R := ℂ) (⇑v)
lemma rankOne_isHermitian (v : EuclideanSpace ℂ (Fin N)) : (rankOne v).IsHermitian :=
  (rankOne_posSemidef v).isHermitian
lemma rankOne_mul_rankOne (v w : EuclideanSpace ℂ (Fin N)) :
    rankOne v * rankOne w = ⟪v, w⟫_ℂ • vecMulVec (⇑v) (star ⇑w) := by
  rw [rankOne, rankOne, vecMulVec_mul_vecMulVec, vecMulVec_smul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
lemma rankOne_mul_self {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) :
    rankOne v * rankOne v = rankOne v := by
  rw [rankOne_mul_rankOne, inner_self_eq_norm_sq_to_K, hv]
  simp [rankOne]
lemma rankOne_mul_rankOne_of_inner_eq_zero {v w : EuclideanSpace ℂ (Fin N)}
    (h : ⟪v, w⟫_ℂ = 0) : rankOne v * rankOne w = 0 := by
  rw [rankOne_mul_rankOne, h, zero_smul]
lemma isStarProjection_rankOne {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) :
    IsStarProjection (rankOne v) where
  isIdempotentElem := rankOne_mul_self hv
  isSelfAdjoint := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
    exact (rankOne_isHermitian v).eq
lemma rankOne_smul_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    rankOne (c • v) = rankOne v := by
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  rw [rankOne, rankOne]
  change vecMulVec (c • ⇑v) (star (c • ⇑v)) = _
  rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, Complex.star_def, hcc, one_smul]
lemma rankOne_mul_rankOne_of_orthonormal {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {i j : Fin k} (hij : i ≠ j) : rankOne (e i) * rankOne (e j) = 0 :=
  rankOne_mul_rankOne_of_inner_eq_zero (he.inner_eq_zero hij)
lemma sum_rankOne_eq (e : Fin N → EuclideanSpace ℂ (Fin N)) :
    ∑ i, rankOne (e i) = colMatrix e * (colMatrix e)ᴴ :=
  sum_vecMulVec_eq_colMatrix_mul e
lemma sum_rankOne_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, rankOne (b i) = 1 := by
  rw [sum_rankOne_eq, colMatrix_mul_conjTranspose_of_orthonormalBasis]
def IsFrameFunction (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (f : EuclideanSpace 𝕜 (Fin n) → ℝ)
    (W : ℝ) : Prop :=
  ∀ b : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)), ∑ i, f (b i) = W
structure ProjectionPackage (N : ℕ) where
  p : Matrix (Fin N) (Fin N) ℂ → ℝ
  nonneg : ∀ P, IsStarProjection P → 0 ≤ p P
  total_one : p 1 = 1
  additive : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 → p (P + Q) = p P + p Q
namespace ProjectionPackage
variable (OP : ProjectionPackage N)
theorem p_zero : OP.p 0 = 0 := by
  have h := OP.additive 0 0 (IsStarProjection.zero _) (IsStarProjection.zero _) (by simp)
  rw [add_zero] at h
  linarith
theorem p_le_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P) : OP.p P ≤ 1 := by
  have h := OP.additive P (1 - P) hP hP.one_sub hP.mul_one_sub_self
  rw [add_sub_cancel, OP.total_one] at h
  have := OP.nonneg (1 - P) hP.one_sub
  linarith
theorem isStarProjection_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) (s : Finset ι) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (hP a).add ih ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => horth a j (fun h => ha (h ▸ hj))
theorem p_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) (s : Finset ι) :
    OP.p (∑ i ∈ s, P i) = ∑ i ∈ s, OP.p (P i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [OP.p_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    refine OP.additive _ _ (hP a) (isStarProjection_sum P hP horth s) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => horth a j (fun h => ha (h ▸ hj))
def frame (v : EuclideanSpace ℂ (Fin N)) : ℝ := OP.p (rankOne v)
theorem frame_nonneg {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : 0 ≤ OP.frame v :=
  OP.nonneg _ (isStarProjection_rankOne hv)
theorem frame_le_one {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : OP.frame v ≤ 1 :=
  OP.p_le_one (isStarProjection_rankOne hv)
theorem frame_smul {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    OP.frame (c • v) = OP.frame v := by
  rw [frame, frame, rankOne_smul_of_norm_one hc]
theorem p_sum_rankOne {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)} (he : Orthonormal ℂ e) :
    OP.p (∑ i, rankOne (e i)) = ∑ i, OP.frame (e i) :=
  OP.p_sum _ (fun i => isStarProjection_rankOne (he.norm_eq_one i))
    (fun _ _ hij => rankOne_mul_rankOne_of_orthonormal he hij) Finset.univ
theorem sum_frame_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, OP.frame (b i) = 1 := by
  rw [← OP.p_sum_rankOne b.orthonormal, sum_rankOne_orthonormalBasis, OP.total_one]
def realCombination {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N))
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℂ (Fin N) :=
  ∑ i, ((x i : ℝ) : ℂ) • e i
lemma orthonormal_realCombination {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {b : Fin k → EuclideanSpace ℝ (Fin k)} (hb : Orthonormal ℝ b) :
    Orthonormal ℂ fun j => realCombination e (b j) := by
  rw [orthonormal_iff_ite]
  intro j l
  have hcol : colMatrix (fun j => realCombination e (b j))
      = colMatrix e * (colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext a j
    simp [realCombination, colMatrix_apply, Matrix.mul_apply, mul_comm]
  have hgram := conjTranspose_mul_colMatrix_apply (fun j => realCombination e (b j)) j l
  rw [hcol, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (colMatrix e)ᴴ,
    conjTranspose_mul_colMatrix_of_orthonormal he, Matrix.one_mul] at hgram
  rw [← hgram]
  have hB := conjTranspose_mul_colMatrix_of_orthonormal hb
  have hBc : ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ * (colMatrix b).map ((↑) : ℝ → ℂ)
      = ((colMatrix b)ᴴ * colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext i i'
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  rw [hBc, hB]
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp
lemma sum_rankOne_realCombination {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N))
    (b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    ∑ j, rankOne (realCombination e (b j)) = ∑ i, rankOne (e i) := by
  have hcol : colMatrix (fun j => realCombination e (b j))
      = colMatrix e * (colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext a j
    simp [realCombination, colMatrix_apply, Matrix.mul_apply, mul_comm]
  have hBB : (colMatrix b).map ((↑) : ℝ → ℂ) * ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ = 1 := by
    have h := colMatrix_mul_conjTranspose_of_orthonormalBasis b
    have hmap : (colMatrix b).map ((↑) : ℝ → ℂ) * ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ
        = (colMatrix b * (colMatrix b)ᴴ).map ((↑) : ℝ → ℂ) := by
      ext i i'
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal]
    rw [hmap, h]
    ext i i'
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [show ∑ j, rankOne (realCombination e (b j))
      = colMatrix (fun j => realCombination e (b j))
        * (colMatrix (fun j => realCombination e (b j)))ᴴ from
      sum_vecMulVec_eq_colMatrix_mul _,
    show ∑ i, rankOne (e i) = colMatrix e * (colMatrix e)ᴴ from
      sum_vecMulVec_eq_colMatrix_mul _,
    hcol, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (colMatrix e)ᴴ,
    hBB, Matrix.one_mul]
lemma norm_realCombination {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    ‖realCombination e x‖ = 1 := by
  have hsq : ‖realCombination e x‖ ^ 2 = 1 := by
    rw [← @inner_self_eq_norm_sq ℂ, realCombination, he.inner_sum]
    have hc : ∑ i, conj ((x i : ℝ) : ℂ) * ((x i : ℝ) : ℂ) = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_ofReal, sq]
    rw [hc]
    change ((∑ i, x i ^ 2 : ℝ) : ℂ).re = 1
    rw [Complex.ofReal_re]
    have hx2 := hx
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hx2
    simpa [Real.norm_eq_abs, sq_abs] using hx2
  have := norm_nonneg (realCombination e x)
  nlinarith
def realRestrict {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N)) (x : EuclideanSpace ℝ (Fin k)) :
    ℝ :=
  OP.frame (realCombination e x)
theorem isFrameFunction_realRestrict {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) :
    IsFrameFunction ℝ (OP.realRestrict e) (OP.p (∑ i, rankOne (e i))) := by
  intro b
  rw [← sum_rankOne_realCombination e b, OP.p_sum_rankOne (orthonormal_realCombination he
    b.orthonormal)]
  rfl
theorem realRestrict_nonneg {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    0 ≤ OP.realRestrict e x := by
  exact OP.frame_nonneg (norm_realCombination he hx)
end ProjectionPackage
end Gleason
open Matrix
open scoped Matrix InnerProductSpace
namespace Gleason
lemma real_inner_eq_dotProduct (x y : EuclideanSpace ℝ (Fin 3)) : ⟪x, y⟫_ℝ = ⇑x ⬝ᵥ ⇑y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
def cross (x y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (⇑x ⨯₃ ⇑y)
@[simp] lemma coe_cross (x y : EuclideanSpace ℝ (Fin 3)) : ⇑(cross x y) = ⇑x ⨯₃ ⇑y := rfl
lemma inner_cross_left (x y : EuclideanSpace ℝ (Fin 3)) : ⟪x, cross x y⟫_ℝ = 0 := by
  rw [real_inner_eq_dotProduct, coe_cross, dot_self_cross]
lemma inner_cross_right (x y : EuclideanSpace ℝ (Fin 3)) : ⟪y, cross x y⟫_ℝ = 0 := by
  rw [real_inner_eq_dotProduct, coe_cross, dot_cross_self]
lemma inner_cross_cross (u v w x : EuclideanSpace ℝ (Fin 3)) :
    ⟪cross u v, cross w x⟫_ℝ = ⟪u, w⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, x⟫_ℝ * ⟪v, w⟫_ℝ := by
  simp only [real_inner_eq_dotProduct, coe_cross, cross_dot_cross]
lemma norm_cross_of_orthonormal {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) : ‖cross x y‖ = 1 := by
  have h : ⟪cross x y, cross x y⟫_ℝ = 1 := by
    rw [inner_cross_cross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy, hxy,
      real_inner_comm, hxy]
    norm_num
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (cross x y)]
lemma orthonormal_triple_iff {x y z : EuclideanSpace ℝ (Fin 3)} :
    Orthonormal ℝ ![x, y, z] ↔ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ‖z‖ = 1 ∧
      ⟪x, y⟫_ℝ = 0 ∧ ⟪x, z⟫_ℝ = 0 ∧ ⟪y, z⟫_ℝ = 0 := by
  have hn : ∀ v : EuclideanSpace ℝ (Fin 3), ⟪v, v⟫_ℝ = 1 ↔ ‖v‖ = 1 := by
    intro v
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h; nlinarith [norm_nonneg v]
    · intro h; rw [h]; norm_num
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    refine ⟨(hn x).mp (by simpa using h 0 0), (hn y).mp (by simpa using h 1 1),
      (hn z).mp (by simpa using h 2 2), by simpa using h 0 1, by simpa using h 0 2,
      by simpa using h 1 2⟩
  · rintro ⟨hx, hy, hz, hxy, hxz, hyz⟩ i j
    have hyx : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy]
    have hzx : ⟪z, x⟫_ℝ = 0 := by rw [real_inner_comm, hxz]
    have hzy : ⟪z, y⟫_ℝ = 0 := by rw [real_inner_comm, hyz]
    fin_cases i <;> fin_cases j <;> simp [hx, hy, hz, hxy, hxz, hyz, hyx, hzx, hzy]
lemma orthonormal_cross {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) : Orthonormal ℝ ![x, y, cross x y] :=
  orthonormal_triple_iff.mpr ⟨hx, hy, norm_cross_of_orthonormal hx hy hxy, hxy,
    inner_cross_left x y, inner_cross_right x y⟩
lemma exists_unit_orthogonal_pair (s t : EuclideanSpace ℝ (Fin 3)) :
    ∃ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 ∧ ⟪s, w⟫_ℝ = 0 ∧ ⟪t, w⟫_ℝ = 0 := by
  classical
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ (({s, t} : Finset (EuclideanSpace ℝ (Fin 3))) : Set _) with hK
  have hKle : Module.finrank ℝ K ≤ 2 :=
    (finrank_span_finset_le_card ({s, t} : Finset _)).trans Finset.card_le_two
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    have := Submodule.finrank_add_finrank_orthogonal K
    rw [h, finrank_bot, finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨w₀, hw₀K, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  refine ⟨(‖w₀‖⁻¹ : ℝ) • w₀, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
      (by simp)) hw₀K, mul_zero]
  · rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
      (by simp)) hw₀K, mul_zero]
lemma exists_unit_orthogonal (s : EuclideanSpace ℝ (Fin 3)) :
    ∃ t : EuclideanSpace ℝ (Fin 3), ‖t‖ = 1 ∧ ⟪s, t⟫_ℝ = 0 := by
  obtain ⟨w, hw, hsw, -⟩ := exists_unit_orthogonal_pair s s
  exact ⟨w, hw, hsw⟩
noncomputable def orthonormalBasisOfTriple {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  OrthonormalBasis.mk hv (by
    have h := (basisOfOrthonormalOfCardEqFinrank hv (by simp)).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at h
    exact h.ge)
@[simp] lemma coe_orthonormalBasisOfTriple {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : ⇑(orthonormalBasisOfTriple hv) = v :=
  OrthonormalBasis.coe_mk hv _
namespace IsFrameFunction
section Linear
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {f g : EuclideanSpace 𝕜 (Fin n) → ℝ} {W W' : ℝ}
theorem const (c : ℝ) : IsFrameFunction 𝕜 (fun _ : EuclideanSpace 𝕜 (Fin n) => c) (n * c) :=
  fun _ => by simp
theorem add (hf : IsFrameFunction 𝕜 f W) (hg : IsFrameFunction 𝕜 g W') :
    IsFrameFunction 𝕜 (fun s => f s + g s) (W + W') :=
  fun b => by rw [Finset.sum_add_distrib, hf b, hg b]
theorem smul (hf : IsFrameFunction 𝕜 f W) (c : ℝ) :
    IsFrameFunction 𝕜 (fun s => c * f s) (c * W) :=
  fun b => by rw [← Finset.mul_sum, hf b]
theorem neg (hf : IsFrameFunction 𝕜 f W) : IsFrameFunction 𝕜 (fun s => -f s) (-W) :=
  fun b => by rw [Finset.sum_neg_distrib, hf b]
theorem sub (hf : IsFrameFunction 𝕜 f W) (hg : IsFrameFunction 𝕜 g W') :
    IsFrameFunction 𝕜 (fun s => f s - g s) (W - W') :=
  fun b => by rw [Finset.sum_sub_distrib, hf b, hg b]
end Linear
variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W : ℝ}
theorem sum_triple (hf : IsFrameFunction ℝ f W) {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : ∑ i, f (v i) = W := by
  have h := hf (orthonormalBasisOfTriple hv)
  simpa only [coe_orthonormalBasisOfTriple] using h
theorem eq_of_triple (hf : IsFrameFunction ℝ f W) {p q r : EuclideanSpace ℝ (Fin 3)}
    (h : Orthonormal ℝ ![p, q, r]) : f p + f q + f r = W := by
  have := hf.sum_triple h
  simpa [Fin.sum_univ_three] using this
theorem neg_apply (hf : IsFrameFunction ℝ f W) {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) :
    f (-s) = f s := by
  obtain ⟨t, ht, hst⟩ := exists_unit_orthogonal s
  have h1 := hf.eq_of_triple (orthonormal_cross hs ht hst)
  have h2 := hf.eq_of_triple (p := -s) (q := t) (r := cross s t)
    (orthonormal_triple_iff.mpr ⟨by rw [norm_neg, hs], ht, norm_cross_of_orthonormal hs ht hst,
      by rw [inner_neg_left, hst, neg_zero], by rw [inner_neg_left, inner_cross_left, neg_zero],
      inner_cross_right s t⟩)
  linarith
theorem four_point (hf : IsFrameFunction ℝ f W) {w s t s' t' : EuclideanSpace ℝ (Fin 3)}
    (hw : ‖w‖ = 1) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hs' : ‖s'‖ = 1) (ht' : ‖t'‖ = 1)
    (hsw : ⟪s, w⟫_ℝ = 0) (htw : ⟪t, w⟫_ℝ = 0) (hs'w : ⟪s', w⟫_ℝ = 0) (ht'w : ⟪t', w⟫_ℝ = 0)
    (hst : ⟪s, t⟫_ℝ = 0) (hs't' : ⟪s', t'⟫_ℝ = 0) : f s + f t = f s' + f t' := by
  have h1 := hf.eq_of_triple (orthonormal_triple_iff.mpr ⟨hs, ht, hw, hst, hsw, htw⟩)
  have h2 := hf.eq_of_triple (orthonormal_triple_iff.mpr ⟨hs', ht', hw, hs't', hs'w, ht'w⟩)
  linarith
theorem exists_orthogonal_lt (hf : IsFrameFunction ℝ f W) {M m : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    (hm : ∀ δ : ℝ, 0 < δ → ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ f u < m + δ)
    {ξ : ℝ} {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) (hfs : M - ξ < f s) :
    ∃ t : EuclideanSpace ℝ (Fin 3), ‖t‖ = 1 ∧ ⟪s, t⟫_ℝ = 0 ∧ f t < m + ξ := by
  set δ : ℝ := (f s - (M - ξ)) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hsδ : M - ξ + δ < f s := by rw [hδ]; linarith
  obtain ⟨t', ht', hft'⟩ := hm δ hδpos
  obtain ⟨w, hw, hsw, ht'w⟩ := exists_unit_orthogonal_pair s t'
  refine ⟨cross s w, norm_cross_of_orthonormal hs hw hsw, inner_cross_left s w, ?_⟩
  have hcw : ⟪cross s w, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_cross_right s w
  have hs'w : ⟪cross t' w, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_cross_right t' w
  have h4 := hf.four_point hw hs (norm_cross_of_orthonormal hs hw hsw)
    (norm_cross_of_orthonormal ht' hw ht'w) ht' hsw hcw hs'w ht'w (inner_cross_left s w)
    (by rw [real_inner_comm]; exact inner_cross_left t' w)
  have hs'M := hM (cross t' w) (norm_cross_of_orthonormal ht' hw ht'w)
  linarith
theorem le_weight_of_nonneg (hf : IsFrameFunction ℝ f W)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : f s ≤ W := by
  obtain ⟨t, ht, hst⟩ := exists_unit_orthogonal s
  have h := hf.eq_of_triple (orthonormal_cross hs ht hst)
  have := h0 t ht
  have := h0 _ (norm_cross_of_orthonormal hs ht hst)
  linarith
end IsFrameFunction
noncomputable def sphereSup (f : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  sSup (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
noncomputable def sphereInf (f : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  sInf (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
section SupInf
variable {f : EuclideanSpace ℝ (Fin 3) → ℝ}
lemma sphere_nonempty : (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
  ⟨f (EuclideanSpace.single 0 1), EuclideanSpace.single 0 (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]; exact norm_one, rfl⟩
lemma bddAbove_sphere {M : ℝ} (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) :
    BddAbove (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hM u (mem_sphere_zero_iff_norm.mp hu)
lemma bddBelow_sphere {m : ℝ} (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    BddBelow (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  refine ⟨m, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hm u (mem_sphere_zero_iff_norm.mp hu)
lemma le_sphereSup {M : ℝ} (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : f s ≤ sphereSup f :=
  le_csSup (bddAbove_sphere hM) ⟨s, mem_sphere_zero_iff_norm.mpr hs, rfl⟩
lemma sphereInf_le {m : ℝ} (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : sphereInf f ≤ f s :=
  csInf_le (bddBelow_sphere hm) ⟨s, mem_sphere_zero_iff_norm.mpr hs, rfl⟩
lemma exists_sphereSup_sub_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ sphereSup f - δ < f u := by
  obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := exists_lt_of_lt_csSup (sphere_nonempty (f := f))
    (show sphereSup f - δ < sphereSup f by linarith)
  exact ⟨u, mem_sphere_zero_iff_norm.mp hu, h⟩
lemma exists_lt_sphereInf_add {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ f u < sphereInf f + δ := by
  obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := exists_lt_of_csInf_lt (sphere_nonempty (f := f))
    (show sphereInf f < sphereInf f + δ by linarith)
  exact ⟨u, mem_sphere_zero_iff_norm.mp hu, h⟩
end SupInf
theorem isFrameFunction_inner_sq {p₀ : EuclideanSpace ℝ (Fin 3)} (hp₀ : ‖p₀‖ = 1) :
    IsFrameFunction ℝ (fun s => ⟪p₀, s⟫_ℝ ^ 2) 1 := by
  intro b
  have h := b.sum_inner_mul_inner p₀ p₀
  rw [real_inner_self_eq_norm_sq, hp₀] at h
  simp only [one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ⟪p₀, b i⟫_ℝ ^ 2 = ⟪p₀, b i⟫_ℝ * ⟪b i, p₀⟫_ℝ
  rw [real_inner_comm p₀ (b i), sq]
end Gleason
open Matrix Real
open scoped Matrix InnerProductSpace ComplexConjugate
namespace Gleason
noncomputable def latitude (p s : EuclideanSpace ℝ (Fin 3)) : ℝ := ⟪p, s⟫_ℝ ^ 2
def northern (p : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {s | ‖s‖ = 1 ∧ 0 ≤ ⟪p, s⟫_ℝ}
def equator (p : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {s | ‖s‖ = 1 ∧ ⟪p, s⟫_ℝ = 0}
noncomputable def coldest (p s : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (‖p - ⟪p, s⟫_ℝ • s‖⁻¹ : ℝ) • (p - ⟪p, s⟫_ℝ • s)
def descent (p s : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {t | t ∈ northern p ∧ ⟪t, coldest p s⟫_ℝ = 0}
lemma equator_subset_northern (p : EuclideanSpace ℝ (Fin 3)) : equator p ⊆ northern p :=
  fun _ h => ⟨h.1, h.2.ge⟩
lemma inner_coldest_self (p : EuclideanSpace ℝ (Fin 3)) {s : EuclideanSpace ℝ (Fin 3)}
    (hs : ‖s‖ = 1) : ⟪s, coldest p s⟫_ℝ = 0 := by
  rw [coldest, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hs, real_inner_comm]
  ring
lemma mem_descent_of_equator {p s t : EuclideanSpace ℝ (Fin 3)} (ht : t ∈ equator p)
    (hts : ⟪t, s⟫_ℝ = 0) : t ∈ descent p s := by
  refine ⟨equator_subset_northern p ht, ?_⟩
  rw [coldest, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_comm p t, ht.2,
    hts]
  ring
noncomputable def lift (p v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (‖p + v‖⁻¹ : ℝ) • (p + v)
section Lift
variable {p v w : EuclideanSpace ℝ (Fin 3)}
lemma norm_sq_add_of_inner_zero (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) :
    ‖p + v‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, hp, hv]; ring
lemma norm_add_pos (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : 0 < ‖p + v‖ := by
  have h := norm_sq_add_of_inner_zero hp hv
  have := norm_nonneg (p + v)
  nlinarith [sq_nonneg ‖v‖]
lemma norm_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : ‖lift p v‖ = 1 := by
  have h := norm_add_pos hp hv
  rw [lift, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']
lemma inner_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : ⟪p, lift p v⟫_ℝ = ‖p + v‖⁻¹ := by
  rw [lift, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hp, hv]
  ring
lemma inner_lift_pos (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : 0 < ⟪p, lift p v⟫_ℝ := by
  rw [inner_lift hp hv]; exact inv_pos.mpr (norm_add_pos hp hv)
lemma lift_mem_northern (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : lift p v ∈ northern p :=
  ⟨norm_lift hp hv, (inner_lift_pos hp hv).le⟩
lemma lift_ne_pole (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hv0 : v ≠ 0) : lift p v ≠ p := by
  intro h
  have h1 : ⟪p, lift p v⟫_ℝ = 1 := by rw [h, real_inner_self_eq_norm_sq, hp]; norm_num
  rw [inner_lift hp hv, inv_eq_one] at h1
  have h2 := norm_sq_add_of_inner_zero hp hv
  rw [h1] at h2
  have : ‖v‖ ^ 2 = 0 := by linarith
  exact hv0 (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
lemma latitude_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) :
    latitude p (lift p v) = 1 / (1 + ‖v‖ ^ 2) := by
  rw [latitude, inner_lift hp hv, inv_pow, ← norm_sq_add_of_inner_zero hp hv, one_div]
lemma latitude_lift_lt_iff (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hw : ⟪p, w⟫_ℝ = 0) :
    latitude p (lift p w) < latitude p (lift p v) ↔ ‖v‖ < ‖w‖ := by
  rw [latitude_lift hp hv, latitude_lift hp hw, one_div_lt_one_div (by positivity) (by positivity)]
  constructor
  · intro h; nlinarith [norm_nonneg v, norm_nonneg w]
  · intro h; nlinarith [norm_nonneg v, norm_nonneg w]
lemma eq_lift_of_northern (hp : ‖p‖ = 1) {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1)
    (hps : 0 < ⟪p, s⟫_ℝ) :
    ⟪p, (⟪p, s⟫_ℝ)⁻¹ • s - p⟫_ℝ = 0 ∧ s = lift p ((⟪p, s⟫_ℝ)⁻¹ • s - p) := by
  have h1 : ⟪p, (⟪p, s⟫_ℝ)⁻¹ • s - p⟫_ℝ = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hp,
      inv_mul_cancel₀ hps.ne']
    ring
  refine ⟨h1, ?_⟩
  have h2 : p + ((⟪p, s⟫_ℝ)⁻¹ • s - p) = (⟪p, s⟫_ℝ)⁻¹ • s := by abel
  rw [lift, h2, norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hps), inv_inv,
    smul_smul, mul_inv_cancel₀ hps.ne', one_smul]
lemma lift_mem_descent_iff (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hw : ⟪p, w⟫_ℝ = 0)
    (hv0 : v ≠ 0) : lift p w ∈ descent p (lift p v) ↔ ⟪w, v⟫_ℝ = ‖v‖ ^ 2 := by
  have hc := inner_lift hp hv
  set c : ℝ := ‖p + v‖⁻¹ with hcdef
  have hcpos : 0 < c := inv_pos.mpr (norm_add_pos hp hv)
  have hc2 : c ^ 2 * (1 + ‖v‖ ^ 2) = 1 := by
    rw [hcdef, inv_pow, ← norm_sq_add_of_inner_zero hp hv, inv_mul_cancel₀]
    exact (pow_pos (norm_add_pos hp hv) 2).ne'
  have hx : p - ⟪p, lift p v⟫_ℝ • lift p v = (1 - c ^ 2) • p - c ^ 2 • v := by
    rw [hc, lift, ← hcdef, smul_smul, ← sq, smul_add, sub_smul, one_smul]
    abel
  have hxne : (1 - c ^ 2) • p - c ^ 2 • v ≠ 0 := by
    intro h
    have h1 : ⟪v, (1 - c ^ 2) • p - c ^ 2 • v⟫_ℝ = -(c ^ 2 * ‖v‖ ^ 2) := by
      rw [inner_sub_right, inner_smul_right, inner_smul_right, real_inner_comm p v, hv,
        real_inner_self_eq_norm_sq]
      ring
    rw [h, inner_zero_right] at h1
    have h2 : c ^ 2 * ‖v‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (pow_pos hcpos 2).ne' h3
    · exact hv0 (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))
  have hin : ⟪lift p w, coldest p (lift p v)⟫_ℝ
      = ‖p + w‖⁻¹ * ‖(1 - c ^ 2) • p - c ^ 2 • v‖⁻¹ * ((1 - c ^ 2) - c ^ 2 * ⟪w, v⟫_ℝ) := by
    rw [coldest, hx, lift, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
      inner_sub_right, inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hp, hv, real_inner_comm p w, hw]
    simp only [RCLike.conj_to_real]
    ring
  constructor
  · rintro ⟨-, h⟩
    rw [hin] at h
    have hne : ‖p + w‖⁻¹ * ‖(1 - c ^ 2) • p - c ^ 2 • v‖⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero (norm_add_pos hp hw).ne') (inv_ne_zero (norm_ne_zero_iff.mpr hxne))
    have h' : (1 - c ^ 2) - c ^ 2 * ⟪w, v⟫_ℝ = 0 := (mul_eq_zero.mp h).resolve_left hne
    have hc0 : c ^ 2 ≠ 0 := (pow_pos hcpos 2).ne'
    field_simp
    nlinarith [hc2, h']
  · intro h
    refine ⟨lift_mem_northern hp hw, ?_⟩
    rw [hin, h]
    have : (1 - c ^ 2) - c ^ 2 * ‖v‖ ^ 2 = 0 := by linarith
    rw [this, mul_zero]
end Lift
noncomputable def tangent (e₁ e₂ : EuclideanSpace ℝ (Fin 3)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  z.re • e₁ + z.im • e₂
section Tangent
variable {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)} (he : Orthonormal ℝ ![p, e₁, e₂])
include he
lemma inner_tangent_tangent (z w : ℂ) :
    ⟪tangent e₁ e₂ z, tangent e₁ e₂ w⟫_ℝ = (z * conj w).re := by
  obtain ⟨-, h1, h2, -, -, h12⟩ := orthonormal_triple_iff.mp he
  have h21 : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm, h12]
  have h11 : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : ⟪e₂, e₂⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h2]; norm_num
  simp only [tangent, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h11,
    h22, h12, h21, RCLike.conj_to_real, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
lemma norm_sq_tangent (z : ℂ) : ‖tangent e₁ e₂ z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangent_tangent he, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_re]
lemma norm_tangent (z : ℂ) : ‖tangent e₁ e₂ z‖ = ‖z‖ := by
  have h := norm_sq_tangent he z
  have := norm_nonneg (tangent e₁ e₂ z)
  have := norm_nonneg z
  nlinarith
lemma inner_pole_tangent (z : ℂ) : ⟪p, tangent e₁ e₂ z⟫_ℝ = 0 := by
  obtain ⟨-, -, -, h01, h02, -⟩ := orthonormal_triple_iff.mp he
  simp [tangent, inner_add_right, inner_smul_right, h01, h02]
lemma tangent_ne_zero {z : ℂ} (hz : z ≠ 0) : tangent e₁ e₂ z ≠ 0 := by
  intro h
  have := norm_tangent he z
  rw [h, norm_zero] at this
  exact hz (norm_eq_zero.mp this.symm)
lemma exists_tangent_eq {v : EuclideanSpace ℝ (Fin 3)} (hv : ⟪p, v⟫_ℝ = 0) :
    ∃ z : ℂ, tangent e₁ e₂ z = v := by
  refine ⟨⟨⟪e₁, v⟫_ℝ, ⟪e₂, v⟫_ℝ⟩, ?_⟩
  have h := (orthonormalBasisOfTriple he).sum_repr' v
  simp only [coe_orthonormalBasisOfTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, hv, zero_smul, zero_add] at h
  simpa [tangent] using h
end Tangent
lemma lift_tangent_mem_descent_iff {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)}
    (he : Orthonormal ℝ ![p, e₁, e₂]) {z w : ℂ} (hz : z ≠ 0) :
    lift p (tangent e₁ e₂ w) ∈ descent p (lift p (tangent e₁ e₂ z))
      ↔ (w * conj z).re = ‖z‖ ^ 2 := by
  have hp : ‖p‖ = 1 := (orthonormal_triple_iff.mp he).1
  rw [lift_mem_descent_iff hp (inner_pole_tangent he z) (inner_pole_tangent he w)
    (tangent_ne_zero he hz), inner_tangent_tangent he, norm_sq_tangent he]
lemma descent_step_ray (ζ : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I) * conj ((ρ : ℂ) * ζ)).re
        = ‖(ρ : ℂ) * ζ‖ ^ 2 ∧
      (ζ * conj ((ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I))).re
        = ‖(ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I)‖ ^ 2 := by
  have hμ : Real.sqrt (1 / ρ - 1) ^ 2 = 1 / ρ - 1 := Real.sq_sqrt (by
    rw [sub_nonneg, one_div, one_le_inv₀ hρ0]; exact hρ1)
  have hμρ : ρ * Real.sqrt (1 / ρ - 1) ^ 2 = 1 - ρ := by
    rw [hμ]; field_simp
  constructor
  · simp only [Complex.sq_norm, Complex.normSq_apply, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.sq_norm, Complex.normSq_apply, map_mul, map_add, map_one,
      Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
      Complex.neg_im]
    linear_combination (-(ρ * (ζ.re ^ 2 + ζ.im ^ 2))) * hμρ
noncomputable def spiral (z₀ : ℂ) (θ : ℝ) (k : ℕ) : ℂ :=
  z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ k * Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)
lemma spiral_zero (z₀ : ℂ) (θ : ℝ) : spiral z₀ θ 0 = z₀ := by
  simp [spiral]
lemma spiral_ne_zero {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    spiral z₀ θ k ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero hz₀ (pow_ne_zero _ ?_)) (Complex.exp_ne_zero _)
  exact_mod_cast (inv_pos.mpr hcos).ne'
lemma norm_sq_spiral {z₀ : ℂ} {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    ‖spiral z₀ θ k‖ ^ 2 = ‖z₀‖ ^ 2 * ((Real.cos θ)⁻¹) ^ (2 * k) := by
  rw [spiral, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcos), mul_pow, ← pow_mul,
    mul_comm k 2]
lemma spiral_succ_mul_conj (z₀ : ℂ) (θ : ℝ) (k : ℕ) :
    spiral z₀ θ (k + 1) * conj (spiral z₀ θ k)
      = ((Complex.normSq z₀ : ℝ) : ℂ) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
        * Complex.exp ((θ : ℂ) * Complex.I) := by
  have hconj : conj (Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hexp : Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
      * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [spiral, map_mul, map_pow, Complex.conj_ofReal, hconj]
  calc z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (k + 1)
        * Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
        * (conj z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ k
          * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)))
      = (z₀ * conj z₀) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
        * (Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))) := by
        rw [show 2 * k + 1 = (k + 1) + k by ring, pow_add]
        ring
    _ = _ := by rw [Complex.mul_conj, hexp]
lemma spiral_step (z₀ : ℂ) {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    (spiral z₀ θ (k + 1) * conj (spiral z₀ θ k)).re = ‖spiral z₀ θ k‖ ^ 2 := by
  rw [spiral_succ_mul_conj, norm_sq_spiral hcos]
  have h1 : ((Complex.normSq z₀ : ℝ) : ℂ) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
      = ((Complex.normSq z₀ * ((Real.cos θ)⁻¹) ^ (2 * k + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.normSq_eq_norm_sq]
  have h2 : (Real.cos θ)⁻¹ ^ (2 * k + 1) * Real.cos θ = (Real.cos θ)⁻¹ ^ (2 * k) := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hcos.ne', mul_one]
  rw [mul_assoc, h2]
lemma spiral_end {z₀ u : ℂ} (hu : ‖u‖ = 1) {n : ℕ} (hn : n ≠ 0) :
    spiral z₀ (Complex.arg u / n) n
      = z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u := by
  rw [spiral]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : ((n : ℝ) * (Complex.arg u / n) : ℝ) = Complex.arg u := by field_simp
  rw [this]
  have h := Complex.norm_mul_exp_arg_mul_I u
  rwa [hu, Complex.ofReal_one, one_mul] at h
lemma cos_arg_div_pos (u : ℂ) {n : ℕ} (hn : 3 ≤ n) : 0 < Real.cos (Complex.arg u / n) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have habs := Complex.abs_arg_le_pi u
  have hpi := Real.pi_pos
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by linarith)]
    have := (abs_le.mp habs).1
    nlinarith
  · rw [div_lt_iff₀ (by linarith)]
    have := (abs_le.mp habs).2
    nlinarith
lemma one_sub_le_cos_arg_div_pow (u : ℂ) {n : ℕ} (hn : 3 ≤ n) :
    1 - Real.pi ^ 2 / (2 * n) ≤ Real.cos (Complex.arg u / n) ^ n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have habs := Complex.abs_arg_le_pi u
  have hpi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  set a : ℝ := -(Real.pi ^ 2 / (2 * n ^ 2)) with ha
  have ha2 : -2 ≤ a := by
    rw [ha, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    nlinarith
  have hcos : 1 + a ≤ Real.cos (Complex.arg u / n) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := Complex.arg u / n)
    have h2 : (Complex.arg u / n) ^ 2 ≤ Real.pi ^ 2 / n ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right
        (by nlinarith [sq_abs (Complex.arg u), abs_nonneg (Complex.arg u)]) (by positivity)
    rw [ha]
    have : Real.pi ^ 2 / (2 * n ^ 2) = (Real.pi ^ 2 / n ^ 2) / 2 := by ring
    rw [this]
    linarith
  have h0 : 0 ≤ 1 + a := by
    rw [ha, ← sub_eq_add_neg, sub_nonneg, div_le_one (by positivity)]
    nlinarith
  calc 1 - Real.pi ^ 2 / (2 * n) = 1 + n * a := by rw [ha]; field_simp; ring
    _ ≤ (1 + a) ^ n := one_add_mul_le_pow ha2 n
    _ ≤ Real.cos (Complex.arg u / n) ^ n := pow_le_pow_left₀ h0 hcos n
structure IsDescentChain (p s t : EuclideanSpace ℝ (Fin 3)) (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin 3)) : Prop where
  head : c 0 = s
  last : c n = t
  mem : ∀ i, i ≤ n → c i ∈ northern p ∧ c i ≠ p
  step : ∀ i, i < n → c (i + 1) ∈ descent p (c i)
section Spiral
variable {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)} (he : Orthonormal ℝ ![p, e₁, e₂])
include he
lemma spiral_chain_step {z₀ : ℂ} {θ : ℝ} (hz₀ : z₀ ≠ 0) (hcos : 0 < Real.cos θ) (k : ℕ) :
    lift p (tangent e₁ e₂ (spiral z₀ θ (k + 1)))
      ∈ descent p (lift p (tangent e₁ e₂ (spiral z₀ θ k))) := by
  rw [lift_tangent_mem_descent_iff he (spiral_ne_zero hz₀ hcos k)]
  exact spiral_step z₀ hcos k
lemma lift_tangent_mem (z : ℂ) (hz : z ≠ 0) :
    lift p (tangent e₁ e₂ z) ∈ northern p ∧ lift p (tangent e₁ e₂ z) ≠ p :=
  have hp : ‖p‖ = 1 := (orthonormal_triple_iff.mp he).1
  ⟨lift_mem_northern hp (inner_pole_tangent he z),
    lift_ne_pole hp (inner_pole_tangent he z) (tangent_ne_zero he hz)⟩
end Spiral
theorem exists_descent_chain {p s t : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1)
    (hs : s ∈ northern p) (hsp : s ≠ p) (ht : t ∈ northern p) (htp : t ≠ p)
    (hl : latitude p t < latitude p s) :
    ∃ (n : ℕ) (c : ℕ → EuclideanSpace ℝ (Fin 3)), 1 ≤ n ∧ IsDescentChain p s t n c := by
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  set e₂ := cross p e₁ with he₂
  have he : Orthonormal ℝ ![p, e₁, e₂] := orthonormal_cross hp he₁ hpe₁
  have hps : 0 < ⟪p, s⟫_ℝ := by
    rcases eq_or_lt_of_le hs.2 with h | h
    · exfalso
      have : latitude p s = 0 := by rw [latitude, ← h]; ring
      rw [this] at hl
      exact absurd hl (not_lt.mpr (sq_nonneg _))
    · exact h
  obtain ⟨hvs, hsl⟩ := eq_lift_of_northern hp hs.1 hps
  obtain ⟨z₀, hz₀⟩ := exists_tangent_eq he hvs
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl
    apply hsp
    rw [hsl, ← hz₀]
    simp [tangent, lift, hp]
  have hx : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀0
  have spiral_reach : ∀ u : ℂ, ‖u‖ = 1 → ∀ n : ℕ, 3 ≤ n →
      ∃ c : ℕ → EuclideanSpace ℝ (Fin 3), c 0 = s ∧
        c n = lift p (tangent e₁ e₂ (z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u))
        ∧ (∀ i, i ≤ n → c i ∈ northern p ∧ c i ≠ p) ∧
        ∀ i, i < n → c (i + 1) ∈ descent p (c i) := by
    intro u hu n hn
    have hcos := cos_arg_div_pos u hn
    refine ⟨fun k => lift p (tangent e₁ e₂ (spiral z₀ (Complex.arg u / n) k)), ?_, ?_, ?_, ?_⟩
    · simp only [spiral_zero]
      rw [hz₀, ← hsl]
    · show lift p (tangent e₁ e₂ (spiral z₀ (Complex.arg u / n) n)) = _
      rw [spiral_end hu (by omega)]
    · intro i _
      exact lift_tangent_mem he _ (spiral_ne_zero hz₀0 hcos i)
    · intro i _
      exact spiral_chain_step he hz₀0 hcos i
  rcases eq_or_lt_of_le ht.2 with hpt | hpt
  ·
    obtain ⟨τ, hτ⟩ := exists_tangent_eq he hpt.symm
    have hτ1 : ‖τ‖ = 1 := by rw [← norm_tangent he τ, hτ, ht.1]
    set u : ℂ := Complex.I * τ * (‖z₀‖ : ℂ) / z₀ with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, norm_mul, Complex.norm_I, hτ1, Complex.norm_real,
        Real.norm_eq_abs, abs_norm, one_mul, one_mul, div_self hx.ne']
    obtain ⟨c, hc0, hcn, hcmem, hcstep⟩ := spiral_reach u hu1 3 le_rfl
    refine ⟨4, fun k => if k ≤ 3 then c k else t, le_add_left le_rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hc0
    · simp
    · intro i hi
      split_ifs with h
      · exact hcmem i h
      · exact ⟨ht, htp⟩
    · intro i hi
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · rw [ite_eq_left (by omega : i + 1 ≤ 3), ite_eq_left h3.le]
        exact hcstep i h3
      · have hi3 : i = 3 := by omega
        rw [hi3, ite_eq_right (by omega : ¬ (3 + 1 ≤ 3)), ite_eq_left le_rfl, hcn]
        refine mem_descent_of_equator ⟨ht.1, hpt.symm⟩ ?_
        rw [lift, inner_smul_right, inner_add_right, real_inner_comm p t, hpt.symm, ← hτ,
          inner_tangent_tangent he]
        have hw : (τ * conj (z₀ * (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ : ℝ) : ℂ) ^ 3
            * u)).re = 0 := by
          have hz₀' : z₀ * (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ : ℝ) : ℂ) ^ 3 * u
              = (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ ^ 3 * ‖z₀‖ : ℝ) : ℂ)
                * (Complex.I * τ) := by
            rw [hu]
            field_simp
            push_cast
            ring
          simp only [hz₀', map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
            Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
          ring
        rw [hw]
        ring
  ·
    obtain ⟨hvt, htl⟩ := eq_lift_of_northern hp ht.1 hpt
    obtain ⟨ζ, hζ⟩ := exists_tangent_eq he hvt
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      apply htp
      rw [htl, ← hζ]
      simp [tangent, lift, hp]
    have hy : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    have hxy : ‖z₀‖ < ‖ζ‖ := by
      rw [hsl, htl, ← hz₀, ← hζ, latitude_lift_lt_iff hp (inner_pole_tangent he z₀)
        (inner_pole_tangent he ζ), norm_tangent he, norm_tangent he] at hl
      exact hl
    set u : ℂ := ζ * (‖z₀‖ : ℂ) / (z₀ * (‖ζ‖ : ℂ)) with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm, mul_comm ‖z₀‖,
        div_self (mul_ne_zero hy.ne' hx.ne')]
    have hratio : ‖z₀‖ / ‖ζ‖ < 1 := (div_lt_one hy).mpr hxy
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (Real.pi ^ 2 / (2 * (1 - ‖z₀‖ / ‖ζ‖)))
    set n : ℕ := n₀ + 3 with hn
    have hn3 : 3 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
    have hcos := cos_arg_div_pos u hn3
    have hpow : ‖z₀‖ / ‖ζ‖ ≤ Real.cos (Complex.arg u / n) ^ n := by
      refine le_trans ?_ (one_sub_le_cos_arg_div_pow u hn3)
      have h1 : Real.pi ^ 2 / (2 * (1 - ‖z₀‖ / ‖ζ‖)) ≤ n := by
        rw [hn]; push_cast; linarith
      rw [div_le_iff₀ (by linarith)] at h1
      rw [sub_nonneg.mpr hratio.le |> fun _ => le_sub_comm, div_le_iff₀ (by positivity)]
      nlinarith
    set ρ : ℝ := ‖z₀‖ / ‖ζ‖ * ((Real.cos (Complex.arg u / n))⁻¹) ^ n with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; positivity
    have hρ1 : ρ ≤ 1 := by
      rw [hρ, inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hcos n)]
      exact hpow
    have hend : z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u = (ρ : ℂ) * ζ := by
      rw [hρ, hu]
      push_cast
      field_simp [hz₀0, Complex.ofReal_ne_zero.mpr hy.ne']
      <;> ring
    obtain ⟨c, hc0, hcn, hcmem, hcstep⟩ := spiral_reach u hu1 n hn3
    rw [hend] at hcn
    set z' : ℂ := (ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I) with hz'
    have hz'0 : z' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ0.ne') hζ0) ?_
      intro h
      have := congrArg Complex.re h
      simp at this
    obtain ⟨hstep1, hstep2⟩ := descent_step_ray ζ hρ0 hρ1
    have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
    refine ⟨n + 2, fun k => if k ≤ n then c k else if k = n + 1 then lift p (tangent e₁ e₂ z')
      else t, by omega, ?_, ?_, ?_, ?_⟩
    · simp [hc0]
    · simp
    · intro i hi
      split_ifs with h1 h2
      · exact hcmem i h1
      · exact lift_tangent_mem he z' hz'0
      · exact ⟨ht, htp⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with h1 | h1
      · rw [ite_eq_left (by omega : i + 1 ≤ n), ite_eq_left h1.le]
        exact hcstep i h1
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [← h2, ite_eq_right (by omega : ¬ (n + 1 ≤ n)), ite_eq_left rfl, ite_eq_left le_rfl, hcn,
            lift_tangent_mem_descent_iff he (mul_ne_zero hρC hζ0)]
          exact hstep1
        · have h3 : i = n + 1 := by omega
          rw [h3, ite_eq_right (by omega : ¬ (n + 1 + 1 ≤ n)), ite_eq_right (by omega : n + 1 + 1 ≠ n + 1),
            ite_eq_right (by omega : ¬ (n + 1 ≤ n)), ite_eq_left rfl, htl, ← hζ,
            lift_tangent_mem_descent_iff he hz'0]
          exact hstep2
end Gleason

end
