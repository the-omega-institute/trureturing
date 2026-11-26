/- GID: D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D
   generality: G
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/ReggeSchlafli4D
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Euclidean simplex normals and the Schläfli variation of the 4D Regge action. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Cofactor normals and the Schläfli differential identity for Euclidean simplices. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Matrix RealInnerProductSpace Topology
open Filter Matrix

namespace D5.S3.Geometry.DiscreteGravity.ReggeSchlafli4D

/-- The Euclidean norm on coordinate vectors is the ℓ² norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}
abbrev Vertices (d : ℕ) := Fin (d + 1) → Vec d
def edges (v : Vertices d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => v i.succ j - v 0 j
def determinantWeight (v : Vertices d) : ℝ := |(edges v).det|
def normal (v : Vertices d) : Fin (d + 1) → Vec d :=
  let column := fun i : Fin d =>
    (-determinantWeight v) • WithLp.toLp 2 (fun j => (edges v)⁻¹ j i)
  Fin.cases (-∑ i, column i) column

theorem minkowski_closure (v : Vertices d) : ∑ i, normal v i = 0 := by
  rw [Fin.sum_univ_succ]
  exact neg_add_cancel _

private theorem inner_coordinates (x y : Vec d) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
private theorem normal_edge (v : Vertices d) (hv : (edges v).det ≠ 0)
    (i : Fin (d + 1)) (j : Fin d) :
    ⟪normal v i, v j.succ - v 0⟫ =
      determinantWeight v * ((if i = 0 then 1 else 0) - (if i = j.succ then 1 else 0)) := by
  have hcol (l : Fin d) :
      ⟪normal v l.succ, v j.succ - v 0⟫ =
        (if j = l then -determinantWeight v else 0) := by
    have hinv := congr_fun (congr_fun
      (Matrix.mul_nonsing_inv (A := edges v) (isUnit_iff_ne_zero.mpr hv)) j) l
    rw [Matrix.mul_apply, Matrix.one_apply] at hinv
    rw [show normal v l.succ =
        (-determinantWeight v) • WithLp.toLp 2 (fun k => (edges v)⁻¹ k l) by rfl,
      real_inner_smul_left, inner_coordinates]
    simp_rw [show ∀ k : Fin d, (WithLp.toLp 2 (fun k => (edges v)⁻¹ k l) : Vec d) k *
        (v j.succ - v 0) k = edges v j k * (edges v)⁻¹ k l by
      intro k
      exact mul_comm _ _]
    change -determinantWeight v * (edges v j ⬝ᵥ fun k => (edges v)⁻¹ k l) = _
    rw [dotProduct, hinv]
    split <;> ring
  refine Fin.cases ?_ (fun l => ?_) i
  · change ⟪-∑ l : Fin d, normal v l.succ, v j.succ - v 0⟫ = _
    simp [inner_neg_left, sum_inner, hcol, Ne.symm (Fin.succ_ne_zero j)]
  · rw [hcol]
    by_cases h : j = l
    · subst l
      simp
    · simp [h, Ne.symm h]
private theorem normal_vertex_difference (v : Vertices d) (hv : (edges v).det ≠ 0)
    (k i j : Fin (d + 1)) :
    ⟪normal v k, v j - v i⟫ =
      determinantWeight v * ((if k = i then 1 else 0) - (if k = j then 1 else 0)) := by
  have aux (l : Fin (d + 1)) :
      ⟪normal v k, v l - v 0⟫ =
        determinantWeight v * ((if k = 0 then 1 else 0) - (if k = l then 1 else 0)) := by
    exact Fin.cases (by simp) (normal_edge v hv k) l
  rw [show v j - v i = (v j - v 0) - (v i - v 0) by abel, inner_sub_right, aux j, aux i]
  ring

theorem outward_normal_orthogonality (v : Vertices d) (hv : (edges v).det ≠ 0)
    (k : Fin (d + 1)) :
    (∀ i j, i ≠ k → j ≠ k → ⟪normal v k, v j - v i⟫ = 0) ∧
    (∀ j, j ≠ k → ⟪normal v k, v k - v j⟫ = -determinantWeight v ∧
      ⟪normal v k, v k - v j⟫ < 0) := by
  have hpos : 0 < determinantWeight v := abs_pos.mpr hv
  constructor
  · intro i j hi hj
    simp [normal_vertex_difference v hv, Ne.symm hi, Ne.symm hj]
  · intro j hj
    simp [normal_vertex_difference v hv, Ne.symm hj, hpos]
def unitNormal (v : Vertices d) (i : Fin (d + 1)) : Vec d :=
  ‖normal v i‖⁻¹ • normal v i
def dihedral (v : Vertices d) (i j : Fin (d + 1)) : ℝ :=
  Real.arccos (-⟪unitNormal v i, unitNormal v j⟫)

private def affineMatrix (v : Vertices d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i => Fin.cases 1 (fun j => v i j)
private theorem affine_det (v : Vertices d) : (affineMatrix v).det = (edges v).det := by
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun i j => if i = 0 then affineMatrix v i j else affineMatrix v i j - affineMatrix v 0 j
  have hm : M.det = (affineMatrix v).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then 0 else -1) 0
    · simp
    · intro i j
      by_cases hi : i = 0 <;> simp [M, hi, sub_eq_add_neg]
  rw [← hm, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [M, affineMatrix]
  congr 1
private theorem determinantWeight_relabel (v : Vertices d) (e : Equiv.Perm (Fin (d + 1))) :
    determinantWeight (v ∘ e) = determinantWeight v := by
  unfold determinantWeight
  rw [← affine_det, ← affine_det]
  exact Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl _) (affineMatrix v)

private theorem normal_relabel (v : Vertices d) (hv : (edges v).det ≠ 0)
    (e : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) :
    normal (v ∘ e) i = normal v (e i) := by
  have hw : (edges (v ∘ e)).det ≠ 0 :=
    by
      have hh : 0 < determinantWeight v := abs_pos.mpr hv
      apply abs_pos.mp
      change 0 < determinantWeight (v ∘ e)
      rwa [determinantWeight_relabel]
  let x := normal (v ∘ e) i - normal v (e i)
  have hz : (edges (v ∘ e)).mulVec (WithLp.ofLp x) = 0 := by
    ext j
    change (∑ k, edges (v ∘ e) j k * x k) = 0
    calc
      _ = ⟪x, (v ∘ e) j.succ - (v ∘ e) 0⟫ := by
        rw [inner_coordinates]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = 0 := by
        have h₁ := normal_vertex_difference (v ∘ e) hw i 0 j.succ
        have h₂ := normal_vertex_difference v hv (e i) (e 0) (e j.succ)
        simp only [Function.comp_apply, determinantWeight_relabel, e.apply_eq_iff_eq] at h₁ h₂
        exact sub_eq_zero.mpr (h₁.trans h₂.symm) |> fun h => by simpa [x, inner_sub_left] using h
  let : Invertible (edges (v ∘ e)) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hw)
  have h := (Matrix.mulVec_injective_of_invertible (edges (v ∘ e)))
    (hz.trans (Matrix.mulVec_zero _).symm)
  exact sub_eq_zero.mp (WithLp.ofLp_injective 2 h)
private theorem complementary_gram_minor {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.PosDef) :
    M.det * (M⁻¹.submatrix Sum.inr Sum.inr).det = (M.submatrix Sum.inl Sum.inl).det := by
  let A := M.submatrix Sum.inl Sum.inl
  let B := M.submatrix Sum.inl Sum.inr
  let C := M.submatrix Sum.inr Sum.inl
  let D := M.submatrix Sum.inr Sum.inr
  have hA : 0 < A.det := (hM.submatrix Sum.inl_injective).det_pos
  have hblock : fromBlocks A B C D = M := by
    ext (i | i) (j | j) <;> rfl
  let : Invertible A := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA.ne')
  let : Invertible (fromBlocks A B C D) := Matrix.invertibleOfIsUnitDet _
    (isUnit_iff_ne_zero.mpr (hblock ▸ hM.det_pos.ne'))
  let S := D - C * ⅟A * B
  let : Invertible S := Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  have hsub : M⁻¹.submatrix Sum.inr Sum.inr = ⅟S := by
    rw [← hblock, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
    rfl
  have hdet : M.det = A.det * S.det := hblock ▸ Matrix.det_fromBlocks₁₁ A B C D
  have hcancel : S⁻¹.det * S.det = 1 :=
    Matrix.det_nonsing_inv_mul_det S (Matrix.isUnit_det_of_invertible (A := S))
  rw [hdet, hsub, mul_assoc, Matrix.invOf_eq_nonsing_inv, mul_comm S.det, hcancel, mul_one]

private def lastPair {n : ℕ} (k : Fin 2) : Fin (n + 2 + 1) :=
  (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin 2)).succ
private theorem exists_hingeChart {n : ℕ} (i j : Fin (n + 2 + 1)) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin (n + 2 + 1)), e (lastPair 0) = i ∧ e (lastPair 1) = j := by
  have hf : Function.Injective (lastPair (n := n)) := fun _ _ h =>
    Sum.inr.inj (finSumFinEquiv.injective (Fin.succ_inj.mp h))
  have hg : Function.Injective (fun k : Fin 2 => if k = 0 then i else j) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  exact ⟨e, by simpa using he 0, by simpa using he 1⟩

private def hingeChart {n : ℕ} (i j : Fin (n + 2 + 1)) : Equiv.Perm (Fin (n + 2 + 1)) :=
  if h : i = j then Equiv.refl _ else Classical.choose (exists_hingeChart i j h)
private theorem hingeChart_spec {n : ℕ} {i j : Fin (n + 2 + 1)} (hij : i ≠ j) :
    hingeChart i j (lastPair 0) = i ∧ hingeChart i j (lastPair 1) = j := by
  simp only [hingeChart, dite_eq_right hij]
  exact Classical.choose_spec (exists_hingeChart i j hij)

private def edgeGram (v : Vertices d) : Matrix (Fin d) (Fin d) ℝ :=
  edges v * (edges v)ᵀ
private theorem edgeGram_posDef (v : Vertices d) (hv : (edges v).det ≠ 0) :
    (edgeGram v).PosDef := by
  have hs : (edgeGram v).PosSemidef := by
    simpa [edgeGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (edges v)
  exact hs.posDef_iff_det_ne_zero.mpr (by simpa [edgeGram, Matrix.det_mul] using mul_ne_zero hv hv)

/-- Gram determinant of the edges from the first vertex of the hinge chart to its remaining
vertices. The other two vertices of the chart are the vertices opposite the hinge. -/
def hingeGramDet {n : ℕ} (v : Vertices (n + 2)) (i j : Fin (n + 2 + 1)) : ℝ :=
  let X := (edges (v ∘ hingeChart i j)).submatrix
    (fun k : Fin n => finSumFinEquiv (Sum.inl k : Fin n ⊕ Fin 2)) id
  (X * Xᵀ).det
def hingeArea {n : ℕ} (v : Vertices (n + 2)) (i j : Fin (n + 2 + 1)) : ℝ :=
  Real.sqrt (hingeGramDet v i j) / (n.factorial : ℝ)
def facetVolume (v : Vertices d) (i : Fin (d + 1)) : ℝ :=
  ‖normal v i‖ / ((d - 1).factorial : ℝ)
def simplexVolume (v : Vertices d) : ℝ :=
  determinantWeight v / (d.factorial : ℝ)

private theorem normal_gram_entry (v : Vertices d) (a b : Fin d) :
    ⟪normal v a.succ, normal v b.succ⟫ =
      determinantWeight v ^ 2 * (edgeGram v)⁻¹ a b := by
  rw [edgeGram, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, Matrix.mul_apply]
  change ⟪(-determinantWeight v) • WithLp.toLp 2 (fun k => (edges v)⁻¹ k a),
    (-determinantWeight v) • WithLp.toLp 2 (fun k => (edges v)⁻¹ k b)⟫ = _
  rw [real_inner_smul_left, real_inner_smul_right, inner_coordinates]
  change (-determinantWeight v) * ((-determinantWeight v) *
    (∑ k, (edges v)⁻¹ k a * (edges v)⁻¹ k b)) =
    determinantWeight v ^ 2 * (∑ k, (edges v)⁻¹ k a * (edges v)⁻¹ k b)
  ring

private theorem hinge_gram_square {n : ℕ} (v : Vertices (n + 2)) (hv : (edges v).det ≠ 0)
    {i j : Fin (n + 2 + 1)} (hij : i ≠ j) :
    0 < hingeGramDet v i j ∧
    ‖normal v i‖ ^ 2 * ‖normal v j‖ ^ 2 - ⟪normal v i, normal v j⟫ ^ 2 =
      determinantWeight v ^ 2 * hingeGramDet v i j := by
  let e := hingeChart i j
  let w := v ∘ e
  let f : Fin n ⊕ Fin 2 ≃ Fin (n + 2) := finSumFinEquiv
  let M := (edgeGram w).submatrix f f
  have hwgt : determinantWeight w = determinantWeight v := determinantWeight_relabel v e
  have hw : (edges w).det ≠ 0 := by
    have hh : 0 < determinantWeight v := abs_pos.mpr hv
    apply abs_pos.mp
    change 0 < determinantWeight w
    rwa [hwgt]
  have hp := (edgeGram_posDef w hw).submatrix f.injective
  have hleft : (M.submatrix Sum.inl Sum.inl).det = hingeGramDet v i j := rfl
  have hdet : M.det = determinantWeight v ^ 2 := by
    rw [Matrix.det_submatrix_equiv_self, edgeGram, Matrix.det_mul, Matrix.det_transpose,
      ← hwgt, determinantWeight, sq_abs, pow_two]
  have hM := complementary_gram_minor M hp
  rw [hdet, hleft, Matrix.det_fin_two] at hM
  have hentry (a b : Fin 2) :
      ⟪normal v (e (lastPair a)), normal v (e (lastPair b))⟫ =
        determinantWeight v ^ 2 * (M⁻¹.submatrix Sum.inr Sum.inr) a b := by
    rw [← normal_relabel v hv e, ← normal_relabel v hv e]
    have h := normal_gram_entry w (f (.inr a)) (f (.inr b))
    rw [hwgt] at h
    simpa only [M, Matrix.inv_submatrix_equiv, Equiv.symm_symm, Matrix.submatrix_apply,
      w, f, lastPair] using h
  have hspec := hingeChart_spec hij
  have ha := hentry 0 0
  have hb := hentry 1 1
  have hc := hentry 0 1
  have hd := hentry 1 0
  change e (lastPair 0) = i ∧ e (lastPair 1) = j at hspec
  rw [hspec.1] at ha hc hd
  rw [hspec.2] at hb hc hd
  rw [real_inner_self_eq_norm_sq] at ha hb
  rw [real_inner_comm (normal v i) (normal v j)] at hd
  refine ⟨hleft ▸ (hp.submatrix Sum.inl_injective).det_pos, ?_⟩
  calc
    _ = (determinantWeight v ^ 2) * (determinantWeight v ^ 2 *
      (M⁻¹.submatrix Sum.inr Sum.inr 0 0 * M⁻¹.submatrix Sum.inr Sum.inr 1 1 -
        M⁻¹.submatrix Sum.inr Sum.inr 0 1 * M⁻¹.submatrix Sum.inr Sum.inr 1 0)) := by
          have he := congrArg₂ (· - ·) (congrArg₂ (· * ·) ha hb)
            (congrArg₂ (· * ·) hc hd)
          rw [pow_two (⟪normal v i, normal v j⟫), he]
          ring
    _ = _ := by rw [hM]
private theorem normal_ne_zero [Nontrivial (Fin (d + 1))] (v : Vertices d)
    (hv : (edges v).det ≠ 0) (i : Fin (d + 1)) : normal v i ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  have h := ((outward_normal_orthogonality v hv i).2 j hj).2
  intro hz
  simp [hz] at h
private theorem unitNormal_norm [Nontrivial (Fin (d + 1))] (v : Vertices d)
    (hv : (edges v).det ≠ 0) (i : Fin (d + 1)) : ‖unitNormal v i‖ = 1 := by
  have hn := norm_pos_iff.mpr (normal_ne_zero v hv i)
  rw [unitNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

theorem gram_normal_hinge_sine_identity {n : ℕ} (v : Vertices (n + 2))
    (hv : (edges v).det ≠ 0) {i j : Fin (n + 2 + 1)} (hij : i ≠ j) :
    |⟪unitNormal v i, unitNormal v j⟫| < 1 ∧
    ‖normal v i‖ * ‖normal v j‖ * Real.sin (dihedral v i j) =
      determinantWeight v * Real.sqrt (hingeGramDet v i j) := by
  obtain ⟨hh, hgram⟩ := hinge_gram_square v hv hij
  have hw : 0 < determinantWeight v := abs_pos.mpr hv
  let p := ‖normal v i‖ * ‖normal v j‖
  have hp : 0 < p := mul_pos (norm_pos_iff.mpr (normal_ne_zero v hv i))
    (norm_pos_iff.mpr (normal_ne_zero v hv j))
  let x := ⟪normal v i, normal v j⟫
  have hcos : ⟪unitNormal v i, unitNormal v j⟫ = x / p := by
    rw [unitNormal, unitNormal, real_inner_smul_left, real_inner_smul_right]
    simp [x, p, div_eq_mul_inv, _root_.mul_inv_rev, mul_comm, mul_left_comm]
  have hgram' : p ^ 2 - x ^ 2 = determinantWeight v ^ 2 * hingeGramDet v i j := by
    simpa [p, x, mul_pow] using hgram
  have hx : |x| < p := by
    have hpos := mul_pos (sq_pos_of_pos hw) hh
    nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) hp.le]
  refine ⟨by rwa [hcos, abs_div, abs_of_pos hp, div_lt_one hp], ?_⟩
  rw [dihedral, hcos, Real.sin_arccos, neg_sq]
  change p * Real.sqrt (1 - (x / p) ^ 2) = _
  have hrad : p ^ 2 * (1 - (x / p) ^ 2) = determinantWeight v ^ 2 * hingeGramDet v i j := by
    calc
      _ = p ^ 2 - x ^ 2 := by field_simp
      _ = _ := hgram'
  calc
    _ = Real.sqrt (p ^ 2 * (1 - (x / p) ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp.le]
    _ = _ := by rw [hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw.le]

theorem facet_volume_hinge_sine {n : ℕ} (v : Vertices (n + 2))
    (hv : (edges v).det ≠ 0) {i j : Fin (n + 2 + 1)} (hij : i ≠ j) :
    facetVolume v i * facetVolume v j * Real.sin (dihedral v i j) =
      ((n : ℝ) + 2) / ((n : ℝ) + 1) * simplexVolume v * hingeArea v i j := by
  have h := (gram_normal_hinge_sine_identity v hv hij).2
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [facetVolume, simplexVolume, hingeArea, show n + 2 - 1 = n + 1 by omega]
  rw [div_mul_div_comm, div_mul_eq_mul_div, h, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  field_simp [hfac, h₁, h₂, show (n : ℝ) + 1 + 1 ≠ 0 by positivity]
  ring

section DifferentialClosure

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem sum_upper_triangle (f : ι → ι → ℝ) (h : ∀ i, f i i = 0) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (f i j + f j i) =
      ∑ i, ∑ j, f i j := by
  classical
  rw [show (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (f i j + f j i)) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if i < j then f j i else 0 by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    congr 1
    ext i
    congr 1
    ext j
    split <;> simp_all]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j i else 0)]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, not_lt_of_ge hij.le]
  · simp [h]
  · simp [hji, not_lt_of_ge hji.le]

theorem normal_closure_schlafli_core (u : ι → ℝ → E) (du : ι → E) (V : ι → ℝ)
    (t : ℝ) (hu : ∀ i, HasDerivAt (u i) (du i) t)
    (hunit : ∀ i, ∀ᶠ s in 𝓝 t, ‖u i s‖ = 1)
    (hstrict : ∀ i j, i ≠ j → |⟪u i t, u j t⟫| < 1)
    (hclosure : ∑ i, V i • u i t = 0) :
    let θ := fun i j s => Real.arccos (-⟪u i s, u j s⟫)
    (∑ i, ∑ j, V i * V j * ⟪u i t, du j⟫) = 0 ∧
    (∀ i j, i ≠ j → HasDerivAt (θ i j)
      ((⟪u i t, du j⟫ + ⟪u j t, du i⟫) / Real.sin (θ i j t)) t) ∧
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      V i * V j * Real.sin (θ i j t) * deriv (θ i j) t) = 0 := by
  dsimp only
  let f := fun i j => V i * V j * ⟪u i t, du j⟫
  have hf : ∑ i, ∑ j, f i j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h := congrArg (fun x => ⟪x, du j⟫) hclosure
    simp only [sum_inner, real_inner_smul_left, inner_zero_left] at h
    simpa [f, Finset.mul_sum, mul_left_comm, mul_assoc] using congrArg (V j * ·) h
  have hdiag (i : ι) : f i i = 0 := by
    have heq : (fun s => ‖u i s‖ ^ 2) =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) :=
      (hunit i).mono fun s hs => by simp [hs]
    have hz := ((hu i).norm_sq.congr_of_eventuallyEq heq.symm).unique
      (hasDerivAt_const t (1 : ℝ))
    simp [f, show ⟪u i t, du i⟫ = 0 by simpa [real_inner_comm] using hz]
  have hsine (i j : ι) (hij : i ≠ j) :
      0 < Real.sin (Real.arccos (-⟪u i t, u j t⟫)) := by
    rw [Real.sin_arccos, neg_sq]
    exact Real.sqrt_pos.2 (by nlinarith [(abs_lt.mp (hstrict i j hij)).1,
      (abs_lt.mp (hstrict i j hij)).2, sq_abs ⟪u i t, u j t⟫])
  have hderiv (i j : ι) (hij : i ≠ j) :
      HasDerivAt (fun s => Real.arccos (-⟪u i s, u j s⟫))
        ((⟪u i t, du j⟫ + ⟪u j t, du i⟫) /
          Real.sin (Real.arccos (-⟪u i t, u j t⟫))) t := by
    have hb := abs_lt.mp (hstrict i j hij)
    have h := (Real.hasDerivAt_arccos (x := -⟪u i t, u j t⟫)
      (by linarith) (by linarith)).comp t (((hu i).inner ℝ (hu j)).neg)
    change HasDerivAt (fun s => Real.arccos (-⟪u i s, u j s⟫)) _ t at h
    rw [real_inner_comm (u j t) (du i)] at h
    convert h using 1
    simp only [Real.sin_arccos, div_eq_mul_inv, neg_sq]
    ring
  refine ⟨hf, hderiv, ?_⟩
  rw [← hf, ← sum_upper_triangle f hdiag]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij := (Finset.mem_filter.mp hj).2.ne
  rw [(hderiv i j hij).deriv]
  field_simp [(hsine i j hij).ne']
  simp only [f]
  ring

end DifferentialClosure

section SimplexVariation

private theorem differentiableAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℝ) (t : ℝ)
    (hF : ∀ i j, DifferentiableAt ℝ (fun s => F s i j) t) :
    DifferentiableAt ℝ (fun s => (F s).det) t := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  exact (DifferentiableAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => hF (σ i) i)).const_mul _

private theorem differentiableAt_edges (v : ℝ → Vertices d) (t : ℝ)
    (hd : ∀ i, DifferentiableAt ℝ (fun s => v s i) t) (a b : Fin d) :
    DifferentiableAt ℝ (fun s => edges (v s) a b) t :=
  ((PiLp.proj 2 (fun _ : Fin d => ℝ) b).differentiableAt.comp t (hd a.succ)).sub
    ((PiLp.proj 2 (fun _ : Fin d => ℝ) b).differentiableAt.comp t (hd 0))

private theorem differentiableAt_unitNormal [Nontrivial (Fin (d + 1))]
    (v : ℝ → Vertices d) (t : ℝ) (hv : (edges (v t)).det ≠ 0)
    (hd : ∀ i : Fin (d + 1), DifferentiableAt ℝ (fun s => v s i) t)
    (i : Fin (d + 1)) : DifferentiableAt ℝ (fun s => unitNormal (v s) i) t := by
  have he := differentiableAt_edges v t hd
  have hdet : DifferentiableAt ℝ (fun s => (edges (v s)).det) t :=
    differentiableAt_matrix_det (fun s => edges (v s)) t he
  have hD : DifferentiableAt ℝ (fun s => determinantWeight (v s)) t := hdet.abs hv
  have hInv (a b : Fin d) : DifferentiableAt ℝ (fun s => (edges (v s))⁻¹ a b) t := by
    have ha : DifferentiableAt ℝ (fun s => (edges (v s)).adjugate a b) t := by
      simp only [Matrix.adjugate_apply]
      apply differentiableAt_matrix_det
      intro j k
      by_cases hj : j = b
      · simp [hj, differentiableAt_const]
      · simpa [Matrix.updateRow_ne hj] using he j k
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact (hdet.inv hv).fun_mul ha
  have hn (j : Fin d) : DifferentiableAt ℝ (fun s => normal (v s) j.succ) t := by
    have h : DifferentiableAt ℝ (fun s => fun k => (edges (v s))⁻¹ k j) t :=
      differentiableAt_pi.mpr fun k => hInv k j
    exact hD.neg.smul
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.differentiableAt.comp t h)
  have hnormal : DifferentiableAt ℝ (fun s => normal (v s) i) t := by
    refine Fin.cases ?_ hn i
    change DifferentiableAt ℝ (fun s => -(∑ j : Fin d, normal (v s) j.succ)) t
    exact (DifferentiableAt.fun_sum (u := Finset.univ) fun j _ => hn j).fun_neg
  exact ((DifferentiableAt.norm ℝ hnormal (normal_ne_zero (v t) hv i)).inv
    (norm_ne_zero_iff.mpr (normal_ne_zero (v t) hv i))).smul hnormal

theorem euclidean_simplex_schlafli {n : ℕ} (v : ℝ → Vertices (n + 2)) (t : ℝ)
    (hv : (edges (v t)).det ≠ 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun s => v s i) t) :
    (∀ i j, i ≠ j → HasDerivAt (fun s => dihedral (v s) i j)
      (deriv (fun s => dihedral (v s) i j) t) t) ∧
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      hingeArea (v t) i j * deriv (fun s => dihedral (v s) i j) t) = 0 := by
  let u := fun i s => unitNormal (v s) i
  let V := fun i => ‖normal (v t) i‖
  have hdet : DifferentiableAt ℝ (fun s => (edges (v s)).det) t :=
    differentiableAt_matrix_det (fun s => edges (v s)) t (differentiableAt_edges v t hd)
  have hx : ∀ᶠ s in 𝓝 t, (edges (v s)).det ≠ 0 := hdet.continuousAt.eventually_ne hv
  have hu i : HasDerivAt (u i) (deriv (u i) t) t :=
    (differentiableAt_unitNormal v t hv hd i).hasDerivAt
  have hunit i : ∀ᶠ s in 𝓝 t, ‖u i s‖ = 1 :=
    hx.mono fun s hs => unitNormal_norm (v s) hs i
  have hstrict i j (hij : i ≠ j) : |⟪u i t, u j t⟫| < 1 :=
    (gram_normal_hinge_sine_identity (v t) hv hij).1
  have hclose : ∑ i, V i • u i t = 0 := by
    simp only [u, V, unitNormal, smul_smul, mul_inv_cancel₀
      (norm_ne_zero_iff.mpr (normal_ne_zero (v t) hv _)), one_smul]
    exact minkowski_closure (v t)
  obtain ⟨_, hangle, hsum⟩ := normal_closure_schlafli_core u _ V t hu hunit hstrict hclose
  refine ⟨fun i j hij => (hangle i j hij).differentiableAt.hasDerivAt, ?_⟩
  have hscale : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ (mul_ne_zero (abs_ne_zero.mpr hv) hscale)
  simp only [mul_zero, Finset.mul_sum]
  convert hsum using 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hs := (gram_normal_hinge_sine_identity (v t) hv (Finset.mem_filter.mp hj).2.ne).2
  change _ = (‖normal (v t) i‖ * ‖normal (v t) j‖ * Real.sin (dihedral (v t) i j)) * _
  rw [hs, hingeArea]
  field_simp
  change _ = Real.sqrt (hingeGramDet (v t) i j) * |(edges (v t)).det| *
    deriv (fun s => dihedral (v s) i j) t
  ring

/-- In four dimensions the codimension-two area is the triangle's Gram factor divided by two. -/
theorem regge_schlafli_4d (v : ℝ → Vertices 4) (t : ℝ)
    (hv : (edges (v t)).det ≠ 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun s => v s i) t) :
    (∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (Real.sqrt (hingeGramDet (n := 2) (v t) i j) / 2) *
        deriv (fun s => dihedral (v s) i j) t) = 0 := by
  simpa [hingeArea, Nat.factorial] using (euclidean_simplex_schlafli v t hv hd).2

end SimplexVariation

/-- Incidence data for a finite four-dimensional Regge action. -/
structure ReggeComplex4D (H Cell : Type*) where
  incident : H → Cell → Prop
  decidableIncident : DecidableRel incident

section ReggeAction

variable {H Cell : Type*} [Fintype H] [Fintype Cell]
  (C : ReggeComplex4D H Cell)

namespace ReggeComplex4D
def incSimplices (h : H) : Finset Cell :=
  @Finset.filter _ (C.incident h) (C.decidableIncident h) Finset.univ
def incHinges (σ : Cell) : Finset H :=
  @Finset.filter _ (fun h => C.incident h σ) (fun h => C.decidableIncident h σ) Finset.univ
def deficit (θ : H → Cell → ℝ → ℝ) (h : H) (s : ℝ) : ℝ :=
  2 * Real.pi - ∑ σ ∈ C.incSimplices h, θ h σ s
def reggeAction (A : H → ℝ → ℝ) (θ : H → Cell → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ h, A h s * C.deficit θ h s
def reggeActionLambda (A : H → ℝ → ℝ) (θ : H → Cell → ℝ → ℝ)
    (Vol : Cell → ℝ → ℝ) (Λ s : ℝ) : ℝ :=
  C.reggeAction A θ s - Λ * ∑ σ, Vol σ s

end ReggeComplex4D

theorem regge_action_palatini_variation (A : H → ℝ → ℝ) (θ : H → Cell → ℝ → ℝ)
    (dA : H → ℝ) (dθ : H → Cell → ℝ) (t : ℝ)
    (hA : ∀ h, HasDerivAt (A h) (dA h) t)
    (hθ : ∀ h σ, σ ∈ C.incSimplices h → HasDerivAt (θ h σ) (dθ h σ) t)
    (hSchlafli : ∀ σ, ∑ h ∈ C.incHinges σ, A h t * dθ h σ = 0) :
    HasDerivAt (C.reggeAction A θ) (∑ h, dA h * C.deficit θ h t) t := by
  classical
  have hdef (h : H) : HasDerivAt (C.deficit θ h) (-(∑ σ ∈ C.incSimplices h, dθ h σ)) t :=
    (HasDerivAt.fun_sum (fun σ hσ => hθ h σ hσ)).const_sub _
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun h _ => (hA h).mul (hdef h))
  have hcancel : ∑ h, A h t * (∑ σ ∈ C.incSimplices h, dθ h σ) = 0 := by
    simp_rw [Finset.mul_sum, ReggeComplex4D.incSimplices, Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun σ _ => by
      simpa [ReggeComplex4D.incHinges, Finset.sum_filter] using hSchlafli σ
  change HasDerivAt (C.reggeAction A θ) _ t at h
  have hz : (∑ i, A i t * -(∑ σ ∈ C.incSimplices i, dθ i σ)) = 0 := by
    simpa only [mul_neg, Finset.sum_neg_distrib, neg_zero] using congrArg Neg.neg hcancel
  rwa [Finset.sum_add_distrib, hz, add_zero] at h

theorem regge_action_lambda_variation (A : H → ℝ → ℝ) (θ : H → Cell → ℝ → ℝ)
    (Vol : Cell → ℝ → ℝ) (dA : H → ℝ) (dθ : H → Cell → ℝ) (dVol : Cell → ℝ) (Λ t : ℝ)
    (hA : ∀ h, HasDerivAt (A h) (dA h) t)
    (hθ : ∀ h σ, σ ∈ C.incSimplices h → HasDerivAt (θ h σ) (dθ h σ) t)
    (hSchlafli : ∀ σ, ∑ h ∈ C.incHinges σ, A h t * dθ h σ = 0)
    (hVol : ∀ σ, HasDerivAt (Vol σ) (dVol σ) t) :
    HasDerivAt (C.reggeActionLambda A θ Vol Λ)
      ((∑ h, dA h * C.deficit θ h t) - Λ * ∑ σ, dVol σ) t :=
  (regge_action_palatini_variation C A θ dA dθ t hA hθ hSchlafli).sub
    ((HasDerivAt.fun_sum fun σ _ => hVol σ).const_mul Λ)

theorem flat_regge_stationarity (A : H → ℝ → ℝ) (θ : H → Cell → ℝ → ℝ)
    (dA : H → ℝ) (dθ : H → Cell → ℝ) (t : ℝ)
    (hA : ∀ h, HasDerivAt (A h) (dA h) t)
    (hθ : ∀ h σ, σ ∈ C.incSimplices h → HasDerivAt (θ h σ) (dθ h σ) t)
    (hSchlafli : ∀ σ, ∑ h ∈ C.incHinges σ, A h t * dθ h σ = 0)
    (hflat : ∀ h, C.deficit θ h t = 0) :
    HasDerivAt (C.reggeAction A θ) 0 t := by
  simpa [hflat] using regge_action_palatini_variation C A θ dA dθ t hA hθ hSchlafli

end ReggeAction

section Holonomy

open scoped Matrix.Norms.Operator
abbrev RotationMatrix := Matrix (Fin 4) (Fin 4) ℝ
def edgeHolonomy {H : Type*} (L : List H) (ε : H → ℝ) (B : H → RotationMatrix)
    (s : ℝ) : RotationMatrix :=
  (L.map fun h => NormedSpace.exp (s • (ε h • B h))).prod

theorem discrete_bianchi_edge_holonomy {H : Type*} (L : List H) (ε : H → ℝ)
    (B : H → RotationMatrix) :
    HasDerivAt (edgeHolonomy L ε B) (L.map fun h => ε h • B h).sum 0 ∧
      (HasDerivAt (edgeHolonomy L ε B) 0 0 ↔ (L.map fun h => ε h • B h).sum = 0) := by
  have hzero (T : List H) : edgeHolonomy T ε B 0 = 1 := by
    induction T with
    | nil => rfl
    | cons h T ih =>
      change NormedSpace.exp ((0 : ℝ) • (ε h • B h)) * edgeHolonomy T ε B 0 = 1
      simp [ih]
  have hprod : HasDerivAt (edgeHolonomy L ε B) (L.map fun h => ε h • B h).sum 0 := by
    induction L with
    | nil => exact hasDerivAt_const 0 1
    | cons h T ih =>
      have hs := (hasDerivAt_id (0 : ℝ)).smul_const (ε h • B h)
      have hexp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (ε h • B h))) (ε h • B h) 0 := by
        have hd := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := RotationMatrix)
        rw [show (0 : RotationMatrix) = (0 : ℝ) • (ε h • B h) by simp] at hd
        convert hd.comp_hasDerivAt (0 : ℝ) hs using 1
        all_goals
          first | rfl | (rw [one_apply_eq_self]; simp only [one_smul])
      have hmul := hexp.mul ih
      rw [hzero T, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hmul
      exact hmul
  exact ⟨hprod, fun hz => hprod.unique hz, fun hz => hz ▸ hprod⟩

end Holonomy

section SphericalTriangle

private def sphericalDot (t : ℝ) : ℝ := Real.cos t / (1 - Real.cos t)

/-- Three points with the same pairwise dot product on the unit sphere. -/
def sphericalVertices (t : ℝ) (i : Fin 3) : Vec 3 :=
  let r := sphericalDot t
  let a := Real.sqrt (1 - r)
  let b := (Real.sqrt (1 + 2 * r) - a) / 3
  WithLp.toLp 2 (fun k => (if i = k then a else 0) + b)

/-- The angle between the tangent directions of two great-circle arcs at vertex i. -/
def sphericalAngle (t : ℝ) (i j k : Fin 3) : ℝ :=
  let p := sphericalVertices t
  let x := p j - ⟪p i, p j⟫ • p i
  let y := p k - ⟪p i, p k⟫ • p i
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

/-- Girard's area formula on the unit sphere for the equal-angle triangle. -/
def sphericalArea (t : ℝ) : ℝ := 3 * t - Real.pi

private theorem spherical_gram (t : ℝ) (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi) :
    -1 / 2 < sphericalDot t ∧ sphericalDot t < 1 ∧
    ∀ i j, ⟪sphericalVertices t i, sphericalVertices t j⟫ =
      if i = j then 1 else sphericalDot t := by
  have hc : Real.cos t < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩ ht.1
  have hcos : -1 < Real.cos t := by
    rw [← Real.cos_pi]
    exact Real.strictAntiOn_cos ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ ht.2
  have hden : 0 < 1 - Real.cos t := by linarith
  have hl : -1 / 2 < sphericalDot t := by
    unfold sphericalDot
    rw [lt_div_iff₀ hden]
    linarith
  have hr : sphericalDot t < 1 := by
    unfold sphericalDot
    rw [div_lt_iff₀ hden]
    linarith
  let r := sphericalDot t
  let a := Real.sqrt (1 - r)
  let b := (Real.sqrt (1 + 2 * r) - a) / 3
  have ha : a ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have hb : 2 * a * b + 3 * b ^ 2 = r := by
    dsimp [b]
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 2 * r by linarith)]
  refine ⟨hl, hr, fun i j => ?_⟩
  rw [inner_coordinates]
  change (∑ k : Fin 3, ((if i = k then a else 0) + b) *
    ((if j = k then a else 0) + b)) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three] <;> nlinarith
private theorem spherical_angle_eq (t : ℝ) (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sphericalAngle t i j k = t := by
  obtain ⟨hl, hr, hg⟩ := spherical_gram t ht
  let p := sphericalVertices t
  let r := sphericalDot t
  have hdiag : ⟪p i, p i⟫ = 1 := by simpa using hg i i
  have hpj : ⟪p j, p j⟫ = 1 := by simpa using hg j j
  have hpk : ⟪p k, p k⟫ = 1 := by simpa using hg k k
  have hj : ⟪p i, p j⟫ = r := by simpa [hij] using hg i j
  have hk : ⟪p i, p k⟫ = r := by simpa [hik] using hg i k
  have hjk' : ⟪p j, p k⟫ = r := by simpa [hjk] using hg j k
  have hji : ⟪p j, p i⟫ = r := (real_inner_comm _ _).trans hj
  have hki : ⟪p k, p i⟫ = r := (real_inner_comm _ _).trans hk
  let x := p j - r • p i
  let y := p k - r • p i
  have hnormx : ‖x‖ ^ 2 = 1 - r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [x, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hj, hji, hpj]
    ring
  have hnormy : ‖y‖ ^ 2 = 1 - r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [y, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hk, hki, hpk]
    ring
  have hp : 0 < 1 - r ^ 2 := by unfold r; nlinarith
  have hp' : ‖x‖ = ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hxy : ⟪x, y⟫ = r - r ^ 2 := by
    simp only [x, y, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hk, hji, hjk']
    ring
  unfold sphericalAngle
  dsimp only
  change Real.arccos (⟪p j - ⟪p i, p j⟫ • p i, p k - ⟪p i, p k⟫ • p i⟫ /
    (‖p j - ⟪p i, p j⟫ • p i‖ * ‖p k - ⟪p i, p k⟫ • p i‖)) = t
  rw [hj, hk]
  change Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖)) = t
  rw [← hp', ← pow_two, hnormx, hxy]
  have hr' : r = Real.cos t * (1 + r) := by
    dsimp [r, sphericalDot]
    have hc : Real.cos t < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩ (by linarith [ht.1, Real.pi_pos])
    field_simp [hc.ne']
    ring
  have hfrac : (r - r ^ 2) / (1 - r ^ 2) = Real.cos t := by
    apply (div_eq_iff hp.ne').mpr
    linear_combination (1 - r) * hr'
  rw [hfrac, Real.arccos_cos (by linarith [ht.1, Real.pi_pos]) ht.2.le]

theorem spherical_triangle_schlafli_counterexample (t : ℝ)
    (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi) :
    (∀ i, ‖sphericalVertices t i‖ = 1) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → HasDerivAt (fun s => sphericalAngle s i j k) 1 t) ∧
    HasDerivAt sphericalArea 3 t ∧
    (∑ i : Fin 3, deriv (fun s => sphericalAngle s i (i + 1) (i + 2)) t) =
      deriv sphericalArea t ∧ deriv sphericalArea t ≠ 0 := by
  have harea : HasDerivAt sphericalArea 3 t := by
    convert ((hasDerivAt_id t).const_mul 3).sub_const Real.pi using 1
    · rfl
    · norm_num
  have hn : ∀ᶠ s in 𝓝 t, s ∈ Set.Ioo (Real.pi / 3) Real.pi := isOpen_Ioo.mem_nhds ht
  have hangle (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      HasDerivAt (fun s => sphericalAngle s i j k) 1 t :=
    (hasDerivAt_id t).congr_of_eventuallyEq
      (hn.mono fun s hs => spherical_angle_eq s hs i j k hij hik hjk)
  refine ⟨fun i => ?_, hangle, harea, ?_, by norm_num [harea.deriv]⟩
  · have h := (spherical_gram t ht).2.2 i i
    simp only [ite_eq_left, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (sphericalVertices t i)]
  · rw [harea.deriv]
    simp only [show ∀ i : Fin 3,
        deriv (fun s => sphericalAngle s i (i + 1) (i + 2)) t = 1 from fun i =>
      (hangle i (i + 1) (i + 2) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)).deriv]
    simp

end SphericalTriangle

end D5.S3.Geometry.DiscreteGravity.ReggeSchlafli4D
