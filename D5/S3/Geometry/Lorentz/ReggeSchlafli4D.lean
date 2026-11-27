/- GID: D5/S3/Geometry/Lorentz/ReggeSchlafli4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/ReggeSchlafli4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simplex facet closure, the Euclidean Schläfli identity and 4D Regge variation. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Barycentric gradients and the first variation of Euclidean simplicial curvature. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.ReggeSchlafli4D

open scoped BigOperators InnerProductSpace Matrix
open Affine EuclideanGeometry

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SimplexData (n : ℕ) := Simplex ℝ (E n) n

/-- A path of affinely independent vertices with pointwise derivatives. -/
structure SimplexPath (n : ℕ) where
  simplex : ℝ → SimplexData n
  differentiable : ∀ i, Differentiable ℝ (fun t => (simplex t).points i)

abbrev Hinge (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2}

private def basis {n : ℕ} (s : SimplexData n) : AffineBasis (Fin (n + 1)) ℝ (E n) :=
  ⟨s.points, s.independent, s.affineSpan_eq_top (by simp [E])⟩

private def grad {n : ℕ} (s : SimplexData n) (i : Fin (n + 1)) : E n :=
  (InnerProductSpace.toDual ℝ (E n)).symm
    ((basis s).coord i).linear.toContinuousLinearMap

private theorem grad_pair {n : ℕ} (s : SimplexData n) (i : Fin (n + 1)) (x y : E n) :
    ⟪grad s i, x - y⟫_ℝ = (basis s).coord i x - (basis s).coord i y := by
  rw [grad, InnerProductSpace.toDual_symm_apply]
  exact ((basis s).coord i).linear_apply_vsub x y

private theorem grad_vertex {n : ℕ} (s : SimplexData n) (i j k : Fin (n + 1)) :
    ⟪grad s i, s.points j - s.points k⟫_ℝ =
      (if i = j then 1 else 0) - (if i = k then 1 else 0) := by
  rw [grad_pair]
  change (basis s).coord i ((basis s) j) - (basis s).coord i ((basis s) k) = _
  rw [AffineBasis.coord_apply, AffineBasis.coord_apply]

private theorem grad_ne_zero {n : ℕ} [NeZero n] (s : SimplexData n) (i : Fin (n + 1)) :
    grad s i ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  intro h
  simpa [h, Ne.symm hj] using grad_vertex s i i j

private theorem sum_grad {n : ℕ} (s : SimplexData n) : ∑ i, grad s i = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [sum_inner]
  let v := ∑ i, grad s i
  change ∑ i, ⟪grad s i, v⟫_ℝ = 0
  have h (i : Fin (n + 1)) :
      ⟪grad s i, v⟫_ℝ = (basis s).coord i v - (basis s).coord i 0 := by
    simpa only [sub_zero v] using grad_pair s i v 0
  simp only [h, Finset.sum_sub_distrib, AffineBasis.sum_coord_apply_eq_one, sub_self]

private theorem coord_zero_iff {n : ℕ} [NeZero n] (s : SimplexData n)
    (i : Fin (n + 1)) (x : E n) :
    x ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points) ↔ (basis s).coord i x = 0 := by
  have h := s.affineCombination_mem_affineSpan_faceOpposite_iff
    ((basis s).sum_coord_apply_eq_one x) (i := i)
  rw [show s.points = ⇑(basis s) from rfl, (basis s).affineCombination_coord_eq_self] at h
  exact h

private theorem direction_iff {n : ℕ} [NeZero n] (s : SimplexData n)
    (i : Fin (n + 1)) (v : E n) :
    v ∈ (affineSpan ℝ (Set.range (s.faceOpposite i).points)).direction ↔
      ⟪grad s i, v⟫_ℝ = 0 := by
  let S := affineSpan ℝ (Set.range (s.faceOpposite i).points)
  let x := (s.faceOpposite i).points 0
  have hx : x ∈ S := mem_affineSpan _ (Set.mem_range_self _)
  have he : (v +ᵥ x) - x = v := by change v + x - x = v; abel
  rw [← he, grad_pair, (coord_zero_iff s i x).mp hx, sub_zero,
    ← coord_zero_iff, he]
  exact (S.vadd_mem_iff_mem_direction v hx).symm

/-- The outward unit normal to the facet opposite the indicated vertex. -/
def facetNormal {n : ℕ} (s : SimplexData n) (i : Fin (n + 1)) : E n :=
  (-‖grad s i‖⁻¹ : ℝ) • grad s i

theorem facet_normal {n : ℕ} [NeZero n] (s : SimplexData n) (i : Fin (n + 1)) :
    ‖facetNormal s i‖ = 1 ∧
      ∀ x ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points),
        ⟪facetNormal s i, s.points i - x⟫_ℝ < 0 ∧
        ∀ v ∈ (affineSpan ℝ (Set.range (s.faceOpposite i).points)).direction,
          ⟪facetNormal s i, v⟫_ℝ = 0 := by
  have hn : 0 < ‖grad s i‖ := norm_pos_iff.mpr (grad_ne_zero s i)
  refine ⟨?_, fun x hx => ⟨?_, fun v hv => ?_⟩⟩
  · simp [facetNormal, norm_smul, hn.ne']
  · rw [facetNormal, real_inner_smul_left, grad_pair, (coord_zero_iff s i x).mp hx]
    change -‖grad s i‖⁻¹ * ((basis s).coord i ((basis s) i) - 0) < 0
    rw [AffineBasis.coord_apply_eq, sub_zero, mul_one]
    exact neg_lt_zero.mpr (inv_pos.mpr hn)
  · rw [facetNormal, real_inner_smul_left, (direction_iff s i v).mp hv, mul_zero]

/-- The Euclidean volume of the opposite facet. -/
def facetArea {n : ℕ} [NeZero n] (s : SimplexData n) (i : Fin (n + 1)) : ℝ :=
  (s.faceOpposite i).volume

private theorem height_of_normal {m n : ℕ} [NeZero m] (s : Simplex ℝ (E n) m)
    (i : Fin (m + 1)) (w : E n)
    (hw : w ∈ (s.altitude i).direction) (hpair : ⟪w, s.points i - s.altitudeFoot i⟫_ℝ = 1) :
    s.height i = ‖w‖⁻¹ := by
  let d := s.points i - s.altitudeFoot i
  have hd : d ∈ (s.altitude i).direction :=
    (s.altitude i).vsub_mem_direction (s.mem_altitude i) (s.altitudeFoot_mem_altitude i)
  have hw0 : w ≠ 0 := by intro h; simp [h] at hpair
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hspan : ℝ ∙ w = (s.altitude i).direction :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
      (by rw [finrank_span_singleton hw0, s.finrank_direction_altitude])
  rw [← hspan, Submodule.mem_span_singleton] at hd
  obtain ⟨a, ha⟩ := hd
  change ⟪w, d⟫_ℝ = 1 at hpair
  rw [← ha, real_inner_smul_right, real_inner_self_eq_norm_sq] at hpair
  have ha' : a = (‖w‖ ^ 2)⁻¹ := by
    rw [← one_div, eq_div_iff (pow_ne_zero _ hn.ne')]
    exact hpair
  change ‖d‖ = _
  rw [← ha, ha', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

private theorem altitude_grad {n : ℕ} [NeZero n] (s : SimplexData n) (i : Fin (n + 1)) :
    s.height i = ‖grad s i‖⁻¹ := by
  apply height_of_normal s i (grad s i)
  · rw [s.direction_altitude, ← direction_affineSpan, ← direction_affineSpan,
      s.affineSpan_eq_top (by simp [E]), AffineSubspace.direction_top, inf_top_eq,
      ← s.range_faceOpposite_points]
    exact (Submodule.mem_orthogonal' _ _).2 fun v hv => (direction_iff s i v).mp hv
  · rw [grad_pair, (coord_zero_iff s i _).mp (s.altitudeFoot_mem_affineSpan_faceOpposite i)]
    exact sub_zero _ |>.trans ((basis s).coord_apply_eq i)

private theorem facetArea_eq {n : ℕ} [NeZero n] (s : SimplexData n) (i : Fin (n + 1)) :
    facetArea s i = (n : ℝ) * s.volume * ‖grad s i‖ := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hg : ‖grad s i‖ ≠ 0 := norm_ne_zero_iff.mpr (grad_ne_zero s i)
  rw [s.volume_eq i, altitude_grad]
  unfold facetArea
  field_simp

theorem facet_closure {n : ℕ} [NeZero n] (s : SimplexData n) :
    (∀ i, 0 < facetArea s i) ∧ ∑ i, facetArea s i • facetNormal s i = 0 := by
  refine ⟨fun i => (s.faceOpposite i).volume_pos, ?_⟩
  simp only [facetArea_eq, facetNormal, smul_smul, mul_neg, mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (grad_ne_zero s _)), mul_one,
    ← Finset.smul_sum, sum_grad, smul_zero]

private instance (n : ℕ) : NeZero (n + 2 - 1) := ⟨by omega⟩

private def facetIndex {n : ℕ} (h : Hinge (n + 2)) : Fin (n + 2) :=
  (finSuccAboveEquiv h.val.1).symm ⟨h.val.2, ne_of_gt h.property⟩
private theorem facetIndex_spec {n : ℕ} (h : Hinge (n + 2)) :
    h.val.1.succAbove (facetIndex h) = h.val.2 :=
  congrArg Subtype.val ((finSuccAboveEquiv h.val.1).apply_symm_apply _)

/-- The ridge obtained by deleting the two vertices opposite the incident facets. -/
def hingeSimplex {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) :
    Simplex ℝ (E (n + 2)) n :=
  (s.faceOpposite h.val.1).faceOpposite (facetIndex h)

def hingeVolume {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) : ℝ :=
  (hingeSimplex s h).volume

def dihedralCos {n : ℕ} (s : SimplexData n) (i j : Fin (n + 1)) : ℝ :=
  -⟪facetNormal s i, facetNormal s j⟫_ℝ
def dihedralAngle {n : ℕ} (s : SimplexData n) (h : Hinge n) : ℝ :=
  Real.arccos (dihedralCos s h.val.1 h.val.2)

private def projectedGrad {n : ℕ} (s : SimplexData n) (i j : Fin (n + 1)) : E n :=
  grad s j - (⟪grad s i, grad s j⟫_ℝ / ‖grad s i‖ ^ 2) • grad s i

private theorem projectedGrad_sq {n : ℕ} [NeZero n] (s : SimplexData n) (i j : Fin (n + 1)) :
    ‖projectedGrad s i j‖ ^ 2 = ‖grad s j‖ ^ 2 * (1 - dihedralCos s i j ^ 2) := by
  have hi := norm_ne_zero_iff.mpr (grad_ne_zero s i)
  have hj := norm_ne_zero_iff.mpr (grad_ne_zero s j)
  rw [← real_inner_self_eq_norm_sq]
  unfold projectedGrad dihedralCos facetNormal
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm (grad s j) (grad s i)]
  field_simp
  ring

private theorem hinge_height {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) :
    (s.faceOpposite h.val.1).height (facetIndex h) =
      ‖projectedGrad s h.val.1 h.val.2‖⁻¹ ∧ projectedGrad s h.val.1 h.val.2 ≠ 0 := by
  let i := h.val.1
  let j := h.val.2
  let k := facetIndex h
  let f := s.faceOpposite i
  let S := affineSpan ℝ (Set.range f.points)
  let T := affineSpan ℝ (Set.range (f.faceOpposite k).points)
  have hTS : T ≤ S := f.affineSpan_faceOpposite_le k
  have hTj : T ≤ affineSpan ℝ (Set.range (s.faceOpposite j).points) := by
    dsimp only [T]
    rw [f.range_faceOpposite_points, s.range_faceOpposite_points]
    apply affineSpan_mono
    rintro _ ⟨l, hl, rfl⟩
    rw [s.faceOpposite_point_eq_point_succAbove]
    refine ⟨i.succAbove l, ?_, rfl⟩
    change i.succAbove l ≠ j
    have hj : i.succAbove k = j := facetIndex_spec h
    rw [← hj]
    exact fun he => hl (Fin.succAbove_right_injective he)
  have hpt : f.points k = s.points j := by
    rw [s.faceOpposite_point_eq_point_succAbove]
    exact congrArg s.points (facetIndex_spec h)
  have hfoot := f.altitudeFoot_mem_affineSpan_faceOpposite k
  have hp : ⟪projectedGrad s i j, f.points k - f.altitudeFoot k⟫_ℝ = 1 := by
    have hz : f.points k - f.altitudeFoot k ∈ S.direction :=
      S.vsub_mem_direction (f.mem_affineSpan_range k) (hTS hfoot)
    unfold projectedGrad
    rw [inner_sub_left, real_inner_smul_left, (direction_iff s i _).mp hz,
      mul_zero, sub_zero, grad_pair, (coord_zero_iff s j _).mp (hTj hfoot), hpt, sub_zero]
    exact (basis s).coord_apply_eq j
  refine ⟨height_of_normal f k _ ?_ hp, ?_⟩
  · rw [f.direction_altitude, ← direction_affineSpan, ← f.range_faceOpposite_points,
      ← direction_affineSpan]
    refine ⟨(Submodule.mem_orthogonal' _ _).2 fun v hv => ?_, (direction_iff s i _).2 ?_⟩
    · unfold projectedGrad
      rw [inner_sub_left, real_inner_smul_left, (direction_iff s i v).mp
        (AffineSubspace.direction_le hTS hv), (direction_iff s j v).mp
        (AffineSubspace.direction_le hTj hv), mul_zero, sub_zero]
    · change ⟪grad s i, projectedGrad s i j⟫_ℝ = 0
      unfold projectedGrad
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.mpr (grad_ne_zero s i)]
      ring
  · intro hz
    change projectedGrad s i j = 0 at hz
    rw [hz, inner_zero_left] at hp
    norm_num at hp

private theorem sine_sq_pos {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) :
    0 < 1 - dihedralCos s h.val.1 h.val.2 ^ 2 := by
  by_contra! hw
  have hx : 0 < ‖projectedGrad s h.val.1 h.val.2‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (hinge_height s h).2) _
  rw [projectedGrad_sq] at hx
  exact hx.not_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hw)

theorem dihedral_cosine {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) :
    Real.cos (dihedralAngle s h) = -⟪facetNormal s h.val.1, facetNormal s h.val.2⟫_ℝ := by
  have hp := sine_sq_pos s h
  exact Real.cos_arccos (by nlinarith) (by nlinarith)

private theorem hingeVolume_eq {n : ℕ} (s : SimplexData (n + 2)) (h : Hinge (n + 2)) :
    hingeVolume s h =
      ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * s.volume *
        ‖grad s h.val.1‖ * ‖grad s h.val.2‖ *
        Real.sqrt (1 - dihedralCos s h.val.1 h.val.2 ^ 2) := by
  let i := h.val.1
  let j := h.val.2
  have hp : ‖projectedGrad s i j‖ =
      ‖grad s j‖ * Real.sqrt (1 - dihedralCos s i j ^ 2) := by
    have he := projectedGrad_sq s i j
    rw [← Real.sq_sqrt (sine_sq_pos s h).le, ← mul_pow] at he
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp he).resolve_right
      (by
        have hh := norm_pos_iff.mpr (hinge_height s h).2
        change 0 < ‖projectedGrad s i j‖ at hh
        linarith [mul_nonneg (norm_nonneg (grad s j))
          (Real.sqrt_nonneg (1 - dihedralCos s i j ^ 2))])
  have hv := (s.faceOpposite i).volume_eq (facetIndex h)
  rw [(hinge_height s h).1] at hv
  change facetArea s i = _ * _ * hingeVolume s h at hv
  rw [facetArea_eq] at hv
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hg : ‖projectedGrad s i j‖ ≠ 0 := norm_ne_zero_iff.mpr (hinge_height s h).2
  change _ = ((n + 1 : ℕ) : ℝ)⁻¹ * ‖projectedGrad s i j‖⁻¹ * _ at hv
  have he : ((n + 2 : ℕ) : ℝ) * s.volume * ‖grad s i‖ *
      ((n + 1 : ℕ) : ℝ) * ‖projectedGrad s i j‖ = hingeVolume s h := by
    field_simp [hn, hg] at hv
    exact hv
  change _ = _ * _ * s.volume * ‖grad s i‖ * ‖grad s j‖ * _
  rw [← he, hp]
  ring

private def edgeMatrix {n : ℕ} (s : SimplexData n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => (s.points j.succ - s.points 0) k
private def gradMatrix {n : ℕ} (s : SimplexData n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k i => grad s i.succ k

private theorem edgeMatrix_mul_gradMatrix {n : ℕ} (s : SimplexData n) :
    edgeMatrix s * gradMatrix s = 1 := by
  ext j i
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [edgeMatrix, gradMatrix, Matrix.of_apply]
  rw [show (∑ k, (s.points j.succ - s.points 0) k * grad s i.succ k) =
      ⟪grad s i.succ, s.points j.succ - s.points 0⟫_ℝ by
        simp [PiLp.inner_apply, mul_comm]]
  simp [grad_vertex, eq_comm]

private theorem differentiable_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ) (t : ℝ)
    (hd : ∀ i j, DifferentiableAt ℝ (fun x => M x i j) t) :
    DifferentiableAt ℝ (fun x => (M x).det) t := by
  simp only [Matrix.det_apply]
  fun_prop (disch := exact hd _ _)

private theorem differentiable_grad {n : ℕ} (p : SimplexPath n) (i : Fin (n + 1)) (t : ℝ) :
    DifferentiableAt ℝ (fun x => grad (p.simplex x) i) t := by
  have hentry (j k : Fin n) : DifferentiableAt ℝ (fun x => edgeMatrix (p.simplex x) j k) t :=
    (differentiableAt_piLp 2).mp
      (((p.differentiable j.succ) t).sub ((p.differentiable 0) t)) k
  have hnz (x : ℝ) := Matrix.isUnit_det_of_right_inverse (edgeMatrix_mul_gradMatrix (p.simplex x))
  have hform (x : ℝ) : gradMatrix (p.simplex x) =
      (edgeMatrix (p.simplex x)).det⁻¹ • (edgeMatrix (p.simplex x)).adjugate := by
    rw [← Matrix.inv_eq_right_inv (edgeMatrix_mul_gradMatrix (p.simplex x)),
      Matrix.inv_def, Ring.inverse_eq_inv]
  have hs (j : Fin n) : DifferentiableAt ℝ (fun x => grad (p.simplex x) j.succ) t := by
    apply (differentiableAt_piLp 2).2
    intro k
    change DifferentiableAt ℝ (fun x => gradMatrix (p.simplex x) k j) t
    simp only [hform, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
    refine ((differentiable_det _ t hentry).inv (hnz t).ne_zero).mul ?_
    apply differentiable_det
    intro a b
    by_cases ha : a = j
    · subst a
      simp [Matrix.updateRow_apply]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  refine Fin.cases ?_ hs i
  have h0 (x : ℝ) : grad (p.simplex x) 0 = -∑ j : Fin n, grad (p.simplex x) j.succ := by
    have h := sum_grad (p.simplex x)
    rw [Fin.sum_univ_succ, add_eq_zero_iff_eq_neg] at h
    exact h
  simp only [h0]
  exact (DifferentiableAt.fun_sum fun j _ => hs j).neg

private theorem differentiable_normal {n : ℕ} [NeZero n] (p : SimplexPath n)
    (i : Fin (n + 1)) (t : ℝ) :
    DifferentiableAt ℝ (fun x => facetNormal (p.simplex x) i) t := by
  have h := differentiable_grad p i t
  exact (((h.norm ℝ (grad_ne_zero _ _)).inv
    (norm_ne_zero_iff.mpr (grad_ne_zero _ _))).neg).smul h

private theorem hasDerivAt_dihedralAngle {n : ℕ} (p : SimplexPath (n + 2)) (t : ℝ)
    (h : Hinge (n + 2)) :
    HasDerivAt (fun x => dihedralAngle (p.simplex x) h)
      (deriv (fun x => ⟪facetNormal (p.simplex x) h.val.1,
        facetNormal (p.simplex x) h.val.2⟫_ℝ) t /
          Real.sqrt (1 - dihedralCos (p.simplex t) h.val.1 h.val.2 ^ 2)) t := by
  have hp := sine_sq_pos (p.simplex t) h
  have hd := (differentiable_normal p h.val.1 t).inner ℝ (differentiable_normal p h.val.2 t)
  convert (Real.hasDerivAt_arccos (x := dihedralCos (p.simplex t) h.val.1 h.val.2)
    (by intro he; rw [he] at hp; norm_num at hp)
    (by intro he; rw [he] at hp; norm_num at hp)).comp t hd.hasDerivAt.neg using 1
  · rfl
  · ring

private theorem sum_pairs {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ h : {p : ι × ι // p.1 < p.2}, f h.val.1 h.val.2 := by
  classical
  let g (i j : ι) := if i < j then f i j else 0
  have he (i j : ι) : f i j = g i j + g j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [g, hij, hij.not_gt]
    · simp [g, hz]
    · simp [g, hji, hji.not_gt, hs i j]
  calc
    ∑ i, ∑ j, f i j = (∑ i, ∑ j, g i j) + ∑ i, ∑ j, g j i := by
      simp only [he, Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, g i j := by rw [Finset.sum_comm (f := fun i j => g j i)]; ring
    _ = _ := by
      rw [← Fintype.sum_prod_type' (f := g)]
      congr 1
      rw [show (Finset.univ : Finset {p : ι × ι // p.1 < p.2}) =
        Finset.univ.subtype (fun p : ι × ι => p.1 < p.2) from by ext; simp,
        Finset.sum_subtype_eq_sum_filter (f := fun p : ι × ι => f p.1 p.2),
        Finset.sum_filter]

/-- Minkowski facet closure annihilates the weighted variation of the normal inner products. -/
theorem euclidean_schlafli {n : ℕ} (p : SimplexPath (n + 2)) (t : ℝ) :
    ∑ h, hingeVolume (p.simplex t) h * deriv (fun x => dihedralAngle (p.simplex x) h) t = 0 := by
  let u (i : Fin (n + 3)) (x : ℝ) := facetNormal (p.simplex x) i
  let a (i : Fin (n + 3)) := ‖grad (p.simplex t) i‖
  let d (i j : Fin (n + 3)) := deriv (fun x => ⟪u i x, u j x⟫_ℝ) t
  have hdu (i : Fin (n + 3)) : HasDerivAt (u i) (deriv (u i) t) t :=
    (differentiable_normal p i t).hasDerivAt
  have ha : ∑ i, a i • u i t = 0 := by
    simp only [a, u, facetNormal, smul_smul, mul_neg,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr (grad_ne_zero (p.simplex t) _))]
    rw [← Finset.smul_sum, sum_grad, smul_zero]
  have hd (i j : Fin (n + 3)) :
      d i j = ⟪u i t, deriv (u j) t⟫_ℝ + ⟪deriv (u i) t, u j t⟫_ℝ :=
    ((hdu i).inner ℝ (hdu j)).deriv
  have hfull : ∑ i, ∑ j, a i * a j * d i j = 0 := by
    simp only [hd, mul_add, Finset.sum_add_distrib]
    have hleft (j : Fin (n + 3)) : ∑ i, a i * a j * ⟪u i t, deriv (u j) t⟫_ℝ = 0 := by
      simp_rw [mul_comm (a _) (a j), mul_assoc]
      rw [← Finset.mul_sum]
      simp only [← real_inner_smul_left, ← sum_inner, ha, inner_zero_left, mul_zero]
    have hright (i : Fin (n + 3)) : ∑ j, a i * a j * ⟪deriv (u i) t, u j t⟫_ℝ = 0 := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp only [← real_inner_smul_right, ← inner_sum, ha, inner_zero_right, mul_zero]
    rw [Finset.sum_comm (f := fun i j => a i * a j * ⟪u i t, deriv (u j) t⟫_ℝ)]
    simp [hleft, hright]
  rw [sum_pairs (fun i j => a i * a j * d i j)] at hfull
  · have hsum : ∑ h : Hinge (n + 2), a h.val.1 * a h.val.2 * d h.val.1 h.val.2 = 0 := by
      linarith
    let c := ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * (p.simplex t).volume
    calc
      _ = ∑ h : Hinge (n + 2), c * (a h.val.1 * a h.val.2 * d h.val.1 h.val.2) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [hingeVolume_eq, (hasDerivAt_dihedralAngle p t h).deriv]
        change c * a h.val.1 * a h.val.2 * _ * (d h.val.1 h.val.2 / _) = _
        field_simp [Real.sqrt_ne_zero'.mpr (sine_sq_pos (p.simplex t) h)]
      _ = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]
  · intro i j
    have he : (fun x => ⟪u i x, u j x⟫_ℝ) = fun x => ⟪u j x, u i x⟫_ℝ :=
      funext fun x => real_inner_comm _ _
    simp only [d, he, mul_comm (a i)]
  · intro i
    have he : (fun x => ⟪u i x, u i x⟫_ℝ) = fun _ : ℝ => (1 : ℝ) := by
      funext x
      rw [real_inner_self_eq_norm_sq, show ‖u i x‖ = 1 from (facet_normal _ _).1, one_pow]
    rw [show d i i = 0 by simp only [d, he, deriv_const], mul_zero]

def edgeLength (s : SimplexData 3) (h : Hinge 3) : ℝ :=
  dist ((hingeSimplex s h).points 0) ((hingeSimplex s h).points 1)

theorem tetrahedron_schlafli (p : SimplexPath 3) (t : ℝ) :
    ∑ h, edgeLength (p.simplex t) h * deriv (fun x => dihedralAngle (p.simplex x) h) t = 0 := by
  simpa only [hingeVolume, Simplex.volume_eq_dist, edgeLength] using euclidean_schlafli p t

abbrev triangleArea (s : SimplexData 4) (h : Hinge 4) : ℝ := hingeVolume s h

theorem four_simplex_schlafli (p : SimplexPath 4) (t : ℝ) :
    ∑ h, triangleArea (p.simplex t) h * deriv (fun x => dihedralAngle (p.simplex x) h) t = 0 :=
  euclidean_schlafli p t

/-- The hinge incidence and metric data used by the Regge action of a finite triangulation. -/
structure ReggePath (σ H : Type*) where
  simplexPath : σ → SimplexPath 4
  hinge : σ → Hinge 4 ↪ H
  area : H → ℝ → ℝ
  area_eq : ∀ s k t, area (hinge s k) t = triangleArea ((simplexPath s).simplex t) k
  differentiable_area : ∀ h, Differentiable ℝ (area h)

def deficit {σ H : Type*} [Fintype σ] [DecidableEq H]
    (p : ReggePath σ H) (h : H) (t : ℝ) : ℝ :=
  2 * Real.pi - ∑ s, ∑ k,
    if p.hinge s k = h then dihedralAngle ((p.simplexPath s).simplex t) k else 0
def reggeAction {σ H : Type*} [Fintype σ] [Fintype H] [DecidableEq H]
    (p : ReggePath σ H) (t : ℝ) : ℝ :=
  ∑ h, p.area h t * deficit p h t
private def angleRate {σ H : Type*} (p : ReggePath σ H) (t : ℝ) (s : σ) (k : Hinge 4) : ℝ :=
  deriv (fun x => dihedralAngle ((p.simplexPath s).simplex x) k) t

private theorem hasDerivAt_deficit {σ H : Type*} [Fintype σ] [DecidableEq H]
    (p : ReggePath σ H) (h : H) (t : ℝ) :
    HasDerivAt (deficit p h) (-(∑ s, ∑ k, if p.hinge s k = h then angleRate p t s k else 0)) t := by
  apply HasDerivAt.const_sub
  apply HasDerivAt.fun_sum
  intro s _
  apply HasDerivAt.fun_sum
  intro k _
  by_cases hk : p.hinge s k = h
  · simpa only [hk, ite_true, angleRate] using
      (hasDerivAt_dihedralAngle (p.simplexPath s) t k).differentiableAt.hasDerivAt
  · simpa only [hk, ite_false] using (hasDerivAt_const t (0 : ℝ))

private theorem angle_cancellation {σ H : Type*} [Fintype σ] [Fintype H] [DecidableEq H]
    (p : ReggePath σ H) (t : ℝ) :
    ∑ h, p.area h t * deriv (deficit p h) t = 0 := by
  simp_rw [(hasDerivAt_deficit p _ t).deriv, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro s _
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_zero]
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, p.area_eq, angleRate] using
    (four_simplex_schlafli (p.simplexPath s) t)

/-- The deficit derivative terms in the first variation cancel simplex by simplex. -/
theorem regge_variation {σ H : Type*} [Fintype σ] [Fintype H] [DecidableEq H]
    (p : ReggePath σ H) (t : ℝ) :
    HasDerivAt (reggeAction p) (∑ h, deriv (p.area h) t * deficit p h t) t := by
  have hd (h : H) := ((p.differentiable_area h t).hasDerivAt).mul
    ((hasDerivAt_deficit p h t).differentiableAt.hasDerivAt)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun h _ => hd h)
  change HasDerivAt (fun x => ∑ h, p.area h x * deficit p h x) _ t
  simpa only [Pi.mul_apply, Finset.sum_add_distrib, angle_cancellation p t, add_zero] using hsum

private def triangleEdge {n : ℕ} (s : Simplex ℝ (E n) 2) (i : Fin 3) : E n :=
  s.points i - s.points 2
private def triangleResidual {n : ℕ} (s : Simplex ℝ (E n) 2) : E n :=
  let e := triangleEdge s 1
  let x := triangleEdge s 0
  x - (⟪e, x⟫_ℝ / ‖e‖ ^ 2) • e

private theorem triangle_edge_ne {n : ℕ} (s : Simplex ℝ (E n) 2) : triangleEdge s 1 ≠ 0 :=
  sub_ne_zero.mpr (fun h => by
    have h12 := s.independent.injective h
    exact (by decide : (1 : Fin 3) ≠ 2) h12)

private theorem triangle_height {n : ℕ} (s : Simplex ℝ (E n) 2) :
    s.height 0 = ‖triangleResidual s‖ := by
  let c := ⟪triangleEdge s 1, triangleEdge s 0⟫_ℝ / ‖triangleEdge s 1‖ ^ 2
  let q := c • triangleEdge s 1 + s.points 2
  have hr : Set.range (s.faceOpposite 0).points = {s.points 1, s.points 2} := by
    ext p
    simp [Fin.exists_fin_succ, eq_comm]
  have hq : s.altitudeFoot 0 = q := by
    unfold Simplex.altitudeFoot Simplex.orthogonalProjectionSpan
    apply coe_orthogonalProjection_eq_iff_mem.mpr
    rw [hr]
    refine ⟨smul_vsub_rev_vadd_mem_affineSpan_pair c (s.points 1) (s.points 2), ?_⟩
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
    change ⟪triangleEdge s 1, s.points 0 - q⟫_ℝ = 0
    rw [show s.points 0 - q = triangleResidual s from by
      dsimp [q, c, triangleResidual, triangleEdge]
      abel]
    simp only [triangleResidual, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr (triangle_edge_ne s)]
    ring
  rw [Simplex.height, hq, dist_eq_norm]
  congr 1
  dsimp [q, c, triangleResidual, triangleEdge]
  abel

private theorem triangle_volume {n : ℕ} (s : Simplex ℝ (E n) 2) :
    s.volume = ‖triangleResidual s‖ * ‖triangleEdge s 1‖ / 2 := by
  rw [s.volume_eq 0, triangle_height, Simplex.volume_eq_dist,
    s.faceOpposite_point_eq_point_succAbove, s.faceOpposite_point_eq_point_succAbove]
  change 2⁻¹ * ‖triangleResidual s‖ * dist (s.points 1) (s.points 2) = _
  rw [dist_eq_norm, triangleEdge]
  ring

private def ones : E 4 := WithLp.toLp 2 (fun _ => 1)

private def regularVector (i : Fin 5) : E 4 :=
  let r := Real.sqrt (1 / 5)
  Fin.cases ((-r) • ones) (fun j => EuclideanSpace.single j 1 + ((r - 1) / 4) • ones) i

private theorem regularVector_inner (i j : Fin 5) :
    ⟪regularVector i, regularVector j⟫_ℝ = (if i = j then 1 else 0) - 1 / 5 := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 5 by norm_num)
  have hoo : ⟪ones, ones⟫_ℝ = 4 := by
    rw [PiLp.inner_apply]
    norm_num [ones]
  have hso (k : Fin 4) : ⟪EuclideanSpace.single k (1 : ℝ), ones⟫_ℝ = 1 := by
    simp [EuclideanSpace.inner_single_left, ones]
  have hos (k : Fin 4) : ⟪ones, EuclideanSpace.single k (1 : ℝ)⟫_ℝ = 1 :=
    (real_inner_comm _ _).trans (hso k)
  have hss (k l : Fin 4) : ⟪EuclideanSpace.single k (1 : ℝ), EuclideanSpace.single l 1⟫_ℝ =
      if k = l then 1 else 0 := by
    simp [EuclideanSpace.inner_single_left, PiLp.single_apply]
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  all_goals
    simp only [regularVector, Fin.cases_zero, Fin.cases_succ, real_inner_smul_left,
      real_inner_smul_right, inner_add_left, inner_add_right, hoo, hso, hos, hss,
      Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj, ite_false, ite_true]
    nlinarith [hr]
private def regularPoint (ℓ : ℝ) (i : Fin 5) : E 4 := (ℓ / Real.sqrt 2) • regularVector i
private theorem regularPoint_inner (ℓ : ℝ) (i j : Fin 5) :
    ⟪regularPoint ℓ i, regularPoint ℓ j⟫_ℝ = (ℓ ^ 2 / 2) * ((if i = j then 1 else 0) - 1 / 5) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [regularPoint, regularPoint, real_inner_smul_left, real_inner_smul_right, regularVector_inner]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- A centered regular Euclidean 4-simplex with positive edge length. -/
def regularSimplex (ℓ : ℝ) (hℓ : 0 < ℓ) : SimplexData 4 where
  points := regularPoint ℓ
  independent := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hv i
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
    have he := congrArg (fun v : E 4 => ⟪regularPoint ℓ i, v⟫_ℝ) hv
    simp only [inner_zero_right, inner_sum, real_inner_smul_right, regularPoint_inner] at he
    simp_rw [mul_left_comm (w _) (ℓ ^ 2 / 2), mul_sub, mul_ite, mul_one, mul_zero] at he
    rw [Finset.sum_sub_distrib] at he
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at he
    rw [← Finset.mul_sum, ← Finset.sum_mul, hw] at he
    simp only [zero_mul, mul_zero, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)

private theorem regular_grad (ℓ : ℝ) (hℓ : 0 < ℓ) (i : Fin 5) :
    grad (regularSimplex ℓ hℓ) i = (2 / ℓ ^ 2) • regularPoint ℓ i := by
  let s := regularSimplex ℓ hℓ
  apply (InnerProductSpace.toDual ℝ (E 4)).injective
  apply ContinuousLinearMap.coe_injective
  apply ((basis s).basisOf 0).ext
  intro j
  simp only [AffineBasis.basisOf_apply]
  change ⟪grad s i, s.points j.val - s.points 0⟫_ℝ =
    ⟪(2 / ℓ ^ 2) • regularPoint ℓ i, regularPoint ℓ j.val - regularPoint ℓ 0⟫_ℝ
  rw [grad_vertex, real_inner_smul_left, inner_sub_right, regularPoint_inner, regularPoint_inner]
  field_simp [hℓ.ne']
  ring

theorem regular_edge_length (ℓ : ℝ) (hℓ : 0 < ℓ) (i j : Fin 5) (hij : i ≠ j) :
    dist ((regularSimplex ℓ hℓ).points i) ((regularSimplex ℓ hℓ).points j) = ℓ := by
  change dist (regularPoint ℓ i) (regularPoint ℓ j) = ℓ
  have he : dist (regularPoint ℓ i) (regularPoint ℓ j) ^ 2 = ℓ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      regularPoint_inner, regularPoint_inner, regularPoint_inner]
    simp [hij]
    ring
  nlinarith [dist_nonneg (x := regularPoint ℓ i) (y := regularPoint ℓ j)]

theorem regular_dihedral_angle (ℓ : ℝ) (hℓ : 0 < ℓ) (h : Hinge 4) :
    dihedralAngle (regularSimplex ℓ hℓ) h = Real.arccos (1 / 4) := by
  have hd (i j : Fin 5) : ⟪grad (regularSimplex ℓ hℓ) i, grad (regularSimplex ℓ hℓ) j⟫_ℝ =
      (2 / ℓ ^ 2) * ((if i = j then 1 else 0) - 1 / 5) := by
    rw [regular_grad, regular_grad, real_inner_smul_left, real_inner_smul_right, regularPoint_inner]
    field_simp [hℓ.ne']
  have hs (i : Fin 5) : ‖grad (regularSimplex ℓ hℓ) i‖ ^ 2 = 8 / (5 * ℓ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, hd]
    simp
    ring
  have hn : ‖grad (regularSimplex ℓ hℓ) h.val.1‖ = ‖grad (regularSimplex ℓ hℓ) h.val.2‖ := by
    nlinarith [hs h.val.1, hs h.val.2, norm_nonneg (grad (regularSimplex ℓ hℓ) h.val.1),
      norm_nonneg (grad (regularSimplex ℓ hℓ) h.val.2)]
  unfold dihedralAngle dihedralCos facetNormal
  congr 1
  rw [real_inner_smul_left, real_inner_smul_right, hd, ite_eq_right (ne_of_lt h.property), hn]
  rw [show ∀ a b : ℝ, -(-a⁻¹ * (-a⁻¹ * b)) = -b / a ^ 2 by intros; ring, hs]
  field_simp [hℓ.ne']
  ring

theorem regular_triangle_area (ℓ : ℝ) (hℓ : 0 < ℓ) (h : Hinge 4) :
    triangleArea (regularSimplex ℓ hℓ) h = Real.sqrt 3 / 4 * ℓ ^ 2 := by
  let s := hingeSimplex (regularSimplex ℓ hℓ) h
  have hd (i j : Fin 3) (hij : i ≠ j) : dist (s.points i) (s.points j) = ℓ := by
    dsimp only [s, hingeSimplex]
    simp only [Simplex.faceOpposite_point_eq_point_succAbove]
    exact regular_edge_length ℓ hℓ _ _ (fun he =>
      hij (Fin.succAbove_right_injective (Fin.succAbove_right_injective he)))
  have he : ‖triangleEdge s 1‖ = ℓ := by simpa only [dist_eq_norm, triangleEdge] using hd 1 2 (by decide)
  have hx : ‖triangleEdge s 0‖ = ℓ := by simpa only [dist_eq_norm, triangleEdge] using hd 0 2 (by decide)
  have hi : ⟪triangleEdge s 1, triangleEdge s 0⟫_ℝ = ℓ ^ 2 / 2 := by
    have hh := norm_sub_sq_real (triangleEdge s 1) (triangleEdge s 0)
    rw [he, hx, show triangleEdge s 1 - triangleEdge s 0 = s.points 1 - s.points 0 from
      by unfold triangleEdge; abel, ← dist_eq_norm, hd 1 0 (by decide)] at hh
    linarith
  have hc : ⟪triangleEdge s 1, triangleEdge s 0⟫_ℝ / ‖triangleEdge s 1‖ ^ 2 = 1 / 2 := by
    rw [hi, he]
    field_simp [hℓ.ne']
  have hr : ‖triangleResidual s‖ = Real.sqrt 3 * ℓ / 2 := by
    have hh : ‖triangleResidual s‖ ^ 2 = 3 * ℓ ^ 2 / 4 := by
      change ‖triangleEdge s 0 -
        (⟪triangleEdge s 1, triangleEdge s 0⟫_ℝ / ‖triangleEdge s 1‖ ^ 2) • triangleEdge s 1‖ ^ 2 = _
      rw [hc]
      rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (triangleEdge s 1) (triangleEdge s 0), hi]
      rw [norm_smul, Real.norm_eq_abs, he, hx]
      norm_num
      ring
    have hs : (Real.sqrt 3 * ℓ / 2) ^ 2 = 3 * ℓ ^ 2 / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      ring
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp (hh.trans hs.symm)).resolve_right
      (by linarith [norm_nonneg (triangleResidual s),
        show 0 < Real.sqrt 3 * ℓ / 2 by positivity])
  change s.volume = _
  rw [triangle_volume, he, hr]
  ring

/-- A uniform dilation with scale equal to one at time zero. -/
def regularScaling (ℓ : ℝ) (hℓ : 0 < ℓ) : SimplexPath 4 where
  simplex t := regularSimplex (ℓ * Real.exp t) (mul_pos hℓ (Real.exp_pos t))
  differentiable i := by
    have h : Differentiable ℝ (fun t => ℓ * Real.exp t / Real.sqrt 2) := by fun_prop
    exact h.smul (differentiable_const (regularVector i))

theorem regular_scaling_cancellation (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) (h : Hinge 4) :
    HasDerivAt (fun x => dihedralAngle ((regularScaling ℓ hℓ).simplex x) h) 0 t := by
  simpa only [regularScaling, regular_dihedral_angle] using hasDerivAt_const t (Real.arccos (1 / 4))

end D5.S3.Geometry.Lorentz.ReggeSchlafli4D
