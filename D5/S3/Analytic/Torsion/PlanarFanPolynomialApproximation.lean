/- GID: D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation
   generality: G
   mirror-B: D5/B/S3/Analytic/Torsion/PlanarFanPolynomialApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result; premises=D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangle_volume,D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap_volume
   digest: Planar fans and polynomial approximation by rotational symmetry. -/

/-
admission_basis: escape-witness
escape_witness: polar_fan_conic_coverage; adjacent_triangles_spoke_interior; finite_cyclic_fan_frontier
Direct frozen dependencies: D5/S3/Geometry/Gluing/CyclicTriangleDisk.positive_circle_angle
(baseline private declaration statement_id: sha256:c2c13b4d22f1a330f80a64a05f4e73fe37aa856cf7477194eb3187b61c7ca716).
Polygon.boundary supplies the closed polygonal path; its segment-union form is normalized
inside the consuming proof using affineSegment_eq_segment and finRotate_apply.
The reference area 1/2 enters triangle_volume; complexCap_volume gives the cap area 1/8.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17590
Declaration metadata: name | proof_shape | escape_witness | consumers.
IsSimplePolygon: proof_shape: bind-only; escape_witness: none; consumers: IsPolygonRegion
IsPolygonRegion: proof_shape: bind-only; escape_witness: none; consumers: no_max_of_unbounded_family
cross_continuous_left: proof_shape: bind-only; escape_witness: none; consumers: adjacent_triangles_spoke_interior
cross_continuous_right: proof_shape: bind-only; escape_witness: none; consumers: adjacent_triangles_spoke_interior
cross_smul_left: proof_shape: bind-only; escape_witness: none; consumers: adjacent_triangles_spoke_interior
cross_smul_right: proof_shape: bind-only; escape_witness: none; consumers: adjacent_triangles_spoke_interior
triangleMap: proof_shape: bind-only; escape_witness: none; consumers: triangleMap_apply
triangleMap_apply: proof_shape: bind-only; escape_witness: none; consumers: triangleMap_hull_image
closedReferenceTriangle_convex: proof_shape: bind-only; escape_witness: none; consumers: closedReferenceTriangle_eq_hull
closedReferenceTriangle_eq_hull: proof_shape: bind-only; escape_witness: none; consumers: triangleMap_hull_image
triangleMap_hull_image: proof_shape: bind-only; escape_witness: none; consumers: triangle_mem_iff_cross
cross_decomposition: proof_shape: bind-only; escape_witness: none; consumers: triangle_mem_iff_cross
triangle_mem_iff_cross: proof_shape: bind-only; escape_witness: none; consumers: adjacent_triangles_spoke_interior
adjacent_triangles_spoke_interior: proof_shape: content; escape_witness: adjacent_triangles_spoke_interior; consumers: finite_cyclic_fan_interior_of_not_trace
aeDisjoint_disjoint_interior_of_regular: proof_shape: bind-only; escape_witness: none; consumers: triangle_open_edge_not_interior_fan
referenceTriangle: proof_shape: bind-only; escape_witness: none; consumers: complexReferenceTriangle
complexReferenceTriangle: proof_shape: bind-only; escape_witness: none; consumers: complexReferenceTriangle_volume
referenceTriangle_volume: proof_shape: bind-only; escape_witness: none; consumers: complexReferenceTriangle_volume
complexReferenceTriangle_volume: proof_shape: bind-only; escape_witness: none; consumers: closedReferenceTriangle_volume
linear_fiber_volume_zero: proof_shape: bind-only; escape_witness: none; consumers: imaginary_axis_null
imaginary_axis_null: proof_shape: bind-only; escape_witness: none; consumers: closedReferenceTriangle_volume
real_axis_null: proof_shape: bind-only; escape_witness: none; consumers: closedReferenceTriangle_volume
reference_diagonal_null: proof_shape: bind-only; escape_witness: none; consumers: closedReferenceTriangle_volume
closedReferenceTriangle_volume: proof_shape: bind-only; escape_witness: none; consumers: triangle_volume
referenceCap: proof_shape: bind-only; escape_witness: none; consumers: referenceCap_isOpen
complexCap: proof_shape: bind-only; escape_witness: none; consumers: complexCap_isOpen
referenceCap_isOpen: proof_shape: bind-only; escape_witness: none; consumers: complexCap_isOpen
complexCap_isOpen: proof_shape: bind-only; escape_witness: none; consumers: triangleCap_subset_starRegion
referenceCap_volume: proof_shape: bind-only; escape_witness: none; consumers: complexCap_volume
complexCap_volume: proof_shape: bind-only; escape_witness: none; consumers: starCap_volume
complex_norm_sub_sq: proof_shape: bind-only; escape_witness: none; consumers: integral_error_eq_secondMoment_add
crossMap_ker_ne_top: proof_shape: bind-only; escape_witness: none; consumers: triangles_aeDisjoint_of_cross_separation
cross_polarPoint: proof_shape: bind-only; escape_witness: none; consumers: polarVertex_before_cross_nonpos
triangle_outer_edge_iff: proof_shape: bind-only; escape_witness: none; consumers: finite_cyclic_fan_interior_of_not_trace
triangle_strict_mem_interior: proof_shape: bind-only; escape_witness: none; consumers: finite_cyclic_fan_interior_of_not_trace
finite_cyclic_fan_interior_of_not_trace: proof_shape: content; escape_witness: adjacent_triangles_spoke_interior; consumers: finite_cyclic_fan_frontier
triangle_interior_nonempty: proof_shape: bind-only; escape_witness: none; consumers: triangle_closure_interior
triangle_closure_interior: proof_shape: bind-only; escape_witness: none; consumers: finite_fan_closure_interior
finite_fan_closure_interior: proof_shape: bind-only; escape_witness: none; consumers: finite_cyclic_fan_frontier
triangle_strict_cone_meets_interior: proof_shape: bind-only; escape_witness: none; consumers: triangle_open_edge_not_interior_fan
triangle_open_edge_not_interior_fan: proof_shape: content; escape_witness: triangle_open_edge_not_interior_fan; consumers: finite_cyclic_fan_frontier
finite_cyclic_fan_frontier: proof_shape: content; escape_witness: adjacent_triangles_spoke_interior; consumers: starRegion_frontier
integrableOn_continuous_bounded: proof_shape: bind-only; escape_witness: none; consumers: integral_error_eq_secondMoment_add
integral_error_eq_secondMoment_add: proof_shape: bind-only; escape_witness: none; consumers: rhoN_eq_secondMoment_of_moments
integral_pow_eq_zero_of_rotation: proof_shape: bind-only; escape_witness: none; consumers: starRegion_moments
integral_z_mul_poly_eq_zero: proof_shape: bind-only; escape_witness: none; consumers: rhoN_eq_secondMoment_of_moments
rhoN: proof_shape: bind-only; escape_witness: none; consumers: no_max_of_unbounded_family
no_max_of_unbounded_family: proof_shape: bind-only; escape_witness: none; consumers: claim_of_star_geometry
norm_sq_smul_add: proof_shape: bind-only; escape_witness: none; consumers: norm_sq_smul_add_ge
norm_sq_smul_add_ge: proof_shape: bind-only; escape_witness: none; consumers: starCap_norm_bound
polarPoint_add_period: proof_shape: bind-only; escape_witness: none; consumers: polar_cyclic_forward_aeDisjoint, polar_cyclic_forward_disjoint
polarPoint_nat_mod: proof_shape: bind-only; escape_witness: none; consumers: polarVertex_next
polarPoint_theta_period: proof_shape: bind-only; escape_witness: none; consumers: polarVertex_next
polarVertex: proof_shape: bind-only; escape_witness: none; consumers: polarVertex_before_cross_nonpos
polarVertex_before_cross_nonpos: proof_shape: bind-only; escape_witness: none; consumers: polar_cyclic_forward_aeDisjoint
polarVertex_next: proof_shape: bind-only; escape_witness: none; consumers: polarVertex_next_cross_self
polarVertex_next_cross_self: proof_shape: bind-only; escape_witness: none; consumers: polar_cyclic_forward_aeDisjoint
polar_angle_representation: proof_shape: bind-only; escape_witness: none; consumers: polar_fan_conic_coverage
triangles_aeDisjoint_of_cross_separation: proof_shape: bind-only; escape_witness: none; consumers: polar_cyclic_forward_aeDisjoint
polar_cyclic_forward_aeDisjoint: proof_shape: content; escape_witness: polar_cyclic_forward_aeDisjoint; consumers: polar_cyclic_fan_pairwise_aeDisjoint
polar_cyclic_fan_pairwise_aeDisjoint: proof_shape: content; escape_witness: polar_cyclic_forward_aeDisjoint; consumers: starVertexRaw_fan_pairwise_aeDisjoint
segments_disjoint_strict_linear: proof_shape: bind-only; escape_witness: none; consumers: polar_cyclic_forward_disjoint
polar_cyclic_forward_disjoint: proof_shape: content; escape_witness: polar_cyclic_forward_disjoint; consumers: polar_cyclic_nonadjacent_disjoint
polar_cyclic_nonadjacent_disjoint: proof_shape: content; escape_witness: polar_cyclic_forward_disjoint; consumers: starVertex_nonadjacent_disjoint
polar_fan_conic_coverage: proof_shape: content; escape_witness: polar_fan_conic_coverage; consumers: starVertex_conic_coverage
rhoN_eq_secondMoment_of_moments: proof_shape: bind-only; escape_witness: none; consumers: rhoN_starRegion
secondMoment_ge_on_subset: proof_shape: bind-only; escape_witness: none; consumers: starRegion_secondMoment_lower_bound
triangleMap_complexCap_subset_hull: proof_shape: bind-only; escape_witness: none; consumers: triangleCap_subset_starRegion
triangleMap_det: proof_shape: bind-only; escape_witness: none; consumers: triangle_volume
triangle_volume: proof_shape: bind-only; escape_witness: none; consumers: starTriangle_volume
-/

import D5.S3.Geometry.Gluing.CyclicTriangleDisk
import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Geometry.Polygon.Basic

namespace D5.S3.Analytic.Torsion.PlanarFanPolynomialApproximation
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Complex.finrank_real_complex_fact
def IsSimplePolygon {n : ℕ} (v : Fin (n + 3) → ℂ) : Prop :=
  (∀ i j : Fin (n + 3), i ≠ j → j ≠ i + 1 → i ≠ j + 1 →
      Disjoint (segment ℝ (v i) (v (i + 1))) (segment ℝ (v j) (v (j + 1)))) ∧
  (∀ i : Fin (n + 3), segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v (i + 1)) (v (i + 2)) = {v (i + 1)}) ∧
  (∀ i : Fin (n + 3), ¬ Collinear ℝ {v i, v (i + 1), v (i + 2)})
def IsPolygonRegion (n : ℕ) (Ω : Set ℂ) : Prop :=
  ∃ v : Fin (n + 3) → ℂ, IsSimplePolygon v ∧ IsOpen Ω ∧ IsConnected Ω ∧
    Bornology.IsBounded Ω ∧ frontier Ω = (⟨v⟩ : Polygon ℂ (n + 3)).boundary ℝ
private lemma cross_continuous_left (b : ℂ) : Continuous (fun z : ℂ => Complex.orientation.areaForm z b) := by
  exact (Complex.orientation.areaForm.flip b).continuous_of_finiteDimensional
private lemma cross_continuous_right (a : ℂ) : Continuous (Complex.orientation.areaForm a) := by
  exact LinearMap.continuous_of_finiteDimensional (Complex.orientation.areaForm a)
private lemma cross_smul_left (r : ℝ) (a b : ℂ) : Complex.orientation.areaForm (r • a) b = r * Complex.orientation.areaForm a b := by
  exact LinearMap.BilinForm.smul_left r a b
private lemma cross_smul_right (r : ℝ) (a b : ℂ) : Complex.orientation.areaForm a (r • b) = r * Complex.orientation.areaForm a b := by
  exact LinearMap.BilinForm.smul_right r a b
noncomputable def triangleMap (a b : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  Complex.basisOneI.constr ℝ ![a,b]
lemma triangleMap_apply (a b z : ℂ) : triangleMap a b z = z.re • a + z.im • b := by
  simp [triangleMap, Module.Basis.constr_apply_fintype, Fin.sum_univ_succ,
    Complex.coe_basisOneI_repr]
private lemma closedReferenceTriangle_convex : Convex ℝ (Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) := by
  rw [Subtype.range_val_subtype]
  change Convex ℝ {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1}
  exact ((convex_Ici (0 : ℝ)).linear_preimage Complex.reLm).inter
    (((convex_Ici (0 : ℝ)).linear_preimage Complex.imLm).inter
      ((convex_Iic (1 : ℝ)).linear_preimage (Complex.reLm + Complex.imLm)))
private lemma closedReferenceTriangle_eq_hull : (Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) = convexHull ℝ {0,1,Complex.I} := by
  apply subset_antisymm
  · intro z hz
    rw [Subtype.range_val_subtype] at hz
    change 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re+z.im ≤ 1 at hz
    apply mem_convexHull_of_exists_fintype (ι := Fin 3)
      ![1-z.re-z.im, z.re, z.im] ![(0 : ℂ),1,Complex.I]
    · intro i
      fin_cases i <;> simp <;> linarith [hz.1, hz.2.1, hz.2.2]
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp
    · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Fin.isValue, smul_zero, zero_add, Finset.sum_empty, add_zero]
      apply Complex.ext <;> simp
  · apply convexHull_min _ closedReferenceTriangle_convex
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> norm_num [Subtype.range_val_subtype, Complex.measurableEquivRealProd_apply]
private lemma triangleMap_hull_image (a b : ℂ) : (triangleMap a b) '' (Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) = convexHull ℝ {0,a,b} := by
  rw [closedReferenceTriangle_eq_hull, LinearMap.image_convexHull]
  congr 1
  simp [image_insert_eq, image_singleton, triangleMap_apply]
private lemma cross_decomposition (a b z : ℂ) (hd : Complex.orientation.areaForm a b ≠ 0) : (Complex.orientation.areaForm z b / Complex.orientation.areaForm a b) • a+(Complex.orientation.areaForm a z / Complex.orientation.areaForm a b) • b = z := by
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,
    Complex.smul_im,smul_eq_mul]
  all_goals field_simp [hd]; simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
lemma triangle_mem_iff_cross (a b z : ℂ) (hd : 0 < Complex.orientation.areaForm a b) : z ∈ convexHull ℝ {0,a,b} ↔ 0 ≤ Complex.orientation.areaForm z b ∧ 0 ≤ Complex.orientation.areaForm a z ∧ Complex.orientation.areaForm z b + Complex.orientation.areaForm a z ≤ Complex.orientation.areaForm a b := by
  let d := Complex.orientation.areaForm a b
  have hrepr : (Complex.orientation.areaForm z b / d) • a + (Complex.orientation.areaForm a z / d) • b = z := by
    exact cross_decomposition a b z hd.ne'
  constructor
  · intro hz
    rw [← triangleMap_hull_image] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    rw [Subtype.range_val_subtype] at hu
    change 0 ≤ u.re ∧ 0 ≤ u.im ∧ u.re+u.im ≤ 1 at hu
    simp only [triangleMap_apply,Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,Complex.add_re,Complex.add_im,Complex.smul_re,
      Complex.smul_im,smul_eq_mul] at *
    exact ⟨by nlinarith [mul_nonneg hu.1 hd.le],
      by nlinarith [mul_nonneg hu.2.1 hd.le],
      by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2.2) hd.le]⟩
  · rintro ⟨h1,h2,h3⟩
    rw [← hrepr]
    rw [← triangleMap_hull_image]
    refine ⟨⟨Complex.orientation.areaForm z b / d,Complex.orientation.areaForm a z / d⟩,?_,
      triangleMap_apply _ _ _⟩
    rw [Subtype.range_val_subtype]
    change 0 ≤ Complex.orientation.areaForm z b / d ∧ 0 ≤ Complex.orientation.areaForm a z / d ∧ Complex.orientation.areaForm z b / d+Complex.orientation.areaForm a z / d ≤ 1
    refine ⟨div_nonneg h1 hd.le,div_nonneg h2 hd.le,?_⟩
    rw [← add_div,div_le_one hd]
    exact h3
private lemma adjacent_triangles_spoke_interior (a b c : ℂ) (hab : 0 < Complex.orientation.areaForm a b) (hbc : 0 < Complex.orientation.areaForm b c) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : t • b ∈ interior (convexHull ℝ {0,a,b} ∪ convexHull ℝ {0,b,c}) := by
  let U : Set ℂ := {z | 0 < Complex.orientation.areaForm a z ∧ 0 < Complex.orientation.areaForm z c ∧
    Complex.orientation.areaForm z b+Complex.orientation.areaForm a z < Complex.orientation.areaForm a b ∧ Complex.orientation.areaForm z c+Complex.orientation.areaForm b z < Complex.orientation.areaForm b c}
  have ho : IsOpen U := (isOpen_lt continuous_const (cross_continuous_right a)).inter
    ((isOpen_lt continuous_const (cross_continuous_left c)).inter
      ((isOpen_lt ((cross_continuous_left b).add (cross_continuous_right a)) continuous_const).inter
        (isOpen_lt ((cross_continuous_left c).add (cross_continuous_right b)) continuous_const)))
  have hm : t • b ∈ U := by
    change 0 < Complex.orientation.areaForm a (t • b) ∧ 0 < Complex.orientation.areaForm (t • b) c ∧
      Complex.orientation.areaForm (t • b) b+Complex.orientation.areaForm a (t • b) < Complex.orientation.areaForm a b ∧
      Complex.orientation.areaForm (t • b) c+Complex.orientation.areaForm b (t • b) < Complex.orientation.areaForm b c
    simp only [cross_smul_left,cross_smul_right,Orientation.areaForm_apply_self,mul_zero,zero_add,add_zero]
    exact ⟨mul_pos ht0 hab,mul_pos ht0 hbc,by nlinarith,by nlinarith⟩
  apply interior_mono (s := U) _ (mem_interior_iff_mem_nhds.mpr (ho.mem_nhds hm))
  intro z hz
  by_cases h : 0 ≤ Complex.orientation.areaForm b z
  · exact Or.inr ((triangle_mem_iff_cross b c z hbc).mpr ⟨hz.2.1.le,h,hz.2.2.2.le⟩)
  · exact Or.inl ((triangle_mem_iff_cross a b z hab).mpr
      ⟨by rw [Orientation.areaForm_swap Complex.orientation z b];linarith,hz.1.le,hz.2.2.1.le⟩)
private lemma aeDisjoint_disjoint_interior_of_regular {s t : Set ℂ} (hd : AEDisjoint volume s t) (ht : closure (interior t) = t) : Disjoint (interior s) t := by
  have hd' : Disjoint (interior s) (interior t) := by
    rw [disjoint_iff_inter_eq_empty]
    apply (isOpen_interior.inter isOpen_interior).eq_empty_of_measure_zero (μ := volume)
    exact measure_mono_null (inter_subset_inter interior_subset interior_subset) hd
  rw [← ht]
  exact hd'.closure_right isOpen_interior
private noncomputable def referenceTriangle : Set (ℝ × ℝ) :=
  regionBetween (fun _ : ℝ => 0) (fun x : ℝ => 1-x) (Ioo 0 1)
private noncomputable def complexReferenceTriangle : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' referenceTriangle
private lemma referenceTriangle_volume : volume referenceTriangle = ENNReal.ofReal (1/2 : ℝ) := by
  have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioo 0 1) := by
    exact integrableOn_zero
  have h1 : IntegrableOn (fun x : ℝ => (1 : ℝ)-x) (Ioo 0 1) := by
    exact ((continuous_const.sub continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hv := volume_regionBetween_eq_integral h0 h1 measurableSet_Ioo (by
    intro x hx
    linarith [hx.2])
  have hi : (∫ x in Ioo (0 : ℝ) 1, ((fun x : ℝ => (1 : ℝ)-x) - (fun _ : ℝ => (0 : ℝ))) x) = 1/2 := by
    simp only [Pi.sub_apply, sub_zero]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hsub := intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
      (g := fun x : ℝ => x) (a := 0) (b := 1) (μ := volume)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
    rw [hsub]
    rw [intervalIntegral.integral_const, integral_id]
    norm_num
  simpa only [referenceTriangle, MeasureTheory.Measure.volume_eq_prod, hi] using hv
private lemma complexReferenceTriangle_volume : volume complexReferenceTriangle = ENNReal.ofReal (1/2 : ℝ) := by
  rw [complexReferenceTriangle, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    referenceTriangle_volume]
private lemma linear_fiber_volume_zero (f : ℂ →ₗ[ℝ] ℝ) (x : ℂ) (hker : f.ker ≠ ⊤) : volume {z : ℂ | f z = f x} = 0 := by
  have heq : {z : ℂ | f z = f x} = (fun z : ℂ => z+x) '' (f.ker : Set ℂ) := by
    ext z
    constructor
    · intro hz
      refine ⟨z-x, ?_, by simp⟩
      change f (z-x) = 0
      rw [map_sub, hz, sub_self]
    · rintro ⟨y, hy, rfl⟩
      change f (y+x) = f x
      rw [map_add, (show f y = 0 from hy), zero_add]
  rw [heq, image_add_right, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume f.ker hker
private lemma imaginary_axis_null : volume {z : ℂ | z.re = 0} = 0 := by
  have hk : Complex.reLm.ker ≠ ⊤ := by
    intro h
    have hi : (1 : ℂ) ∈ Complex.reLm.ker := h.symm ▸ Submodule.mem_top
    simpa using hi
  exact linear_fiber_volume_zero Complex.reLm 0 hk
private lemma real_axis_null : volume {z : ℂ | z.im = 0} = 0 := by
  have hk : Complex.imLm.ker ≠ ⊤ := by
    intro h
    have hi : Complex.I ∈ Complex.imLm.ker := h.symm ▸ Submodule.mem_top
    simpa using hi
  exact linear_fiber_volume_zero Complex.imLm 0 hk
private lemma reference_diagonal_null : volume {z : ℂ | z.re+z.im = 1} = 0 := by
  let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm + Complex.imLm
  have hk : f.ker ≠ ⊤ := by
    intro h
    have hi : (1 : ℂ) ∈ f.ker := h.symm ▸ Submodule.mem_top
    change f 1 = 0 at hi
    simpa [f] using hi
  simpa [f] using linear_fiber_volume_zero f 1 hk
private lemma closedReferenceTriangle_volume : volume (Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) = ENNReal.ofReal (1/2 : ℝ) := by
  have hsub : complexReferenceTriangle ⊆ (Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) := by
    rw [Subtype.range_val_subtype]
    intro z hz
    change z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) (1-z.re) at hz
    change 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re+z.im ≤ 1
    exact ⟨hz.1.1.le, hz.2.1.le, by linarith [hz.2.2]⟩
  have hnull : volume ((Complex.measurableEquivRealProd ⁻¹' Set.range (Subtype.val : D5.S3.Geometry.Gluing.CyclicTriangleDisk.Triangle → ℝ × ℝ)) \ complexReferenceTriangle) = 0 := by
    rw [Subtype.range_val_subtype]
    apply measure_mono_null (t := {z : ℂ | z.re = 0} ∪ {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re+z.im = 1})
    · rintro z ⟨hz, hn⟩
      change 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re+z.im ≤ 1 at hz
      simp only [mem_union, mem_setOf_eq]
      by_contra hc
      push_neg at hc
      apply hn
      change z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) (1-z.re)
      have hxp : 0 < z.re := lt_of_le_of_ne hz.1 hc.1.1.symm
      have hyp : 0 < z.im := lt_of_le_of_ne hz.2.1 hc.1.2.symm
      have hsum : z.re+z.im < 1 := lt_of_le_of_ne hz.2.2 hc.2
      exact ⟨⟨hxp, by linarith⟩, ⟨hyp, by linarith⟩⟩
    · exact measure_union_null (measure_union_null imaginary_axis_null real_axis_null) reference_diagonal_null
  rw [← measure_eq_measure_of_null_sdiff hsub hnull, complexReferenceTriangle_volume]
private noncomputable def referenceCap : Set (ℝ × ℝ) :=
  regionBetween (fun _ : ℝ => 0) (fun x : ℝ => 1-x) (Ioo (1/2) 1)
noncomputable def complexCap : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (regionBetween (Function.const ℝ 0) (fun x : ℝ => 1-x) (Ioo (1/2) 1))
private lemma referenceCap_isOpen : IsOpen referenceCap := by
  unfold referenceCap regionBetween
  change IsOpen {p : ℝ × ℝ | ((1/2 : ℝ) < p.1 ∧ p.1 < 1) ∧
    (0 < p.2 ∧ p.2 < 1-p.1)}
  exact ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd (continuous_const.sub continuous_fst)))
lemma complexCap_isOpen : IsOpen complexCap := by
  exact referenceCap_isOpen.preimage Complex.equivRealProdCLM.continuous
private lemma referenceCap_volume : volume referenceCap = ENNReal.ofReal (1/8 : ℝ) := by
  have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioo (1/2) 1) :=
    integrableOn_zero
  have h1 : IntegrableOn (fun x : ℝ => (1 : ℝ)-x) (Ioo (1/2) 1) :=
    ((continuous_const.sub continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hv := volume_regionBetween_eq_integral h0 h1 measurableSet_Ioo (by
    intro x hx
    linarith [hx.2])
  have hi : (∫ x in Ioo (1/2 : ℝ) 1, ((fun x : ℝ => (1 : ℝ)-x) - (fun _ : ℝ => (0 : ℝ))) x) = 1/8 := by
    simp only [Pi.sub_apply, sub_zero]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
    have hsub := intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
      (g := fun x : ℝ => x) (a := 1/2) (b := 1) (μ := volume)
      intervalIntegrable_const (continuous_id.intervalIntegrable (1/2) 1)
    rw [hsub, intervalIntegral.integral_const, integral_id]
    norm_num
  simpa only [referenceCap, MeasureTheory.Measure.volume_eq_prod, hi] using hv
lemma complexCap_volume : volume complexCap = ENNReal.ofReal (1/8 : ℝ) := by
  rw [complexCap, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  change volume referenceCap = _
  exact referenceCap_volume
private theorem complex_norm_sub_sq (x y : ℂ) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * conj y).re := by
  simpa only [Complex.sq_norm] using Complex.normSq_sub x y
private lemma crossMap_ker_ne_top (u : ℂ) (hu : u ≠ 0) : (Complex.orientation.areaForm u).ker ≠ ⊤ := by
  intro h
  have h1 : (1:ℂ) ∈ (Complex.orientation.areaForm u).ker := h.symm ▸ Submodule.mem_top
  have hI : Complex.I ∈ (Complex.orientation.areaForm u).ker := h.symm ▸ Submodule.mem_top
  change Complex.orientation.areaForm u 1 = 0 at h1
  change Complex.orientation.areaForm u Complex.I = 0 at hI
  simp [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im] at h1 hI
  apply hu
  exact Complex.ext hI h1
lemma cross_polarPoint (A B θ φ : ℝ) : Complex.orientation.areaForm (circleMap 0 A θ) (circleMap 0 B φ) = A*B*Real.sin (φ-θ) := by
  simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,circleMap_zero_re,circleMap_zero_im,Real.sin_sub]
  ring
private lemma triangle_outer_edge_iff (a b z : ℂ) (hd : 0 < Complex.orientation.areaForm a b) (h1 : 0 ≤ Complex.orientation.areaForm z b) (h2 : 0 ≤ Complex.orientation.areaForm a z) : z ∈ segment ℝ a b ↔ Complex.orientation.areaForm z b+Complex.orientation.areaForm a z = Complex.orientation.areaForm a b := by
  constructor
  · rintro ⟨α,β,hα,hβ,hs,rfl⟩
    simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
      smul_eq_mul] at *
    linear_combination (a.re*b.im-a.im*b.re)*hs
  · intro hs
    refine ⟨Complex.orientation.areaForm z b/Complex.orientation.areaForm a b,Complex.orientation.areaForm a z/Complex.orientation.areaForm a b,
      div_nonneg h1 hd.le,div_nonneg h2 hd.le,?_,cross_decomposition a b z hd.ne'⟩
    rw [← add_div,hs,div_self hd.ne']
private lemma triangle_strict_mem_interior (a b z : ℂ) (hd : 0 < Complex.orientation.areaForm a b) (h1 : 0 < Complex.orientation.areaForm z b) (h2 : 0 < Complex.orientation.areaForm a z) (h3 : Complex.orientation.areaForm z b+Complex.orientation.areaForm a z < Complex.orientation.areaForm a b) : z ∈ interior (convexHull ℝ {0,a,b}) := by
  let U : Set ℂ := {w | 0 < Complex.orientation.areaForm w b ∧ 0 < Complex.orientation.areaForm a w ∧ Complex.orientation.areaForm w b+Complex.orientation.areaForm a w < Complex.orientation.areaForm a b}
  have ho : IsOpen U := (isOpen_lt continuous_const (cross_continuous_left b)).inter
    ((isOpen_lt continuous_const (cross_continuous_right a)).inter
      (isOpen_lt ((cross_continuous_left b).add (cross_continuous_right a)) continuous_const))
  exact interior_mono (s := U) (fun w hw => (triangle_mem_iff_cross a b w hd).mpr
    ⟨hw.1.le,hw.2.1.le,hw.2.2.le⟩) (mem_interior_iff_mem_nhds.mpr (ho.mem_nhds ⟨h1,h2,h3⟩))
private lemma finite_cyclic_fan_interior_of_not_trace {t : ℕ} [NeZero t] (v : Fin t → ℂ) (hd : ∀ i, 0 < Complex.orientation.areaForm (v i) (v (i+1))) (hzero : (0:ℂ) ∈ interior (⋃ i,convexHull ℝ {0,v i,v (i+1)})) (z : ℂ) (hz : z ∈ ⋃ i,convexHull ℝ {0,v i,v (i+1)}) (hne : z ∉ ⋃ i,segment ℝ (v i) (v (i+1))) : z ∈ interior (⋃ i,convexHull ℝ {0,v i,v (i+1)}) := by
  by_cases hz0 : z = 0
  · simpa [hz0] using hzero
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  have hp := (triangle_mem_iff_cross _ _ _ (hd i)).mp hi
  have hlt : Complex.orientation.areaForm z (v (i+1))+Complex.orientation.areaForm (v i) z < Complex.orientation.areaForm (v i) (v (i+1)) := by
    apply lt_of_le_of_ne hp.2.2
    intro he
    exact hne (mem_iUnion.mpr ⟨i,(triangle_outer_edge_iff _ _ _ (hd i) hp.1 hp.2.1).mpr he⟩)
  have hre := cross_decomposition (v i) (v (i+1)) z (hd i).ne'
  by_cases h1 : Complex.orientation.areaForm z (v (i+1)) = 0
  · have hrz : z = (Complex.orientation.areaForm (v i) z/Complex.orientation.areaForm (v i) (v (i+1))) • v (i+1) := by
      simpa only [h1,zero_div,zero_smul,zero_add] using hre.symm
    have hpz : 0 < Complex.orientation.areaForm (v i) z := lt_of_le_of_ne hp.2.1 (by
      intro he
      apply hz0
      rw [hrz,← he,zero_div,zero_smul])
    have hq : Complex.orientation.areaForm (v i) z/Complex.orientation.areaForm (v i) (v (i+1)) < 1 := by
      rw [div_lt_one (hd i)]
      simpa [h1] using hlt
    rw [hrz]
    apply interior_mono (s := convexHull ℝ {0,v i,v (i+1)} ∪
      convexHull ℝ {0,v (i+1),v (i+1+1)}) _
      (adjacent_triangles_spoke_interior _ _ _ (hd i) (hd (i+1)) _
        (div_pos hpz (hd i)) hq)
    exact union_subset (subset_iUnion (fun j => convexHull ℝ {0,v j,v (j+1)}) i) (subset_iUnion (fun j => convexHull ℝ {0,v j,v (j+1)}) (i+1))
  · by_cases h2 : Complex.orientation.areaForm (v i) z = 0
    · have hrz : z = (Complex.orientation.areaForm z (v (i+1))/Complex.orientation.areaForm (v i) (v (i+1))) • v i := by
        simpa only [h2,zero_div,zero_smul,add_zero] using hre.symm
      have hpz : 0 < Complex.orientation.areaForm z (v (i+1)) := lt_of_le_of_ne hp.1 (Ne.symm h1)
      have hq : Complex.orientation.areaForm z (v (i+1))/Complex.orientation.areaForm (v i) (v (i+1)) < 1 := by
        rw [div_lt_one (hd i)]
        simpa [h2] using hlt
      have hprev : i-1+1 = i := sub_add_cancel i 1
      have hs := adjacent_triangles_spoke_interior (v (i-1)) (v i) (v (i+1))
        (by simpa only [hprev] using hd (i-1)) (hd i) _ (div_pos hpz (hd i)) hq
      rw [hrz]
      apply interior_mono (s := convexHull ℝ {0,v (i-1),v i} ∪
        convexHull ℝ {0,v i,v (i+1)}) _ hs
      apply union_subset
      · simpa only [hprev] using subset_iUnion (fun j => convexHull ℝ {0,v j,v (j+1)}) (i-1)
      · exact subset_iUnion (fun j => convexHull ℝ {0,v j,v (j+1)}) i
    · exact interior_mono (subset_iUnion (fun j => convexHull ℝ {0,v j,v (j+1)}) i)
        (triangle_strict_mem_interior _ _ _ (hd i)
          (lt_of_le_of_ne hp.1 (Ne.symm h1))
          (lt_of_le_of_ne hp.2.1 (Ne.symm h2)) hlt)
private lemma triangle_interior_nonempty (a b : ℂ) (hd : 0 < Complex.orientation.areaForm a b) : (interior (convexHull ℝ {0,a,b})).Nonempty := by
  refine ⟨(1/3:ℝ) • a+(1/3:ℝ) • b,triangle_strict_mem_interior a b _ hd ?_ ?_ ?_⟩
  all_goals simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
    smul_eq_mul] at *
  all_goals nlinarith
private lemma triangle_closure_interior (a b : ℂ) (hd : 0 < Complex.orientation.areaForm a b) : closure (interior (convexHull ℝ {0,a,b})) = convexHull ℝ {0,a,b} := by
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (triangle_interior_nonempty a b hd)]
  exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp : ({0,a,b}:Set ℂ).Finite)).isClosed.closure_eq
private lemma finite_fan_closure_interior {ι : Type*} [Fintype ι] (a b : ι → ℂ) (hd : ∀ i, 0 < Complex.orientation.areaForm (a i) (b i)) : closure (interior (⋃ i,convexHull ℝ {0,a i,b i})) = ⋃ i,convexHull ℝ {0,a i,b i} := by
  have hc : IsClosed (⋃ i,convexHull ℝ {0,a i,b i}) := isClosed_iUnion_of_finite (fun i =>
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp : ({0,a i,b i}:Set ℂ).Finite)).isClosed)
  apply subset_antisymm (closure_minimal interior_subset hc)
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  apply closure_mono (interior_mono (subset_iUnion (fun j => convexHull ℝ {0,a j,b j}) i))
  rwa [triangle_closure_interior _ _ (hd i)]
private lemma triangle_strict_cone_meets_interior (a b z : ℂ) (hd : 0 < Complex.orientation.areaForm a b) (h1 : 0 < Complex.orientation.areaForm z b) (h2 : 0 < Complex.orientation.areaForm a z) : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t • z ∈ interior (convexHull ℝ {0,a,b}) := by
  obtain ⟨c,hc,hc'⟩ := exists_pos_mul_lt hd (Complex.orientation.areaForm z b+Complex.orientation.areaForm a z)
  let t : ℝ := min c (1/2)
  have ht : 0 < t := lt_min hc (by norm_num)
  refine ⟨t,ht,le_trans (min_le_right _ _) (by norm_num),
    triangle_strict_mem_interior a b (t • z) hd ?_ ?_ ?_⟩
  · rw [cross_smul_left]
    exact mul_pos ht h1
  · rw [cross_smul_right]
    exact mul_pos ht h2
  · rw [cross_smul_left,cross_smul_right,← mul_add]
    calc
      t*(Complex.orientation.areaForm z b+Complex.orientation.areaForm a z) ≤ c*(Complex.orientation.areaForm z b+Complex.orientation.areaForm a z) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
      _ < Complex.orientation.areaForm a b := by simpa only [mul_comm] using hc'
private lemma triangle_open_edge_not_interior_fan {ι : Type*} [Fintype ι] (a b : ι → ℂ) (hd : ∀ i, 0 < Complex.orientation.areaForm (a i) (b i)) (had : Pairwise (fun i j => AEDisjoint volume (convexHull ℝ {0,a i,b i}) (convexHull ℝ {0,a j,b j}))) (i : ι) (z : ℂ) (hz : z ∈ openSegment ℝ (a i) (b i)) : z ∉ interior (⋃ j,convexHull ℝ {0,a j,b j}) := by
  obtain ⟨α,β,hα,hβ,hs,rfl⟩ := hz
  let z := α • a i+β • b i
  have hz1 : 0 < Complex.orientation.areaForm z (b i) := by
    have he : Complex.orientation.areaForm z (b i) = α*Complex.orientation.areaForm (a i) (b i) := by
      dsimp only [z]
      simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
      ring
    rw [he]
    exact mul_pos hα (hd i)
  have hz2 : 0 < Complex.orientation.areaForm (a i) z := by
    have he : Complex.orientation.areaForm (a i) z = β*Complex.orientation.areaForm (a i) (b i) := by
      dsimp only [z]
      simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
      ring
    rw [he]
    exact mul_pos hβ (hd i)
  have hzs : Complex.orientation.areaForm z (b i)+Complex.orientation.areaForm (a i) z = Complex.orientation.areaForm (a i) (b i) := by
    apply (triangle_outer_edge_iff _ _ _ (hd i) hz1.le hz2.le).mp
    exact ⟨α,β,hα.le,hβ.le,hs,rfl⟩
  change z ∉ interior (⋃ j,convexHull ℝ {0,a j,b j})
  intro hzint
  have hc : Filter.Tendsto (fun t : ℝ => t • z) (nhds 1) (nhds z) := by
    exact Filter.Tendsto.one_smul_const (fun ⦃U⦄ a => a) z
  obtain ⟨s,hs1,hsm⟩ := (hc.eventually_mem (isOpen_interior.mem_nhds hzint)).exists_gt
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  obtain ⟨j,hj⟩ := mem_iUnion.mp (interior_subset hsm)
  by_cases hij : i = j
  · subst j
    have hb := (triangle_mem_iff_cross _ _ _ (hd i)).mp hj
    rw [cross_smul_left,cross_smul_right,← mul_add,hzs] at hb
    nlinarith [mul_pos (sub_pos.mpr hs1) (hd i)]
  · obtain ⟨t,ht0,ht1,hti⟩ := triangle_strict_cone_meets_interior (a i) (b i) (s • z) (hd i)
      (by rw [cross_smul_left];exact mul_pos hs0 hz1)
      (by rw [cross_smul_right];exact mul_pos hs0 hz2)
    have htj : t • (s • z) ∈ convexHull ℝ {0,a j,b j} :=
      (convex_convexHull ℝ _).smul_mem_of_zero_mem (subset_convexHull ℝ _ (by simp)) hj ⟨ht0.le,ht1⟩
    exact (disjoint_left.mp (aeDisjoint_disjoint_interior_of_regular (had hij)
      (triangle_closure_interior _ _ (hd j)))) hti htj
lemma finite_cyclic_fan_frontier {t : ℕ} [NeZero t] (v : Fin t → ℂ) (hd : ∀ i, 0 < Complex.orientation.areaForm (v i) (v (i+1))) (hzero : (0:ℂ) ∈ interior (⋃ i,convexHull ℝ {0,v i,v (i+1)})) (had : Pairwise (fun i j => AEDisjoint volume (convexHull ℝ {0,v i,v (i+1)}) (convexHull ℝ {0,v j,v (j+1)}))) : frontier (interior (⋃ i,convexHull ℝ {0,v i,v (i+1)})) = ⋃ i,segment ℝ (v i) (v (i+1)) := by
  let F : Set ℂ := ⋃ i,convexHull ℝ {0,v i,v (i+1)}
  have hcl : closure (interior F) = F := finite_fan_closure_interior v _ hd
  have he : frontier (interior F) = F \ interior F := by
    rw [frontier,interior_interior,hcl]
  apply subset_antisymm
  · rw [he]
    rintro z ⟨hz,hzn⟩
    by_contra hn
    exact hzn (finite_cyclic_fan_interior_of_not_trace v hd hzero z hz hn)
  · apply iUnion_subset
    intro i
    have hsub : openSegment ℝ (v i) (v (i+1)) ⊆ frontier (interior F) := by
      intro z hz
      rw [he]
      refine ⟨?_,triangle_open_edge_not_interior_fan v _ hd had i z hz⟩
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
        (openSegment_subset_segment ℝ _ _ hz)
    rw [← closure_openSegment]
    exact closure_minimal hsub isClosed_frontier
private lemma integrableOn_continuous_bounded {E : Type*} [NormedAddCommGroup E] {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) {f : ℂ → E} (hf : Continuous f) : IntegrableOn f Ω := by
  exact (hf.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
private lemma integral_error_eq_secondMoment_add (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (p : Polynomial ℂ) (hM : (∫ z in Ω, z * p.eval z) = 0) : (∫ z in Ω, ‖(starRingEnd ℂ) z - p.eval z‖ ^ 2) = (∫ z in Ω, ‖z‖ ^ 2) + (∫ z in Ω, ‖p.eval z‖ ^ 2) := by
  have hpoint : (fun z : ℂ => ‖(starRingEnd ℂ) z - p.eval z‖ ^ 2) =
      fun z : ℂ => ‖z‖ ^ 2 + ‖p.eval z‖ ^ 2 - 2 * (z * p.eval z).re := by
    funext z
    rw [complex_norm_sub_sq, Complex.norm_conj]
    have hprod : conj z * conj (p.eval z) = conj (z * p.eval z) :=
      (map_mul (starRingEnd ℂ) z (p.eval z)).symm
    rw [hprod, Complex.conj_re]
  have hi : IntegrableOn (fun z : ℂ => ‖z‖ ^ 2) Ω :=
    integrableOn_continuous_bounded hb (by fun_prop)
  have hp : IntegrableOn (fun z : ℂ => ‖p.eval z‖ ^ 2) Ω :=
    integrableOn_continuous_bounded hb (by fun_prop)
  have hc : IntegrableOn (fun z : ℂ => z * p.eval z) Ω :=
    integrableOn_continuous_bounded hb (by fun_prop)
  have hcre : IntegrableOn (fun z : ℂ => (z * p.eval z).re) Ω :=
    integrableOn_continuous_bounded hb (by fun_prop)
  have hcrezero : (∫ z in Ω, (z * p.eval z).re) = 0 := by
    simpa [hM] using (integral_re hc)
  rw [hpoint]
  have hsub := integral_sub (hi.add hp) (hcre.const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hi hp, integral_const_mul, hcrezero]
  ring
theorem integral_pow_eq_zero_of_rotation (a : Circle) (k : ℕ) (Ω : Set ℂ) (hΩ : (rotation a) '' Ω = Ω) (hneq : (a : ℂ) ^ k ≠ 1) : (∫ z in Ω, z ^ k) = 0 := by
  have hmp := LinearIsometryEquiv.measurePreserving (rotation a)
  have he := hmp.setIntegral_image_emb
      (rotation a).toHomeomorph.measurableEmbedding (fun z : ℂ => z ^ k) Ω
  rw [hΩ] at he
  have hpow : ∀ z : ℂ, ((rotation a) z) ^ k = ((a : ℂ) ^ k) • z ^ k := by
    intro z
    rw [rotation_apply, mul_pow]
    simp only [smul_eq_mul]
  have he' : (∫ z in Ω, z ^ k) =
      ∫ z in Ω, ((a : ℂ) ^ k) • z ^ k := by
    simpa only [hpow] using he
  rw [MeasureTheory.integral_smul] at he'
  have hz : ((1 : ℂ) - (a : ℂ)^k) * (∫ z in Ω, z^k) = 0 := by
    linear_combination he'
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exfalso
    apply hneq
    exact (sub_eq_zero.mp hzero).symm
  · exact hzero
private lemma integral_z_mul_poly_eq_zero (N : ℕ) (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (hM : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → (∫ z in Ω, z ^ k) = 0) (p : Polynomial.degreeLE ℂ (N : WithBot ℕ)) : (∫ z in Ω, z * (p : Polynomial ℂ).eval z) = 0 := by
  have hpdeg : (p : Polynomial ℂ).natDegree < N + 1 := by
    have hdeg := Polynomial.mem_degreeLE.mp p.property
    have hd := Polynomial.natDegree_le_iff_degree_le.mpr hdeg
    omega
  have hfun : (fun z : ℂ => z * (p : Polynomial ℂ).eval z) =
      fun z : ℂ => ∑ j ∈ Finset.range (N + 1), (p : Polynomial ℂ).coeff j * z ^ (j + 1) := by
    funext z
    rw [Polynomial.eval_eq_sum_range' hpdeg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [integral_const_mul, hM (j+1) (by omega) (by omega)]
    simp
  · intro j hj
    apply integrableOn_continuous_bounded hb
    fun_prop
noncomputable def rhoN (N : ℕ) (Ω : Set ℂ) : ℝ :=
  ⨅ p : Polynomial.degreeLE ℂ (N : WithBot ℕ),
    ∫ z in Ω, ‖(starRingEnd ℂ) z - (p : Polynomial ℂ).eval z‖ ^ 2
theorem no_max_of_unbounded_family (N n : ℕ) (F : ℕ → Set ℂ) (hreg : ∀ r, IsPolygonRegion n (F r)) (hvol : ∀ r, volume (F r) = 1) (hunbd : ∀ C : ℝ, ∃ r, C < rhoN N (F r)) : ¬ ∃ P : Set ℂ, IsPolygonRegion n P ∧ volume P = 1 ∧ ∀ Q : Set ℂ, IsPolygonRegion n Q → volume Q = 1 → rhoN N Q ≤ rhoN N P := by
  rintro ⟨P, hP, hPvol, hmax⟩
  obtain ⟨r, hr⟩ := hunbd (rhoN N P)
  have hle := hmax (F r) (hreg r) (hvol r)
  linarith
private lemma norm_sq_smul_add (a b : ℂ) (s t : ℝ) : ‖s • a + t • b‖^2 = s^2*‖a‖^2 + t^2*‖b‖^2 + 2*s*t*(a * conj b).re := by
  rw [Complex.sq_norm, Complex.normSq_add]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.smul_re, Complex.smul_im,
    smul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
lemma norm_sq_smul_add_ge (a b : ℂ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hdot : 0 ≤ (a * conj b).re) : s^2*‖a‖^2 ≤ ‖s • a + t • b‖^2 := by
  rw [norm_sq_smul_add]
  have h1 : 0 ≤ t^2*‖b‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ 2*s*t*(a * conj b).re := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hs) ht) hdot
  linarith
private lemma polarPoint_add_period (A θ : ℝ) (n : ℕ) : circleMap 0 A (θ+(n:ℝ)*(2*Real.pi)) = circleMap 0 A θ := by
  exact (periodic_circleMap 0 A).nat_mul n θ
private lemma polarPoint_nat_mod (A θ : ℝ) (t k : ℕ) (hperiod : (t:ℝ)*θ = 2*Real.pi) : circleMap 0 A (((k%t:ℕ):ℝ)*θ) = circleMap 0 A ((k:ℝ)*θ) := by
  have hp : Function.Periodic (fun n : ℕ => circleMap 0 A ((n:ℝ)*θ)) t := by
    intro n
    push_cast
    rw [add_mul, hperiod]
    exact periodic_circleMap (0:ℂ) A ((n:ℝ)*θ)
  exact hp.map_mod_nat k
private lemma polarPoint_theta_period (m : ℕ) (hm : 0 < m) : ((2*m:ℕ):ℝ)*(Real.pi/(m:ℝ)) = 2*Real.pi := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
noncomputable def polarVertex (m : ℕ) (r : Fin (2*m) → ℝ) (i : Fin (2*m)) : ℂ :=
  circleMap 0 (r i) ((i.val:ℝ)*(Real.pi/(m:ℝ)))
private lemma polarVertex_before_cross_nonpos (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 ≤ r i) (i : Fin (2*m)) : Complex.orientation.areaForm (circleMap 0 1 (((i.val:ℝ)+1)*(Real.pi/(m:ℝ)))) (polarVertex m r i) ≤ 0 := by
  unfold polarVertex
  rw [cross_polarPoint]
  have harg : ((i.val:ℝ)*(Real.pi/(m:ℝ)))-(((i.val:ℝ)+1)*(Real.pi/(m:ℝ))) =
      -(Real.pi/(m:ℝ)) := by ring
  rw [harg,Real.sin_neg]
  apply mul_nonpos_of_nonneg_of_nonpos (by simpa using hr i)
  apply neg_nonpos.mpr
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    exact div_le_self Real.pi_pos.le hm1
private lemma polarVertex_next (m : ℕ) [NeZero m] (r : Fin (2*m) → ℝ) (i : Fin (2*m)) : polarVertex m r (i+1) = circleMap 0 (r (i+1)) (((i.val:ℝ)+1)*(Real.pi/(m:ℝ))) := by
  have h1 : ((1:Fin (2*m)):ℕ) = 1 := by
    change 1%(2*m) = 1
    exact Nat.mod_eq_of_lt (by have := NeZero.pos m;omega)
  have hv : (i+1).val = (i.val+1)%(2*m) := by
    rw [Fin.val_add,h1]
  unfold polarVertex
  rw [hv,polarPoint_nat_mod _ _ _ _ (polarPoint_theta_period m (NeZero.pos m))]
  push_cast
  rfl
private lemma polarVertex_next_cross_self (m : ℕ) [NeZero m] (r : Fin (2*m) → ℝ) (i : Fin (2*m)) : Complex.orientation.areaForm (circleMap 0 1 (((i.val:ℝ)+1)*(Real.pi/(m:ℝ)))) (polarVertex m r (i+1)) = 0 := by
  rw [polarVertex_next,cross_polarPoint,sub_self,Real.sin_zero,mul_zero]
private lemma polar_angle_representation (z : ℂ) : ∃ φ : ℝ, 0 ≤ φ ∧ φ < 2*Real.pi ∧ circleMap 0 ‖z‖ φ = z := by
  obtain ⟨φ, hφ, e⟩ := D5.S3.Geometry.Gluing.CyclicTriangleDisk.positive_circle_angle (z := z)
  exact ⟨φ, hφ.1, hφ.2, e⟩
private lemma triangles_aeDisjoint_of_cross_separation (u a b c d : ℂ) (hu : u ≠ 0) (ha : Complex.orientation.areaForm u a ≤ 0) (hb : Complex.orientation.areaForm u b ≤ 0) (hc : 0 ≤ Complex.orientation.areaForm u c) (hd : 0 ≤ Complex.orientation.areaForm u d) : AEDisjoint volume (convexHull ℝ {0,a,b}) (convexHull ℝ {0,c,d}) := by
  have hleft : convexHull ℝ {0,a,b} ⊆ {z : ℂ | Complex.orientation.areaForm u z ≤ 0} := by
    apply convexHull_min _ ((convex_Iic (0:ℝ)).linear_preimage (Complex.orientation.areaForm u))
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · simp [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    · change Complex.orientation.areaForm u z ≤ 0
      exact ha
    · change Complex.orientation.areaForm u z ≤ 0
      exact hb
  have hright : convexHull ℝ {0,c,d} ⊆ {z : ℂ | 0 ≤ Complex.orientation.areaForm u z} := by
    apply convexHull_min _ ((convex_Ici (0:ℝ)).linear_preimage (Complex.orientation.areaForm u))
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · simp [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    · change 0 ≤ Complex.orientation.areaForm u z
      exact hc
    · change 0 ≤ Complex.orientation.areaForm u z
      exact hd
  change volume (convexHull ℝ {0,a,b} ∩ convexHull ℝ {0,c,d}) = 0
  apply measure_mono_null (t := {z : ℂ | Complex.orientation.areaForm u z = Complex.orientation.areaForm u 0})
  · rintro z ⟨hz,hz'⟩
    change Complex.orientation.areaForm u z = Complex.orientation.areaForm u 0
    rw [map_zero]
    exact le_antisymm (hleft hz) (hright hz')
  · exact linear_fiber_volume_zero _ _ (crossMap_ker_ne_top u hu)
private lemma polar_cyclic_forward_aeDisjoint (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 ≤ r i) (i j : Fin (2*m)) (s : ℕ) (hs : s = 0 ∨ s = 2*m) (hlo : (i.val:ℝ)+1 ≤ (j.val:ℝ)+(s:ℝ)) (hhi : (j.val:ℝ)+(s:ℝ) ≤ (i.val:ℝ)+(m:ℝ)) : AEDisjoint volume (convexHull ℝ {0,polarVertex m r i,polarVertex m r (i+1)}) (convexHull ℝ {0,polarVertex m r j,polarVertex m r (j+1)}) := by
  let θ : ℝ := Real.pi/(m:ℝ)
  let β : ℝ := ((i.val:ℝ)+1)*θ
  let u : ℂ := circleMap 0 1 β
  have hθ : 0 ≤ θ := by dsimp [θ];positivity
  have hθm : (m:ℝ)*θ = Real.pi := by
    have h := polarPoint_theta_period m (NeZero.pos m)
    push_cast at h
    change (m:ℝ)*(Real.pi/(m:ℝ)) = Real.pi
    linarith
  have hn : ‖u‖ = 1 := by
    simpa only [u, abs_one] using norm_circleMap_zero 1 β
  have hu : u ≠ 0 := by intro hz;rw [hz,norm_zero] at hn;norm_num at hn
  have hj : polarVertex m r j = circleMap 0 (r j) (((j.val:ℝ)+(s:ℝ))*θ) := by
    rcases hs with hs | hs
    · simp [hs,polarVertex,θ]
    · have hper := polarPoint_theta_period m (NeZero.pos m)
      have heq : ((j.val:ℝ)+(s:ℝ))*θ = (j.val:ℝ)*θ+1*(2*Real.pi) := by
        rw [hs]
        dsimp [θ]
        rw [← hper]
        ring
      rw [heq]
      have hp := polarPoint_add_period (r j) ((j.val:ℝ)*θ) 1
      simp only [Nat.cast_one] at hp
      rw [hp]
      rfl
  have hj' : polarVertex m r (j+1) = circleMap 0 (r (j+1)) (((j.val:ℝ)+1+(s:ℝ))*θ) := by
    rw [polarVertex_next]
    rcases hs with hs | hs
    · simp [hs,θ]
    · have hper := polarPoint_theta_period m (NeZero.pos m)
      have heq : ((j.val:ℝ)+1+(s:ℝ))*θ = ((j.val:ℝ)+1)*θ+1*(2*Real.pi) := by
        rw [hs]
        dsimp [θ]
        rw [← hper]
        ring
      rw [heq]
      have hp := polarPoint_add_period (r (j+1)) (((j.val:ℝ)+1)*θ) 1
      simp only [Nat.cast_one] at hp
      rw [hp]
  apply triangles_aeDisjoint_of_cross_separation u _ _ _ _ hu
  · exact polarVertex_before_cross_nonpos m hm r hr i
  · exact (polarVertex_next_cross_self m r i).le
  · rw [hj,cross_polarPoint]
    apply mul_nonneg (by simpa using hr j)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hθ]
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hθ]
  · rw [hj',cross_polarPoint]
    apply mul_nonneg (by simpa using hr (j+1))
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hθ]
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hθ]
lemma polar_cyclic_fan_pairwise_aeDisjoint (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 ≤ r i) : Pairwise (fun i j : Fin (2*m) => AEDisjoint volume (convexHull ℝ {0,polarVertex m r i,polarVertex m r (i+1)}) (convexHull ℝ {0,polarVertex m r j,polarVertex m r (j+1)})) := by
  have hord : ∀ i j : Fin (2*m), i.val < j.val → AEDisjoint volume
      (convexHull ℝ {0,polarVertex m r i,polarVertex m r (i+1)})
      (convexHull ℝ {0,polarVertex m r j,polarVertex m r (j+1)}) := by
    intro i j hij
    by_cases hgap : j.val ≤ i.val+m
    · apply polar_cyclic_forward_aeDisjoint m hm r hr i j 0 (Or.inl rfl)
      · exact_mod_cast (show i.val+1 ≤ j.val by omega)
      · exact_mod_cast hgap
    · apply AEDisjoint.symm
      apply polar_cyclic_forward_aeDisjoint m hm r hr j i (2*m) (Or.inr rfl)
      · exact_mod_cast (show j.val+1 ≤ i.val+2*m by have := j.isLt;omega)
      · exact_mod_cast (show i.val+2*m ≤ j.val+m by omega)
  intro i j hij
  have hv : i.val ≠ j.val := Fin.val_ne_of_ne hij
  by_cases hlt : i.val < j.val
  · exact hord i j hlt
  · exact (hord j i (by omega)).symm
private lemma segments_disjoint_strict_linear (f : ℂ →ₗ[ℝ] ℝ) (a b c d : ℂ) (ha : f a < 0) (hb : f b < 0) (hc : 0 < f c) (hd : 0 < f d) : Disjoint (segment ℝ a b) (segment ℝ c d) := by
  have hl : convexHull ℝ {a,b} ⊆ f ⁻¹' Iio 0 := by
    apply convexHull_min _ ((convex_Iio (0:ℝ)).linear_preimage f)
    intro z hz
    rcases hz with rfl | hz
    · exact ha
    · exact mem_singleton_iff.mp hz ▸ hb
  have hr : convexHull ℝ {c,d} ⊆ f ⁻¹' Ioi 0 := by
    apply convexHull_min _ ((convex_Ioi (0:ℝ)).linear_preimage f)
    intro z hz
    rcases hz with rfl | hz
    · exact hc
    · exact mem_singleton_iff.mp hz ▸ hd
  rw [convexHull_pair] at hl hr
  exact disjoint_left.mpr (fun z hz hz' => (lt_irrefl (0:ℝ)) ((hr hz').trans (hl hz)))
private lemma polar_cyclic_forward_disjoint (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 < r i) (i j : Fin (2*m)) (s : ℕ) (hs : s = 0 ∨ s = 2*m) (hlo : (i.val:ℝ)+2 ≤ (j.val:ℝ)+(s:ℝ)) (hhi : (j.val:ℝ)+(s:ℝ) ≤ (i.val:ℝ)+(m:ℝ)) : Disjoint (segment ℝ (polarVertex m r i) (polarVertex m r (i+1))) (segment ℝ (polarVertex m r j) (polarVertex m r (j+1))) := by
  let θ : ℝ := Real.pi/(m:ℝ)
  let β : ℝ := ((i.val:ℝ)+3/2)*θ
  let u : ℂ := circleMap 0 1 β
  have hθ : 0 < θ := by dsimp [θ];positivity
  have hθm : (m:ℝ)*θ = Real.pi := by
    have h := polarPoint_theta_period m (NeZero.pos m)
    push_cast at h
    change (m:ℝ)*(Real.pi/(m:ℝ)) = Real.pi
    linarith
  have hθ3 : 3*θ ≤ Real.pi := by
    have hm3 : (3:ℝ) ≤ (m:ℝ) := Nat.ofNat_le_cast.mpr hm
    nlinarith [mul_nonneg (sub_nonneg.mpr hm3) hθ.le]
  have hj : polarVertex m r j = circleMap 0 (r j) (((j.val:ℝ)+(s:ℝ))*θ) := by
    rcases hs with hs | hs
    · simp [hs,polarVertex,θ]
    · have heq : ((j.val:ℝ)+(s:ℝ))*θ = (j.val:ℝ)*θ+1*(2*Real.pi) := by
        rw [hs,← polarPoint_theta_period m (NeZero.pos m)]
        dsimp [θ]
        ring
      rw [heq]
      have hp := polarPoint_add_period (r j) ((j.val:ℝ)*θ) 1
      simp only [Nat.cast_one] at hp
      rw [hp]
      rfl
  have hj' : polarVertex m r (j+1) = circleMap 0 (r (j+1)) (((j.val:ℝ)+1+(s:ℝ))*θ) := by
    rw [polarVertex_next]
    rcases hs with hs | hs
    · simp [hs,θ]
    · have heq : ((j.val:ℝ)+1+(s:ℝ))*θ = ((j.val:ℝ)+1)*θ+1*(2*Real.pi) := by
        rw [hs,← polarPoint_theta_period m (NeZero.pos m)]
        dsimp [θ]
        ring
      rw [heq]
      have hp := polarPoint_add_period (r (j+1)) (((j.val:ℝ)+1)*θ) 1
      simp only [Nat.cast_one] at hp
      rw [hp]
  apply segments_disjoint_strict_linear (Complex.orientation.areaForm u)
  · unfold polarVertex
    rw [cross_polarPoint]
    have heq : (i.val:ℝ)*θ-β = -(3/2*θ) := by dsimp [β];ring
    rw [heq,Real.sin_neg,one_mul]
    have hs' := Real.sin_pos_of_pos_of_lt_pi (show 0 < 3/2*θ by positivity) (show 3/2*θ < Real.pi by nlinarith)
    nlinarith [mul_pos (hr i) hs']
  · rw [polarVertex_next,cross_polarPoint]
    have heq : ((i.val:ℝ)+1)*θ-β = -(θ/2) := by dsimp [β];ring
    rw [heq,Real.sin_neg,one_mul]
    have hs' := Real.sin_pos_of_pos_of_lt_pi (show 0 < θ/2 by positivity) (show θ/2 < Real.pi by nlinarith)
    nlinarith [mul_pos (hr (i+1)) hs']
  · rw [hj,cross_polarPoint,one_mul]
    apply mul_pos (hr j)
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hθ.le]
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hθ.le]
  · rw [hj',cross_polarPoint,one_mul]
    apply mul_pos (hr (j+1))
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hθ.le]
    · dsimp [β]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hθ.le]
lemma polar_cyclic_nonadjacent_disjoint (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 < r i) : ∀ i j : Fin (2*m), i ≠ j → j ≠ i+1 → i ≠ j+1 → Disjoint (segment ℝ (polarVertex m r i) (polarVertex m r (i+1))) (segment ℝ (polarVertex m r j) (polarVertex m r (j+1))) := by
  have hval : ∀ i : Fin (2*m), (i+1).val = (i.val+1)%(2*m) := by
    intro i
    have h1 : ((1:Fin (2*m)):ℕ) = 1 := by
      change 1%(2*m) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add,h1]
  have hord : ∀ i j : Fin (2*m), i.val < j.val → j ≠ i+1 → i ≠ j+1 →
      Disjoint (segment ℝ (polarVertex m r i) (polarVertex m r (i+1)))
        (segment ℝ (polarVertex m r j) (polarVertex m r (j+1))) := by
    intro i j hij hji hij'
    by_cases hgap : j.val ≤ i.val+m
    · have hg : i.val+2 ≤ j.val := by
        by_contra hn
        apply hji
        apply Fin.ext
        rw [hval, Nat.mod_eq_of_lt (show i.val+1 < 2*m by have := j.isLt;omega)]
        omega
      apply polar_cyclic_forward_disjoint m hm r hr i j 0 (Or.inl rfl)
      · exact_mod_cast hg
      · exact_mod_cast hgap
    · have hg : j.val+2 ≤ i.val+2*m := by
        by_contra hn
        have hi : i.val = 0 := by have := j.isLt;omega
        have hj : j.val+1 = 2*m := by have := j.isLt;omega
        apply hij'
        apply Fin.ext
        rw [hval,hj,Nat.mod_self,hi]
      apply Disjoint.symm
      apply polar_cyclic_forward_disjoint m hm r hr j i (2*m) (Or.inr rfl)
      · exact_mod_cast hg
      · exact_mod_cast (show i.val+2*m ≤ j.val+m by omega)
  intro i j hij hji hij'
  have hv : i.val ≠ j.val := Fin.val_ne_of_ne hij
  by_cases hlt : i.val < j.val
  · exact hord i j hlt hji hij'
  · exact (hord j i (by omega) hij' hji).symm
lemma polar_fan_conic_coverage (m : ℕ) [NeZero m] (hm : 3 ≤ m) (r : Fin (2*m) → ℝ) (hr : ∀ i, 0 < r i) (z : ℂ) : ∃ i : Fin (2*m), 0 ≤ Complex.orientation.areaForm (polarVertex m r i) z ∧ 0 ≤ Complex.orientation.areaForm z (polarVertex m r (i+1)) := by
  obtain ⟨φ,hφ0,hφlt,hφz⟩ := polar_angle_representation z
  let θ := Real.pi/(m:ℝ)
  have hθ : 0 < θ := by dsimp [θ];positivity
  have ht : ((2*m:ℕ):ℝ)*θ = 2*Real.pi := polarPoint_theta_period m (NeZero.pos m)
  let k : ℕ := ⌊φ/θ⌋₊
  have hklo : (k:ℝ)*θ ≤ φ := by
    have := Nat.floor_le (div_nonneg hφ0 hθ.le)
    exact (le_div_iff₀ hθ).mp this
  have hkhi : φ < ((k:ℝ)+1)*θ := by
    have := Nat.lt_floor_add_one (φ/θ)
    exact (div_lt_iff₀ hθ).mp this
  have hk : k < 2*m := by
    apply Nat.floor_lt (div_nonneg hφ0 hθ.le) |>.mpr
    apply (div_lt_iff₀ hθ).mpr
    rwa [ht]
  refine ⟨⟨k,hk⟩,?_,?_⟩
  · rw [← hφz]
    unfold polarVertex
    rw [cross_polarPoint]
    apply mul_nonneg (mul_nonneg (hr _).le (norm_nonneg _))
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact sub_nonneg.mpr hklo
    · have hθπ : θ ≤ Real.pi := by
        dsimp [θ]
        exact div_le_self Real.pi_pos.le (by exact_mod_cast (show 1 ≤ m by omega))
      nlinarith
  · rw [← hφz,polarVertex_next,cross_polarPoint]
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (hr _).le)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · dsimp only
      linarith
    · have hθπ : θ ≤ Real.pi := by
        dsimp [θ]
        exact div_le_self Real.pi_pos.le (by exact_mod_cast (show 1 ≤ m by omega))
      nlinarith
lemma rhoN_eq_secondMoment_of_moments (N : ℕ) (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (hM : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → (∫ z in Ω, z ^ k) = 0) : rhoN N Ω = ∫ z in Ω, ‖z‖ ^ 2 := by
  unfold rhoN
  have hge : ∀ p : Polynomial.degreeLE ℂ (N : WithBot ℕ),
      (∫ z in Ω, ‖z‖ ^ 2) ≤
        ∫ z in Ω, ‖(starRingEnd ℂ) z - (p : Polynomial ℂ).eval z‖ ^ 2 := by
    intro p
    rw [integral_error_eq_secondMoment_add Ω hb _ (integral_z_mul_poly_eq_zero N Ω hb hM p)]
    have hn : 0 ≤ ∫ z in Ω, ‖(p : Polynomial ℂ).eval z‖ ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    linarith
  have hbelow : BddBelow (Set.range (fun p : Polynomial.degreeLE ℂ (N : WithBot ℕ) =>
      ∫ z in Ω, ‖(starRingEnd ℂ) z - (p : Polynomial ℂ).eval z‖ ^ 2)) := by
    refine ⟨(∫ z in Ω, ‖z‖ ^ 2), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hge p
  apply le_antisymm
  · simpa using (ciInf_le hbelow (0 : Polynomial.degreeLE ℂ (N : WithBot ℕ)))
  · exact le_ciInf hge
lemma secondMoment_ge_on_subset (Ω s : Set ℂ) (hb : Bornology.IsBounded Ω) (hs : MeasurableSet s) (hsub : s ⊆ Ω) (C : ℝ) (hpoint : ∀ z ∈ s, C ≤ ‖z‖^2) : C * (volume s).toReal ≤ ∫ z in Ω, ‖z‖^2 := by
  have hi : IntegrableOn (fun z : ℂ => ‖z‖^2) Ω :=
    integrableOn_continuous_bounded hb (by fun_prop)
  have hf : volume s ≠ ⊤ := by
    exact (measure_mono hsub).trans_lt hb.measure_lt_top |>.ne
  calc
    C * (volume s).toReal ≤ ∫ z in s, ‖z‖^2 :=
      setIntegral_ge_of_const_le_real hs hf hpoint (hi.mono_set hsub)
    _ ≤ ∫ z in Ω, ‖z‖^2 :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        (Filter.Eventually.of_forall (fun z hz => hsub hz))
lemma triangleMap_complexCap_subset_hull (a b : ℂ) : (triangleMap a b) '' complexCap ⊆ convexHull ℝ {0,a,b} := by
  rintro _ ⟨z, hz, rfl⟩
  change z.re ∈ Ioo (1/2 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) (1-z.re) at hz
  apply mem_convexHull_of_exists_fintype (ι := Fin 3)
    ![1-z.re-z.im, z.re, z.im] ![(0 : ℂ),a,b]
  · intro i
    fin_cases i <;> simp <;> linarith [hz.1.1, hz.2.1, hz.2.2]
  · simp [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> simp
  · simp [Fin.sum_univ_succ, triangleMap_apply]
lemma triangleMap_det (a b : ℂ) : LinearMap.det (triangleMap a b) = a.re*b.im-a.im*b.re := by
  have hm : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (triangleMap a b) =
      !![a.re,b.re; a.im,b.im] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      triangleMap_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hm, Matrix.det_fin_two]
  simp [mul_comm]
lemma triangle_volume (a b : ℂ) : volume (convexHull ℝ {0,a,b}) = ENNReal.ofReal (|a.re*b.im-a.im*b.re|/2) := by
  rw [← triangleMap_hull_image, Measure.addHaar_image_linearMap, closedReferenceTriangle_volume,
    triangleMap_det, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring
end D5.S3.Analytic.Torsion.PlanarFanPolynomialApproximation
