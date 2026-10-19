/- GID: D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer
   generality: G
   mirror-B: D5/B/S3/Analytic/Torsion/PolynomialContentNoMaximizer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Polynomial content has no maximizer on suitable unit-area polygons. -/

/-
admission_basis: open-problem-resolution (#16916; Proved)
escape_witness: none
Transitive frozen reuse through PlanarFanPolynomialApproximation:
D5/S3/Geometry/Gluing/CyclicTriangleDisk.positive_circle_angle
(baseline private declaration statement_id: sha256:c2c13b4d22f1a330f80a64a05f4e73fe37aa856cf7477194eb3187b61c7ca716).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17590
Declaration metadata: name | proof_shape | escape_witness | consumers.
adjacent_segments_inter_of_cross_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_adjacent_inter
base_edge_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
cross_mul_left: proof_shape: bind-only; escape_witness: none; consumers: base_even_triple_cross
exp_angle_norm: proof_shape: bind-only; escape_witness: none; consumers: base_even_triple_cross
polarPoint_mul: proof_shape: bind-only; escape_witness: none; consumers: base_even_triple_cross
radial_triple_cross: proof_shape: bind-only; escape_witness: none; consumers: base_even_triple_cross
base_even_triple_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_triple_cross_even
base_odd_edge_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
base_odd_triple_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_triple_cross_odd
cast_fin_add_one: proof_shape: bind-only; escape_witness: none; consumers: starClosedFan_image_rotation
cast_fin_add_two: proof_shape: bind-only; escape_witness: none; consumers: starVertex_adjacent_inter
claim: proof_shape: bind-only; escape_witness: none; consumers: claim_of_star_geometry
symmetryOrder: proof_shape: bind-only; escape_witness: none; consumers: sideIndex
sideIndex: proof_shape: bind-only; escape_witness: none; consumers: sideIndex_add_three
starBase: proof_shape: bind-only; escape_witness: none; consumers: starParameter
starParameter: proof_shape: bind-only; escape_witness: none; consumers: starParameter_large
starParameter_large: proof_shape: bind-only; escape_witness: none; consumers: claim_of_star_geometry
starParameter_pos: proof_shape: bind-only; escape_witness: none; consumers: starParameter_rhoN_lower_bound
sideIndex_add_three: proof_shape: bind-only; escape_witness: none; consumers: starVertex
starRadius: proof_shape: bind-only; escape_witness: none; consumers: starProfile
starProfile: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw
starVertexRaw: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_formula
starVertexRaw_formula: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_add_two
starVertex: proof_shape: bind-only; escape_witness: none; consumers: starClosedFan
starClosedFan: proof_shape: bind-only; escape_witness: none; consumers: starRegion
starRegion: proof_shape: bind-only; escape_witness: none; consumers: starRegion_isBounded
quadratic_lower_bound_unbounded: proof_shape: bind-only; escape_witness: none; consumers: starRegion_rhoN_unbounded
starClosedFan_isCompact: proof_shape: bind-only; escape_witness: none; consumers: starRegion_isBounded
starRegion_isBounded: proof_shape: bind-only; escape_witness: none; consumers: rhoN_starRegion
cyclicFan_image_rotation: proof_shape: bind-only; escape_witness: none; consumers: starClosedFan_image_rotation
starRotation: proof_shape: bind-only; escape_witness: none; consumers: starRotation_eq_exp
starRotation_eq_exp: proof_shape: bind-only; escape_witness: none; consumers: starRotation_primitive
starRotation_primitive: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_add_two
starVertexRaw_add_two: proof_shape: bind-only; escape_witness: none; consumers: starClosedFan_image_rotation
symmetryOrder_ge_three: proof_shape: bind-only; escape_witness: none; consumers: starClosedFan_image_rotation
starClosedFan_image_rotation: proof_shape: bind-only; escape_witness: none; consumers: starRegion_image_rotation
starRegion_image_rotation: proof_shape: bind-only; escape_witness: none; consumers: starRegion_moments
symmetryOrder_gt_relevant_degree: proof_shape: bind-only; escape_witness: none; consumers: starRotation_pow_ne_one
starRotation_pow_ne_one: proof_shape: bind-only; escape_witness: none; consumers: starRegion_moments
starRegion_moments: proof_shape: bind-only; escape_witness: none; consumers: rhoN_starRegion
rhoN_starRegion: proof_shape: bind-only; escape_witness: none; consumers: starParameter_rhoN_lower_bound
starParameter_sq_ge: proof_shape: bind-only; escape_witness: none; consumers: starParameter_rhoN_lower_bound
starAngle_bounds: proof_shape: bind-only; escape_witness: none; consumers: starAngle_cos_pos
starAngle_cos_pos: proof_shape: bind-only; escape_witness: none; consumers: starFirstTriangle_dot_nonneg
starAngle_sin_pos: proof_shape: bind-only; escape_witness: none; consumers: starRadius_pos
starRadius_pos: proof_shape: bind-only; escape_witness: none; consumers: starFirstTriangle_dot_nonneg
starVertex_one: proof_shape: bind-only; escape_witness: none; consumers: starFirstTriangle_dot_nonneg
starVertex_zero: proof_shape: bind-only; escape_witness: none; consumers: starFirstTriangle_dot_nonneg
starFirstTriangle_dot_nonneg: proof_shape: bind-only; escape_witness: none; consumers: starCap_norm_bound
starCap_norm_bound: proof_shape: bind-only; escape_witness: none; consumers: starRegion_secondMoment_lower_bound
fanArea_total: proof_shape: bind-only; escape_witness: none; consumers: starCap_volume
starFirstTriangle_det: proof_shape: bind-only; escape_witness: none; consumers: starFirstTriangle_det_pos
starFirstTriangle_det_pos: proof_shape: bind-only; escape_witness: none; consumers: starCap_volume
starCap_volume: proof_shape: bind-only; escape_witness: none; consumers: starRegion_secondMoment_lower_bound
triangleMap_isOpenMap: proof_shape: bind-only; escape_witness: none; consumers: triangleCap_subset_starRegion
triangleCap_subset_starRegion: proof_shape: bind-only; escape_witness: none; consumers: starRegion_secondMoment_lower_bound
starRegion_secondMoment_lower_bound: proof_shape: bind-only; escape_witness: none; consumers: starParameter_rhoN_lower_bound
starParameter_rhoN_lower_bound: proof_shape: bind-only; escape_witness: none; consumers: starRegion_rhoN_unbounded
starRegion_rhoN_unbounded: proof_shape: bind-only; escape_witness: none; consumers: claim_of_star_geometry
claim_of_star_geometry: proof_shape: bind-only; escape_witness: none; consumers: claim_of_star_polygon_geometry
starProfile_nonneg: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_fan_pairwise_aeDisjoint
starVertexRaw_eq_polarVertex: proof_shape: bind-only; escape_witness: none; consumers: starVertex_norm_le_radius_sum
starVertexRaw_fan_pairwise_aeDisjoint: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_aeDisjoint; consumers: starFan_pairwise_aeDisjoint
starFan_pairwise_aeDisjoint: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_aeDisjoint; consumers: starRegion_unitArea
finite_convex_union_frontier_null: proof_shape: bind-only; escape_witness: none; consumers: convex_union_interior_volume
convex_union_interior_volume: proof_shape: bind-only; escape_witness: none; consumers: starRegion_volume_eq_closedFan
starRegion_volume_eq_closedFan: proof_shape: bind-only; escape_witness: none; consumers: starRegion_volume_one_of_aeDisjoint
starVertexRaw_add_one_even: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
starVertexRaw_add_one_odd: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
starVertexRaw_even: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
starVertexRaw_odd: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_edge_cross
starVertexRaw_edge_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertex_edge_cross
starVertex_edge_cross: proof_shape: bind-only; escape_witness: none; consumers: starVertex_edge_cross_pos
starVertex_edge_cross_pos: proof_shape: bind-only; escape_witness: none; consumers: starTriangle_volume
starTriangle_volume: proof_shape: bind-only; escape_witness: none; consumers: starRegion_volume_one_of_aeDisjoint
starRegion_volume_one_of_aeDisjoint: proof_shape: bind-only; escape_witness: none; consumers: starRegion_unitArea
starRegion_unitArea: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_aeDisjoint; consumers: claim_of_star_polygon_geometry
claim_of_star_polygon_geometry: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_aeDisjoint; consumers: claim_of_zero_mem_and_frontier
interior_starConvex_at_zero: proof_shape: bind-only; escape_witness: none; consumers: starRegion_isConnected_of_zero_mem
starClosedFan_starConvex: proof_shape: bind-only; escape_witness: none; consumers: starRegion_isConnected_of_zero_mem
starRegion_isConnected_of_zero_mem: proof_shape: bind-only; escape_witness: none; consumers: claim_of_zero_mem_and_frontier
starRegion_isOpen: proof_shape: bind-only; escape_witness: none; consumers: claim_of_zero_mem_and_frontier
cross_adjacent_sign: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_adjacent_inter
starRadius_lt_outer_cos: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_triple_cross_ne_zero
starVertexRaw_triple_cross_even: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_triple_cross_ne_zero
starVertexRaw_triple_cross_odd: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_triple_cross_ne_zero
starVertexRaw_triple_cross_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_adjacent_inter
starVertexRaw_adjacent_inter: proof_shape: bind-only; escape_witness: none; consumers: starVertex_adjacent_inter
starVertex_adjacent_inter: proof_shape: bind-only; escape_witness: none; consumers: starVertex_isSimplePolygon_of_disjoint
not_collinear_of_cross_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: starVertexRaw_not_collinear
starVertexRaw_not_collinear: proof_shape: bind-only; escape_witness: none; consumers: starVertex_not_collinear
starVertex_not_collinear: proof_shape: bind-only; escape_witness: none; consumers: starVertex_isSimplePolygon_of_disjoint
starVertex_isSimplePolygon_of_disjoint: proof_shape: bind-only; escape_witness: none; consumers: starVertex_isSimplePolygon
starProfile_pos: proof_shape: bind-only; escape_witness: none; consumers: starVertex_nonadjacent_disjoint
starVertex_nonadjacent_disjoint: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_disjoint; consumers: starVertex_isSimplePolygon
starVertex_isSimplePolygon: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_disjoint; consumers: claim_of_zero_mem_and_frontier
claim_of_zero_mem_and_frontier: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_cyclic_forward_disjoint; consumers: result
starVertex_conic_coverage: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_fan_conic_coverage; consumers: starRegion_positive_inradius
starVertex_norm_le_radius_sum: proof_shape: bind-only; escape_witness: none; consumers: starRegion_positive_inradius
starRegion_positive_inradius: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_fan_conic_coverage; consumers: starRegion_zero_mem_of_inradius
starRegion_zero_mem_of_inradius: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_fan_conic_coverage; consumers: starRegion_frontier
starRegion_frontier: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.adjacent_triangles_spoke_interior; consumers: result
result: proof_shape: content; escape_witness: PlanarFanPolynomialApproximation.polar_fan_conic_coverage; consumers: settling result
-/

import D5.S3.Analytic.Torsion.PlanarFanPolynomialApproximation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Convex.Measure
namespace D5.S3.Analytic.Torsion.PolynomialContentNoMaximizer
open Set MeasureTheory
open D5.S3.Analytic.Torsion.PlanarFanPolynomialApproximation
open scoped ComplexConjugate
attribute [local instance] Complex.finrank_real_complex_fact
private lemma adjacent_segments_inter_of_cross_ne_zero (a b c : ℂ) (h : Complex.orientation.areaForm (a-b) (c-b) ≠ 0) : segment ℝ a b ∩ segment ℝ b c = {b} := by
  have hli : LinearIndependent ℝ ![a-b,c-b] := by
    by_contra hh
    apply h
    rw [Orientation.areaForm_to_volumeForm]
    exact Complex.orientation.volumeForm.map_linearDependent _ hh
  rw [segment_symm ℝ a b]
  exact segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hli
private lemma base_edge_cross (A B θ : ℝ) : Complex.orientation.areaForm (A:ℂ) (circleMap 0 B θ) = A*B*Real.sin θ := by
  simpa [circleMap_zero] using cross_polarPoint A B 0 θ
private lemma cross_mul_left (a x y : ℂ) : Complex.orientation.areaForm (a*x) (a*y) = ‖a‖^2 * Complex.orientation.areaForm x y := by
  simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring
private lemma exp_angle_norm (θ : ℝ) : ‖Complex.exp ((θ : ℂ)*Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I θ
private lemma polarPoint_mul (A θ φ : ℝ) : circleMap 0 A θ * Complex.exp ((φ : ℂ) * Complex.I) = circleMap 0 A (θ+φ) := by
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul, mul_one] using
    circleMap_zero_mul A 1 θ φ
private lemma radial_triple_cross (A B θ : ℝ) : Complex.orientation.areaForm ((B : ℂ) - circleMap 0 A (-θ)) (circleMap 0 A θ - circleMap 0 A (-θ)) = 2*A*Real.sin θ*(B-A*Real.cos θ) := by
  simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    circleMap_zero_re, circleMap_zero_im, Real.cos_neg, Real.sin_neg]
  ring
private lemma base_even_triple_cross (R r θ : ℝ) : Complex.orientation.areaForm (circleMap 0 r θ - (R : ℂ)) (circleMap 0 R (2*θ) - (R : ℂ)) = 2*R*Real.sin θ*(r-R*Real.cos θ) := by
  let w := Complex.exp ((θ : ℂ)*Complex.I)
  have ha : w * circleMap 0 R (-θ) = (R : ℂ) := by
    rw [mul_comm, polarPoint_mul]
    simp [circleMap_zero]
  have hb : w * (r : ℂ) = circleMap 0 r θ := by dsimp [w, circleMap]; ring
  have hc : w * circleMap 0 R θ = circleMap 0 R (2*θ) := by
    rw [mul_comm, polarPoint_mul]
    congr 1
    ring
  have hh := cross_mul_left w ((r : ℂ)-circleMap 0 R (-θ))
    (circleMap 0 R θ-circleMap 0 R (-θ))
  simp only [mul_sub, ha, hb, hc] at hh
  rw [show ‖w‖ = 1 from exp_angle_norm θ, one_pow, one_mul, radial_triple_cross] at hh
  exact hh
private lemma base_odd_edge_cross (A B θ : ℝ) : Complex.orientation.areaForm (circleMap 0 B θ) (circleMap 0 A (2*θ)) = A*B*Real.sin θ := by
  have h := cross_polarPoint B A θ (2*θ)
  rw [show 2*θ-θ=θ by ring] at h
  simpa only [mul_comm] using h
private lemma base_odd_triple_cross (R r θ : ℝ) : Complex.orientation.areaForm (circleMap 0 R (2*θ) - circleMap 0 r θ) (circleMap 0 r (3*θ) - circleMap 0 r θ) = 2*r*Real.sin θ*(R-r*Real.cos θ) := by
  let w := Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I)
  have ha : w * circleMap 0 r (-θ) = circleMap 0 r θ := by
    rw [mul_comm, polarPoint_mul]
    congr 1
    ring
  have hb : w * (R : ℂ) = circleMap 0 R (2*θ) := by dsimp [w, circleMap]; ring
  have hc : w * circleMap 0 r θ = circleMap 0 r (3*θ) := by
    rw [mul_comm, polarPoint_mul]
    congr 1
    ring
  have hh := cross_mul_left w ((R : ℂ)-circleMap 0 r (-θ))
    (circleMap 0 r θ-circleMap 0 r (-θ))
  simp only [mul_sub, ha, hb, hc] at hh
  rw [show ‖w‖ = 1 from exp_angle_norm (2*θ), one_pow, one_mul, radial_triple_cross] at hh
  exact hh
private lemma cast_fin_add_one {t u : ℕ} [NeZero t] [NeZero u] (h : t = u) (i : Fin t) : Fin.cast h (i+1) = Fin.cast h i + 1 := by
  subst u
  rfl
private lemma cast_fin_add_two {t u : ℕ} [NeZero t] [NeZero u] (h : t = u) (i : Fin t) : Fin.cast h (i+2) = Fin.cast h i + 2 := by
  subst u
  rfl
def claim : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, ¬ ∃ P : Set ℂ, IsPolygonRegion n P ∧ volume P = 1 ∧
    ∀ Q : Set ℂ, IsPolygonRegion n Q → volume Q = 1 → rhoN N Q ≤ rhoN N P
private def symmetryOrder (N : ℕ) : ℕ := max 3 (N + 2)
private def sideIndex (N : ℕ) : ℕ := 2 * symmetryOrder N - 3
private noncomputable def starBase (N : ℕ) : ℝ :=
  max 1 (1 / ((symmetryOrder N : ℝ) * Real.sin (Real.pi / (symmetryOrder N : ℝ)) *
    Real.cos (Real.pi / (symmetryOrder N : ℝ))) + 1)
private noncomputable def starParameter (N k : ℕ) : ℝ := (k : ℝ) + starBase N
private lemma starParameter_large (N k : ℕ) : 1 / ((symmetryOrder N : ℝ) * Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ))) < (starParameter N k)^2 := by
  unfold starParameter starBase
  have hn := Nat.cast_nonneg (α := ℝ) k
  have h1 : (1 : ℝ) ≤ max 1 (1 / ((symmetryOrder N : ℝ) *
      Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ)))+1) :=
    le_max_left _ _
  have h2 := le_max_right (1 : ℝ) (1 / ((symmetryOrder N : ℝ) *
      Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ)))+1)
  nlinarith
private lemma starParameter_pos (N k : ℕ) : 0 < starParameter N k := by
  unfold starParameter starBase
  have hn := Nat.cast_nonneg (α := ℝ) k
  have hh : (1 : ℝ) ≤ max 1 (1 / ((symmetryOrder N : ℝ) *
      Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ)))+1) :=
    le_max_left _ _
  linarith
private lemma sideIndex_add_three (N : ℕ) : sideIndex N + 3 = 2 * symmetryOrder N := by
  unfold sideIndex symmetryOrder
  omega
private noncomputable def starRadius (m : ℕ) (R : ℝ) : ℝ :=
  1 / ((m : ℝ) * R * Real.sin (Real.pi / (m : ℝ)))
private noncomputable def starProfile (m : ℕ) (R : ℝ) (i : Fin (2*m)) : ℝ :=
  if i.val%2 = 0 then R else starRadius m R
private noncomputable def starVertexRaw (m : ℕ) (R : ℝ) (i : Fin (2 * m)) : ℂ :=
  polarVertex m (starProfile m R) i
private lemma starVertexRaw_formula (m : ℕ) (R : ℝ) (i : Fin (2*m)) :
    starVertexRaw m R i =
      let θ : ℝ := Real.pi / (m : ℝ)
      let ζ : ℂ := Complex.exp ((2 * θ : ℝ) * Complex.I)
      if i.val % 2 = 0 then (R : ℂ) * ζ ^ (i.val / 2)
      else (starRadius m R : ℂ) * Complex.exp (θ * Complex.I) * ζ ^ (i.val / 2) := by
  dsimp [starVertexRaw,polarVertex,starProfile,circleMap]
  symm
  split_ifs with hi
  · rw [← Complex.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    have hn : (i.val:ℂ) = 2*((i.val/2:ℕ):ℂ) := by
      exact_mod_cast (by simpa only [hi, zero_add] using (Nat.mod_add_div i.val 2).symm)
    rw [hn]
    ring
  · rw [mul_assoc,← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    have hn : (i.val:ℂ) = 2*((i.val/2:ℕ):ℂ)+1 := by
      exact_mod_cast (by
        simpa only [show i.val % 2 = 1 by omega, add_comm] using
          (Nat.mod_add_div i.val 2).symm)
    rw [hn]
    ring
private noncomputable def starVertex (N : ℕ) (R : ℝ) (i : Fin (sideIndex N + 3)) : ℂ :=
  starVertexRaw (symmetryOrder N) R (Fin.cast (sideIndex_add_three N) i)
private noncomputable def starClosedFan (N : ℕ) (R : ℝ) : Set ℂ :=
  ⋃ i : Fin (sideIndex N + 3),
    convexHull ℝ {0, starVertex N R i, starVertex N R (i+1)}
private noncomputable def starRegion (N : ℕ) (R : ℝ) : Set ℂ := interior (starClosedFan N R)
private theorem quadratic_lower_bound_unbounded (c : ℝ) (hc : 0 < c) (A : ℕ → ℝ) (hA : ∀ r : ℕ, c * (r : ℝ)^2 ≤ A r) : ∀ C : ℝ, ∃ r : ℕ, C < A r := by
  intro C
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 (C / c) + 1)
  refine ⟨r, lt_of_lt_of_le ?_ (hA r)⟩
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrc : C / c < (r : ℝ) := by
    calc
      C / c ≤ max 0 (C / c) := le_max_right _ _
      _ < (r : ℝ) := by linarith [hr]
  have hC : C < c * (r : ℝ) := (div_lt_iff₀' hc).mp hrc
  have hr1 : (1 : ℝ) < (r : ℝ) := by
    have hm : (0 : ℝ) ≤ max 0 (C / c) := le_max_left _ _
    nlinarith [hr]
  have hstep : c * (r : ℝ) < c * (r : ℝ)^2 := by
    have hp : 0 < (r : ℝ) := lt_trans (by norm_num) hr1
    nlinarith [mul_pos hc (sub_pos.mpr hr1)]
  exact hC.trans hstep
private lemma starClosedFan_isCompact (N : ℕ) (R : ℝ) : IsCompact (starClosedFan N R) := by
  unfold starClosedFan
  apply isCompact_iUnion
  intro i
  have hf : ({0, starVertex N R i, starVertex N R (i+1)} : Set ℂ).Finite := toFinite _
  exact hf.isCompact_convexHull (𝕜 := ℝ)
private lemma starRegion_isBounded (N : ℕ) (R : ℝ) : Bornology.IsBounded (starRegion N R) :=
  (starClosedFan_isCompact N R).isBounded.subset interior_subset
private lemma cyclicFan_image_rotation {t : ℕ} [NeZero t] (v : Fin t → ℂ) (a : Circle) (c : Fin t) (hv : ∀ i, v (i+c) = (rotation a) (v i)) : (rotation a) '' (⋃ i : Fin t, convexHull ℝ {0, v i, v (i+1)}) = ⋃ i : Fin t, convexHull ℝ {0, v i, v (i+1)} := by
  rw [image_iUnion]
  have ht : ∀ i : Fin t,
      (rotation a) '' convexHull ℝ {0, v i, v (i+1)} =
        convexHull ℝ {0, v (i+c), v (i+c+1)} := by
    intro i
    have him := (rotation a).toLinearEquiv.toLinearMap.image_convexHull
      ({0, v i, v (i+1)} : Set ℂ)
    change (rotation a) '' convexHull ℝ {0,v i,v (i+1)} =
      convexHull ℝ ((rotation a) '' {0,v i,v (i+1)}) at him
    rw [him]
    congr 1
    simp only [image_insert_eq, image_singleton, map_zero, ← hv]
    rw [add_right_comm i 1 c]
  simp_rw [ht]
  exact (Equiv.addRight c).surjective.iUnion_comp
    (fun i : Fin t => convexHull ℝ {0, v i, v (i+1)})
private noncomputable def starRotation (m : ℕ) : Circle := Circle.exp (2 * Real.pi / (m : ℝ))
private lemma starRotation_eq_exp (m : ℕ) : (starRotation m : ℂ) = Complex.exp (((2*(Real.pi/(m:ℝ)) : ℝ) : ℂ)*Complex.I) := by
  simp only [starRotation, Circle.coe_exp]
  congr 1
  push_cast
  ring
private lemma starRotation_primitive (m : ℕ) (hm : m ≠ 0) : IsPrimitiveRoot (starRotation m : ℂ) m := by
  have heq : (starRotation m : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) := by
    rw [starRotation_eq_exp]
    congr 1
    push_cast
    ring
  rw [heq]
  exact Complex.isPrimitiveRoot_exp m hm
private lemma starVertexRaw_add_two (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) : starVertexRaw m R (i+2) = (starRotation m : ℂ) * starVertexRaw m R i := by
  have h2 : ((2 : Fin (2*m)) : ℕ) = 2 := by
    change 2 % (2*m) = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hζ : Complex.exp (((2 * (Real.pi / (m : ℝ))) : ℝ) * Complex.I) =
      (starRotation m : ℂ) := by
    exact (starRotation_eq_exp m).symm
  have hval := Fin.val_add_eq_ite i (2 : Fin (2*m))
  rw [h2] at hval
  by_cases hlt : i.val + 2 < 2*m
  · rw [if_neg (by omega)] at hval
    have hpar : (i+2).val % 2 = i.val % 2 := by omega
    have hdiv : (i+2).val / 2 = i.val / 2 + 1 := by omega
    simp only [starVertexRaw_formula, hζ, hpar, hdiv, pow_succ]
    split_ifs <;> ring
  · rw [if_pos (by omega)] at hval
    have hpar : (i+2).val % 2 = i.val % 2 := by omega
    have hdiv : (i+2).val / 2 = 0 := by omega
    have hdiv' : i.val / 2 + 1 = m := by omega
    have hpow : (starRotation m : ℂ) * (starRotation m : ℂ)^(i.val/2) = 1 := by
      rw [← pow_succ', hdiv']
      exact (starRotation_primitive m (by omega)).pow_eq_one
    simp only [starVertexRaw_formula, hζ, hpar, hdiv, pow_zero]
    split_ifs
    · calc
        (R : ℂ) * 1 = (R : ℂ) * ((starRotation m : ℂ) * (starRotation m : ℂ)^(i.val/2)) := by rw [hpow]
        _ = _ := by ring
    · calc
        (starRadius m R : ℂ) * Complex.exp (((Real.pi / (m : ℝ) : ℝ) : ℂ) * Complex.I) * 1 =
            (starRadius m R : ℂ) * Complex.exp (((Real.pi / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by ring
        _ = (starRadius m R : ℂ) * Complex.exp (((Real.pi / (m : ℝ) : ℝ) : ℂ) * Complex.I) *
            ((starRotation m : ℂ) * (starRotation m : ℂ)^(i.val/2)) := by rw [hpow]; ring
        _ = _ := by ring
private lemma symmetryOrder_ge_three (N : ℕ) : 3 ≤ symmetryOrder N := le_max_left _ _
private lemma starClosedFan_image_rotation (N : ℕ) (R : ℝ) : (rotation (starRotation (symmetryOrder N))) '' starClosedFan N R = starClosedFan N R := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  have heq : starClosedFan N R =
      ⋃ i : Fin (2*symmetryOrder N), convexHull ℝ
        {0, starVertexRaw (symmetryOrder N) R i, starVertexRaw (symmetryOrder N) R (i+1)} := by
    unfold starClosedFan starVertex
    simp_rw [cast_fin_add_one]
    exact (Fin.rightInverse_cast (sideIndex_add_three N)).surjective.iUnion_comp
      (fun i : Fin (2*symmetryOrder N) => convexHull ℝ
        {0, starVertexRaw (symmetryOrder N) R i, starVertexRaw (symmetryOrder N) R (i+1)})
  rw [heq]
  apply cyclicFan_image_rotation _ _ (2 : Fin (2*symmetryOrder N))
  intro i
  simpa only [rotation_apply] using starVertexRaw_add_two (symmetryOrder N) hm R i
private lemma starRegion_image_rotation (N : ℕ) (R : ℝ) : (rotation (starRotation (symmetryOrder N))) '' starRegion N R = starRegion N R := by
  unfold starRegion
  have him := (rotation (starRotation (symmetryOrder N))).toHomeomorph.image_interior
    (starClosedFan N R)
  change (rotation (starRotation (symmetryOrder N))) '' interior (starClosedFan N R) =
    interior ((rotation (starRotation (symmetryOrder N))) '' starClosedFan N R) at him
  rw [him]
  rw [starClosedFan_image_rotation]
private lemma symmetryOrder_gt_relevant_degree (N : ℕ) : N + 1 < symmetryOrder N := by
  have h : N+2 ≤ symmetryOrder N := le_max_right _ _
  omega
private lemma starRotation_pow_ne_one (N k : ℕ) (hk : 1 ≤ k) (hle : k ≤ N+1) : (starRotation (symmetryOrder N) : ℂ)^k ≠ 1 := by
  apply (starRotation_primitive (symmetryOrder N) (by have := symmetryOrder_ge_three N; omega)).pow_ne_one_of_pos_of_lt
  · omega
  · have := symmetryOrder_gt_relevant_degree N
    omega
private lemma starRegion_moments (N : ℕ) (R : ℝ) (k : ℕ) (hk : 1 ≤ k) (hle : k ≤ N+1) : (∫ z in starRegion N R, z^k) = 0 := by
  exact integral_pow_eq_zero_of_rotation (starRotation (symmetryOrder N)) k (starRegion N R)
    (starRegion_image_rotation N R) (starRotation_pow_ne_one N k hk hle)
private lemma rhoN_starRegion (N : ℕ) (R : ℝ) : rhoN N (starRegion N R) = ∫ z in starRegion N R, ‖z‖^2 := by
  exact rhoN_eq_secondMoment_of_moments N (starRegion N R) (starRegion_isBounded N R)
    (starRegion_moments N R)
private lemma starParameter_sq_ge (N k : ℕ) : (k : ℝ)^2 ≤ (starParameter N k)^2 := by
  unfold starParameter starBase
  have hn := Nat.cast_nonneg (α := ℝ) k
  have h1 : (1 : ℝ) ≤ max 1 (1 / ((symmetryOrder N : ℝ) *
      Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ)))+1) :=
    le_max_left _ _
  nlinarith
private lemma starAngle_bounds (m : ℕ) (hm : 3 ≤ m) : 0 < Real.pi / (m : ℝ) ∧ Real.pi / (m : ℝ) < Real.pi / 2 := by
  have hmc : (2 : ℝ) < (m : ℝ) := Nat.ofNat_lt_cast.mpr hm
  constructor
  · exact div_pos Real.pi_pos (by linarith)
  · exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hmc
private lemma starAngle_cos_pos (m : ℕ) (hm : 3 ≤ m) : 0 < Real.cos (Real.pi / (m : ℝ)) := by
  obtain ⟨hpos, hlt⟩ := starAngle_bounds m hm
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [Real.pi_pos]
  · exact hlt
private lemma starAngle_sin_pos (m : ℕ) (hm : 3 ≤ m) : 0 < Real.sin (Real.pi / (m : ℝ)) := by
  obtain ⟨hpos, hlt⟩ := starAngle_bounds m hm
  apply Real.sin_pos_of_pos_of_lt_pi hpos
  linarith [Real.pi_pos]
private lemma starRadius_pos (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) : 0 < starRadius m R := by
  unfold starRadius
  exact one_div_pos.mpr (mul_pos (mul_pos (by exact_mod_cast (show 0 < m by omega)) hR)
    (starAngle_sin_pos m hm))
private lemma starVertex_one (N : ℕ) (R : ℝ) : starVertex N R 1 = (starRadius (symmetryOrder N) R : ℂ) * Complex.exp (((Real.pi / (symmetryOrder N : ℝ) : ℝ) : ℂ) * Complex.I) := by
  simp [starVertex, starVertexRaw_formula]
private lemma starVertex_zero (N : ℕ) (R : ℝ) : starVertex N R 0 = (R : ℂ) := by
  simp [starVertex, starVertexRaw_formula]
private lemma starFirstTriangle_dot_nonneg (N : ℕ) (R : ℝ) (hR : 0 < R) : 0 ≤ ((starVertex N R 0) * conj (starVertex N R 1)).re := by
  rw [starVertex_zero, starVertex_one]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, mul_zero, sub_zero,
    add_zero]
  exact mul_nonneg hR.le (mul_nonneg (starRadius_pos _ (symmetryOrder_ge_three N) R hR).le
    (starAngle_cos_pos _ (symmetryOrder_ge_three N)).le)
private lemma starCap_norm_bound (N : ℕ) (R : ℝ) (hR : 0 < R) : ∀ z ∈ ((triangleMap (starVertex N R 0) (starVertex N R 1)) '' complexCap), R^2/4 ≤ ‖z‖^2 := by
  rintro _ ⟨z, hz, rfl⟩
  change z.re ∈ Ioo (1/2 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) (1-z.re) at hz
  rw [triangleMap_apply, starVertex_zero]
  have hnorm := norm_sq_smul_add_ge (starVertex N R 0) (starVertex N R 1) z.re z.im
    (by linarith [hz.1.1]) hz.2.1.le (starFirstTriangle_dot_nonneg N R hR)
  rw [starVertex_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hnorm
  have hx2 : (1/4 : ℝ) ≤ z.re^2 := by nlinarith [hz.1.1]
  have hmul := mul_le_mul_of_nonneg_right hx2 (sq_nonneg R)
  nlinarith [hnorm, hmul]
private lemma fanArea_total (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) : (m : ℝ) * R * starRadius m R * Real.sin (Real.pi / (m : ℝ)) = 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hsin := starAngle_sin_pos m hm
  unfold starRadius
  field_simp
private lemma starProfile_pos (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) : ∀ i, 0 < starProfile m R i := by
  intro i
  unfold starProfile
  split_ifs
  · exact hR
  · exact starRadius_pos m hm R hR
private lemma starProfile_nonneg (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) : ∀ i, 0 ≤ starProfile m R i := by
  intro i
  exact (starProfile_pos m hm R hR i).le
private lemma starVertexRaw_eq_polarVertex (m : ℕ) [NeZero m] (R : ℝ) (i : Fin (2*m)) : starVertexRaw m R i = polarVertex m (starProfile m R) i := by
  exact Complex.ext rfl rfl
private lemma starVertexRaw_fan_pairwise_aeDisjoint (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) : Pairwise (fun i j : Fin (2*m) => AEDisjoint volume (convexHull ℝ {0,starVertexRaw m R i,starVertexRaw m R (i+1)}) (convexHull ℝ {0,starVertexRaw m R j,starVertexRaw m R (j+1)})) := by
  exact polar_cyclic_fan_pairwise_aeDisjoint m hm _ (starProfile_nonneg m hm R hR)
private lemma starFan_pairwise_aeDisjoint (N : ℕ) (R : ℝ) (hR : 0 < R) : Pairwise (fun i j : Fin (sideIndex N+3) => AEDisjoint volume (convexHull ℝ {0,starVertex N R i,starVertex N R (i+1)}) (convexHull ℝ {0,starVertex N R j,starVertex N R (j+1)})) := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  intro i j hij
  have hijc : Fin.cast (sideIndex_add_three N) i ≠ Fin.cast (sideIndex_add_three N) j := by
    intro heq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val heq
  simpa only [starVertex,cast_fin_add_one] using starVertexRaw_fan_pairwise_aeDisjoint
    (symmetryOrder N) hm R hR hijc
private lemma finite_convex_union_frontier_null {ι : Type*} (t : ι → Set ℂ) (s : Finset ι) (hc : ∀ i, Convex ℝ (t i)) : volume (frontier (⋃ i ∈ s, t i)) = 0 := by
  classical
  exact measure_mono_null (s.frontier_biUnion_subset t)
    ((measure_biUnion_null_iff (s.finite_toSet.countable)).2 (fun i _hi => (hc i).addHaar_frontier volume))
private lemma convex_union_interior_volume {ι : Type*} [Fintype ι] (t : ι → Set ℂ) (hc : ∀ i, Convex ℝ (t i)) : volume (interior (⋃ i, t i)) = volume (⋃ i, t i) := by
  apply measure_interior_of_null_frontier
  simpa using finite_convex_union_frontier_null t Finset.univ hc
private lemma starRegion_volume_eq_closedFan (N : ℕ) (R : ℝ) : volume (starRegion N R) = volume (starClosedFan N R) := by
  exact convex_union_interior_volume _ (fun i => convex_convexHull ℝ _)
private lemma starVertexRaw_add_one_even (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) (heven : i.val % 2 = 0) : starVertexRaw m R (i+1) = (starRadius m R : ℂ) * Complex.exp (((Real.pi / (m : ℝ) : ℝ) : ℂ) * Complex.I) * (starRotation m : ℂ)^(i.val/2) := by
  have h1 : ((1 : Fin (2*m)) : ℕ) = 1 := by
    change 1 % (2*m) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : i.val + 1 < 2*m := by omega
  have hlt' : i.val + ((1 : Fin (2*m)) : ℕ) < 2*m := by rw [h1]; exact hlt
  have hval := Fin.val_add_eq_of_add_lt (a := i) (b := (1 : Fin (2*m))) hlt'
  rw [h1] at hval
  have hpar : (i+1).val % 2 ≠ 0 := by omega
  have hdiv : (i+1).val / 2 = i.val / 2 := by omega
  have hζ : Complex.exp (((2 * (Real.pi / (m : ℝ))) : ℝ) * Complex.I) =
      (starRotation m : ℂ) := by
    exact (starRotation_eq_exp m).symm
  simp only [starVertexRaw_formula, hζ, if_neg hpar, hdiv]
private lemma starVertexRaw_add_one_odd (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) (hodd : i.val % 2 ≠ 0) : starVertexRaw m R (i+1) = (starRotation m : ℂ) * (R : ℂ) * (starRotation m : ℂ)^(i.val/2) := by
  have h1 : ((1 : Fin (2*m)) : ℕ) = 1 := by
    change 1 % (2*m) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hval := Fin.val_add_eq_ite i (1 : Fin (2*m))
  rw [h1] at hval
  have hζ : Complex.exp (((2 * (Real.pi / (m : ℝ))) : ℝ) * Complex.I) =
      (starRotation m : ℂ) := by
    exact (starRotation_eq_exp m).symm
  by_cases hlt : i.val + 1 < 2*m
  · rw [if_neg (by omega)] at hval
    have hpar : (i+1).val % 2 = 0 := by omega
    have hdiv : (i+1).val / 2 = i.val / 2 + 1 := by omega
    simp only [starVertexRaw_formula, hζ, if_pos hpar, hdiv, pow_succ]
    ring
  · rw [if_pos (by omega)] at hval
    have hpar : (i+1).val % 2 = 0 := by omega
    have hdiv : (i+1).val / 2 = 0 := by omega
    have hdiv' : i.val / 2 + 1 = m := by omega
    have hpow : (starRotation m : ℂ) * (starRotation m : ℂ)^(i.val/2) = 1 := by
      rw [← pow_succ', hdiv']
      exact (starRotation_primitive m (by omega)).pow_eq_one
    simp only [starVertexRaw_formula, hζ, if_pos hpar, hdiv, pow_zero]
    calc
      (R : ℂ)*1 = (R : ℂ)*((starRotation m : ℂ) * (starRotation m : ℂ)^(i.val/2)) := by rw [hpow]
      _ = _ := by ring
private lemma starVertexRaw_even (m : ℕ) [NeZero m] (R : ℝ) (i : Fin (2*m)) (heven : i.val % 2 = 0) : starVertexRaw m R i = (starRotation m : ℂ)^(i.val/2) * (R : ℂ) := by
  simp only [starVertexRaw_formula, if_pos heven, ← starRotation_eq_exp]
  ring
private lemma starVertexRaw_odd (m : ℕ) [NeZero m] (R : ℝ) (i : Fin (2*m)) (hodd : i.val % 2 ≠ 0) : starVertexRaw m R i = (starRotation m : ℂ)^(i.val/2) * circleMap 0 (starRadius m R) (Real.pi/(m:ℝ)) := by
  simp only [starVertexRaw_formula, if_neg hodd, ← starRotation_eq_exp, circleMap_zero]
  ring
private lemma starVertexRaw_edge_cross (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) : Complex.orientation.areaForm (starVertexRaw m R i) (starVertexRaw m R (i+1)) = R*starRadius m R*Real.sin (Real.pi/(m:ℝ)) := by
  let p : ℂ := (starRotation m : ℂ)^(i.val/2)
  let θ : ℝ := Real.pi/(m:ℝ)
  have hp : ‖p‖ = 1 := by
    simp only [p,norm_pow]
    rw [starRotation_eq_exp,Complex.norm_exp_ofReal_mul_I,one_pow]
  by_cases heven : i.val % 2 = 0
  · have ha : starVertexRaw m R i = p*(R:ℂ) := starVertexRaw_even m R i heven
    have hb : starVertexRaw m R (i+1) = p*circleMap 0 (starRadius m R) θ := by
      rw [starVertexRaw_add_one_even m hm R i heven]
      dsimp [p,θ,circleMap]
      ring
    rw [ha,hb,cross_mul_left,hp,one_pow,one_mul]
    exact base_edge_cross R (starRadius m R) θ
  · have ha : starVertexRaw m R i = p*circleMap 0 (starRadius m R) θ := starVertexRaw_odd m R i heven
    have hb : starVertexRaw m R (i+1) = p*circleMap 0 R (2*θ) := by
      rw [starVertexRaw_add_one_odd m hm R i heven]
      simp only [p,θ,circleMap_zero,starRotation_eq_exp]
      ring
    rw [ha,hb,cross_mul_left,hp,one_pow,one_mul]
    exact base_odd_edge_cross R (starRadius m R) θ
private lemma starVertex_edge_cross (N : ℕ) (R : ℝ) (i : Fin (sideIndex N+3)) : Complex.orientation.areaForm (starVertex N R i) (starVertex N R (i+1)) = R*starRadius (symmetryOrder N) R*Real.sin (Real.pi/(symmetryOrder N:ℝ)) := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  simp only [starVertex,cast_fin_add_one]
  exact starVertexRaw_edge_cross _ hm R _
private lemma starFirstTriangle_det (N : ℕ) (R : ℝ) : LinearMap.det (triangleMap (starVertex N R 0) (starVertex N R 1)) = R * starRadius (symmetryOrder N) R * Real.sin (Real.pi / (symmetryOrder N : ℝ)) := by
  rw [triangleMap_det]
  have h := starVertex_edge_cross N R (0 : Fin (sideIndex N+3))
  simpa only [zero_add, Complex.areaForm, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, sub_eq_add_neg, neg_mul] using h
private lemma starFirstTriangle_det_pos (N : ℕ) (R : ℝ) (hR : 0 < R) : 0 < LinearMap.det (triangleMap (starVertex N R 0) (starVertex N R 1)) := by
  rw [starFirstTriangle_det]
  exact mul_pos (mul_pos hR (starRadius_pos _ (symmetryOrder_ge_three N) R hR))
    (starAngle_sin_pos _ (symmetryOrder_ge_three N))
private lemma starCap_volume (N : ℕ) (R : ℝ) (hR : 0 < R) : volume ((triangleMap (starVertex N R 0) (starVertex N R 1)) '' complexCap) = ENNReal.ofReal (1 / (8 * (symmetryOrder N : ℝ))) := by
  rw [Measure.addHaar_image_linearMap, abs_of_pos (starFirstTriangle_det_pos N R hR),
    complexCap_volume, ← ENNReal.ofReal_mul (starFirstTriangle_det_pos N R hR).le]
  rw [starFirstTriangle_det]
  congr 1
  have h := fanArea_total (symmetryOrder N) (symmetryOrder_ge_three N) R hR
  have hm : (symmetryOrder N : ℝ) ≠ 0 := by
    have hh : (0 : ℝ) < (symmetryOrder N : ℝ) := by
      exact_mod_cast (show 0 < symmetryOrder N by have := symmetryOrder_ge_three N; omega)
    exact hh.ne'
  apply (eq_div_iff (mul_ne_zero (by norm_num) hm)).mpr
  nlinarith [h]
private lemma triangleMap_isOpenMap (a b : ℂ) (hdet : a.re*b.im-a.im*b.re ≠ 0) : IsOpenMap (triangleMap a b) := by
  have hdet' : LinearMap.det (triangleMap a b) ≠ 0 := by rwa [triangleMap_det]
  exact (triangleMap a b).equivOfDetNeZero hdet' |>.toContinuousLinearEquiv.toHomeomorph.isOpenMap
private lemma triangleCap_subset_starRegion (N : ℕ) (R : ℝ) (hdet : (starVertex N R 0).re * (starVertex N R 1).im - (starVertex N R 0).im * (starVertex N R 1).re ≠ 0) : (triangleMap (starVertex N R 0) (starVertex N R 1)) '' complexCap ⊆ starRegion N R := by
  apply interior_maximal
  · apply (triangleMap_complexCap_subset_hull _ _).trans
    unfold starClosedFan
    simpa only [zero_add] using (subset_iUnion (fun i : Fin (sideIndex N+3) =>
      convexHull ℝ {0,starVertex N R i,starVertex N R (i+1)}) (0 : Fin (sideIndex N+3)))
  · exact (triangleMap_isOpenMap _ _ hdet) _ complexCap_isOpen
private lemma starRegion_secondMoment_lower_bound (N : ℕ) (R : ℝ) (hR : 0 < R) : R^2 / (32*(symmetryOrder N : ℝ)) ≤ ∫ z in starRegion N R, ‖z‖^2 := by
  let f := triangleMap (starVertex N R 0) (starVertex N R 1)
  have hdet : (starVertex N R 0).re * (starVertex N R 1).im -
      (starVertex N R 0).im * (starVertex N R 1).re ≠ 0 := by
    rw [← triangleMap_det]
    exact (starFirstTriangle_det_pos N R hR).ne'
  have hopen : IsOpen (f '' complexCap) := (triangleMap_isOpenMap _ _ hdet) _ complexCap_isOpen
  have hbound := secondMoment_ge_on_subset (starRegion N R) (f '' complexCap)
    (starRegion_isBounded N R) hopen.measurableSet (triangleCap_subset_starRegion N R hdet)
    (R^2/4) (starCap_norm_bound N R hR)
  rw [starCap_volume N R hR, ENNReal.toReal_ofReal (by positivity)] at hbound
  convert hbound using 1 <;> field_simp <;> ring
private lemma starParameter_rhoN_lower_bound (N k : ℕ) : (1 / (32*(symmetryOrder N : ℝ))) * (k : ℝ)^2 ≤ rhoN N (starRegion N (starParameter N k)) := by
  rw [rhoN_starRegion]
  calc
    (1 / (32*(symmetryOrder N : ℝ))) * (k : ℝ)^2 =
        (k : ℝ)^2 / (32*(symmetryOrder N : ℝ)) := by ring
    _ ≤ (starParameter N k)^2 / (32*(symmetryOrder N : ℝ)) :=
      div_le_div_of_nonneg_right (starParameter_sq_ge N k) (by positivity)
    _ ≤ _ := starRegion_secondMoment_lower_bound N _ (starParameter_pos N k)
private lemma starRegion_rhoN_unbounded (N : ℕ) : ∀ C : ℝ, ∃ k : ℕ, C < rhoN N (starRegion N (starParameter N k)) := by
  have hm : (0 : ℝ) < (symmetryOrder N : ℝ) := by
    exact_mod_cast (show 0 < symmetryOrder N by have := symmetryOrder_ge_three N; omega)
  exact quadratic_lower_bound_unbounded (1 / (32*(symmetryOrder N : ℝ))) (by positivity)
    (fun k => rhoN N (starRegion N (starParameter N k))) (starParameter_rhoN_lower_bound N)
private lemma claim_of_star_geometry (hgeometry : ∀ N : ℕ, ∀ R : ℝ, 0 < R → 1 / ((symmetryOrder N : ℝ) * Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ))) < R^2 → IsPolygonRegion (sideIndex N) (starRegion N R) ∧ volume (starRegion N R) = 1) : claim := by
  intro N
  refine ⟨sideIndex N, ?_⟩
  apply no_max_of_unbounded_family N (sideIndex N) (fun k => starRegion N (starParameter N k))
  · intro k
    exact (hgeometry N _ (starParameter_pos N k) (starParameter_large N k)).1
  · intro k
    exact (hgeometry N _ (starParameter_pos N k) (starParameter_large N k)).2
  · exact starRegion_rhoN_unbounded N
private lemma starVertex_edge_cross_pos (N : ℕ) (R : ℝ) (hR : 0 < R) (i : Fin (sideIndex N+3)) : 0 < Complex.orientation.areaForm (starVertex N R i) (starVertex N R (i+1)) := by
  rw [starVertex_edge_cross]
  exact mul_pos (mul_pos hR (starRadius_pos _ (symmetryOrder_ge_three N) R hR))
    (starAngle_sin_pos _ (symmetryOrder_ge_three N))
private lemma starTriangle_volume (N : ℕ) (R : ℝ) (hR : 0 < R) (i : Fin (sideIndex N+3)) : volume (convexHull ℝ {0,starVertex N R i,starVertex N R (i+1)}) = ENNReal.ofReal (1 / (2*(symmetryOrder N:ℝ))) := by
  rw [triangle_volume]
  rw [show (starVertex N R i).re * (starVertex N R (i+1)).im -
    (starVertex N R i).im * (starVertex N R (i+1)).re =
    Complex.orientation.areaForm (starVertex N R i) (starVertex N R (i+1)) by
      simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring]
  rw [abs_of_pos (starVertex_edge_cross_pos N R hR i),starVertex_edge_cross]
  congr 1
  have hm0 : (symmetryOrder N:ℝ) ≠ 0 := by
    exact_mod_cast (show symmetryOrder N ≠ 0 by have := symmetryOrder_ge_three N;omega)
  have hs0 := (starAngle_sin_pos _ (symmetryOrder_ge_three N)).ne'
  unfold starRadius
  field_simp [hm0, hs0, hR.ne']
private lemma starRegion_volume_one_of_aeDisjoint (N : ℕ) (R : ℝ) (hR : 0 < R) (hd : Pairwise (fun i j : Fin (sideIndex N+3) => AEDisjoint volume (convexHull ℝ {0,starVertex N R i,starVertex N R (i+1)}) (convexHull ℝ {0,starVertex N R j,starVertex N R (j+1)}))) : volume (starRegion N R) = 1 := by
  rw [starRegion_volume_eq_closedFan]
  unfold starClosedFan
  rw [measure_iUnion₀ hd (fun i => (convex_convexHull ℝ _).nullMeasurableSet volume),tsum_fintype]
  simp_rw [starTriangle_volume N R hR]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hm0 : (symmetryOrder N:ℝ) ≠ 0 := by
    exact_mod_cast (show symmetryOrder N ≠ 0 by have := symmetryOrder_ge_three N;omega)
  rw [sideIndex_add_three]
  push_cast
  field_simp
  norm_num
private lemma starRegion_unitArea (N : ℕ) (R : ℝ) (hR : 0 < R) : volume (starRegion N R) = 1 := by
  exact starRegion_volume_one_of_aeDisjoint N R hR (starFan_pairwise_aeDisjoint N R hR)
private lemma claim_of_star_polygon_geometry (hgeometry : ∀ N : ℕ, ∀ R : ℝ, 0 < R → 1 / ((symmetryOrder N : ℝ) * Real.sin (Real.pi / (symmetryOrder N : ℝ)) * Real.cos (Real.pi / (symmetryOrder N : ℝ))) < R^2 → IsPolygonRegion (sideIndex N) (starRegion N R)) : claim := by
  apply claim_of_star_geometry
  intro N R hR hl
  exact ⟨hgeometry N R hR hl,starRegion_unitArea N R hR⟩
private lemma interior_starConvex_at_zero {s : Set ℂ} (hs : StarConvex ℝ 0 s) (h0 : (0 : ℂ) ∈ interior s) : StarConvex ℝ 0 (interior s) := by
  intro y hy a b ha hb hab
  by_cases hb0 : b = 0
  · simpa [hb0] using h0
  · have hmaps : (fun z : ℂ => b • z) '' s ⊆ s := by
      rintro _ ⟨z, hz, rfl⟩
      simpa using hs hz ha hb hab
    have hi : b • y ∈ interior ((fun z : ℂ => b • z) '' s) :=
      (isOpenMap_smul₀ hb0).image_interior_subset s ⟨y, hy, rfl⟩
    simpa using interior_mono hmaps hi
private lemma starClosedFan_starConvex (N : ℕ) (R : ℝ) : StarConvex ℝ 0 (starClosedFan N R) := by
  unfold starClosedFan
  apply starConvex_iUnion
  intro i
  apply convex_convexHull ℝ _
  apply subset_convexHull
  simp
private lemma starRegion_isConnected_of_zero_mem (N : ℕ) (R : ℝ) (h0 : (0 : ℂ) ∈ starRegion N R) : IsConnected (starRegion N R) :=
  ((interior_starConvex_at_zero (starClosedFan_starConvex N R) h0).isPathConnected h0).isConnected
private lemma starRegion_isOpen (N : ℕ) (R : ℝ) : IsOpen (starRegion N R) := isOpen_interior
private lemma cross_adjacent_sign (a b c : ℂ) : Complex.orientation.areaForm (a-b) (c-b) = -Complex.orientation.areaForm (b-a) (c-a) := by
  simp only [Complex.areaForm, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring
private lemma starRadius_lt_outer_cos (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((m : ℝ) * Real.sin (Real.pi / (m : ℝ)) * Real.cos (Real.pi / (m : ℝ))) < R^2) : starRadius m R < R * Real.cos (Real.pi / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hsin := starAngle_sin_pos m hm
  have hcos := starAngle_cos_pos m hm
  have hprod : 0 < (m : ℝ)*Real.sin (Real.pi / (m : ℝ))*Real.cos (Real.pi / (m : ℝ)) :=
    mul_pos (mul_pos hmpos hsin) hcos
  have hone := (div_lt_iff₀ hprod).mp hlarge
  unfold starRadius
  apply (div_lt_iff₀ (mul_pos (mul_pos hmpos hR) hsin)).mpr
  nlinarith [hone]
private lemma starVertexRaw_triple_cross_even (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) (heven : i.val % 2 = 0) : Complex.orientation.areaForm (starVertexRaw m R (i+1)-starVertexRaw m R i) (starVertexRaw m R (i+2)-starVertexRaw m R i) = 2*R*Real.sin (Real.pi/(m:ℝ))*(starRadius m R-R*Real.cos (Real.pi/(m:ℝ))) := by
  let p : ℂ := (starRotation m : ℂ)^(i.val/2)
  let θ : ℝ := Real.pi/(m:ℝ)
  have hp : ‖p‖ = 1 := by
    simp only [p, norm_pow]
    rw [starRotation_eq_exp, Complex.norm_exp_ofReal_mul_I, one_pow]
  have ha : starVertexRaw m R i = p*(R:ℂ) := starVertexRaw_even m R i heven
  have hb : starVertexRaw m R (i+1) = p*circleMap 0 (starRadius m R) θ := by
    rw [starVertexRaw_add_one_even m hm R i heven]
    dsimp [p, θ, circleMap]
    ring
  have hc : starVertexRaw m R (i+2) = p*circleMap 0 R (2*θ) := by
    rw [starVertexRaw_add_two m hm R i, ha, starRotation_eq_exp]
    dsimp [circleMap, θ]
    ring
  rw [ha, hb, hc, ← mul_sub, ← mul_sub, cross_mul_left, hp, one_pow, one_mul]
  exact base_even_triple_cross R (starRadius m R) θ
private lemma starVertexRaw_triple_cross_odd (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (i : Fin (2*m)) (hodd : i.val % 2 ≠ 0) : Complex.orientation.areaForm (starVertexRaw m R (i+1)-starVertexRaw m R i) (starVertexRaw m R (i+2)-starVertexRaw m R i) = 2*starRadius m R*Real.sin (Real.pi/(m:ℝ))*(R-starRadius m R*Real.cos (Real.pi/(m:ℝ))) := by
  let p : ℂ := (starRotation m : ℂ)^(i.val/2)
  let θ : ℝ := Real.pi/(m:ℝ)
  have hp : ‖p‖ = 1 := by
    simp only [p, norm_pow]
    rw [starRotation_eq_exp, Complex.norm_exp_ofReal_mul_I, one_pow]
  have ha : starVertexRaw m R i = p*circleMap 0 (starRadius m R) θ := starVertexRaw_odd m R i hodd
  have hb : starVertexRaw m R (i+1) = p*circleMap 0 R (2*θ) := by
    rw [starVertexRaw_add_one_odd m hm R i hodd]
    simp only [p, θ, circleMap_zero, starRotation_eq_exp]
    ring
  have hc : starVertexRaw m R (i+2) = p*circleMap 0 (starRadius m R) (3*θ) := by
    rw [starVertexRaw_add_two m hm R i, ha, starRotation_eq_exp]
    have hpolar := polarPoint_mul (starRadius m R) θ (2*θ)
    rw [show θ+2*θ = 3*θ by ring] at hpolar
    calc
      _ = p*(circleMap 0 (starRadius m R) θ * Complex.exp (((2*θ:ℝ):ℂ)*Complex.I)) := by
        dsimp [θ]
        ring
      _ = _ := by rw [hpolar]
  rw [ha, hb, hc, ← mul_sub, ← mul_sub, cross_mul_left, hp, one_pow, one_mul]
  exact base_odd_triple_cross R (starRadius m R) θ
private lemma starVertexRaw_triple_cross_ne_zero (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((m:ℝ)*Real.sin (Real.pi/(m:ℝ))*Real.cos (Real.pi/(m:ℝ))) < R^2) (i : Fin (2*m)) : Complex.orientation.areaForm (starVertexRaw m R (i+1)-starVertexRaw m R i) (starVertexRaw m R (i+2)-starVertexRaw m R i) ≠ 0 := by
  have hr := starRadius_pos m hm R hR
  have hrc := starRadius_lt_outer_cos m hm R hR hlarge
  have hsin := starAngle_sin_pos m hm
  have hcos := starAngle_cos_pos m hm
  have hcosle := Real.cos_le_one (Real.pi/(m:ℝ))
  have hrR : starRadius m R < R := by nlinarith [mul_le_mul_of_nonneg_left hcosle hR.le]
  have hdiff : 0 < R-starRadius m R*Real.cos (Real.pi/(m:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcosle hr.le]
  by_cases heven : i.val % 2 = 0
  · rw [starVertexRaw_triple_cross_even m hm R i heven]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hR.ne') hsin.ne')
      (sub_ne_zero.mpr hrc.ne)
  · rw [starVertexRaw_triple_cross_odd m hm R i heven]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hr.ne') hsin.ne') hdiff.ne'
private lemma starVertexRaw_adjacent_inter (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((m:ℝ)*Real.sin (Real.pi/(m:ℝ))*Real.cos (Real.pi/(m:ℝ))) < R^2) (i : Fin (2*m)) : segment ℝ (starVertexRaw m R i) (starVertexRaw m R (i+1)) ∩ segment ℝ (starVertexRaw m R (i+1)) (starVertexRaw m R (i+2)) = {starVertexRaw m R (i+1)} := by
  apply adjacent_segments_inter_of_cross_ne_zero
  rw [cross_adjacent_sign]
  exact neg_ne_zero.mpr (starVertexRaw_triple_cross_ne_zero m hm R hR hlarge i)
private lemma starVertex_adjacent_inter (N : ℕ) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((symmetryOrder N:ℝ)*Real.sin (Real.pi/(symmetryOrder N:ℝ))* Real.cos (Real.pi/(symmetryOrder N:ℝ))) < R^2) (i : Fin (sideIndex N+3)) : segment ℝ (starVertex N R i) (starVertex N R (i+1)) ∩ segment ℝ (starVertex N R (i+1)) (starVertex N R (i+2)) = {starVertex N R (i+1)} := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  simp only [starVertex, cast_fin_add_one, cast_fin_add_two]
  exact starVertexRaw_adjacent_inter _ hm R hR hlarge _
private lemma not_collinear_of_cross_ne_zero (a b c : ℂ) (h : Complex.orientation.areaForm (b-a) (c-a) ≠ 0) : ¬ Collinear ℝ {a,b,c} := by
  have hli : LinearIndependent ℝ ![b-a,c-a] := by
    by_contra hh
    apply h
    rw [Orientation.areaForm_to_volumeForm]
    exact Complex.orientation.volumeForm.map_linearDependent _ hh
  apply affineIndependent_iff_not_collinear_set.mp
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0:Fin 3),
    ← linearIndependent_equiv (finSuccAboveEquiv (0:Fin 3))]
  convert hli using 1
  ext i
  fin_cases i <;> rfl
private lemma starVertexRaw_not_collinear (m : ℕ) [NeZero m] (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((m:ℝ)*Real.sin (Real.pi/(m:ℝ))*Real.cos (Real.pi/(m:ℝ))) < R^2) (i : Fin (2*m)) : ¬ Collinear ℝ {starVertexRaw m R i, starVertexRaw m R (i+1), starVertexRaw m R (i+2)} := by
  exact not_collinear_of_cross_ne_zero _ _ _ (starVertexRaw_triple_cross_ne_zero m hm R hR hlarge i)
private lemma starVertex_not_collinear (N : ℕ) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((symmetryOrder N:ℝ)*Real.sin (Real.pi/(symmetryOrder N:ℝ))* Real.cos (Real.pi/(symmetryOrder N:ℝ))) < R^2) (i : Fin (sideIndex N+3)) : ¬ Collinear ℝ {starVertex N R i, starVertex N R (i+1), starVertex N R (i+2)} := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  simp only [starVertex, cast_fin_add_one, cast_fin_add_two]
  exact starVertexRaw_not_collinear _ hm R hR hlarge _
private lemma starVertex_isSimplePolygon_of_disjoint (N : ℕ) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((symmetryOrder N:ℝ)*Real.sin (Real.pi/(symmetryOrder N:ℝ))* Real.cos (Real.pi/(symmetryOrder N:ℝ))) < R^2) (hd : ∀ i j : Fin (sideIndex N+3), i ≠ j → j ≠ i+1 → i ≠ j+1 → Disjoint (segment ℝ (starVertex N R i) (starVertex N R (i+1))) (segment ℝ (starVertex N R j) (starVertex N R (j+1)))) : IsSimplePolygon (starVertex N R) := by
  exact ⟨hd,starVertex_adjacent_inter N R hR hlarge,starVertex_not_collinear N R hR hlarge⟩
private lemma starVertex_nonadjacent_disjoint (N : ℕ) (R : ℝ) (hR : 0 < R) : ∀ i j : Fin (sideIndex N+3), i ≠ j → j ≠ i+1 → i ≠ j+1 → Disjoint (segment ℝ (starVertex N R i) (starVertex N R (i+1))) (segment ℝ (starVertex N R j) (starVertex N R (j+1))) := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  intro i j hij hji hij'
  have hcast : ∀ a b : Fin (sideIndex N+3),
      Fin.cast (sideIndex_add_three N) a = Fin.cast (sideIndex_add_three N) b → a = b := by
    exact Fin.cast_injective (sideIndex_add_three N)
  have hc0 : Fin.cast (sideIndex_add_three N) i ≠ Fin.cast (sideIndex_add_three N) j := fun h => hij (hcast i j h)
  have hc1 : Fin.cast (sideIndex_add_three N) j ≠ Fin.cast (sideIndex_add_three N) i+1 := by
    rw [← cast_fin_add_one]
    exact fun h => hji (hcast j (i+1) h)
  have hc2 : Fin.cast (sideIndex_add_three N) i ≠ Fin.cast (sideIndex_add_three N) j+1 := by
    rw [← cast_fin_add_one]
    exact fun h => hij' (hcast i (j+1) h)
  have h := polar_cyclic_nonadjacent_disjoint (symmetryOrder N) hm (starProfile _ R)
    (starProfile_pos _ hm R hR) _ _ hc0 hc1 hc2
  simpa only [starVertex,cast_fin_add_one,starVertexRaw_eq_polarVertex] using h
private lemma starVertex_isSimplePolygon (N : ℕ) (R : ℝ) (hR : 0 < R) (hlarge : 1 / ((symmetryOrder N:ℝ)*Real.sin (Real.pi/(symmetryOrder N:ℝ))* Real.cos (Real.pi/(symmetryOrder N:ℝ))) < R^2) : IsSimplePolygon (starVertex N R) := by
  exact starVertex_isSimplePolygon_of_disjoint N R hR hlarge (starVertex_nonadjacent_disjoint N R hR)
private lemma claim_of_zero_mem_and_frontier (hzero : ∀ N : ℕ, ∀ R : ℝ, 0 < R → (0:ℂ) ∈ starRegion N R) (hfrontier : ∀ N : ℕ, ∀ R : ℝ, 0 < R → frontier (starRegion N R) = (⟨starVertex N R⟩ : Polygon ℂ (sideIndex N + 3)).boundary ℝ) : claim := by
  apply claim_of_star_polygon_geometry
  intro N R hR hl
  refine ⟨starVertex N R,starVertex_isSimplePolygon N R hR hl,
    starRegion_isOpen N R,starRegion_isConnected_of_zero_mem N R (hzero N R hR),
    starRegion_isBounded N R,hfrontier N R hR⟩
private lemma starVertex_conic_coverage (N : ℕ) (R : ℝ) (hR : 0 < R) (z : ℂ) : ∃ i : Fin (sideIndex N+3), 0 ≤ Complex.orientation.areaForm z (starVertex N R (i+1)) ∧ 0 ≤ Complex.orientation.areaForm (starVertex N R i) z := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  obtain ⟨i,h1,h2⟩ := polar_fan_conic_coverage (symmetryOrder N) hm
    (starProfile _ R) (starProfile_pos _ hm R hR) z
  refine ⟨Fin.cast (sideIndex_add_three N).symm i,?_,?_⟩
  · simpa only [starVertex,cast_fin_add_one,Fin.cast_cast,
      Fin.cast_eq_self,starVertexRaw_eq_polarVertex] using h2
  · simpa only [starVertex,Fin.cast_cast,
      Fin.cast_eq_self,starVertexRaw_eq_polarVertex] using h1
private lemma starVertex_norm_le_radius_sum (N : ℕ) (R : ℝ) (hR : 0 < R) (i : Fin (sideIndex N+3)) : ‖starVertex N R i‖ ≤ R+starRadius (symmetryOrder N) R := by
  have hm := symmetryOrder_ge_three N
  haveI : NeZero (symmetryOrder N) := NeZero.of_gt hm
  have hr := starRadius_pos _ hm R hR
  simp only [starVertex,starVertexRaw_eq_polarVertex,polarVertex,circleMap_zero,norm_mul,
    Complex.norm_real,Complex.norm_exp_ofReal_mul_I,mul_one]
  unfold starProfile
  split_ifs <;> rw [Real.norm_eq_abs,abs_of_pos (by assumption)] <;> linarith
private lemma starRegion_positive_inradius (N : ℕ) (R : ℝ) (hR : 0 < R) : let d := R*starRadius (symmetryOrder N) R*Real.sin (Real.pi/(symmetryOrder N:ℝ))
    let B := R+starRadius (symmetryOrder N) R
    0 < d/(2*B) ∧ Metric.ball (0:ℂ) (d/(2*B)) ⊆ starClosedFan N R := by
  dsimp only
  let d := R*starRadius (symmetryOrder N) R*Real.sin (Real.pi/(symmetryOrder N:ℝ))
  let B := R+starRadius (symmetryOrder N) R
  have hd : 0 < d := by
    simpa only [starVertex_edge_cross] using
      starVertex_edge_cross_pos N R hR (0 : Fin (sideIndex N+3))
  have hB : 0 < B := add_pos hR (starRadius_pos _ (symmetryOrder_ge_three N) R hR)
  refine ⟨div_pos hd (by positivity),?_⟩
  intro z hz
  have hzn : ‖z‖ < d/(2*B) := mem_ball_zero_iff.mp hz
  have hmul : ‖z‖*(2*B) < d := (lt_div_iff₀ (by positivity : 0 < 2*B)).mp hzn
  obtain ⟨i,h1,h2⟩ := starVertex_conic_coverage N R hR z
  apply mem_iUnion.mpr
  refine ⟨i,(triangle_mem_iff_cross _ _ _ (starVertex_edge_cross_pos N R hR i)).mpr ⟨h1,h2,?_⟩⟩
  have ha := starVertex_norm_le_radius_sum N R hR i
  have hb := starVertex_norm_le_radius_sum N R hR (i+1)
  have h3 := Complex.orientation.areaForm_le z (starVertex N R (i+1))
  have h4 := Complex.orientation.areaForm_le (starVertex N R i) z
  rw [starVertex_edge_cross]
  dsimp [d,B] at *
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg z),
    mul_le_mul_of_nonneg_right ha (norm_nonneg z)]
private lemma starRegion_zero_mem_of_inradius (N : ℕ) (R : ℝ) (hR : 0 < R) : (0:ℂ) ∈ starRegion N R := by
  obtain ⟨hp,hsub⟩ := starRegion_positive_inradius N R hR
  exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨_,hp,hsub⟩)
private lemma starRegion_frontier (N : ℕ) (R : ℝ) (hR : 0 < R) : frontier (starRegion N R) = (⟨starVertex N R⟩ : Polygon ℂ (sideIndex N + 3)).boundary ℝ := by
  simpa only [starRegion, starClosedFan, Polygon.boundary, Polygon.edgeSet,
    affineSegment_eq_segment, finRotate_apply]
    using finite_cyclic_fan_frontier (starVertex N R)
    (starVertex_edge_cross_pos N R hR) (starRegion_zero_mem_of_inradius N R hR)
    (starFan_pairwise_aeDisjoint N R hR)
theorem result : claim :=
  claim_of_zero_mem_and_frontier starRegion_zero_mem_of_inradius starRegion_frontier
end D5.S3.Analytic.Torsion.PolynomialContentNoMaximizer
