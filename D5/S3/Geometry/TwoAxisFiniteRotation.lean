/- GID: D5/S3/Geometry/TwoAxisFiniteRotation
   generality: G
   mirror-B: D5/B/S3/Geometry/TwoAxisFiniteRotation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional, mathlib/module/Mathlib.Analysis.Normed.Module.Connected]
   utility: none
   digest: Exact finite words in two axis circles and transport along moving axes. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! Exact algebraic generation of rotations and fixed-output moving-axis transport. -/

noncomputable section

open Set Metric Module
open scoped InnerProductSpace

namespace D5.S3.Geometry.TwoAxisFiniteRotation

/-- The original three dimensional Euclidean vector carrier. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Actual orthogonal linear maps, with composition as multiplication. -/
abbrev Orthogonal := Space ≃ₗᵢ[ℝ] Space

/-- Orientation is measured on the original real linear map. -/
def determinant (R : Orthogonal) : ℝ := LinearMap.det R.toLinearMap

private theorem determinant_one : determinant (1 : Orthogonal) = 1 := by
  change LinearMap.det (1 : Space →ₗ[ℝ] Space) = 1
  simp

private theorem determinant_mul (R S : Orthogonal) :
    determinant (R * S) = determinant R * determinant S := by
  change LinearMap.det (R.toLinearMap * S.toLinearMap) = _
  exact map_mul _ _ _

private theorem determinant_inv_one {R : Orthogonal} (h : determinant R = 1) :
    determinant R⁻¹ = 1 := by
  have hm := determinant_mul R R⁻¹
  simpa only [mul_inv_cancel, determinant_one, h, one_mul] using hm.symm

/-- The full circle about an axis: every determinant-one isometry fixing that vector.
No particular angle, dense subset, or closure of angles is selected. -/
def axisCircle (a : Space) : Subgroup Orthogonal where
  carrier := {R | determinant R = 1 ∧ R a = a}
  one_mem' := ⟨determinant_one, rfl⟩
  mul_mem' := by
    rintro R S ⟨hR, hRa⟩ ⟨hS, hSa⟩
    exact ⟨by rw [determinant_mul, hR, hS]; norm_num, by simp [hRa, hSa]⟩
  inv_mem' := by
    rintro R ⟨hR, hRa⟩
    refine ⟨determinant_inv_one hR, ?_⟩
    apply R.injective
    simpa using hRa.symm

/-- An explicit finite word, with a letter in either of the two full axis circles. -/
def IsAxisWord (a b : Space) (l : List Orthogonal) : Prop :=
  ∀ R ∈ l, R ∈ axisCircle a ∨ R ∈ axisCircle b

/-- Algebraic finite-word membership. This definition uses no topological closure. -/
def wordGroup (a b : Space) : Subgroup Orthogonal where
  carrier := {R | ∃ l : List Orthogonal, IsAxisWord a b l ∧ l.prod = R}
  one_mem' := ⟨[], by simp [IsAxisWord], rfl⟩
  mul_mem' := by
    rintro R S ⟨l, hl, rfl⟩ ⟨k, hk, rfl⟩
    refine ⟨l ++ k, ?_, List.prod_append⟩
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · exact hl T hT
    · exact hk T hT
  inv_mem' := by
    rintro R ⟨l, hl, rfl⟩
    refine ⟨(l.map (fun T => T⁻¹)).reverse, ?_, (List.prod_inv_reverse l).symm⟩
    intro T hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hT)
    exact (hl S hS).elim (fun h => Or.inl ((axisCircle a).inv_mem h))
      (fun h => Or.inr ((axisCircle b).inv_mem h))

private theorem circle_le_word_left (a b : Space) : axisCircle a ≤ wordGroup a b := by
  intro R hR
  refine ⟨[R], ?_, by simp⟩
  intro S hS
  have hSR : S = R := List.mem_singleton.mp hS
  subst S
  exact Or.inl hR

private theorem circle_le_word_right (a b : Space) : axisCircle b ≤ wordGroup a b := by
  intro R hR
  refine ⟨[R], ?_, by simp⟩
  intro S hS
  have hSR : S = R := List.mem_singleton.mp hS
  subst S
  exact Or.inr hR

private theorem word_determinant {a b : Space} {l : List Orthogonal}
    (hl : IsAxisWord a b l) : determinant l.prod = 1 := by
  revert hl
  induction l with
  | nil => intro hl; exact determinant_one
  | cons R l ih =>
    intro hl
    have hR : determinant R = 1 :=
      (hl R (by simp)).elim (fun h => h.1) (fun h => h.1)
    have hl' : IsAxisWord a b l := fun S hS => hl S (by simp [hS])
    rw [List.prod_cons, determinant_mul, hR, ih hl', one_mul]

private theorem determinant_plane_reflection {n : Space} (hn : n ≠ 0) :
    determinant (ℝ ∙ n)ᗮ.reflection = -1 := by
  rw [determinant, Submodule.det_reflection, (ℝ ∙ n).orthogonal_orthogonal,
    finrank_span_singleton hn]
  norm_num

theorem unit_perpendicular_pair (a b : Space) :
    ∃ n : Space, ‖n‖ = 1 ∧ ⟪a, n⟫_ℝ = 0 ∧ ⟪b, n⟫_ℝ = 0 := by
  classical
  let P : Submodule ℝ Space := Submodule.span ℝ (↑({a, b} : Finset Space) : Set Space)
  have hdim : finrank ℝ P ≤ 2 := by
    exact
      (finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset Space)).trans
        Finset.card_le_two
  have hne : Pᗮ ≠ ⊥ := by
    intro h
    have hd := P.finrank_add_finrank_orthogonal
    rw [h, finrank_bot] at hd
    have hV : finrank ℝ Space = 3 := by simp [Space]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hav : ⟪a, v⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) hv
  have hbv : ⟪b, v⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) hv
  refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
  · simp [norm_smul, norm_ne_zero_iff.mpr hv0]
  · simp [real_inner_smul_right, hav]
  · simp [real_inner_smul_right, hbv]

/-- Equal latitude circles are orbits of the full axis circle. The determinant
correction fixes both the axis and the source vector. -/
private theorem equal_latitude (a u v : Space) (huv : ‖u‖ = ‖v‖)
    (hinner : ⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ) :
    ∃ R : Orthogonal, R ∈ axisCircle a ∧ R u = v := by
  by_cases h : u = v
  · exact ⟨1, (axisCircle a).one_mem, by simpa using h⟩
  obtain ⟨n, hn, han, hun⟩ := unit_perpendicular_pair a u
  have hn0 : n ≠ 0 := by intro hz; simpa [hz] using hn
  let T : Orthogonal := (ℝ ∙ (u - v))ᗮ.reflection
  let S : Orthogonal := (ℝ ∙ n)ᗮ.reflection
  have hTa : T a = a := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hinner, sub_self]
  have hSa : S a = a := by
    apply Submodule.reflection_mem_subspace_eq_self
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr han
  have hSu : S u = u := by
    apply Submodule.reflection_mem_subspace_eq_self
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hun
  refine ⟨T * S, ⟨?_, ?_⟩, ?_⟩
  · rw [determinant_mul, determinant_plane_reflection (sub_ne_zero.mpr h),
      determinant_plane_reflection hn0]
    norm_num
  · change T (S a) = a
    rw [hSa, hTa]
  · change T (S u) = v
    rw [hSu]
    exact Submodule.reflection_sub huv

private theorem unit_inner_self {a : Space} (ha : ‖a‖ = 1) : ⟪a, a⟫_ℝ = 1 := by
  exact inner_self_eq_one_of_norm_eq_one ha

/-- A prescribed latitude near the first pole intersects the latitude of that
pole about the second axis. The third coordinate is constructed in the original
space, rather than obtained as a limit of rotations. -/
private theorem intersect_latitudes {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ ^ 2 < 1) (t : ℝ)
    (ht0 : ⟪a, b⟫_ℝ ^ 2 ≤ t) (ht1 : t ≤ 1) :
    ∃ u : Space, ‖u‖ = 1 ∧ ⟪b, u⟫_ℝ = ⟪b, a⟫_ℝ ∧ ⟪a, u⟫_ℝ = t := by
  let d := ⟪a, b⟫_ℝ
  let q := 1 - d ^ 2
  have hq : 0 < q := sub_pos.mpr hab
  have hdq : d ^ 2 + q = 1 := by dsimp [q]; ring
  let c := (t - d ^ 2) / q
  have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.mpr ht0) hq.le
  have hc1 : c ≤ 1 := (div_le_one hq).mpr (by dsimp [q]; linarith)
  have hc2 : c ^ 2 ≤ 1 := by
    simpa only [pow_two, mul_one] using mul_self_le_mul_self hc0 hc1
  have hcq : 0 ≤ q * (1 - c ^ 2) := mul_nonneg hq.le (sub_nonneg.mpr hc2)
  let z := Real.sqrt (q * (1 - c ^ 2))
  have hz : z ^ 2 = q * (1 - c ^ 2) := Real.sq_sqrt hcq
  obtain ⟨n, hn, han, hbn⟩ := unit_perpendicular_pair a b
  let e := a - d • b
  have he : ⟪e, e⟫_ℝ = q := by
    dsimp [e, q, d]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      unit_inner_self ha, unit_inner_self hb, real_inner_comm b a]
    ring
  have hbe : ⟪b, e⟫_ℝ = 0 := by
    simp [e, d, inner_sub_right, real_inner_smul_right, hb, real_inner_comm b a]
  have hae : ⟪a, e⟫_ℝ = q := by
    simp [e, q, d, inner_sub_right, real_inner_smul_right, ha, pow_two]
  have hen : ⟪e, n⟫_ℝ = 0 := by
    simp [e, inner_sub_left, real_inner_smul_left, han, hbn]
  have heb : ⟪e, b⟫_ℝ = 0 := (real_inner_comm b e).trans hbe
  have hnb : ⟪n, b⟫_ℝ = 0 := (real_inner_comm b n).trans hbn
  have hne : ⟪n, e⟫_ℝ = 0 := (real_inner_comm e n).trans hen
  have hct : c * q = t - d ^ 2 := div_mul_cancel₀ _ (ne_of_gt hq)
  refine ⟨d • b + c • e + z • n, ?_, ?_, ?_⟩
  · have hi : ⟪d • b + c • e + z • n, d • b + c • e + z • n⟫_ℝ = 1 := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        unit_inner_self hb, unit_inner_self hn, hbe, hbn, hen, heb, hnb, hne,
        mul_zero, zero_mul, add_zero, zero_add, mul_one]
      rw [he]
      nlinarith [hz, hdq]
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (d • b + c • e + z • n)]
  · simp [inner_add_right, real_inner_smul_right, hb, hbe, hbn, d,
      real_inner_comm b a]
  · simp only [inner_add_right, real_inner_smul_right, hae, han, mul_zero, add_zero]
    change d * d + c * q = t
    nlinarith [hct]

private theorem cap_reachable {a b y : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ ^ 2 < 1) (hy : ‖y‖ = 1)
    (hcap : ⟪a, b⟫_ℝ ^ 2 ≤ ⟪a, y⟫_ℝ) :
    ∃ R : Orthogonal, R ∈ wordGroup a b ∧ R a = y := by
  have htop : ⟪a, y⟫_ℝ ≤ 1 := by
    simpa [ha, hy] using real_inner_le_norm a y
  obtain ⟨u, hu, hbu, hau⟩ := intersect_latitudes ha hb hab _ hcap htop
  obtain ⟨S, hS, hSu⟩ := equal_latitude b a u (ha.trans hu.symm) hbu.symm
  obtain ⟨T, hT, hTy⟩ := equal_latitude a u y (hu.trans hy.symm) hau
  refine ⟨T * S, (wordGroup a b).mul_mem (circle_le_word_left a b hT)
    (circle_le_word_right a b hS), ?_⟩
  change T (S a) = y
  rw [hSu, hTy]

private theorem nearby_reachable {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ ^ 2 < 1) :
    ∃ δ > 0, ∀ y : Space, ‖y‖ = 1 → dist a y < δ →
      ∃ R : Orthogonal, R ∈ wordGroup a b ∧ R a = y := by
  let δ := 1 - ⟪a, b⟫_ℝ ^ 2
  have hδ : 0 < δ := sub_pos.mpr hab
  have hδeq : δ + ⟪a, b⟫_ℝ ^ 2 = 1 := by dsimp [δ]; ring
  refine ⟨δ, hδ, ?_⟩
  intro y hy hnear
  apply cap_reachable ha hb hab hy
  have hdist : dist a y ^ 2 = 2 - 2 * ⟪a, y⟫_ℝ := by
    simp [dist_eq_norm, norm_sub_sq_real, ha, hy]
    ring
  have hsquare := mul_self_lt_mul_self (dist_nonneg (x := a) (y := y)) hnear
  have hδ1 : δ ≤ 1 := by dsimp [δ]; nlinarith [sq_nonneg ⟪a, b⟫_ℝ]
  have hδsq : δ ^ 2 ≤ δ := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hδ1 hδ.le
  nlinarith [hδeq]

private theorem sphere_orbit {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ ^ 2 < 1) (y : Space) (hy : ‖y‖ = 1) :
    ∃ R : Orthogonal, R ∈ wordGroup a b ∧ R a = y := by
  obtain ⟨δ, hδ, hnear⟩ := nearby_reachable ha hb hab
  let Sphere := ↥(Metric.sphere (0 : Space) 1)
  have hnorm (v : Sphere) : ‖(v : Space)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  let U : Set Sphere := {v | ∃ R : Orthogonal, R ∈ wordGroup a b ∧ R a = (v : Space)}
  have hlocal (v z : Sphere) (hv : v ∈ U) (hz : dist v z < δ) : z ∈ U := by
    obtain ⟨R, hR, hRv⟩ := hv
    have hd : dist a (R⁻¹ (z : Space)) = dist (v : Space) (z : Space) := by
      rw [← hRv]
      simpa using (R.isometry.dist_eq a (R⁻¹ (z : Space))).symm
    obtain ⟨S, hS, hSx⟩ := hnear (R⁻¹ (z : Space))
      (by simpa using hnorm z) (by rw [hd]; exact hz)
    refine ⟨R * S, (wordGroup a b).mul_mem hR hS, ?_⟩
    change R (S a) = (z : Space)
    rw [hSx]
    simp
  have hopen : IsOpen U := Metric.isOpen_iff.mpr fun v hv =>
    ⟨δ, hδ, fun z hz => hlocal v z hv (by simpa [dist_comm] using hz)⟩
  have hcompl : IsOpen Uᶜ := by
    apply Metric.isOpen_iff.mpr
    intro v hv
    refine ⟨δ, hδ, ?_⟩
    intro z hz hzu
    exact hv (hlocal z v hzu (by simpa using hz))
  have hrank : 1 < Module.rank ℝ Space := by
    rw [← Module.finrank_eq_rank]
    norm_num [Space]
  letI : PreconnectedSpace Sphere := isPreconnected_iff_preconnectedSpace.mp
    (_root_.isPreconnected_sphere hrank (0 : Space) 1)
  have hU : U = Set.univ := (show IsClopen U from ⟨isOpen_compl_iff.mp hcompl, hopen⟩).eq_univ
    ⟨⟨a, by simpa only [Metric.mem_sphere, dist_zero_right] using ha⟩,
      1, (wordGroup a b).one_mem, rfl⟩
  change (⟨y, by simpa only [Metric.mem_sphere, dist_zero_right] using hy⟩ : Sphere) ∈ U
  rw [hU]
  exact Set.mem_univ _

private theorem unit_axes_generate {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ ^ 2 < 1) (R : Orthogonal) (hR : determinant R = 1) :
    R ∈ wordGroup a b := by
  obtain ⟨S, hS, hSa⟩ := sphere_orbit ha hb hab (R a) (by simpa using ha)
  have hSdet : determinant S = 1 := by
    obtain ⟨l, hl, rfl⟩ := hS
    exact word_determinant hl
  have hfix : S⁻¹ * R ∈ axisCircle a := by
    refine ⟨?_, ?_⟩
    · rw [determinant_mul, determinant_inv_one hSdet, hR]
      norm_num
    · change S⁻¹ (R a) = a
      rw [← hSa]
      simp
  have hmem := (wordGroup a b).mul_mem hS (circle_le_word_left a b hfix)
  simpa only [mul_inv_cancel_left] using hmem

private theorem axisCircle_smul {a : Space} {c : ℝ} (hc : c ≠ 0) :
    axisCircle (c • a) = axisCircle a := by
  ext R
  change (determinant R = 1 ∧ R (c • a) = c • a) ↔
    (determinant R = 1 ∧ R a = a)
  simp only [map_smul, smul_right_inj hc]

/-- Every original determinant-one orthogonal map is an exact finite word in
the full circles about two arbitrary nonparallel axes. Nonparallelism is given
by the strictly positive Gram determinant; neither axis is normalized in the result. -/
theorem two_axis_finite_word (a b : Space)
    (hab : ⟪a, b⟫_ℝ ^ 2 < ‖a‖ ^ 2 * ‖b‖ ^ 2)
    (R : Orthogonal) (hR : determinant R = 1) :
    ∃ l : List Orthogonal, IsAxisWord a b l ∧ l.prod = R := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at hab
  have hb0 : b ≠ 0 := by intro h; simp [h] at hab
  have ha : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
  let a' := ‖a‖⁻¹ • a
  let b' := ‖b‖⁻¹ • b
  have ha' : ‖a'‖ = 1 := by simp [a', norm_smul, ha]
  have hb' : ‖b'‖ = 1 := by simp [b', norm_smul, hb]
  have hab' : ⟪a', b'⟫_ℝ ^ 2 < 1 := by
    have hp : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 := mul_pos (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
    have hd : (⟪a', b'⟫_ℝ ^ 2) * (‖a‖ ^ 2 * ‖b‖ ^ 2) = ⟪a, b⟫_ℝ ^ 2 := by
      dsimp [a', b']
      simp only [real_inner_smul_left, real_inner_smul_right]
      field_simp [ha, hb] <;> ring
    nlinarith [hd]
  obtain ⟨l, hl, he⟩ := unit_axes_generate ha' hb' hab' R hR
  refine ⟨l, ?_, he⟩
  intro S hS
  have hca : axisCircle a' = axisCircle a := axisCircle_smul (inv_ne_zero ha)
  have hcb : axisCircle b' = axisCircle b := axisCircle_smul (inv_ne_zero hb)
  simpa only [hca, hcb] using hl S hS

/-- Simultaneous rotation of the original two vector inputs. Scalar coordinates
may be fixed parameters of the function evaluated on these pairs. -/
def rotatePair (R : Orthogonal) (p : Space × Space) : Space × Space :=
  (R p.1, R p.2)

private theorem rotatePair_mul (R S : Orthogonal) (p : Space × Space) :
    rotatePair (R * S) p = rotatePair R (rotatePair S p) := rfl

/-- Fixed-output transport under moving axes. At the actual input `rotatePair O p`,
the available circles fix `O a` and `O b`. No action is applied to the output of
`F`. In particular this applies to a scalar/vector residual without assuming
any regularity of that residual or of the original total relation.

The local hypothesis is required only along the rotation orbit of this one
original pair. A right letter `g` is implemented there by the left rotation
`O * g * O⁻¹`, which fixes the corresponding current axis. -/
theorem moving_axis_invariance {Y : Type*} (F : (Space × Space) → Y)
    (p : Space × Space) (a b : Space)
    (hab : ⟪a, b⟫_ℝ ^ 2 < ‖a‖ ^ 2 * ‖b‖ ^ 2)
    (hlocal : ∀ (O : Orthogonal), determinant O = 1 →
      ∀ (T : Orthogonal),
        (T ∈ axisCircle (O a) ∨ T ∈ axisCircle (O b)) →
        F (rotatePair T (rotatePair O p)) = F (rotatePair O p))
    (R : Orthogonal) (hR : determinant R = 1) :
    F (rotatePair R p) = F p := by
  have hright (O g : Orthogonal) (hO : determinant O = 1)
      (hg : g ∈ axisCircle a ∨ g ∈ axisCircle b) :
      F (rotatePair (O * g) p) = F (rotatePair O p) := by
    have hgdet : determinant g = 1 := hg.elim (fun h => h.1) (fun h => h.1)
    have hdet : determinant (O * g * O⁻¹) = 1 := by
      rw [determinant_mul, determinant_mul, hO, hgdet, determinant_inv_one hO]
      norm_num
    have hfix (c : Space) (hc : g c = c) : (O * g * O⁻¹) (O c) = O c := by
      change O (g (O⁻¹ (O c))) = O c
      simp [hc]
    have hcircle : O * g * O⁻¹ ∈ axisCircle (O a) ∨
        O * g * O⁻¹ ∈ axisCircle (O b) :=
      hg.elim (fun h => Or.inl ⟨hdet, hfix a h.2⟩)
        (fun h => Or.inr ⟨hdet, hfix b h.2⟩)
    have h := hlocal O hO (O * g * O⁻¹) hcircle
    rw [← rotatePair_mul] at h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have hword : ∀ (l : List Orthogonal), IsAxisWord a b l →
      ∀ (O : Orthogonal), determinant O = 1 →
        F (rotatePair (O * l.prod) p) = F (rotatePair O p) := by
    intro l
    induction l with
    | nil => intro hl O hO; simp
    | cons g l ih =>
      intro hl O hO
      have hg : g ∈ axisCircle a ∨ g ∈ axisCircle b := hl g (by simp)
      have hl' : IsAxisWord a b l := fun S hS => hl S (by simp [hS])
      have hOg : determinant (O * g) = 1 := by
        rw [determinant_mul, hO, hg.elim (fun h => h.1) (fun h => h.1), one_mul]
      calc
        F (rotatePair (O * (g :: l).prod) p) =
            F (rotatePair ((O * g) * l.prod) p) := by rw [List.prod_cons, mul_assoc]
        _ = F (rotatePair (O * g) p) := ih hl' (O * g) hOg
        _ = F (rotatePair O p) := hright O g hO hg
  obtain ⟨l, hl, he⟩ := two_axis_finite_word a b hab R hR
  have h := hword l hl 1 determinant_one
  simpa [he, rotatePair] using h

end D5.S3.Geometry.TwoAxisFiniteRotation
