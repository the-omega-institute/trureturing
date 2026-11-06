/- GID: D5/S3/Geometry/FiniteSubcomplexCylinder
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSubcomplexCylinder
   mirror-E: none(waiver:finite-subcomplex-cylinder)
   anchors: [mathlib/module/Mathlib.Topology.Compactness.Compact, mathlib/module/Mathlib.Topology.Piecewise]
   utility: none
   digest: The original coordinate collar retracts the entire bottom-or-subcomplex cylinder and gives arbitrary-target homotopy extension. -/
import D5.S3.Geometry.FiniteConeUnionWedge
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Piecewise

/-!
Source-preparation draft; no elaboration or kernel check has been run.

The carrier and deformation are the original coordinate realization and the
generalized collar in `FiniteConeCollapse`. There is no subdivision, replacement
label type, cone hypothesis, or assumed extension property. The time selector
below is deliberately NOT asserted continuous where the control vanishes.
The compact-parameter lemma is used precisely at that singular set.
-/

noncomputable section

open Set Topology Filter
open scoped unitInterval ContinuousMap
open D5.S3.Geometry.FiniteConeCollapse

namespace D5.S3.Geometry.FiniteSubcomplexCylinder

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Space (K : PreAbstractSimplicialComplex V) := ↥(realization K)

/-- The subspace on the original coordinates, inside the original ambient space. -/
def Subspace (K L : PreAbstractSimplicialComplex V) : Set (Space K) :=
  {x | x.val ∈ realization L}

/-- The whole bottom together with the whole cylinder over the subcomplex. -/
def Cylinder (K L : PreAbstractSimplicialComplex V) : Set (Space K × I) :=
  {z | z.2 = 0 ∨ z.1.val ∈ realization L}

/-- A face witness really supplies a coordinate point: Mathlib faces are nonempty.
No inhabitant of the original label type is assumed. -/
theorem realization_nonempty_iff_faces_nonempty (L : PreAbstractSimplicialComplex V) :
    (realization L).Nonempty ↔ (L : Set (Finset V)).Nonempty := by
  constructor
  · rintro ⟨x, s, hs, _⟩
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    obtain ⟨v, hv⟩ := (L.isRelLowerSet_faces hs).1
    exact ⟨Pi.single v (1 : ℝ), s, hs,
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩

theorem realization_eq_empty_of_no_faces (L : PreAbstractSimplicialComplex V)
    (hL : ¬ (L : Set (Finset V)).Nonempty) : realization L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hL ((realization_nonempty_iff_faces_nonempty L).1 ⟨x, hx⟩)

/-- Uniform control at a point fixed for every value of a compact parameter.
The selector `s` is arbitrary; its continuity is neither needed nor asserted. -/
private theorem continuousAt_arbitrary_time
    {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    (H : I × X → X) (hH : Continuous H) (b : W → X) (s : W → I)
    (w : W) (hb : ContinuousAt b w) (hfixed : ∀ t, H (t, b w) = b w) :
    ContinuousAt (fun y => H (s y, b y)) w := by
  rw [continuousAt_def]
  intro O hO
  rw [hfixed (s w)] at hO
  obtain ⟨U, hUO, hU, hwU⟩ := mem_nhds_iff.mp hO
  have hpre : IsOpen (H ⁻¹' U) := hU.preimage hH
  have hprod : (univ : Set I) ×ˢ {b w} ⊆ H ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    obtain rfl := Set.mem_singleton_iff.mp hx
    change H (t, b w) ∈ U
    rw [hfixed t]
    exact hwU
  obtain ⟨J, N, _, hN, hIJ, hwN, hJN⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hpre hprod
  have hNb : N ∈ 𝓝 (b w) := hN.mem_nhds (hwN (by simp))
  apply Filter.mem_of_superset (hb.preimage_mem_nhds hNb)
  intro y hy
  exact hUO (hJN ⟨hIJ (mem_univ (s y)), hy⟩)

section NonemptyFaces

variable (P : SubcomplexPair V)

/-- The collar control, truncated to the unit interval. -/
def control (x : P.Space) : I :=
  ⟨min (P.delta x / P.epsilon) 1,
    le_min (div_nonneg (P.delta_nonneg x) P.epsilon_pos.le) zero_le_one,
    min_le_right _ _⟩

private theorem continuous_control : Continuous (control P) :=
  ((P.continuous_delta.div_const P.epsilon).min continuous_const).subtype_mk _

private theorem control_eq_zero_iff (x : P.Space) :
    (control P x : ℝ) = 0 ↔ x ∈ P.subcomplexSet := by
  constructor
  · intro h
    apply (P.delta_eq_zero_iff x).1
    have hd : P.delta x / P.epsilon = 0 := by
      by_cases hle : P.delta x / P.epsilon ≤ 1
      · simpa only [control, min_eq_left hle] using h
      · have he : (1 : ℝ) = 0 := by
          simpa only [control, min_eq_right (le_of_not_ge hle)] using h
        norm_num at he
    exact (div_eq_zero_iff.mp hd).resolve_right P.epsilon_pos.ne'
  · intro h
    have hd : P.delta x = 0 := (P.delta_eq_zero_iff x).2 h
    simp [control, hd]

private theorem deform_one_mem_of_control_lt_one (x : P.Space)
    (hx : (control P x : ℝ) < 1) : P.deform 1 x ∈ P.subcomplexSet := by
  have hmin : min (P.delta x / P.epsilon) 1 < 1 := hx
  have hdiv : P.delta x / P.epsilon < 1 :=
    (min_lt_iff.mp hmin).resolve_right (lt_irrefl 1)
  have hd : P.delta x < P.epsilon := by
    simpa only [one_mul] using (div_lt_iff₀ P.epsilon_pos).mp hdiv
  exact P.deform_one_mem_subcomplex x hd.le

/-- At zero control, division is explicitly zero; its value need not be continuous.
For positive control this is the usual ratio, clamped at one. -/
private def time (x : P.Space) (t : I) : I :=
  ⟨min ((t : ℝ) / (control P x : ℝ)) 1,
    le_min (div_nonneg t.property.1 (control P x).property.1) zero_le_one,
    min_le_right _ _⟩

private theorem time_zero_control (x : P.Space) (t : I)
    (hx : (control P x : ℝ) = 0) : time P x t = 0 := by
  apply Subtype.ext
  simp [time, hx]

private theorem time_lower (x : P.Space) (t : I)
    (hx : 0 < (control P x : ℝ)) (ht : (t : ℝ) ≤ (control P x : ℝ)) :
    (time P x t : ℝ) = (t : ℝ) / (control P x : ℝ) := by
  exact min_eq_left ((div_le_one hx).mpr ht)

private theorem time_upper (x : P.Space) (t : I)
    (hx : 0 < (control P x : ℝ)) (ht : (control P x : ℝ) ≤ (t : ℝ)) :
    time P x t = 1 := by
  apply Subtype.ext
  exact min_eq_right ((one_le_div hx).mpr ht)

private def horizontal (z : P.Space × I) : P.Space :=
  P.deform (time P z.1 z.2) z.1

private theorem continuous_horizontal : Continuous (horizontal P) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : (control P z.1 : ℝ) = 0
  · exact continuousAt_arbitrary_time
      (fun q : I × P.Space => P.deform q.1 q.2) P.continuous_deform
      Prod.fst (fun q => time P q.1 q.2) z continuous_fst.continuousAt
      (fun t => P.deform_fixed t z.1 ((control_eq_zero_iff P z.1).mp hz))
  · have hc : ContinuousAt (fun q : P.Space × I => (control P q.1 : ℝ)) z :=
      (continuous_subtype_val.comp ((continuous_control P).comp continuous_fst)).continuousAt
    have ht : ContinuousAt
        (fun q : P.Space × I => min ((q.2 : ℝ) / (control P q.1 : ℝ)) 1) z :=
      ((continuous_subtype_val.comp continuous_snd).continuousAt.div hc hz).min
        continuous_const.continuousAt
    have hs : ContinuousAt (fun q : P.Space × I => time P q.1 q.2) z :=
      tendsto_subtype_rng.mpr ht
    exact P.continuous_deform.continuousAt.comp (hs.prodMk continuous_fst.continuousAt)

private def height (z : P.Space × I) : I :=
  ⟨max ((z.2 : ℝ) - (control P z.1 : ℝ)) 0,
    le_max_right _ _,
    max_le ((sub_le_self _ (control P z.1).property.1).trans z.2.property.2) zero_le_one⟩

private theorem continuous_height : Continuous (height P) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp ((continuous_control P).comp continuous_fst))).max continuous_const

private theorem height_eq_zero (z : P.Space × I)
    (hz : (z.2 : ℝ) ≤ (control P z.1 : ℝ)) : height P z = 0 := by
  apply Subtype.ext
  exact max_eq_right (sub_nonpos.mpr hz)

private theorem horizontal_mem_of_height_ne_zero (z : P.Space × I)
    (hz : height P z ≠ 0) : horizontal P z ∈ P.subcomplexSet := by
  have hlt : (control P z.1 : ℝ) < (z.2 : ℝ) := by
    by_contra h
    exact hz (height_eq_zero P z (le_of_not_gt h))
  by_cases hu : (control P z.1 : ℝ) = 0
  · change P.deform (time P z.1 z.2) z.1 ∈ P.subcomplexSet
    rw [time_zero_control P z.1 z.2 hu, P.deform_zero]
    exact (control_eq_zero_iff P z.1).mp hu
  · have hu0 : 0 < (control P z.1 : ℝ) :=
      lt_of_le_of_ne (control P z.1).property.1 (Ne.symm hu)
    change P.deform (time P z.1 z.2) z.1 ∈ P.subcomplexSet
    rw [time_upper P z.1 z.2 hu0 hlt.le]
    exact deform_one_mem_of_control_lt_one P z.1 (hlt.trans_le z.2.property.2)

/-- The formula retraction for an inhabited face collection. The singular
continuity proof above covers both zero-control strata, the positive-control
seam, and the full-control top corner. -/
def nonemptyRetraction : C(P.Space × I, Cylinder P.ambient P.subcomplex) where
  toFun z := ⟨(horizontal P z, height P z), by
    by_cases hz : height P z = 0
    · exact Or.inl hz
    · exact Or.inr (horizontal_mem_of_height_ne_zero P z hz)⟩
  continuous_toFun := ((continuous_horizontal P).prodMk (continuous_height P)).subtype_mk _

/-- Exact lower-branch formula, with a bounded ratio. Equality at the seam
uses this formula; the upper expression has the same value there. -/
theorem nonemptyRetraction_lower (x : P.Space) (t : I)
    (hx : 0 < (control P x : ℝ)) (ht : (t : ℝ) ≤ (control P x : ℝ)) :
    (nonemptyRetraction P (x, t)).val =
      (P.deform ⟨(t : ℝ) / (control P x : ℝ),
        div_nonneg t.property.1 hx.le, (div_le_one hx).mpr ht⟩ x, 0) := by
  apply Prod.ext
  · change P.deform (time P x t) x = _
    exact congrArg (fun s : I => P.deform s x)
      (Subtype.ext (time_lower P x t hx ht))
  · exact height_eq_zero P (x, t) ht

/-- Exact upper-branch formula. The height is the unnormalized difference. -/
theorem nonemptyRetraction_upper (x : P.Space) (t : I)
    (hx : 0 < (control P x : ℝ)) (ht : (control P x : ℝ) < (t : ℝ)) :
    (nonemptyRetraction P (x, t)).val =
      (P.deform 1 x, ⟨(t : ℝ) - (control P x : ℝ), sub_nonneg.mpr ht.le,
        (sub_le_self _ hx.le).trans t.property.2⟩) := by
  apply Prod.ext
  · change P.deform (time P x t) x = _
    rw [time_upper P x t hx ht.le]
  · apply Subtype.ext
    exact max_eq_left (sub_nonneg.mpr ht.le)

private theorem nonemptyRetraction_bottom (x : P.Space) :
    (nonemptyRetraction P (x, 0)).val = (x, 0) := by
  apply Prod.ext
  · have ht : time P x 0 = 0 := by apply Subtype.ext; simp [time]
    change P.deform (time P x 0) x = x
    rw [ht, P.deform_zero]
  · exact height_eq_zero P (x, 0) (control P x).property.1

private theorem nonemptyRetraction_side (x : P.Space) (t : I)
    (hx : x ∈ P.subcomplexSet) : (nonemptyRetraction P (x, t)).val = (x, t) := by
  apply Prod.ext
  · exact P.deform_fixed _ x hx
  · apply Subtype.ext
    have hu := (control_eq_zero_iff P x).mpr hx
    change max ((t : ℝ) - (control P x : ℝ)) 0 = (t : ℝ)
    rw [hu, sub_zero, max_eq_left t.property.1]

theorem nonemptyRetraction_fixed (z : P.Space × I)
    (hz : z.2 = 0 ∨ z.1.val ∈ realization P.subcomplex) :
    (nonemptyRetraction P z).val = z := by
  rcases z with ⟨x, t⟩
  rcases hz with ht | hx
  · subst t
    exact nonemptyRetraction_bottom P x
  · exact nonemptyRetraction_side P x t hx

end NonemptyFaces

variable (K L : PreAbstractSimplicialComplex V)

/-- No face minimum or point of the subcomplex is used in this branch. -/
private def bottomRetraction : C(Space K × I, Cylinder K L) :=
  ⟨fun z => ⟨(z.1, 0), Or.inl rfl⟩,
    (continuous_fst.prodMk continuous_const).subtype_mk _⟩

/-- A continuous retraction for every finite subcomplex inclusion, including
empty label types, empty realizations, empty subcomplexes and ghost labels. -/
def retraction (hLK : L ≤ K) : C(Space K × I, Cylinder K L) := by
  classical
  exact if hL : (L : Set (Finset V)).Nonempty then
    nonemptyRetraction ⟨K, L, hLK, hL⟩
  else bottomRetraction K L

/-- Every point of the entire target is fixed, at every time. -/
theorem retraction_fixed (hLK : L ≤ K) (z : Space K × I)
    (hz : z.2 = 0 ∨ z.1.val ∈ realization L) : (retraction K L hLK z).val = z := by
  classical
  unfold retraction
  split_ifs with hL
  · exact nonemptyRetraction_fixed ⟨K, L, hLK, hL⟩ z hz
  · rcases hz with ht | hx
    · apply Prod.ext
      · rfl
      · exact ht.symm
    · have hempty := realization_eq_empty_of_no_faces L hL
      rw [hempty] at hx
      exact False.elim hx

private theorem subspace_closed : IsClosed (Subspace K L) :=
  (FiniteConeUnionWedge.realization_closed L).preimage continuous_subtype_val

section Extension

variable {Y : Type*} [TopologicalSpace Y]
variable (f : C(Space K, Y)) (g : C(I × Subspace K L, Y))

private def boundaryMap : Cylinder K L → Y := by
  classical
  exact fun z => if hx : z.val.1.val ∈ realization L then
    g (z.val.2, ⟨z.val.1, hx⟩) else f z.val.1

private theorem boundaryMap_bottom
    (hzero : ∀ a : Subspace K L, g (0, a) = f a.val)
    (z : Cylinder K L) (hz : z.val.2 = 0) :
    boundaryMap K L f g z = f z.val.1 := by
  dsimp only [boundaryMap]
  split_ifs with hx
  · rw [hz]
    exact hzero ⟨z.val.1, hx⟩
  · rfl

private theorem boundaryMap_side (z : Cylinder K L) (hz : z.val.1.val ∈ realization L) :
    boundaryMap K L f g z = g (z.val.2, ⟨z.val.1, hz⟩) := by
  dsimp only [boundaryMap]
  rw [dif_pos hz]

private theorem continuous_boundaryMap
    (hzero : ∀ a : Subspace K L, g (0, a) = f a.val) :
    Continuous (boundaryMap K L f g) := by
  let T₀ : Set (Cylinder K L) := {z | z.val.2 = 0}
  let T₁ : Set (Cylinder K L) := {z | z.val.1.val ∈ realization L}
  have hT₀ : IsClosed T₀ :=
    isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hT₁ : IsClosed T₁ :=
    (subspace_closed K L).preimage (continuous_fst.comp continuous_subtype_val)
  have hf : ContinuousOn (boundaryMap K L f g) T₀ := by
    apply (f.continuous.comp (continuous_fst.comp continuous_subtype_val)).continuousOn.congr
    intro z hz
    exact boundaryMap_bottom K L f g hzero z hz
  have hg : ContinuousOn (boundaryMap K L f g) T₁ := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let j : T₁ → I × Subspace K L := fun z =>
      (z.val.val.2, ⟨z.val.val.1, z.property⟩)
    have hj : Continuous j := by
      exact (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
    apply (g.continuous.comp hj).congr
    intro z
    exact (boundaryMap_side K L f g z.val z.property).symm
  have hcover : T₀ ∪ T₁ = univ := by
    ext z
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact z.property
  rw [← continuousOn_univ, ← hcover]
  exact hf.union_of_isClosed hg hT₀ hT₁

/-- Arbitrary-target HEP, with time first as in Mathlib's homotopies.
No separation axiom on the target, or supplied HEP, is used. -/
theorem homotopy_extension (hLK : L ≤ K)
    (hzero : ∀ a : Subspace K L, g (0, a) = f a.val) :
    ∃ F : C(I × Space K, Y), (∀ x, F (0, x) = f x) ∧
      ∀ (t : I) (a : Subspace K L), F (t, a.val) = g (t, a) := by
  let k : C(Cylinder K L, Y) :=
    ⟨boundaryMap K L f g, continuous_boundaryMap K L f g hzero⟩
  let F : C(I × Space K, Y) :=
    ⟨fun z => k (retraction K L hLK (z.2, z.1)),
      k.continuous.comp ((retraction K L hLK).continuous.comp continuous_swap)⟩
  refine ⟨F, ?_, ?_⟩
  · intro x
    have hr : retraction K L hLK (x, 0) = ⟨(x, 0), Or.inl rfl⟩ :=
      Subtype.ext (retraction_fixed K L hLK (x, 0) (Or.inl rfl))
    change boundaryMap K L f g (retraction K L hLK (x, 0)) = f x
    rw [hr]
    exact boundaryMap_bottom K L f g hzero _ rfl
  · intro t a
    have hr : retraction K L hLK (a.val, t) = ⟨(a.val, t), Or.inr a.property⟩ :=
      Subtype.ext (retraction_fixed K L hLK (a.val, t) (Or.inr a.property))
    change boundaryMap K L f g (retraction K L hLK (a.val, t)) = g (t, a)
    rw [hr]
    exact boundaryMap_side K L f g _ a.property

end Extension

end D5.S3.Geometry.FiniteSubcomplexCylinder
