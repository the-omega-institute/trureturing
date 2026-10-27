/- GID: D5/S3/Geometry/FiniteVertexCylinder
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteVertexCylinder
   mirror-E: none(waiver:finite-vertex-cylinder)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Basic]
   utility: none
   digest: A division-free coordinate retraction gives homotopy extension at every realized vertex. -/
import D5.S3.Geometry.FiniteConeCollapse
import Mathlib.Topology.Piecewise

/-!
# Homotopy extension at an actual vertex

The finite coordinate realization is unchanged. Positive-part truncation of
the coordinates other than a chosen vertex gives a continuous retraction onto
the bottom and the vertical line over that vertex. Closed-set gluing then
extends an arbitrary target-valued path at the vertex.
-/

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap
open D5.S3.Geometry.FiniteConeCollapse

namespace D5.S3.Geometry.FiniteVertexCylinder

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Space (M : PreAbstractSimplicialComplex V) := ↥(realization M)

variable (M : PreAbstractSimplicialComplex V) (v : V)

/-- The actual coordinate vertex of a face singleton. -/
def vertexPoint (hv : ({v} : Finset V) ∈ M) : Space M :=
  ⟨Pi.single v 1, {v}, hv, subset_convexHull ℝ _ ⟨v, by simp, rfl⟩⟩

private theorem simplex_data (x : Space M) :
    (∀ w, 0 ≤ x.val w) ∧ (∑ w, x.val w) = 1 := by
  obtain ⟨s, _, hx⟩ := (realization_mem_iff M x.val).1 x.property
  exact ⟨hx.1, hx.2.1⟩

private theorem coord_le_one (x : Space M) (w : V) : x.val w ≤ 1 := by
  rw [← (simplex_data M x).2]
  exact single_le_sum (fun a _ => (simplex_data M x).1 a) (mem_univ w)

private theorem off_sum (x : Space M) :
    (∑ w ∈ univ.erase v, x.val w) = 1 - x.val v := by
  have h := sum_erase_add univ (fun w => x.val w) (mem_univ v)
  rw [(simplex_data M x).2] at h
  linarith

private def amount (t : I) (x : Space M) : ℝ := (t : ℝ) * x.val v

private theorem amount_nonneg (t : I) (x : Space M) : 0 ≤ amount M v t x :=
  mul_nonneg t.property.1 ((simplex_data M x).1 v)

private def shortened (t : I) (x : Space M) (w : V) : ℝ :=
  max (x.val w - amount M v t x) 0

private theorem shortened_le (t : I) (x : Space M) (w : V) :
    shortened M v t x w ≤ x.val w :=
  max_le (sub_le_self _ (amount_nonneg M v t x)) ((simplex_data M x).1 w)

private def coordinates (t : I) (x : Space M) (w : V) : ℝ :=
  if w = v then 1 - ∑ a ∈ univ.erase v, shortened M v t x a else shortened M v t x w

private theorem coordinates_sum (t : I) (x : Space M) :
    (∑ w, coordinates M v t x w) = 1 := by
  rw [← sum_erase_add univ (coordinates M v t x) (mem_univ v)]
  have hsum : (∑ w ∈ univ.erase v, coordinates M v t x w) =
      ∑ w ∈ univ.erase v, shortened M v t x w := by
    apply sum_congr rfl
    intro w hw
    simp only [coordinates, if_neg (mem_erase.mp hw).1]
  rw [hsum]
  simp only [coordinates, if_pos rfl]
  ring

private theorem coordinates_nonneg (t : I) (x : Space M) (w : V) :
    0 ≤ coordinates M v t x w := by
  by_cases hw : w = v
  · simp only [coordinates, if_pos hw]
    have hs : (∑ a ∈ univ.erase v, shortened M v t x a) ≤ 1 - x.val v := by
      rw [← off_sum M v x]
      exact sum_le_sum (fun a _ => shortened_le M v t x a)
    linarith [(simplex_data M x).1 v]
  · simp only [coordinates, if_neg hw]
    exact le_max_right _ _

private theorem coordinates_eq_of_coord_zero (t : I) (x : Space M) (hx : x.val v = 0) :
    coordinates M v t x = x.val := by
  have ha : amount M v t x = 0 := by simp [amount, hx]
  have hs (w) : shortened M v t x w = x.val w := by
    simp [shortened, ha, max_eq_left ((simplex_data M x).1 w)]
  funext w
  by_cases hw : w = v
  · simp only [coordinates, if_pos hw, hs, off_sum M v x]
    rw [hw]
    ring
  · simp only [coordinates, if_neg hw, hs]

private theorem coordinates_mem_face (t : I) (x : Space M) {s : Finset V}
    (hx : x.val ∈ faceSimplex s) : coordinates M v t x ∈ faceSimplex s := by
  refine ⟨coordinates_nonneg M v t x, coordinates_sum M v t x, ?_⟩
  intro w hw
  by_cases h : w = v
  · have hv : x.val v = 0 := hx.2.2 v (h ▸ hw)
    rw [coordinates_eq_of_coord_zero M v t x hv]
    exact hx.2.2 w hw
  · simp only [coordinates, if_neg h, shortened, hx.2.2 w hw, zero_sub]
    exact max_eq_right (neg_nonpos.mpr (amount_nonneg M v t x))

private def horizontal (t : I) (x : Space M) : Space M :=
  ⟨coordinates M v t x, by
    obtain ⟨s, hs, hx⟩ := (realization_mem_iff M x.val).1 x.property
    exact (realization_mem_iff M _).2 ⟨s, hs, coordinates_mem_face M v t x hx⟩⟩

private def heightValue (t : I) (x : Space M) : ℝ :=
  max (amount M v t x + x.val v - 1) 0

private theorem height_bounds (t : I) (x : Space M) :
    0 ≤ heightValue M v t x ∧ heightValue M v t x ≤ 1 := by
  refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
  have hb : amount M v t x ≤ 1 :=
    (mul_le_mul_of_nonneg_right t.property.2 ((simplex_data M x).1 v)).trans
      (by simpa using coord_le_one M x v)
  linarith [coord_le_one M x v]

private def height (t : I) (x : Space M) : I :=
  ⟨heightValue M v t x, height_bounds M v t x⟩

variable (hv : ({v} : Finset V) ∈ M)

private theorem horizontal_eq_vertex_of_height_ne_zero (t : I) (x : Space M)
    (hq : height M v t x ≠ 0) : horizontal M v t x = vertexPoint M v hv := by
  have hq' : heightValue M v t x ≠ 0 := fun h => hq (Subtype.ext h)
  have hb : 1 - x.val v < amount M v t x := by
    by_contra h
    exact hq' (max_eq_right (by linarith : amount M v t x + x.val v - 1 ≤ 0))
  have hs : ∀ w ∈ univ.erase v, shortened M v t x w = 0 := by
    intro w hw
    have hw' : x.val w ≤ 1 - x.val v := by
      rw [← off_sum M v x]
      exact single_le_sum (fun a _ => (simplex_data M x).1 a) hw
    exact max_eq_right (by linarith : x.val w - amount M v t x ≤ 0)
  apply Subtype.ext
  funext w
  change coordinates M v t x w = Pi.single v 1 w
  by_cases hw : w = v
  · simp [coordinates, hw, sum_eq_zero hs]
  · have hsw := hs w (by simp [hw])
    simp [coordinates, hw, hsw, Pi.single_apply, Ne.symm hw]

private theorem horizontal_zero (x : Space M) : horizontal M v 0 x = x := by
  have hs (w) : shortened M v 0 x w = x.val w := by
    simp [shortened, amount, max_eq_left ((simplex_data M x).1 w)]
  apply Subtype.ext
  funext w
  change coordinates M v 0 x w = x.val w
  by_cases hw : w = v
  · simp only [coordinates, if_pos hw, hs, off_sum M v x]
    rw [hw]
    ring
  · simp only [coordinates, if_neg hw, hs]

private theorem height_zero (x : Space M) : height M v 0 x = 0 := by
  apply Subtype.ext
  exact max_eq_right (by simpa [amount] using sub_nonpos.mpr (coord_le_one M x v))

private theorem horizontal_vertex (t : I) :
    horizontal M v t (vertexPoint M v hv) = vertexPoint M v hv := by
  have hs : ∀ w ∈ univ.erase v, shortened M v t (vertexPoint M v hv) w = 0 := by
    intro w hw
    have hw' := (mem_erase.mp hw).1
    simp [shortened, vertexPoint, amount, Pi.single_apply, hw', Ne.symm hw',
      max_eq_right (neg_nonpos.mpr t.property.1)]
  apply Subtype.ext
  funext w
  change coordinates M v t (vertexPoint M v hv) w = Pi.single v 1 w
  by_cases hw : w = v
  · simp [coordinates, hw, sum_eq_zero hs]
  · simp [coordinates, hw, hs w (by simp [hw]), Pi.single_apply, Ne.symm hw]

private theorem height_vertex (t : I) : height M v t (vertexPoint M v hv) = t := by
  apply Subtype.ext
  simp [height, heightValue, amount, vertexPoint, max_eq_left t.property.1]

private theorem continuous_horizontal :
    Continuous (fun z : Space M × I => horizontal M v z.2 z.1) := by
  have hc (w : V) : Continuous (fun z : Space M × I => z.1.val w) :=
    (continuous_apply w).comp (continuous_subtype_val.comp continuous_fst)
  have ha : Continuous (fun z : Space M × I => amount M v z.2 z.1) :=
    (continuous_subtype_val.comp continuous_snd).mul (hc v)
  have hs (w : V) : Continuous (fun z : Space M × I => shortened M v z.2 z.1 w) :=
    ((hc w).sub ha).max continuous_const
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  by_cases hw : w = v
  · simp only [coordinates, if_pos hw]
    exact continuous_const.sub (continuous_finset_sum _ (fun a _ => hs a))
  · simp only [coordinates, if_neg hw]
    exact hs w

private theorem continuous_height :
    Continuous (fun z : Space M × I => height M v z.2 z.1) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun z : Space M × I => z.1.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_fst)
  exact (((continuous_subtype_val.comp continuous_snd).mul hc).add hc |>.sub
    continuous_const).max continuous_const

/-- The actual bottom together with the entire cylinder over the chosen vertex. -/
def Cylinder : Set (Space M × I) := {z | z.2 = 0 ∨ z.1 = vertexPoint M v hv}

/-- The division-free continuous retraction into the bottom-or-vertex cylinder. -/
def retraction : C(Space M × I, Cylinder M v hv) where
  toFun z := ⟨(horizontal M v z.2 z.1, height M v z.2 z.1), by
    by_cases h : height M v z.2 z.1 = 0
    · exact Or.inl h
    · exact Or.inr (horizontal_eq_vertex_of_height_ne_zero M v hv z.2 z.1 h)⟩
  continuous_toFun := (continuous_horizontal M v |>.prodMk (continuous_height M v)).subtype_mk _

private theorem retraction_bottom (x : Space M) :
    (retraction M v hv (x, 0)).val = (x, 0) := by
  exact Prod.ext (horizontal_zero M v x) (height_zero M v x)

private theorem retraction_vertex (t : I) :
    (retraction M v hv (vertexPoint M v hv, t)).val = (vertexPoint M v hv, t) := by
  exact Prod.ext (horizontal_vertex M v hv t) (height_vertex M v hv t)

/-- Both parts of the bottom-or-vertex cylinder are fixed pointwise. -/
theorem retraction_fixed (z : Cylinder M v hv) :
    (retraction M v hv z.val).val = z.val := by
  rcases z with ⟨⟨x, t⟩, hz⟩
  rcases hz with h | h
  · change t = 0 at h
    subst t
    exact retraction_bottom M v hv x
  · change x = vertexPoint M v hv at h
    subst x
    exact retraction_vertex M v hv t

variable {Y : Type*} [TopologicalSpace Y]

private def boundaryMap (f : C(Space M, Y)) (h : C(I, Y)) : Cylinder M v hv → Y :=
  fun z => if z.val.2 = 0 then f z.val.1 else h z.val.2

private theorem continuous_boundaryMap (f : C(Space M, Y)) (h : C(I, Y))
    (hzero : h 0 = f (vertexPoint M v hv)) : Continuous (boundaryMap M v hv f h) := by
  let A : Set (Cylinder M v hv) := {z | z.val.2 = 0}
  let B : Set (Cylinder M v hv) := {z | z.val.1 = vertexPoint M v hv}
  have hA : IsClosed A := isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hB : IsClosed B := isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hf : ContinuousOn (boundaryMap M v hv f h) A := by
    apply (f.continuous.comp (continuous_fst.comp continuous_subtype_val)).continuousOn.congr
    intro z hz
    simp [boundaryMap, show z.val.2 = 0 from hz]
  have hh : ContinuousOn (boundaryMap M v hv f h) B := by
    apply (h.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
    intro z hz
    have hx : z.val.1 = vertexPoint M v hv := hz
    by_cases ht : z.val.2 = 0
    · simp [boundaryMap, ht, hx, hzero]
    · simp [boundaryMap, ht]
  have hcover : A ∪ B = univ := by
    ext z
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact z.property
  rw [← continuousOn_univ, ← hcover]
  exact hf.union_of_isClosed hh hA hB

/-- An arbitrary target-valued vertex path extends while preserving the whole initial map. -/
theorem vertex_homotopy_extension (f : C(Space M, Y)) (h : C(I, Y))
    (hzero : h 0 = f (vertexPoint M v hv)) :
    ∃ F : C(Space M × I, Y), (∀ x, F (x, 0) = f x) ∧
      ∀ t, F (vertexPoint M v hv, t) = h t := by
  let k : C(Cylinder M v hv, Y) :=
    ⟨boundaryMap M v hv f h, continuous_boundaryMap M v hv f h hzero⟩
  refine ⟨k.comp (retraction M v hv), ?_, ?_⟩
  · intro x
    change boundaryMap M v hv f h (retraction M v hv (x, 0)) = f x
    simp only [boundaryMap, retraction_bottom M v hv x, if_pos rfl]
  · intro t
    change boundaryMap M v hv f h (retraction M v hv (vertexPoint M v hv, t)) = h t
    simp only [boundaryMap, retraction_vertex M v hv t]
    split_ifs with ht
    · simpa [ht] using hzero.symm
    · rfl

#print axioms vertex_homotopy_extension
#print axioms retraction_fixed

end D5.S3.Geometry.FiniteVertexCylinder
