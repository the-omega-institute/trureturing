/- GID: D5/S3/Topology/StableCategory/LebesgueStarAssignment
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/LebesgueStarAssignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two categorical opens give four stable categorical lower sets in dimension four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteVertexCylinder
import D5.S3.Topology.StableCategory.ColourGraphJoin
import D5.S3.Topology.StableCategory.DimensionFourCategoricalColour
import D5.S3.Topology.StableCategory.TerminalCarrierIteration
import D5.S3.Topology.TauCeti.Analysis.Normed.Affine.Centroid
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
The geometric input to the dimension-four categorical colour theorem.
All distances are measured in the finite coordinate space of the original complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.LebesgueStarAssignment

open D5.S3.Geometry.FiniteConeCollapse
  (faceSimplex faceSimplex_eq_convexHull realization_mem_iff)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Geometry.FiniteSimplicialJoin (Space realizationCompactSpace)
open D5.S3.Geometry.FiniteVertexCylinder (vertexPoint)
open BarycentricBaseRigidity (sd skeleton)
open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open BarycentricRealization (barycentricCoords realizationHomeomorph)
open ConnectedCategoryGraft (HasCategoricalCover)
open OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open Set
open scoped BigOperators ContinuousMap

open private faceBarycenter faceBarycenter_apply
  from D5.S3.Topology.BarycentricRealization
open private chainComplex from D5.S3.Topology.SubdivisionCategoricalCover
open private chainPoset transport_lower_cover from
  D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X]

abbrev DepthVertices (K : PreAbstractSimplicialComplex X) (n : ℕ) :=
  (iteratedAmbient K n).1

abbrev depthComplex (K : PreAbstractSimplicialComplex X) (n : ℕ) :=
  (iteratedAmbient K n).2

private def depthFintype (K : PreAbstractSimplicialComplex X) :
    (n : ℕ) → Fintype (DepthVertices K n)
  | 0 => ‹Fintype X›
  | n + 1 =>
    letI : Fintype (DepthVertices K n) := depthFintype K n
    Fintype.ofFinite (Face (depthComplex K n))

private def depthDecEq (K : PreAbstractSimplicialComplex X) :
    (n : ℕ) → DecidableEq (DepthVertices K n)
  | 0 => inferInstance
  | n + 1 =>
    letI : DecidableEq (DepthVertices K n) := depthDecEq K n
    inferInstanceAs (DecidableEq (Face (depthComplex K n)))

attribute [local instance] depthFintype depthDecEq

variable (K : PreAbstractSimplicialComplex X)

private def oneStepCoordinates (L : PreAbstractSimplicialComplex X) :
    (Face L → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := barycentricCoords (K := L)
  map_add' w z := by
    funext v
    change barycentricCoords (w + z) v = barycentricCoords w v + barycentricCoords z v
    simp only [barycentricCoords, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext v
    change barycentricCoords (c • w) v = c * barycentricCoords w v
    simp only [barycentricCoords, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem oneStepCoordinates_single (a : Face K) :
    oneStepCoordinates K (Pi.single a (1 : ℝ)) =
      a.val.centroid ℝ (fun v : X => Pi.single v (1 : ℝ)) := by
  have ha := (K.isRelLowerSet_faces a.property).1
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (a.val.sum_centroidWeights_eq_one_of_nonempty ℝ ha)]
  funext v
  letI : Fintype (Face K) := Fintype.ofFinite _
  change (∑ f : Face K, Pi.single (M := fun _ : Face K => ℝ) a 1 f *
      faceBarycenter f.val v) =
    (∑ u ∈ a.val, a.val.centroidWeights ℝ u • Pi.single u (1 : ℝ)) v
  rw [Fintype.sum_eq_single a (fun f hf => by simp [Pi.single_eq_of_ne hf])]
  simp only [Pi.single_eq_same, one_mul, faceBarycenter_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.centroidWeights_apply]
  by_cases hv : v ∈ a.val
  · rw [if_pos hv, Finset.sum_eq_single_of_mem v hv]
    · simp [one_div]
    · intro u _ huv
      simp [Pi.single_eq_of_ne huv.symm]
  · rw [if_neg hv, Finset.sum_eq_zero]
    intro u hu
    have hne : v ≠ u := fun e => hv (e.symm ▸ hu)
    simp [Pi.single_eq_of_ne hne]

/-- The linear map carrying coordinates at depth n back to the original coordinates. -/
def iteratedCoordinates :
    (n : ℕ) → (DepthVertices K n → ℝ) →ₗ[ℝ] (X → ℝ)
  | 0 => LinearMap.id
  | n + 1 =>
    letI : Fintype (DepthVertices K n) := depthFintype K n
    letI : DecidableEq (DepthVertices K n) := depthDecEq K n
    (iteratedCoordinates n).comp (oneStepCoordinates (depthComplex K n))

/-- The composition of the ordinary barycentric realization homeomorphisms. -/
def iteratedRealization :
    (n : ℕ) → Space (depthComplex K n) ≃ₜ Space K
  | 0 => Homeomorph.refl _
  | n + 1 =>
    letI : Fintype (DepthVertices K n) := depthFintype K n
    letI : DecidableEq (DepthVertices K n) := depthDecEq K n
    (realizationHomeomorph (depthComplex K n)).trans (iteratedRealization n)

theorem iteratedRealization_coordinates (n : ℕ) (x : Space (depthComplex K n)) :
    (iteratedRealization K n x).val = iteratedCoordinates K n x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (iteratedRealization K n
      (realizationHomeomorph (depthComplex K n) x)).val =
        iteratedCoordinates K n (oneStepCoordinates (depthComplex K n) x.val)
    exact ih (realizationHomeomorph (depthComplex K n) x)

/-- The original coordinate position of a depth-n vertex. -/
def vertexCoordinates (n : ℕ) (v : DepthVertices K n) : X → ℝ :=
  iteratedCoordinates K n (Pi.single v 1)

theorem vertexCoordinates_succ (n : ℕ) (a : Face (depthComplex K n)) :
    vertexCoordinates K (n + 1) a = a.val.centroid ℝ (vertexCoordinates K n) := by
  let L := depthComplex K n
  letI : Fintype (DepthVertices K n) := depthFintype K n
  letI : DecidableEq (DepthVertices K n) := depthDecEq K n
  change iteratedCoordinates K n (oneStepCoordinates L (Pi.single a (1 : ℝ))) = _
  have ha := (L.isRelLowerSet_faces a.property).1
  rw [oneStepCoordinates_single, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (a.val.sum_centroidWeights_eq_one_of_nonempty ℝ ha), map_sum]
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (a.val.sum_centroidWeights_eq_one_of_nonempty ℝ ha)]
  simp only [map_smul, vertexCoordinates]

theorem iteratedRealization_barycentric_formula (n : ℕ) (x : Space (depthComplex K n)) :
    (iteratedRealization K n x).val = ∑ v, x.val v • vertexCoordinates K n v := by
  calc
    _ = iteratedCoordinates K n x.val := iteratedRealization_coordinates K n x
    _ = iteratedCoordinates K n (∑ v, x.val v • Pi.single v (1 : ℝ)) :=
      congrArg (fun w => iteratedCoordinates K n w) (pi_eq_sum_univ' x.val)
    _ = _ := by simp only [map_sum, map_smul, vertexCoordinates]

theorem face_card_le_five (dimension : ∀ s ∈ K, s.card ≤ 5) (n : ℕ) :
    ∀ s ∈ depthComplex K n, s.card ≤ 5 := by
  induction n with
  | zero => exact dimension
  | succ n ih =>
    exact (ColourGraphJoin.subdivision_rank_colouring (depthComplex K n) ih).1

/-- Each ordinary subdivision multiplies the vertex mesh bound by 4/5 in
dimension at most four. This estimate uses the original coordinate sup metric. -/
theorem iterated_vertex_mesh_four_fifths (dimension : ∀ s ∈ K, s.card ≤ 5) (n : ℕ) :
    ∀ s ∈ depthComplex K n, ∀ a ∈ s, ∀ b ∈ s,
      dist (vertexCoordinates K n a) (vertexCoordinates K n b) ≤ (4 / 5 : ℝ) ^ n := by
  induction n with
  | zero =>
    intro s hs a ha b hb
    change dist (Pi.single (M := fun _ : X => ℝ) a 1)
      (Pi.single (M := fun _ : X => ℝ) b 1) ≤ (4 / 5 : ℝ) ^ 0
    rw [pow_zero, dist_pi_le_iff (zero_le_one : (0 : ℝ) ≤ 1)]
    intro v
    simp only [Pi.single_apply, Real.dist_eq]
    split_ifs <;> norm_num
  | succ n ih =>
    let L := depthComplex K n
    intro s hs a ha b hb
    have nested (p q : Face L) (hpq : p ≤ q) :
        dist (vertexCoordinates K (n + 1) p) (vertexCoordinates K (n + 1) q) ≤
          (4 / 5 : ℝ) ^ (n + 1) := by
      have hnonempty := (L.isRelLowerSet_faces p.property).1
      have hqpos : (0 : ℝ) < (q.val.card : ℝ) := by
        exact_mod_cast (L.isRelLowerSet_faces q.property).1.card_pos
      have hpone : (1 : ℝ) ≤ (p.val.card : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hnonempty.card_pos)
      have hqfive : (q.val.card : ℝ) ≤ 5 := by
        exact_mod_cast (face_card_le_five K dimension n q.val q.property)
      have hratio : (1 / 5 : ℝ) ≤ (p.val.card : ℝ) / (q.val.card : ℝ) := by
        apply (le_div_iff₀ hqpos).2
        linarith
      rw [vertexCoordinates_succ K n p, vertexCoordinates_succ K n q]
      calc
        _ ≤ (1 - (p.val.card : ℝ) / (q.val.card : ℝ)) * (4 / 5 : ℝ) ^ n :=
          Finset.dist_centroid_centroid_le_of_subset
            (fun u hu v hv => ih q.val q.property u (Finset.mem_sdiff.mp hu).1 v (hpq hv))
            hpq hnonempty
        _ ≤ (4 / 5 : ℝ) * (4 / 5 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (4 / 5 : ℝ) ^ (n + 1) := by rw [pow_succ, mul_comm]
    by_cases he : a = b
    · subst b
      exact nested a a le_rfl
    · rcases hs.2.1 ha hb he with hab | hba
      · exact nested a b hab.le
      · rw [dist_comm]
        exact nested b a hba.le

/-- An entire closed simplex lies within the mesh bound of each of its vertices
after both are mapped into the original coordinates. -/
theorem dist_face_to_vertex_le (dimension : ∀ s ∈ K, s.card ≤ 5) (n : ℕ)
    {s : Finset (DepthVertices K n)} (hs : s ∈ depthComplex K n)
    {v : DepthVertices K n} (hv : v ∈ s)
    {x : DepthVertices K n → ℝ} (hx : x ∈ faceSimplex s) :
    dist (iteratedCoordinates K n x) (vertexCoordinates K n v) ≤ (4 / 5 : ℝ) ^ n := by
  let B := Metric.closedBall (vertexCoordinates K n v) ((4 / 5 : ℝ) ^ n)
  have hconv : Convex ℝ (iteratedCoordinates K n ⁻¹' B) :=
    (convex_closedBall _ _).linear_preimage (iteratedCoordinates K n)
  have hvertices : (fun w : DepthVertices K n => Pi.single w (1 : ℝ)) '' (s : Set _) ⊆
      iteratedCoordinates K n ⁻¹' B := by
    rintro _ ⟨w, hw, rfl⟩
    exact Metric.mem_closedBall.mpr
      (iterated_vertex_mesh_four_fifths K dimension n s hs w hw v hv)
  rw [faceSimplex_eq_convexHull] at hx
  exact Metric.mem_closedBall.mp (convexHull_min hvertices hconv hx)

private def facePoint {Y : Type} [Fintype Y] [DecidableEq Y]
    {L : PreAbstractSimplicialComplex Y} {s : Finset Y} (hs : s ∈ L)
    {x : Y → ℝ} (hx : x ∈ faceSimplex s) : Space L :=
  ⟨x, (realization_mem_iff L x).mpr ⟨s, hs, hx⟩⟩

private def subcomplexInOpen {Y : Type} [Fintype Y] [DecidableEq Y]
    {L : PreAbstractSimplicialComplex Y} (e : Space L ≃ₜ Space K) (U : Set (Space K)) :
    PreAbstractSimplicialComplex Y where
  faces := {s | ∃ hs : s ∈ L, ∀ x (hx : x ∈ faceSimplex s), e (facePoint hs hx) ∈ U}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨hs, hlands⟩ := hs
    refine ⟨(L.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    refine ⟨(L.isRelLowerSet_faces hs).2 hts ht, fun x hx => ?_⟩
    have hx' : x ∈ faceSimplex s :=
      ⟨hx.1, hx.2.1, fun w hw => hx.2.2 w (fun hwt => hw (hts hwt))⟩
    exact hlands x hx'

/-- A categorical open cover by two sets yields two categorical subcomplexes
containing all incident faces of their assigned vertices at a finite ordinary depth.
The homotopies preserve the chosen endpoint of each original contraction under the
iterated realization homeomorphism. -/
theorem categorical_subcomplexes_of_open_cover
    (dimension : ∀ s ∈ K, s.card ≤ 5) (U : Bool → Set (Space K))
    (hopen : ∀ i, IsOpen (U i)) (hcover : (Set.univ : Set (Space K)) ⊆ ⋃ i, U i)
    (point : Bool → Space K)
    (H : ∀ i, Nonempty ((ContinuousMap.subtypeVal (U i)).Homotopy
      (ContinuousMap.const ↥(U i) (point i)))) :
    ∃ n : ℕ, ∃ label : DepthVertices K n → Bool,
      ∃ A : Bool → PreAbstractSimplicialComplex (DepthVertices K n),
      ∃ hA : ∀ i, A i ≤ depthComplex K n,
        (∀ s ∈ depthComplex K n, ∀ v ∈ s, s ∈ A (label v)) ∧
        (∀ i (x : Space (A i)), iteratedRealization K n (realizationInclusion (hA i) x) ∈ U i) ∧
        (∀ i, Nonempty ((realizationInclusion (hA i)).Homotopy
          (ContinuousMap.const (Space (A i)) ((iteratedRealization K n).symm (point i))))) := by
  classical
  letI : CompactSpace (Space K) := realizationCompactSpace K
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (4 / 5 : ℝ) < 1 by norm_num)
  let L := depthComplex K n
  let e := iteratedRealization K n
  let chooseColour (v : Vertex L) : Bool :=
    (hball (e (vertexPoint L v.val v.property)) (Set.mem_univ _)).choose
  have chooseColour_spec (v : Vertex L) :
      Metric.ball (e (vertexPoint L v.val v.property)) δ ⊆ U (chooseColour v) :=
    (hball (e (vertexPoint L v.val v.property)) (Set.mem_univ _)).choose_spec
  let label (v : DepthVertices K n) : Bool :=
    if hv : ({v} : Finset (DepthVertices K n)) ∈ L then chooseColour ⟨v, hv⟩ else false
  let A (i : Bool) := subcomplexInOpen K e (U i)
  have hA (i : Bool) : A i ≤ L := fun _ hs => hs.choose
  have hsubordinate : ∀ s ∈ L, ∀ v ∈ s, s ∈ A (label v) := by
    intro s hs v hv
    have hsingleton : ({v} : Finset (DepthVertices K n)) ∈ L :=
      (L.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    have hlabel : label v = chooseColour ⟨v, hsingleton⟩ := dif_pos hsingleton
    refine ⟨hs, fun x hx => ?_⟩
    rw [hlabel]
    apply chooseColour_spec ⟨v, hsingleton⟩
    apply Metric.mem_ball.mpr
    change dist (iteratedRealization K n (facePoint hs hx)).val
      (iteratedRealization K n (vertexPoint L v hsingleton)).val < δ
    simp only [iteratedRealization_coordinates]
    exact (dist_face_to_vertex_le K dimension n hs hv hx).trans_lt hn
  have hlands (i : Bool) (x : Space (A i)) :
      e (realizationInclusion (hA i) x) ∈ U i := by
    obtain ⟨s, hs, hx⟩ := (realization_mem_iff (A i) x.val).mp x.property
    obtain ⟨hs', hwhole⟩ := hs
    exact hwhole x.val hx
  refine ⟨n, label, A, hA, hsubordinate, hlands, fun i => ?_⟩
  let inc := realizationInclusion (hA i)
  let into : C(Space (A i), ↥(U i)) :=
    ⟨fun x => ⟨e (inc x), hlands i x⟩, (e.continuous.comp inc.continuous).subtype_mk _⟩
  let F := (ContinuousMap.Homotopy.refl (toContinuousMap e.symm)).comp
    ((H i).some.compContinuousMap into)
  refine ⟨F.cast ?_ rfl⟩
  apply ContinuousMap.ext
  intro x
  exact e.symm_apply_apply (inc x)

/-- Points of one closed face are joined by paths in the realization. -/
private theorem joined_in_face {s : Finset X} (hs : s ∈ K)
    {x y : X → ℝ} (hx : x ∈ faceSimplex s) (hy : y ∈ faceSimplex s) :
    Joined (facePoint hs hx) (facePoint hs hy) := by
  have hconv : Convex ℝ (faceSimplex s) := by
    rw [faceSimplex_eq_convexHull]
    exact convex_convexHull ℝ _
  have hpath := (hconv.isPathConnected ⟨x, hx⟩).joinedIn x hx y hy
  have hjoined := (joinedIn_iff_joined hx hy).mp hpath
  let f : faceSimplex s → Space K := fun z => facePoint hs z.property
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact hjoined.map hf

private theorem single_mem_face {s : Finset X} {v : X} (hv : v ∈ s) :
    Pi.single v (1 : ℝ) ∈ faceSimplex s := by
  rw [faceSimplex_eq_convexHull]
  exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

private theorem joined_of_connected_skeleton
    (connected : ∀ a b : Vertex K, (skeleton K).Reachable a b) (x y : Space K) :
    Joined x y := by
  let p (a : Vertex K) := vertexPoint K a.val a.property
  have attached (z : Space K) : ∃ a : Vertex K, Joined z (p a) := by
    obtain ⟨s, hs, hz⟩ := (realization_mem_iff K z.val).mp z.property
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hs).1
    have hv' : ({v} : Finset X) ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    exact ⟨⟨v, hv'⟩, joined_in_face K hs hz (single_mem_face hv)⟩
  have adjacent {a b : Vertex K} (hab : (skeleton K).Adj a b) : Joined (p a) (p b) := by
    let s : Finset X :=
      letI : DecidableEq X := Classical.decEq X
      {a.val, b.val}
    have hs : s ∈ K := hab.2
    have ha : a.val ∈ s := by
      letI : DecidableEq X := Classical.decEq X
      exact Finset.mem_insert_self _ _
    have hb : b.val ∈ s := by
      letI : DecidableEq X := Classical.decEq X
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact joined_in_face K hs (single_mem_face ha) (single_mem_face hb)
  have alongWalk {a b : Vertex K} (w : (skeleton K).Walk a b) : Joined (p a) (p b) := by
    induction w with
    | nil => exact Joined.refl _
    | cons h _ ih => exact (adjacent h).trans ih
  obtain ⟨a, ha⟩ := attached x
  obtain ⟨b, hb⟩ := attached y
  obtain ⟨w⟩ := connected a b
  exact ha.trans ((alongWalk w).trans hb.symm)

/-- The open-cover bridge followed by the existing four-lower-set assembly.
Connectivity allows the two contractions to end at a common point. -/
theorem four_lower_sets_of_categorical_open_cover
    (dimension : ∀ s ∈ K, s.card ≤ 5) (U : Bool → Set (Space K))
    (hopen : ∀ i, IsOpen (U i)) (hcover : (Set.univ : Set (Space K)) ⊆ ⋃ i, U i)
    (point : Bool → Space K)
    (H : ∀ i, Nonempty ((ContinuousMap.subtypeVal (U i)).Homotopy
      (ContinuousMap.const ↥(U i) (point i))))
    (connected : ∀ a b : Vertex K, (skeleton K).Reachable a b) :
    ∃ n, HasCategoricalCover (Face (iteratedAmbient K n).2) 4 := by
  obtain ⟨endpointPath⟩ := joined_of_connected_skeleton K connected (point true) (point false)
  have H' (i : Bool) : Nonempty ((ContinuousMap.subtypeVal (U i)).Homotopy
      (ContinuousMap.const ↥(U i) (point false))) := by
    cases i
    · exact H false
    · exact ⟨(H true).some.trans endpointPath.toHomotopyConst⟩
  obtain ⟨n, label, A, hA, hsubordinate, _, hcontracts⟩ :=
    categorical_subcomplexes_of_open_cover K dimension U hopen hcover (fun _ => point false) H'
  let L := depthComplex K n
  have hconnected : ∀ a b : Vertex (sd L), (skeleton (sd L)).Reachable a b :=
    TerminalCarrierIteration.subdivision_connected K connected (n + 1)
  obtain ⟨r, h⟩ := DimensionFourCategoricalColour.four_lower_sets_of_categorical_stars
    label (face_card_le_five K dimension n) A hA hsubordinate
    ((iteratedRealization K n).symm (point false)) (fun i => (hcontracts i).some) hconnected
  refine ⟨n + r, ?_⟩
  rw [← OrdinaryContiguityLift.iterated_ambient_add K n r]
  exact h

/-- The dimension-four weak-category-two case for connected finite posets,
expressed directly using the two categorical opens of the order complex. -/
theorem four_lower_sets_of_two_categorical_opens
    (P : Type) [Fintype P] [deq : DecidableEq P] [PartialOrder P]
    [pre : PreconnectedSpace (Space (chainComplex P))]
    (dimension : Order.krullDim P ≤ (4 : ℕ∞))
    (U : Bool → Set (Space (chainComplex P))) (hopen : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i) (point : Bool → Space (chainComplex P))
    (H : ∀ i, Nonempty ((ContinuousMap.subtypeVal (U i)).Homotopy
      (ContinuousMap.const ↥(U i) (point i)))) :
    ∃ n, @HasCategoricalCover (finiteSpaceSubdivision P n).1
      (finiteSpaceSubdivision P n).2 4 := by
  have he : deq = Classical.decEq P := Subsingleton.elim _ _
  subst deq
  letI : DecidableEq P := Classical.decEq _
  have hle (x : P) : Order.height x ≤ (4 : ℕ∞) :=
    WithBot.coe_le_coe.mp ((Order.height_le_krullDim x).trans dimension)
  have hfin (x : P) : Order.height x < ⊤ := (hle x).trans_lt (ENat.natCast_lt_top 4)
  let rank (x : P) : Fin 5 := ⟨(Order.height x).toNat, Nat.lt_succ_of_le
    (ENat.toNat_le_of_le_natCast (hle x))⟩
  have strict : StrictMono rank := by
    intro x y hxy
    have h := Order.height_strictMono hxy (hfin x)
    rw [← ENat.natCast_toNat (hfin x).ne, ← ENat.natCast_toNat (hfin y).ne] at h
    exact_mod_cast h
  have card (s : Finset P) (hs : s ∈ chainComplex P) : s.card ≤ 5 := by
    have inj : Set.InjOn rank (s : Set P) := by
      intro x hx y hy he
      by_contra hn
      rcases hs.2 hx hy hn with h | h
      · exact (strict (lt_of_le_of_ne h hn)).ne he
      · exact (strict (lt_of_le_of_ne h (Ne.symm hn))).ne he.symm
    rw [← Finset.card_image_of_injOn inj]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (s.image rank)
  obtain ⟨n, cover⟩ := four_lower_sets_of_categorical_open_cover (chainComplex P)
    card U hopen hcover point H
    (@TetrahedralGraphIteration.skeleton_reachable_of_preconnected_realization
      P _ (chainComplex P) pre)
  letI := (finiteSpaceSubdivision P (n + 1)).2
  exact ⟨n + 1, transport_lower_cover (chainPoset P n) cover⟩

end

end D5.S3.Topology.StableCategory.LebesgueStarAssignment
