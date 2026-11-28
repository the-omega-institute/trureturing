/- GID: D5/S3/Topology/StableCategory/DimensionFourCategoricalColour
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/DimensionFourCategoricalColour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A subordinate categorical star assignment gives four stable categorical pieces in dimension four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.BarycentricRealization
import D5.S3.Topology.StableCategory.DimensionFourColour
import D5.S3.Topology.StableCategory.FourPieceCategoricalCover
import D5.S3.Geometry.FiniteConeUnionWedge
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Equiv.Fin.Basic

/-! Categorical induced colours at one ordinary subdivision from a subordinate
vertex labelling and two ambient contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.DimensionFourCategoricalColour

open D5.S3.Geometry.FiniteConeCollapse (faceSimplex realization realization_mem_iff)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open BarycentricBaseRigidity (sd skeleton)
open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (iteratedAmbient subdivision)
open BarycentricRealization (barycentricCoords barycentricCoords_mem_subcomplex_iff
  realizationHomeomorph toOriginal)
open ConnectedCategoryGraft (HasCategoricalCover)
open FourPieceCategoricalCover (CategoricalMapCover four_pieces_of_two_categorical_colours
  lower_cover_of_simplicial_cover)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (iterated_ambient_add)
open private exists_vertex_in_star from D5.S3.Topology.GeometricGraphTermination
open scoped ContinuousMap unitInterval

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] {K : PreAbstractSimplicialComplex X}

local instance faceFintype (K : PreAbstractSimplicialComplex X) : Fintype (Face K) :=
  Fintype.ofFinite _

private theorem colour_le (p : Face K → Bool) : colourComplex (sd K) p ≤ sd K :=
  fun _ hs => hs.1

private def faceIndex (label : X → Bool) (f : Face K) : Bool :=
  if false ∈ f.val.image label then false else true

private theorem faceIndex_mem (label : X → Bool) (f : Face K) :
    faceIndex label f ∈ f.val.image label := by
  by_cases h : false ∈ f.val.image label
  · simpa only [faceIndex, if_pos h] using h
  · obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces f.property).1
    have hl : label v = true := Bool.eq_true_of_not_eq_false fun hv' =>
      h (Finset.mem_image.mpr ⟨v, hv, hv'⟩)
    simpa only [faceIndex, if_neg h] using
      (Finset.mem_image.mpr ⟨v, hv, hl⟩ : true ∈ f.val.image label)

private def inducedColourHomotopy (label : X → Bool) (p : Face K → Bool)
    (sameImage : ∀ a b : Face K, a ≤ b → p a = true → p b = true →
      a.val.image label = b.val.image label)
    (A : Bool → PreAbstractSimplicialComplex X) (hA : ∀ i, A i ≤ K)
    (subordinate : ∀ s ∈ K, ∀ v ∈ s, s ∈ A (label v))
    (point : Space K)
    (H : ∀ i, (realizationInclusion (hA i)).Homotopy (ContinuousMap.const (Space (A i)) point)) :
    (realizationInclusion (colour_le p)).Homotopy
      (ContinuousMap.const (Space (colourComplex (sd K) p))
        ((realizationHomeomorph K).symm point)) := by
  let R := colourComplex (sd K) p
  let inc := realizationInclusion (colour_le p)
  let old := (toOriginal K).comp inc
  have sameIndex {s : Finset (Face K)} (hs : s ∈ R) {a b : Face K}
      (ha : a ∈ s) (hb : b ∈ s) : faceIndex label a = faceIndex label b := by
    by_cases e : a = b
    · rw [e]
    have h : a.val.image label = b.val.image label := by
      rcases hs.1.2.1 ha hb e with hab | hba
      · exact sameImage a b hab.le (hs.2 a ha) (hs.2 b hb)
      · exact (sameImage b a hba.le (hs.2 b hb) (hs.2 a ha)).symm
    simp only [faceIndex, h]
  have carrier (x : Space R) : ∃ s ∈ R, x.val ∈ faceSimplex s :=
    (realization_mem_iff R x.val).mp x.property
  have positive (x : Space R) : ∃ f : Face K, 0 < x.val f := by
    obtain ⟨s, hs, hx⟩ := carrier x
    by_contra h
    have hz (f : Face K) : x.val f = 0 :=
      le_antisymm (le_of_not_gt fun hf => h ⟨f, hf⟩) (hx.1 f)
    have hsum := hx.2.1
    simp [hz] at hsum
  have mem_carrier {s : Finset (Face K)} {x : Space R} (hx : x.val ∈ faceSimplex s)
      {f : Face K} (hf : 0 < x.val f) : f ∈ s := by
    by_contra hn
    exact (ne_of_gt hf) (hx.2.2 f hn)
  let index (x : Space R) : Bool := faceIndex label (positive x).choose
  have index_eq (x : Space R) {f : Face K} (hf : 0 < x.val f) :
      index x = faceIndex label f := by
    obtain ⟨s, hs, hx⟩ := carrier x
    exact sameIndex hs (mem_carrier hx (positive x).choose_spec) (mem_carrier hx hf)
  -- The two fibres are complementary open sets, witnessed by positive-coordinate stars.
  have openIndex (i : Bool) : IsOpen {x : Space R | index x = i} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    let f := (positive x).choose
    have hf : 0 < x.val f := (positive x).choose_spec
    have hstar : IsOpen {y : Space R | 0 < y.val f} :=
      isOpen_lt continuous_const ((continuous_apply f).comp continuous_subtype_val)
    exact Filter.mem_of_superset (hstar.mem_nhds hf) fun y hy =>
      (index_eq y hy).trans ((index_eq x hf).symm.trans hx)
  have lands (x : Space R) : (old x).val ∈ realization (A (index x)) := by
    change barycentricCoords (inc x).val ∈ realization (A (index x))
    apply (barycentricCoords_mem_subcomplex_iff (P := A (index x)) (inc x)).mpr
    obtain ⟨s, hs, hx⟩ := carrier x
    refine (realization_mem_iff (subdivision K (A (index x))) (inc x).val).mpr
      ⟨s, ⟨hs.1.1, hs.1.2.1, ?_⟩, hx⟩
    intro f hf
    have he : faceIndex label f = index x :=
      (sameIndex hs (mem_carrier hx (positive x).choose_spec) hf).symm
    have hmem : index x ∈ f.val.image label := he ▸ faceIndex_mem label f
    obtain ⟨v, hv, hl⟩ := Finset.mem_image.mp hmem
    rw [← hl]
    exact subordinate f.val f.property v hv
  let domain (i : Bool) : Set (I × Space R) := {z | index z.2 = i}
  let into (i : Bool) (z : domain i) : Space (A i) :=
    ⟨(old z.val.2).val, by
      have h : index z.val.2 = i := z.property
      have hz := lands z.val.2
      rw [h] at hz
      exact hz⟩
  let glue (z : I × Space R) : Space K :=
    H (index z.2) (z.1, ⟨(old z.2).val, lands z.2⟩)
  have continuous_glue : Continuous glue := by
    apply continuous_of_cover_nhds (s := domain)
    · intro z
      have ho : IsOpen (domain (index z.2)) := (openIndex _).preimage continuous_snd
      exact ⟨index z.2, ho.mem_nhds rfl⟩
    · intro i
      apply continuousOn_iff_continuous_domRestrict.mpr
      have hi : Continuous (into i) :=
        ((continuous_subtype_val.comp old.continuous).comp
          (continuous_snd.comp continuous_subtype_val)).subtype_mk _
      have hh : Continuous (fun z : domain i => H i (z.val.1, into i z)) :=
        (H i).continuous_toFun.comp ((continuous_fst.comp continuous_subtype_val).prodMk hi)
      refine hh.congr ?_
      rintro ⟨⟨t, x⟩, hx⟩
      have he : index x = i := hx
      subst i
      rfl
  let e := realizationHomeomorph K
  refine
    { toFun := fun z => e.symm (glue z)
      continuous_toFun := e.symm.continuous.comp continuous_glue
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    change e.symm (H (index x) (0, ⟨(old x).val, lands x⟩)) = inc x
    calc
      _ = e.symm (old x) := congrArg e.symm ((H (index x)).apply_zero _)
      _ = inc x := e.symm_apply_apply (inc x)
  · intro x
    change e.symm (H (index x) (1, ⟨(old x).val, lands x⟩)) = e.symm point
    exact congrArg e.symm ((H (index x)).apply_one _)

-- The realization homeomorphism uses the equality decision inherited from the old
-- coordinates. The cover assembly uses classical equality on subdivision vertices.
private def faceDecEq (K : PreAbstractSimplicialComplex X) : DecidableEq (Face K) :=
  inferInstance

private theorem homotopiesWithDecidableEq (d : DecidableEq (Face K))
    (label : X → Bool) (p : Fin 2 → Face K → Bool)
    (sameImage : ∀ i, ∀ a b : Face K, a ≤ b → p i a = true → p i b = true →
      a.val.image label = b.val.image label)
    (A : Bool → PreAbstractSimplicialComplex X) (hA : ∀ i, A i ≤ K)
    (subordinate : ∀ s ∈ K, ∀ v ∈ s, s ∈ A (label v))
    (point : Space K)
    (H : ∀ i, (realizationInclusion (hA i)).Homotopy (ContinuousMap.const (Space (A i)) point)) :
    letI := d
    ∃ q : Space (sd K), ∀ i, Nonempty
      ((realizationInclusion (colour_le (p i))).Homotopy
        (ContinuousMap.const (Space (colourComplex (sd K) (p i))) q)) := by
  have he : d = faceDecEq K := Subsingleton.elim _ _
  subst d
  exact ⟨(realizationHomeomorph K).symm point, fun i =>
    ⟨inducedColourHomotopy label (p i) (sameImage i) A hA subordinate point H⟩⟩

private theorem properRank (p : Face K → Bool)
    (bound : ∀ s ∈ colourComplex (sd K) p, s.card ≤ 4) :
    ∃ rank : Face K → Fin 4, ∀ s ∈ colourComplex (sd K) p, Set.InjOn rank (s : Set (Face K)) := by
  classical
  -- Rank counts a longest chain of selected faces strictly below a face.
  let chains (f : Face K) : Finset (Finset (Face K)) :=
    Finset.univ.filter fun s =>
      IsChain (· < ·) (s : Set (Face K)) ∧ ∀ a ∈ s, p a = true ∧ a < f
  let height (f : Face K) := (chains f).sup Finset.card
  have longest (f : Face K) : ∃ s ∈ chains f, height f = s.card := by
    apply Finset.exists_mem_eq_sup
    exact ⟨∅, by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp
      · simp⟩
  have extend {s : Finset (Face K)} {a : Face K} (hs : s ∈ chains a) :
      IsChain (· < ·) ((insert a s : Finset (Face K)) : Set (Face K)) ∧ a ∉ s := by
    have h := (Finset.mem_filter.mp hs).2
    refine ⟨?_, fun ha => (lt_irrefl a) (h.2 a ha).2⟩
    rw [Finset.coe_insert]
    exact h.1.insert fun b hb _ => Or.inr (h.2 b hb).2
  have height_lt (a : Face K) (ha : p a = true) : height a < 4 := by
    obtain ⟨s, hs, hcard⟩ := longest a
    obtain ⟨hchain, hnot⟩ := extend hs
    have hsel := (Finset.mem_filter.mp hs).2.2
    have hface : insert a s ∈ colourComplex (sd K) p := by
      refine ⟨⟨⟨a, Finset.mem_insert_self _ _⟩, hchain, fun f _ => f.property⟩, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ha
      · exact (hsel f hf).1
    have h := bound _ hface
    rw [Finset.card_insert_of_notMem hnot, ← hcard] at h
    omega
  have height_mono {a b : Face K} (hab : a < b) (ha : p a = true) : height a < height b := by
    obtain ⟨s, hs, hcard⟩ := longest a
    obtain ⟨hchain, hnot⟩ := extend hs
    have hsel := (Finset.mem_filter.mp hs).2.2
    have hins : insert a s ∈ chains b := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchain, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨ha, hab⟩
      · exact ⟨(hsel f hf).1, (hsel f hf).2.trans hab⟩
    have h : (insert a s).card ≤ height b := Finset.le_sup hins
    rw [Finset.card_insert_of_notMem hnot, ← hcard] at h
    omega
  let rank (a : Face K) : Fin 4 := ⟨min (height a) 3, by omega⟩
  have rank_val (a : Face K) (ha : p a = true) : (rank a).val = height a := by
    change min (height a) 3 = height a
    exact min_eq_left (Nat.le_of_lt_succ (height_lt a ha))
  refine ⟨rank, ?_⟩
  intro s hs a ha b hb he
  by_contra hn
  have hpa := hs.2 a ha
  have hpb := hs.2 b hb
  have hval := congrArg Fin.val he
  rw [rank_val a hpa, rank_val b hpb] at hval
  rcases hs.1.2.1 ha hb hn with hab | hba
  · exact (height_mono hab hpa).ne hval
  · exact (height_mono hba hpb).ne hval.symm

/-- Given contractions of the two subordinate subcomplexes to a common
point, both induced colours are categorical after one ordinary subdivision.
The ranks and ambient endpoint have the types used by the four-piece assembly.
-/
theorem two_categorical_colours (label : X → Bool)
    (dimension : ∀ s ∈ K, s.card ≤ 5)
    (A : Bool → PreAbstractSimplicialComplex X) (hA : ∀ i, A i ≤ K)
    (subordinate : ∀ s ∈ K, ∀ v ∈ s, s ∈ A (label v))
    (point : Space K)
    (H : ∀ i, (realizationInclusion (hA i)).Homotopy (ContinuousMap.const (Space (A i)) point)) :
    letI : DecidableEq (Face K) := Classical.decEq _
    ∃ colour : Face K → Fin 2, ∃ rank : Fin 2 → Face K → Fin 4, ∃ q : Space (sd K),
      (∀ i, ∀ s ∈ colourComplex (sd K) (fun f => decide (colour f = i)),
        Set.InjOn (rank i) (s : Set (Face K))) ∧
      (∀ i, Nonempty
        ((realizationInclusion (colour_le (fun f => decide (colour f = i)))).Homotopy
          (ContinuousMap.const (Space (colourComplex (sd K) (fun f => decide (colour f = i)))) q))) := by
  obtain ⟨c, lowTrue, lowFalse, images⟩ := DimensionFourColour.two_low_dimensional_colours label dimension
  let colour (f : Face K) : Fin 2 := if c f then 1 else 0
  let p (i : Fin 2) (f : Face K) : Bool := decide (colour f = i)
  have p_zero : p 0 = fun f => !c f := by
    funext f
    cases hf : c f <;> simp [p, colour, hf]
  have p_one : p 1 = c := by
    funext f
    cases hf : c f <;> simp [p, colour, hf]
  have finTwo (i : Fin 2) : i = 0 ∨ i = 1 :=
    (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp i.isLt)).imp Fin.ext Fin.ext
  have bound (i : Fin 2) : ∀ s ∈ colourComplex (sd K) (p i), s.card ≤ 4 := by
    rcases finTwo i with rfl | rfl
    · simpa only [p_zero] using lowFalse
    · simpa only [p_one] using lowTrue
  have sameImage (i : Fin 2) (a b : Face K) (hab : a ≤ b)
      (ha : p i a = true) (hb : p i b = true) : a.val.image label = b.val.image label := by
    have ha' : colour a = i := of_decide_eq_true ha
    have hb' : colour b = i := of_decide_eq_true hb
    have he : colour a = colour b := ha'.trans hb'.symm
    have he' : c a = c b := by
      cases hca : c a <;> cases hcb : c b <;> simp [colour, hca, hcb] at he ⊢
    have eq := images a b hab he'
    ext z
    simpa only [Finset.mem_image] using
      (iff_of_eq (congrArg (fun s : Finset Bool => z ∈ s) eq))
  have ranks (i : Fin 2) := properRank (p i) (bound i)
  choose rank proper using ranks
  obtain ⟨q, contracts⟩ := homotopiesWithDecidableEq (Classical.decEq _) label p
    sameImage A hA subordinate point H
  exact ⟨colour, rank, q, proper, contracts⟩

/-- In dimension at most four, two nullhomotopic subcomplex inclusions that
contain all faces incident to their assigned vertices give a categorical
lower cover by four pieces after finitely many ordinary subdivisions. -/
theorem four_lower_sets_of_categorical_stars (label : X → Bool)
    (dimension : ∀ s ∈ K, s.card ≤ 5)
    (A : Bool → PreAbstractSimplicialComplex X) (hA : ∀ i, A i ≤ K)
    (subordinate : ∀ s ∈ K, ∀ v ∈ s, s ∈ A (label v))
    (point : Space K)
    (H : ∀ i, (realizationInclusion (hA i)).Homotopy (ContinuousMap.const (Space (A i)) point))
    (connected : ∀ a b : Vertex (sd K), (skeleton (sd K)).Reachable a b) :
    ∃ n, HasCategoricalCover (Face (iteratedAmbient K n).2) 4 := by
  letI : DecidableEq (Face K) := Classical.decEq _
  obtain ⟨colour, rank, q, proper, contracts⟩ :=
    two_categorical_colours label dimension A hA subordinate point H
  obtain ⟨b, _⟩ := exists_vertex_in_star q
  obtain ⟨r, cover⟩ :=
    four_pieces_of_two_categorical_colours (sd K) colour rank proper b q
      (fun i => (contracts i).some) connected
  let e : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  obtain ⟨P, hP, covers, categorical⟩ := cover
  let D := (iteratedAmbient (sd K) r).2
  have indexed : CategoricalMapCover (Fin 4) (id : Vertex D → Vertex D) := by
    refine ⟨P ∘ e.symm, fun i => hP (e.symm i), ?_, fun i => categorical (e.symm i)⟩
    intro s hs
    obtain ⟨i, hi⟩ := covers s hs
    exact ⟨e i, by simpa only [Function.comp_apply, e.symm_apply_apply] using hi⟩
  refine ⟨1 + r, ?_⟩
  rw [← iterated_ambient_add K 1 r]
  exact lower_cover_of_simplicial_cover indexed

end

end D5.S3.Topology.StableCategory.DimensionFourCategoricalColour
