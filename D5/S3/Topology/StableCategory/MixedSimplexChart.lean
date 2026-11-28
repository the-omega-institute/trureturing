/- GID: D5/S3/Topology/StableCategory/MixedSimplexChart
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/MixedSimplexChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Second subdivisions of simplex block folds give two full regions that retract to horns. -/

import D5.S3.Topology.StableCategory.OrdinaryCollarNaturality

/-! The simplex chart for the mixed simplex attachment construction for
Mosquera–Lois–Tanaka Question 6.3. The two subdivisions use actual chains of
nonempty faces, with the horn and the chart in the same ambient subdivision. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.MixedSimplexChart

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd vertexOfFace)
open BarycentricNeighborhoodIteration (FullIn subdivision iteratedSubcomplex)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryCollarNaturality (pullback)
open OrdinaryContiguityLift (Simplicial includeSubcomplex)
open OrdinarySubdivisionMap (iterate)
open Relation (ReflTransGen)
open private vertexIn from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V
attribute [local instance] Classical.propDecidable

variable {V : Type}

/-- All nonempty subsets of a finite raw simplex. -/
def simplex (S : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ⊆ S}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩

/-- The horn opposite the raw face `L` of the simplex on `insert a L`. -/
def horn (a : V) (L : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ simplex (insert a L) ∧ ¬ L ⊆ s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1.1, fun _ hts ht => ⟨⟨ht, hts.trans hs.1.2⟩, ?_⟩⟩
    exact fun h => hs.2 (h.trans hts)

/-- The simplex spanned by an apex and its opposite block. -/
abbrev Tau (a : V) (L : Finset V) := simplex (insert a L)

private def topFace (a : V) (L : Finset V) : Face (Tau a L) :=
  ⟨insert a L, ⟨⟨a, Finset.mem_insert_self _ _⟩, fun _ hx => hx⟩⟩

private def apexFace (a : V) (L : Finset V) : Face (Tau a L) :=
  ⟨{a}, ⟨Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr
    (Finset.mem_insert_self _ _)⟩⟩

/-- The forbidden chain vertices contain the opposite face, or they contain
the top face together with a raw face omitting the apex. -/
def Forbidden (a : V) (L : Finset V) (t : Face (sd (Tau a L))) : Prop :=
  (∃ q ∈ t.val, q.val = L) ∨
    (topFace a L ∈ t.val ∧ ∃ q ∈ t.val, a ∉ q.val)

private def keep (a : V) (L : Finset V) (t : Face (sd (Tau a L))) : Bool :=
  decide (¬ Forbidden a L t)

private theorem keep_iff {a : V} {L : Finset V} {t : Face (sd (Tau a L))} :
    keep a L t = true ↔ ¬ Forbidden a L t := by
  simp [keep]

/-- The full subcomplex spanned by the retained vertices of the actual
second subdivision of the simplex. -/
def chart (a : V) (L : Finset V) : PreAbstractSimplicialComplex (Face (sd (Tau a L))) :=
  colourComplex (sd (sd (Tau a L))) (keep a L)

theorem chart_full (a : V) (L : Finset V) : FullIn (chart a L) (sd (sd (Tau a L))) :=
  ⟨fun _ hs => hs.1,
    fun s hs => ⟨s.property, fun t ht => (hs t ht).2 t (Finset.mem_singleton_self t)⟩⟩

/-- The horn in the same second subdivision as the chart. -/
abbrev hornSubdivision (a : V) (L : Finset V) :=
  iteratedSubcomplex (Tau a L) (horn a L) 2

private abbrev ChartVertex (a : V) (L : Finset V) :=
  {t : Face (sd (Tau a L)) // keep a L t = true}

private theorem forbidden_mono {a : V} {L : Finset V}
    {s t : Face (sd (Tau a L))} (h : s ≤ t) :
    Forbidden a L s → Forbidden a L t := by
  rintro (⟨q, hq, he⟩ | ⟨ht, q, hq, ha⟩)
  · exact Or.inl ⟨q, h hq, he⟩
  · exact Or.inr ⟨h ht, q, h hq, ha⟩

private theorem apex_ne_top {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty) :
    apexFace a L ≠ topFace a L := by
  intro he
  obtain ⟨x, hx⟩ := hL
  have hx' : x ∈ (topFace a L).val := Finset.mem_insert_of_mem hx
  have hx'' : x ∈ (apexFace a L).val := he.symm ▸ hx'
  have hxa : x = a := Finset.mem_singleton.mp hx''
  exact ha (hxa ▸ hx)

private theorem all_contain_apex {a : V} {L : Finset V} {t : ChartVertex a L}
    (ht : topFace a L ∈ t.val.val) {q : Face (Tau a L)} (hq : q ∈ t.val.val) :
    a ∈ q.val := by
  by_contra ha
  exact (keep_iff.mp t.property) (Or.inr ⟨ht, q, hq, ha⟩)

private def insertApex {a : V} {L : Finset V} (ha : a ∉ L)
    (t : ChartVertex a L) (ht : topFace a L ∈ t.val.val) : ChartVertex a L := by
  have hgood : ∀ q ∈ insert (apexFace a L) t.val.val, a ∈ q.val := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_singleton_self a
    · exact all_contain_apex ht hq
  let u : Face (sd (Tau a L)) := ⟨insert (apexFace a L) t.val.val,
    ⟨apexFace a L, Finset.mem_insert_self _ _⟩, by
      intro q hq r hr hqr
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Or.inl (lt_of_le_of_ne (Finset.singleton_subset_iff.mpr (hgood r hr)) hqr)
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · exact Or.inr (lt_of_le_of_ne (Finset.singleton_subset_iff.mpr (hgood q
            (Finset.mem_insert_of_mem hq))) hqr.symm)
        · exact t.val.property.2.1 hq hr hqr,
    fun q _ => q.property⟩
  refine ⟨u, keep_iff.mpr ?_⟩
  rintro (⟨q, hq, he⟩ | ⟨_, q, hq, hn⟩)
  · exact ha (he ▸ hgood q hq)
  · exact hn (hgood q hq)

/-- Adjoin the singleton apex to every retained chain containing the top. -/
private def adjoin {a : V} {L : Finset V} (ha : a ∉ L) :
    ChartVertex a L →o ChartVertex a L where
  toFun t := if ht : topFace a L ∈ t.val.val then insertApex ha t ht else t
  monotone' := by
    intro s t hst
    by_cases hs : topFace a L ∈ s.val.val
    · have ht : topFace a L ∈ t.val.val := hst hs
      simp only [dite_eq_left hs, dite_eq_left ht]
      exact Finset.insert_subset_insert _ hst
    · by_cases ht : topFace a L ∈ t.val.val
      · simp only [dite_eq_right hs, dite_eq_left ht]
        exact hst.trans (Finset.subset_insert _ _)
      · simpa only [dite_eq_right hs, dite_eq_right ht] using hst

private theorem le_adjoin {a : V} {L : Finset V} (ha : a ∉ L) (t : ChartVertex a L) :
    t ≤ adjoin ha t := by
  change t ≤ (if ht : topFace a L ∈ t.val.val then insertApex ha t ht else t)
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

private theorem adjoin_eq_of_top_not_mem {a : V} {L : Finset V} (ha : a ∉ L)
    (t : ChartVertex a L) (ht : topFace a L ∉ t.val.val) :
    adjoin ha t = t := by
  change (if h : topFace a L ∈ t.val.val then insertApex ha t h else t) = t
  exact dite_eq_right ht

private theorem erase_top_nonempty {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty)
    (t : ChartVertex a L) : ((adjoin ha t).val.val.erase (topFace a L)).Nonempty := by
  by_cases ht : topFace a L ∈ t.val.val
  · refine ⟨apexFace a L, Finset.mem_erase.mpr ⟨apex_ne_top ha hL, ?_⟩⟩
    change apexFace a L ∈
      (if h : topFace a L ∈ t.val.val then insertApex ha t h else t).val.val
    rw [dite_eq_left ht]
    exact Finset.mem_insert_self _ _
  · rw [adjoin_eq_of_top_not_mem ha t ht, Finset.erase_eq_of_notMem ht]
    exact t.val.property.1

/-- After adjoining the apex, delete the top face from every chain. -/
private def trim {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty) :
    ChartVertex a L →o ChartVertex a L where
  toFun t := by
    let u : Face (sd (Tau a L)) := ⟨(adjoin ha t).val.val.erase (topFace a L),
      ((sd (Tau a L)).isRelLowerSet_faces (adjoin ha t).val.property).2
        (Finset.erase_subset _ _) (erase_top_nonempty ha hL t)⟩
    exact ⟨u, keep_iff.mpr (fun h => (keep_iff.mp (adjoin ha t).property)
      (forbidden_mono (Finset.erase_subset _ _) h))⟩
  monotone' := fun _ _ h => Finset.erase_subset_erase _ ((adjoin ha).monotone h)

private theorem trim_le_adjoin {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty)
    (t : ChartVertex a L) : trim ha hL t ≤ adjoin ha t :=
  Finset.erase_subset _ _

private theorem trim_eq_of_top_not_mem {a : V} {L : Finset V}
    (ha : a ∉ L) (hL : L.Nonempty) (t : ChartVertex a L)
    (ht : topFace a L ∉ t.val.val) : trim ha hL t = t := by
  apply Subtype.ext
  apply Subtype.ext
  change (adjoin ha t).val.val.erase (topFace a L) = t.val.val
  rw [adjoin_eq_of_top_not_mem ha t ht, Finset.erase_eq_of_notMem ht]

private theorem raw_subset_block {a : V} {L s : Finset V}
    (hs : s ⊆ insert a L) (ha : a ∉ s) : s ⊆ L := by
  intro x hx
  rcases Finset.mem_insert.mp (hs hx) with rfl | hx'
  · exact (ha hx).elim
  · exact hx'

private theorem top_not_mem_of_horn {a : V} {L : Finset V} {t : Face (sd (Tau a L))}
    (ht : t.val ∈ subdivision (Tau a L) (horn a L)) :
    topFace a L ∉ t.val := by
  intro h
  exact (ht.2.2 _ h).2 (fun _ hx => Finset.mem_insert_of_mem hx)

/-- The same-ambient second subdivision of the horn is contained in the chart. -/
theorem hornSubdivision_le_chart (a : V) (L : Finset V) :
    hornSubdivision a L ≤ chart a L := by
  intro s hs
  refine ⟨⟨hs.1, hs.2.1, fun t _ => t.property⟩, fun t ht => keep_iff.mpr ?_⟩
  rintro (⟨q, hq, he⟩ | ⟨h, _⟩)
  · exact ((hs.2.2 t ht).2.2 q hq).2 (fun _ hx => he.symm ▸ hx)
  · exact top_not_mem_of_horn (hs.2.2 t ht) h

private theorem trim_mem_horn {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty)
    (t : ChartVertex a L) :
    (trim ha hL t).val.val ∈ subdivision (Tau a L) (horn a L) := by
  let u := trim ha hL t
  refine ⟨u.val.property.1, u.val.property.2.1, fun q hq => ⟨q.property, ?_⟩⟩
  intro hLq
  by_cases haq : a ∈ q.val
  · have he : q = topFace a L := Subtype.ext (Finset.Subset.antisymm q.property.2
      (Finset.insert_subset_iff.mpr ⟨haq, hLq⟩))
    exact (Finset.mem_erase.mp hq).1 he
  · have he : q.val = L := Finset.Subset.antisymm (raw_subset_block q.property.2 haq) hLq
    exact (keep_iff.mp u.property) (Or.inl ⟨q, hq, he⟩)

private def mapChart {a : V} {L : Finset V} (f : ChartVertex a L →o ChartVertex a L) :
    Vertex (chart a L) → Vertex (chart a L) :=
  fun v =>
    let u := f (vertexIn v)
    ⟨u.val, (vertexOfFace (sd (Tau a L)) u.val).property, by
      intro t ht
      rw [Finset.mem_singleton.mp ht]
      exact u.property⟩

private theorem mapChart_contiguous {a : V} {L : Finset V}
    (f g : ChartVertex a L →o ChartVertex a L)
    (h : ∀ C : Set (ChartVertex a L), IsChain (· ≤ ·) C →
      IsChain (· ≤ ·) (f '' C ∪ g '' C)) :
    Contiguous (mapChart f) (mapChart g) := by
  intro s hs
  let C : Set (ChartVertex a L) := {t | t.val ∈ s}
  have hC : IsChain (· ≤ ·) C := by
    intro u hu v hv huv
    exact (hs.1.2.1 hu hv (fun he => huv (Subtype.ext he))).imp LT.lt.le LT.lt.le
  let T := faceImage (mapChart f) hs ∪ faceImage (mapChart g) hs
  have memT (t : Face (sd (Tau a L))) (ht : t ∈ T) :
      ∃ u ∈ f '' C ∪ g '' C, u.val = t := by
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff (mapChart f) hs t).mp ht
      exact ⟨_, Or.inl ⟨vertexIn v, hv, rfl⟩, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff (mapChart g) hs t).mp ht
      exact ⟨_, Or.inr ⟨vertexIn v, hv, rfl⟩, rfl⟩
  have hne : (faceImage (mapChart f) hs).Nonempty := hs.1.1.attach.image _
  refine ⟨⟨hne.mono Finset.subset_union_left, ?_, fun t _ => t.property⟩, ?_⟩
  · intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := memT u hu
    obtain ⟨v', hv', rfl⟩ := memT v hv
    rcases h C hC hu' hv' (fun he => huv (congrArg Subtype.val he)) with huv' | hvu'
    · exact Or.inl (lt_of_le_of_ne huv' huv)
    · exact Or.inr (lt_of_le_of_ne hvu' huv.symm)
  · intro t ht
    obtain ⟨u, _, rfl⟩ := memT t ht
    exact u.property

private theorem mapChart_simplicial {a : V} {L : Finset V}
    (f : ChartVertex a L →o ChartVertex a L) : Simplicial (mapChart f) := by
  have h := mapChart_contiguous f f (by
    intro C hC
    rw [Set.union_self]
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact (hC hx hy (fun he => huv (congrArg f he))).imp (fun h => f.monotone h) (fun h => f.monotone h))
  intro s hs
  simpa only [Finset.union_idempotent] using h s hs

/-- The chart retraction takes its values in the same-ambient horn. -/
def retraction {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty) :
    Vertex (chart a L) → Vertex (hornSubdivision a L) :=
  fun v =>
    let u := trim ha hL (vertexIn v)
    ⟨u.val, (vertexOfFace (sd (Tau a L)) u.val).property.1,
      (vertexOfFace (sd (Tau a L)) u.val).property.2.1, by
        intro t ht
        rw [Finset.mem_singleton.mp ht]
        exact trim_mem_horn ha hL (vertexIn v)⟩

theorem retraction_simplicial {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty) :
    Simplicial (retraction ha hL) := by
  intro s hs
  have hc := mapChart_simplicial (trim ha hL) s hs
  change faceImage (mapChart (trim ha hL)) hs ∈ chart a L at hc
  have he : faceImage (mapChart (trim ha hL)) hs = faceImage (retraction ha hL) hs := rfl
  rw [he] at hc
  refine ⟨hc.1.1, hc.1.2.1, ?_⟩
  intro t ht
  obtain ⟨v, _, rfl⟩ := (mem_faceImage_iff (retraction ha hL) hs t).mp ht
  exact trim_mem_horn ha hL (vertexIn v)

theorem retraction_fixes_horn {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty)
    (v : Vertex (hornSubdivision a L)) :
    retraction ha hL (includeSubcomplex (hornSubdivision_le_chart a L) v) = v := by
  let i := includeSubcomplex (hornSubdivision_le_chart a L) v
  have htop : topFace a L ∉ (vertexIn i).val.val :=
    top_not_mem_of_horn (v.property.2.2 v.val (Finset.mem_singleton_self _))
  apply Subtype.ext
  change (trim ha hL (vertexIn i)).val = (vertexIn i).val
  exact congrArg (fun t : ChartVertex a L => t.val)
    (trim_eq_of_top_not_mem ha hL (vertexIn i) htop)

/-- A contiguity in the chart relative to its copy of the subdivided horn. -/
def HornContiguous {a : V} {L : Finset V}
    (f g : Vertex (chart a L) → Vertex (chart a L)) : Prop :=
  Contiguous f g ∧ ∀ v : Vertex (hornSubdivision a L),
    let i := includeSubcomplex (hornSubdivision_le_chart a L) v
    f i = i ∧ g i = i

private theorem relative_of_le {a : V} {L : Finset V}
    (f g : ChartVertex a L →o ChartVertex a L) (hle : ∀ t, g t ≤ f t)
    (hf : ∀ v : Vertex (hornSubdivision a L),
      let u := vertexIn (includeSubcomplex (hornSubdivision_le_chart a L) v)
      f u = u)
    (hg : ∀ v : Vertex (hornSubdivision a L),
      let u := vertexIn (includeSubcomplex (hornSubdivision_le_chart a L) v)
      g u = u) :
    ReflTransGen HornContiguous (mapChart f) (mapChart g) ∧
      ReflTransGen HornContiguous (mapChart g) (mapChart f) := by
  let rank (t : ChartVertex a L) := t.val.val.card
  have hrank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hbound (t : ChartVertex a L) : rank t ≤ (insert a L).powerset.card := by
    change t.val.val.card ≤ _
    rw [← Finset.card_image_of_injective t.val.val Subtype.val_injective]
    apply Finset.card_le_card
    intro r hr
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_powerset.mpr q.property.2
  obtain ⟨F, h0, hlast, hfix, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank f g hle _ hbound
  have hfixed (k : ℕ) (v : Vertex (hornSubdivision a L)) :
      let i := includeSubcomplex (hornSubdivision_le_chart a L) v
      mapChart (F k) i = i := by
    let i := includeSubcomplex (hornSubdivision_le_chart a L) v
    have he : F k (vertexIn i) = vertexIn i :=
      (hfix k (vertexIn i) ((hg v).trans (hf v).symm)).trans (hf v)
    apply Subtype.ext
    change (F k (vertexIn i)).val = (vertexIn i).val
    exact congrArg (fun t : ChartVertex a L => t.val) he
  have hs (k : ℕ) : HornContiguous (mapChart (F k)) (mapChart (F (k + 1))) :=
    ⟨mapChart_contiguous _ _ (hstep k), fun v => ⟨hfixed k v, hfixed (k + 1) v⟩⟩
  have hs' (k : ℕ) : HornContiguous (mapChart (F (k + 1))) (mapChart (F k)) := by
    refine ⟨fun s h => ?_, fun v => ((hs k).2 v).symm⟩
    rw [Finset.union_comm]
    exact (hs k).1 s h
  have both (k : ℕ) :
      ReflTransGen HornContiguous (mapChart (F 0)) (mapChart (F k)) ∧
      ReflTransGen HornContiguous (mapChart (F k)) (mapChart (F 0)) := by
    induction k with
    | zero => exact ⟨.refl, .refl⟩
    | succ k ih => exact ⟨ih.1.tail (hs k), (ReflTransGen.single (hs' k)).trans ih.2⟩
  simpa only [h0, hlast] using both ((insert a L).powerset.card + 1)

/-- Adjoining the apex and deleting the top deform the chart onto the
subdivided horn through simplicial contiguities in the chart, fixing the horn
at every step. -/
theorem chart_retracts_rel_horn {a : V} {L : Finset V} (ha : a ∉ L) (hL : L.Nonempty) :
    ReflTransGen HornContiguous id
      (includeSubcomplex (hornSubdivision_le_chart a L) ∘ retraction ha hL) := by
  have hstart : mapChart (OrderHom.id : ChartVertex a L →o ChartVertex a L) = id := by
    funext v
    exact Subtype.ext rfl
  have hend : mapChart (trim ha hL) =
      includeSubcomplex (hornSubdivision_le_chart a L) ∘ retraction ha hL := by
    funext v
    exact Subtype.ext rfl
  have htop (v : Vertex (hornSubdivision a L)) :
      topFace a L ∉ (vertexIn (includeSubcomplex (hornSubdivision_le_chart a L) v)).val.val :=
    top_not_mem_of_horn (v.property.2.2 v.val (Finset.mem_singleton_self _))
  have up := (relative_of_le (adjoin ha) OrderHom.id (le_adjoin ha)
    (fun v => adjoin_eq_of_top_not_mem ha _ (htop v)) (fun _ => rfl)).2
  have down := (relative_of_le (adjoin ha) (trim ha hL) (trim_le_adjoin ha hL)
    (fun v => adjoin_eq_of_top_not_mem ha _ (htop v))
    (fun v => trim_eq_of_top_not_mem ha hL _ (htop v))).1
  rw [← hstart, ← hend]
  exact up.trans down

/-- The fold from the larger simplex fixes the block and sends its complement
to the apex. -/
def fold (a : V) (L : Finset V) (x : V) : V :=
  if x ∈ L then x else a

theorem fold_simplicial (S : Finset V) (a : V) (L : Finset V) :
    ∀ s ∈ simplex S, image s (fold a L) ∈ Tau a L := by
  intro s hs
  refine ⟨hs.1.image _, ?_⟩
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  by_cases hy : y ∈ L
  · rw [fold, ite_eq_left hy]
    exact Finset.mem_insert_of_mem hy
  · rw [fold, ite_eq_right hy]
    exact Finset.mem_insert_self _ _

/-- The actual second subdivision of the block fold. -/
abbrev foldTwice (S : Finset V) (a : V) (L : Finset V) :=
  (iterate (fold a L) (fold_simplicial S a L) 2).val

/-- The pullback of the chart along the second subdivision of the block fold. -/
def piece (S : Finset V) (a : V) (L : Finset V) :
    PreAbstractSimplicialComplex (Face (sd (simplex S))) :=
  pullback (sd (sd (simplex S))) (foldTwice S a L) (chart a L)

theorem mem_piece_iff {S : Finset V} {a : V} {L : Finset V}
    {s : Finset (Face (sd (simplex S)))} :
    s ∈ piece S a L ↔
      s ∈ sd (sd (simplex S)) ∧ ∀ t ∈ s, ¬ Forbidden a L (foldTwice S a L t) := by
  constructor
  · intro hs
    exact ⟨hs.1, fun t ht => keep_iff.mp (hs.2.2 _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, (iterate (fold a L) (fold_simplicial S a L) 2).property _ hs, ?_⟩
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact keep_iff.mpr (h t ht)

theorem piece_full (S : Finset V) (a : V) (L : Finset V) :
    FullIn (piece S a L) (sd (sd (simplex S))) := by
  refine ⟨fun _ hs => hs.1, fun s hs => mem_piece_iff.mpr ⟨s.property, ?_⟩⟩
  intro t ht
  exact (mem_piece_iff.mp (hs t ht)).2 t (Finset.mem_singleton_self _)

private theorem forbidden_has_block_face {a : V} {L : Finset V} {t : Face (sd (Tau a L))}
    (ht : Forbidden a L t) : ∃ q ∈ t.val, q.val ⊆ L := by
  rcases ht with ⟨q, hq, he⟩ | ⟨_, q, hq, ha⟩
  · refine ⟨q, hq, ?_⟩
    simpa only [he] using (Finset.Subset.refl L)
  · exact ⟨q, hq, raw_subset_block q.property.2 ha⟩

/-- A forbidden image has a nonempty witness face in the original chain
whose raw vertices all lie in the block. -/
theorem forbidden_fold_has_block_face {S : Finset V} {a : V} {L : Finset V}
    (ha : a ∉ L) {t : Face (sd (simplex S))}
    (ht : Forbidden a L (foldTwice S a L t)) :
    ∃ p ∈ t.val, p.val ⊆ L := by
  obtain ⟨q, hq, hqL⟩ := forbidden_has_block_face ht
  change q ∈ image t.val (iterate (fold a L) (fold_simplicial S a L) 1).val at hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  have he : image p.val (fold a L) = q.val := congrArg Subtype.val hpq
  refine ⟨p, hp, fun x hx => ?_⟩
  by_contra hxL
  have h : fold a L x ∈ image p.val (fold a L) :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [he, fold, ite_eq_right hxL] at h
  exact ha (hqL h)

private theorem chain_comparable {P : Type*} [PartialOrder P] {s : Set P}
    (hs : IsChain (· < ·) s) {x y : P} (hx : x ∈ s) (hy : y ∈ s) :
    x ≤ y ∨ y ≤ x := by
  by_cases he : x = y
  · exact Or.inl he.le
  · exact (hs hx hy he).imp LT.lt.le LT.lt.le

private theorem no_joint_forbidden {S : Finset V} {a : V} {L₀ L₁ : Finset V}
    (ha₀ : a ∉ L₀) (ha₁ : a ∉ L₁) (hdisj : Disjoint L₀ L₁)
    {s : Finset (Face (sd (simplex S)))} (hs : s ∈ sd (sd (simplex S)))
    {t₀ t₁ : Face (sd (simplex S))} (ht₀ : t₀ ∈ s) (ht₁ : t₁ ∈ s)
    (h₀ : Forbidden a L₀ (foldTwice S a L₀ t₀))
    (h₁ : Forbidden a L₁ (foldTwice S a L₁ t₁)) : False := by
  obtain ⟨q₀, hq₀, hq₀L⟩ := forbidden_fold_has_block_face ha₀ h₀
  obtain ⟨q₁, hq₁, hq₁L⟩ := forbidden_fold_has_block_face ha₁ h₁
  have hcomp : q₀ ≤ q₁ ∨ q₁ ≤ q₀ := by
    rcases chain_comparable hs.2.1 ht₀ ht₁ with h | h
    · exact chain_comparable t₁.property.2.1 (h hq₀) hq₁
    · exact chain_comparable t₀.property.2.1 hq₀ (h hq₁)
  rcases hcomp with h | h
  · obtain ⟨x, hx⟩ := q₀.property.1
    exact (Finset.disjoint_left.mp hdisj) (hq₀L hx) (hq₁L (h hx))
  · obtain ⟨x, hx⟩ := q₁.property.1
    exact (Finset.disjoint_left.mp hdisj) (hq₀L (h hx)) (hq₁L hx)

/-- The two full pullbacks cover every simplex of the same ordinary second
subdivision of the larger simplex. -/
theorem mixed_block_cover (S : Finset V) (a : V) (L₀ L₁ : Finset V)
    (ha₀ : a ∉ L₀) (ha₁ : a ∉ L₁) (hdisj : Disjoint L₀ L₁) :
    piece S a L₀ ⊔ piece S a L₁ = sd (sd (simplex S)) := by
  apply le_antisymm (sup_le (piece_full S a L₀).1 (piece_full S a L₁).1)
  intro s hs
  change s ∈ piece S a L₀ ∨ s ∈ piece S a L₁
  by_cases hex : ∃ t ∈ s, Forbidden a L₀ (foldTwice S a L₀ t)
  · obtain ⟨t₀, ht₀, h₀⟩ := hex
    exact Or.inr (mem_piece_iff.mpr ⟨hs, fun t₁ ht₁ h₁ =>
      no_joint_forbidden ha₀ ha₁ hdisj hs ht₀ ht₁ h₀ h₁⟩)
  · exact Or.inl (mem_piece_iff.mpr ⟨hs, fun t ht hf => hex ⟨t, ht, hf⟩⟩)

end

end D5.S3.Topology.StableCategory.MixedSimplexChart
