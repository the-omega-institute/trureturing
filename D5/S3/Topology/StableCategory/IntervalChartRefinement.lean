/- GID: D5/S3/Topology/StableCategory/IntervalChartRefinement
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer height functions lift to ordinary refinements of edge charts. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.GraphSubdivisionIntervals

/-! Refinement of an interval chart with a specified carrier selection. -/

set_option autoImplicit false

namespace D5.S3.Topology.StableCategory.IntervalChartRefinement

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (faceImage sd vertexOfFace subdividedVertex)
open GraphSubdivisionIntervals (faceImage_singleton originalSupport originalSupport_mem)
open PathContiguity (intervalComplex)
open private parityFace parityFace_adj_iff parityFace_even faceImage_subset_iff mem_faceImage_iff
  from D5.S3.Topology.GraphSubdivisionIntervals

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V

/-- Refining an interval chart preserves simpliciality. The floor of the
halved index gives an actual member of the predecessor face, and at an
even index that predecessor face is a singleton. -/
theorem refined_chart_floor {V : Type} {A : PreAbstractSimplicialComplex V}
    {n : ℕ} (chart : Vertex (intervalComplex n) → Vertex A)
    (hinj : Function.Injective chart)
    (hface : ∀ s (hs : s ∈ intervalComplex n), faceImage chart hs ∈ A) :
    ∃ lift : Vertex (intervalComplex (2 * n)) → Vertex (sd A),
      (∀ s (hs : s ∈ intervalComplex (2 * n)), faceImage lift hs ∈ sd A) ∧
      (∀ i x, x ∈ (lift i).val.val ↔
        ∃ j : Vertex (intervalComplex n),
          i.val / 2 ≤ j.val ∧ j.val ≤ (i.val + 1) / 2 ∧ (chart j).val = x) ∧
      (∀ i j, i.val = 2 * j.val → lift i = subdividedVertex (chart j)) := by
  let C (i : Vertex (intervalComplex (2 * n))) : Face A :=
    ⟨faceImage chart (parityFace i).property, hface _ (parityFace i).property⟩
  let lift (i : Vertex (intervalComplex (2 * n))) : Vertex (sd A) :=
    vertexOfFace A (C i)
  have hle (i j : Vertex (intervalComplex (2 * n))) :
      C i ≤ C j ↔ parityFace i ≤ parityFace j :=
    faceImage_subset_iff hinj (parityFace i).property (parityFace j).property
  have hlt (i j : Vertex (intervalComplex (2 * n))) :
      C i < C j ↔ parityFace i < parityFace j := by
    simp only [lt_iff_le_not_ge, hle]
  refine ⟨lift, ?_, ?_, ?_⟩
  · intro s hs
    refine ⟨hs.1.attach.image _, ?_, fun x _ => x.property⟩
    intro a ha b hb hab
    obtain ⟨i, hi, hia⟩ := (mem_faceImage_iff lift hs a).mp ha
    obtain ⟨j, hj, hjb⟩ := (mem_faceImage_iff lift hs b).mp hb
    change C i = a at hia
    change C j = b at hjb
    rw [← hia, ← hjb]
    have hne : i.val ≠ j.val := fun h => hab (hia.symm.trans ((congrArg C (Subtype.ext h)).trans hjb))
    have hij : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      have hu := hs.2.2 _ hi _ hj
      have hv := hs.2.2 _ hj _ hi
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl (Nat.le_antisymm (Nat.succ_le_of_lt h) hv)
      · exact Or.inr (Nat.le_antisymm (Nat.succ_le_of_lt h) hu)
    exact ((parityFace_adj_iff i j).mpr hij).imp (hlt i j).2 (hlt j i).2
  · intro i x
    change x ∈ faceImage chart (parityFace i).property ↔ _
    rw [mem_faceImage_iff]
    change (∃ j : Vertex (intervalComplex n),
      j.val ∈ Finset.Icc (i.val / 2) ((i.val + 1) / 2) ∧ (chart j).val = x) ↔ _
    simp only [Finset.mem_Icc, and_assoc]
  · intro i j hij
    have hp : parityFace i = (⟨{j.val}, j.property⟩ : Face (intervalComplex n)) :=
      Subtype.ext (parityFace_even i hij)
    apply Subtype.ext
    apply Subtype.ext
    change faceImage chart (parityFace i).property = {(chart j).val}
    exact (congrArg (fun q : Face (intervalComplex n) => faceImage chart q.property) hp).trans
      (faceImage_singleton chart j)

/-- A single carrier selector can be chosen by a coordinate on the
entire coarse complex. Equal coordinates may occur in distinct faces. -/
theorem exists_coordinate_minimum_selector {V : Type}
    (A : PreAbstractSimplicialComplex V) (q : V → ℕ) :
    ∃ select : Vertex (sd A) → Vertex A,
      (∀ x, (select x).val ∈ x.val.val ∧ ∀ y ∈ x.val.val, q (select x).val ≤ q y) ∧
      ∀ s (hs : s ∈ sd A), faceImage select hs ∈ A := by
  classical
  have minima (x : Vertex (sd A)) : ∃ y : Vertex A,
      y.val ∈ x.val.val ∧ ∀ z ∈ x.val.val, q y.val ≤ q z := by
    let values := x.val.val.image q
    have hn : values.Nonempty := (A.isRelLowerSet_faces x.val.property).1.image _
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp (Finset.min'_mem values hn)
    let v : Vertex A := ⟨y, (A.isRelLowerSet_faces x.val.property).2
      (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty _)⟩
    refine ⟨v, hy, fun z hz => ?_⟩
    change q y ≤ q z
    rw [he]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  choose select hselect using minima
  refine ⟨select, hselect, ?_⟩
  intro s hs
  apply (A.isRelLowerSet_faces (originalSupport_mem 1 hs)).2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff select hs y).mp hy
    change (select x).val ∈ s.biUnion Subtype.val
    exact Finset.mem_biUnion.mpr ⟨x.val, hx, (hselect x).1⟩
  · exact hs.1.attach.image _

/-- With the measured coarse coordinate, one global minimum selector
reads the halved index in any compatible refined chart. -/
theorem minimum_selector_eq_half {V : Type} {A : PreAbstractSimplicialComplex V}
    {n : ℕ} (q : V → ℕ) (select : Vertex (sd A) → Vertex A)
    (hselect : ∀ x, (select x).val ∈ x.val.val ∧
      ∀ y ∈ x.val.val, q (select x).val ≤ q y)
    (chart : Vertex (intervalComplex n) → Vertex A)
    (hlabel : ∀ j, q (chart j).val = j.val)
    (lift : Vertex (intervalComplex (2 * n)) → Vertex (sd A))
    (hparent : ∀ i x, x ∈ (lift i).val.val ↔
      ∃ j : Vertex (intervalComplex n),
        i.val / 2 ≤ j.val ∧ j.val ≤ (i.val + 1) / 2 ∧ (chart j).val = x)
    (i : Vertex (intervalComplex (2 * n))) (j : Vertex (intervalComplex n))
    (hj : j.val = i.val / 2) : select (lift i) = chart j := by
  have hjmem : (chart j).val ∈ (lift i).val.val :=
    (hparent i _).mpr ⟨j, hj.ge, hj ▸ Nat.div_le_div_right (Nat.le_succ i.val), rfl⟩
  obtain ⟨k, hlow, _, hk⟩ := (hparent i _).mp (hselect (lift i)).1
  have hk' : k.val ≤ j.val := by
    rw [← hlabel k, hk, ← hlabel j]
    exact (hselect (lift i)).2 _ hjmem
  have he : k = j := Subtype.ext (Nat.le_antisymm hk' (hj ▸ hlow))
  exact Subtype.ext (hk.symm.trans (congrArg (fun l => (chart l).val) he))

end

end D5.S3.Topology.StableCategory.IntervalChartRefinement
