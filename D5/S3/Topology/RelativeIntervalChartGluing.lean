/- GID: D5/S3/Topology/RelativeIntervalChartGluing
   generality: G
   mirror-B: D5/B/S3/Topology/RelativeIntervalChartGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: One relative interval homotopy glues across compatible charts on source faces. -/

import D5.S3.Topology.PathContiguity

/-! Relative interval homotopies glue when each face has a common chart
and alternative charts agree at the fixed vertices. -/

set_option autoImplicit false

namespace D5.S3.Topology.RelativeIntervalChartGluing

open BarycentricBaseRigidity (faceImage)
open PathContiguity (IsIntervalMap intervalComplex relative_complex_contiguity)
open BarycentricGraphDistance (Vertex oneSkeleton)
open Relation (ReflTransGen)

noncomputable section

local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A

variable {X Y : Type} {P : PreAbstractSimplicialComplex X}
  {Q : PreAbstractSimplicialComplex Y}

/-- Relative contiguity in interval coordinates gives relative
contiguity after interpreting the coordinates in a chart for each
source face. Charts may differ across faces. At fixed vertices only
their agreed coordinate is used. -/
theorem relative_contiguity_of_interval_charts [Finite (Vertex P)]
    (N : ℕ) (S : Set (Vertex P)) (f g : Vertex P → Vertex (intervalComplex N))
    (hf : IsIntervalMap (oneSkeleton P) N (fun x => (f x).val))
    (hg : IsIntervalMap (oneSkeleton P) N (fun x => (g x).val))
    (hfix : Set.EqOn f g S)
    (place : Vertex P → Vertex (intervalComplex N) → Vertex Q)
    (hchart : ∀ s ∈ P, ∃ e : Vertex (intervalComplex N) → Vertex Q,
      (∀ t (ht : t ∈ intervalComplex N), faceImage e ht ∈ Q) ∧
        ∀ x : Vertex P, x.val ∈ s → ∀ i : Vertex (intervalComplex N),
          (x ∈ S → i = f x) → place x i = e i) :
    ReflTransGen (fun a b : Vertex P → Vertex Q =>
      BarycentricBaseRigidity.Contiguous a b ∧
        Set.EqOn a (fun x => place x (f x)) S ∧ Set.EqOn b (fun x => place x (f x)) S)
      (fun x => place x (f x)) (fun x => place x (g x)) := by
  let lift (a : Vertex P → Vertex (intervalComplex N)) : Vertex P → Vertex Q :=
    fun x => place x (a x)
  have chain := relative_complex_contiguity N S hf hg hfix
  refine ReflTransGen.lift lift ?_ _ _ chain
  intro a b h
  obtain ⟨hc, ha, hb⟩ := h
  refine ⟨?_, fun x hx => congrArg (place x) (ha hx), fun x hx => congrArg (place x) (hb hx)⟩
  intro s hs
  obtain ⟨e, he, hagree⟩ := hchart s hs
  let T := faceImage a hs ∪ faceImage b hs
  have hT : T ∈ intervalComplex N := hc s hs
  have lifted (k : Vertex P → Vertex (intervalComplex N))
      (hk : Set.EqOn k f S) (hsub : faceImage k hs ⊆ T) :
      faceImage (lift k) hs ⊆ faceImage e hT := by
    intro y hy
    unfold faceImage at hy ⊢
    obtain ⟨x, _, hxy⟩ := Finset.mem_image.mp hy
    let v : Vertex P := ⟨x.val, (P.isRelLowerSet_faces hs).2
      (Finset.singleton_subset_iff.mpr x.property) (Finset.singleton_nonempty _)⟩
    have hv : (k v).val ∈ T := hsub (Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩)
    refine Finset.mem_image.mpr ⟨⟨(k v).val, hv⟩, Finset.mem_attach _ _, ?_⟩
    change (e (k v)).val = y
    rw [← hagree v x.property (k v) (fun h => hk h)]
    exact hxy
  have hsub : faceImage (lift a) hs ∪ faceImage (lift b) hs ⊆ faceImage e hT :=
    Finset.union_subset (lifted a ha Finset.subset_union_left)
      (lifted b hb Finset.subset_union_right)
  have hne : (faceImage (lift a) hs).Nonempty :=
    Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr (P.isRelLowerSet_faces hs).1)
  exact (Q.isRelLowerSet_faces (he T hT)).2 hsub (hne.mono Finset.subset_union_left)

end

end D5.S3.Topology.RelativeIntervalChartGluing
