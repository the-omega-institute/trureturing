/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CompilerStages
   mirror-E: none(waiver:original-label-two-sum-compiler-stages)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice]
   utility: none
   digest: The original filling-main and separate collar stages assemble native lists on their actual computed parent families. -/
import D5.S3.Geometry.OriginalLabelTwoSum.ParentFibres

/-! UNCOMPILED. The collar stage starts at Cout ALONE. It never operates on the
retained critical simplices. Every application of the finite batch constructor
uses the actual boundary/interference proofs from ParentFibres. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

def selectFilling {Y Z : Finset V} {E : Family V} (e : V)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (q : Finset V) : Filling (localWindow e Y Z q) (localBase e Z q E) := by
  by_cases he : e ∈ q
  · simpa only [localWindow,localBase,if_pos he] using f1
  · simpa only [localWindow,localBase,if_neg he] using f0

private theorem filling_endpoint_supported {W : Finset V} {A : Family V}
    (f : Filling W A) : Supported W (endpoint f.collar f.critical) := by
  rintro s (hs | ⟨t,ht,hst⟩)
  · exact f.supported s hs
  · exact hst.trans (f.critical_supported t ht)

private theorem join_endpoint (a : Finset V) (B : Family V)
    (C : Finset (Finset V)) :
    rawJoin (delta a) (endpoint B C) =
      rawJoin (delta a) B ⊔ facets (C.image (fun t => a ∪ t)) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨x,hx,t,ht,rfl⟩
    rcases ht with ht | ⟨u,hu,htu⟩
    · exact Or.inl ⟨x,hx,t,ht,rfl⟩
    · exact Or.inr ⟨a ∪ u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,
        Finset.union_subset_union hx htu⟩
  · rintro (hs | ⟨u,hu,hsu⟩)
    · obtain ⟨x,hx,t,ht,rfl⟩ := hs
      exact ⟨x,hx,t,Or.inl ht,rfl⟩
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
      refine ⟨s ∩ a,Finset.inter_subset_right,s ∩ t,
        Or.inr ⟨t,ht,Finset.inter_subset_right⟩,?_⟩
      ext v
      simp only [Finset.mem_union,Finset.mem_inter]
      exact ⟨fun hv => (Finset.mem_union.mp (hsu hv)).elim
        (fun ha => Or.inl ⟨hv,ha⟩) (fun ht => Or.inr ⟨hv,ht⟩),by tauto⟩

private theorem core_layers {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (is : List (Finset V)) (his : ∀ q, q ∈ is ↔ q ∈ c.critical) :
    parentCore X Y Z e E c.core c.critical f0.collar f1.collar =
      parentOf X Y Z e E c.core ⊔ fibreLayers (criticalPart e)
        (fun q => (selectFilling e f0 f1 q).collar) is := by
  apply SetLike.ext
  intro s
  constructor
  · rintro (hb | ⟨q,hq,h0 | h1⟩)
    · exact Or.inl hb
    · exact Or.inr ((mem_fibreLayers _ _ _ _).mpr ⟨q,(his q).mpr hq,
        by simpa [criticalPart,selectFilling,h0.1] using h0.2⟩)
    · exact Or.inr ((mem_fibreLayers _ _ _ _).mpr ⟨q,(his q).mpr hq,
        by simpa [criticalPart,selectFilling,h1.1] using h1.2⟩)
  · rintro (hb | hf)
    · exact Or.inl hb
    · obtain ⟨q,hq,hm⟩ := (mem_fibreLayers _ _ _ _).mp hf
      refine Or.inr ⟨q,(his q).mp hq,?_⟩
      by_cases he : e ∈ q
      · exact Or.inr ⟨he,by simpa [criticalPart,selectFilling,he] using hm⟩
      · exact Or.inl ⟨he,by simpa [criticalPart,selectFilling,he] using hm⟩

private theorem endpoint_layers {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (is : List (Finset V)) (his : ∀ q, q ∈ is ↔ q ∈ c.critical) :
    parentOf X Y Z e E c.core ⊔ fibreLayers (criticalPart e)
      (fun q => endpoint (selectFilling e f0 f1 q).collar
        (selectFilling e f0 f1 q).critical) is =
      endpoint (parentCore X Y Z e E c.core c.critical f0.collar f1.collar)
        (parentCritical e c.critical f0.critical f1.critical) := by
  rw [core_layers c f0 f1 is his]
  apply SetLike.ext
  intro s
  constructor
  · rintro (hb | hf)
    · exact Or.inl (Or.inl hb)
    · obtain ⟨q,hq,hm⟩ := (mem_fibreLayers _ _ _ _).mp hf
      rw [join_endpoint] at hm
      rcases hm with hm | ⟨u,hu,hsu⟩
      · exact Or.inl (Or.inr ((mem_fibreLayers _ _ _ _).mpr ⟨q,hq,hm⟩))
      · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
        refine Or.inr ⟨criticalPart e q ∪ t,?_,hsu⟩
        apply mem_parentCritical.mpr
        by_cases he : e ∈ q
        · exact Or.inr ⟨q,(his q).mp hq,he,t,
            by simpa [selectFilling,he] using ht,by simp [criticalPart,he]⟩
        · exact Or.inl ⟨q,(his q).mp hq,he,t,
            by simpa [selectFilling,he] using ht,by simp [criticalPart,he]⟩
  · rintro ((hb | hf) | ⟨u,hu,hsu⟩)
    · exact Or.inl hb
    · obtain ⟨q,hq,hm⟩ := (mem_fibreLayers _ _ _ _).mp hf
      apply Or.inr
      apply (mem_fibreLayers _ _ _ _).mpr
      refine ⟨q,hq,?_⟩
      rw [join_endpoint]
      exact Or.inl hm
    · rcases mem_parentCritical.mp hu with
        ⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩
      · apply Or.inr
        apply (mem_fibreLayers _ _ _ _).mpr
        refine ⟨q,(his q).mpr hq,?_⟩
        rw [join_endpoint]
        refine Or.inr ⟨q ∪ t,Finset.mem_image.mpr ⟨t,?_,?_⟩,hsu⟩
        · simpa [selectFilling,he] using ht
        · simp [criticalPart,he]
      · apply Or.inr
        apply (mem_fibreLayers _ _ _ _).mpr
        refine ⟨q,(his q).mpr hq,?_⟩
        rw [join_endpoint]
        refine Or.inr ⟨q.erase e ∪ t,Finset.mem_image.mpr ⟨t,?_,?_⟩,hsu⟩
        · simpa [selectFilling,he] using ht
        · simp [criticalPart,he]

/-- Construct the filling-main stage on the ACTUAL parent after child replay.
The list is assembled from all P0/P1 lists; its target families are computed. -/
def parentFillingStage {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y) (hE : Supported Y E) :
    Sequence (project (parentOf X Y Z e E (endpoint c.core c.critical)))
      (project (endpoint
        (parentCore X Y Z e E c.core c.critical f0.collar f1.collar)
        (parentCritical e c.critical f0.critical f1.critical))) := by
  let is := fibres c.critical
  have hi (q) : q ∈ is ↔ q ∈ c.critical := by
    simpa only [(fibres_spec c.critical).2.1] using
      (show q ∈ is ↔ q ∈ is.toFinset from List.mem_toFinset.symm)
  let f := selectFilling e f0 f1
  let T := batchFibre is (fibres_spec c.critical).1 (parentOf X Y Z e E c.core)
    (criticalPart e) (localWindow e Y Z)
    (fun q => delta (localWindow e Y Z q))
    (fun q => endpoint (f q).collar (f q).critical)
    (fun q => (f q).main)
    (by intro q hq; exact Finset.empty_subset _)
    (by intro q hq; exact Or.inl ((f q).contains (f q).empty_mem))
    (fun q _ => filling_endpoint_supported (f q))
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.1)
    (by intro q hq s hs; exact hs)
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.1)
    (by
      intro q hq t ht hb
      exact Or.inl ((f q).contains
        ((parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.2 t ht hb)))
    (by
      intro q hq q' hq' hne t ht hm
      exact Or.inl ((f q).contains (parent_fibre_cross c hXY hZ
        ((hi q).mp hq) ((hi q').mp hq') hne (fun _ hs => hs) ht hm)))
  exact T.1.cast (congrArg project (parent_initial_fibres c heX is hi)).symm
    (congrArg project (endpoint_layers c f0 f1 is hi))

/-- Construct all Q0/Q1 collar lists on Cout ALONE. Every emitted coface is
checked against the other collars; the retained parent critical cells are absent
from the domain of this Sequence. -/
def parentCollarStage {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y) (hE : Supported Y E) :
    Sequence (project (parentCore X Y Z e E c.core c.critical f0.collar f1.collar))
      (project (parentOf X Y Z e E c.core)) := by
  let is := fibres c.critical
  have hi (q) : q ∈ is ↔ q ∈ c.critical := by
    simpa only [(fibres_spec c.critical).2.1] using
      (show q ∈ is ↔ q ∈ is.toFinset from List.mem_toFinset.symm)
  let f := selectFilling e f0 f1
  let T := batchFibre is (fibres_spec c.critical).1 (parentOf X Y Z e E c.core)
    (criticalPart e) (localWindow e Y Z) (fun q => (f q).collar)
    (fun q => localBase e Z q E) (fun q => (f q).separate)
    (fun q _ => (f q).contains (f q).empty_mem)
    (fun q _ => (f q).empty_mem) (fun q _ => (f q).contains)
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.1)
    (fun q _ => (f q).supported)
    (fun q hq x hx t ht =>
      (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.1 x hx t
        ((f q).supported t ht))
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.2)
    (fun q hq q' hq' hne t ht hm => parent_fibre_cross c hXY hZ
      ((hi q).mp hq) ((hi q').mp hq') hne (f q').supported ht hm)
  have htarget : parentOf X Y Z e E c.core ⊔
      fibreLayers (criticalPart e) (fun q => localBase e Z q E) is =
        parentOf X Y Z e E c.core := by
    apply sup_eq_left.mpr
    intro s hs
    obtain ⟨q,hq,x,hx,t,ht,rfl⟩ := (mem_fibreLayers _ _ _ _).mp hs
    have hqC := (hi q).mp hq
    have haX := (parent_fibre_base c heX hXY hZ hE hqC).1
    by_cases he : e ∈ q
    · have ht' : t ∈ E ∨ t ⊆ Z := by simpa [localBase,he] using ht
      rcases ht' with htE | htZ
      · exact Or.inr ⟨x,hx.trans haX,t,htE,rfl⟩
      · have hproper : x ⊂ q := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
          · have hh : criticalPart e q ⊆ q := by simp [criticalPart,he]
            exact hx.trans hh
          · intro h
            exact heX (haX (hx (h.symm ▸ he)))
        exact Or.inl (Or.inl ⟨x,⟨c.cells.boundary q hqC x hproper,hx.trans haX⟩,
          t,htZ,rfl⟩)
    · have ht' : t ∈ E ∧ t ⊆ Z := by simpa [localBase,he] using ht
      exact Or.inr ⟨x,hx.trans haX,t,ht'.1,rfl⟩
  exact T.1.cast (congrArg project (core_layers c f0 f1 is hi)).symm
    (congrArg project htarget)


/-- Global ordered expansion of the filling-main batch.  `fibres` is the real
    cardinality/finite-enumeration comparator, so this records descending
    critical order rather than an arbitrary permutation. -/
theorem parentFillingStage_orderedPairs
    {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hE : Supported Y E) :
    orderedPairs (parentFillingStage c f0 f1 heX hXY hZ hE) =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).main.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) := by
  classical
  let is := fibres c.critical
  have hi (q) : q ∈ is ↔ q ∈ c.critical := by
    simpa only [(fibres_spec c.critical).2.1] using
      (show q ∈ is ↔ q ∈ is.toFinset from List.mem_toFinset.symm)
  let f := selectFilling e f0 f1
  let T := batchFibre is (fibres_spec c.critical).1 (parentOf X Y Z e E c.core)
    (criticalPart e) (localWindow e Y Z)
    (fun q => delta (localWindow e Y Z q))
    (fun q => endpoint (f q).collar (f q).critical)
    (fun q => (f q).main)
    (by intro q hq; exact Finset.empty_subset _)
    (by intro q hq; exact Or.inl ((f q).contains (f q).empty_mem))
    (fun q _ => filling_endpoint_supported (f q))
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.1)
    (by intro q hq s hs; exact hs)
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.1)
    (by
      intro q hq t ht hb
      exact Or.inl ((f q).contains
        ((parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.2 t ht hb)))
    (by
      intro q hq q' hq' hne t ht hm
      exact Or.inl ((f q).contains (parent_fibre_cross c hXY hZ
        ((hi q).mp hq) ((hi q').mp hq') hne (fun _ hs => hs) ht hm)))
  change orderedPairs (T.1.cast
    (congrArg project (parent_initial_fibres c heX is hi)).symm
    (congrArg project (endpoint_layers c f0 f1 is hi))) = _
  rw [orderedPairs_cast]
  exact T.2

/-- Global ordered expansion of the collar batch.  Its domain is `Cout` alone;
    the retained critical simplices are not silently inserted into this list. -/
theorem parentCollarStage_orderedPairs
    {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hE : Supported Y E) :
    orderedPairs (parentCollarStage c f0 f1 heX hXY hZ hE) =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).separate.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) := by
  classical
  let is := fibres c.critical
  have hi (q) : q ∈ is ↔ q ∈ c.critical := by
    simpa only [(fibres_spec c.critical).2.1] using
      (show q ∈ is ↔ q ∈ is.toFinset from List.mem_toFinset.symm)
  let f := selectFilling e f0 f1
  let T := batchFibre is (fibres_spec c.critical).1 (parentOf X Y Z e E c.core)
    (criticalPart e) (localWindow e Y Z) (fun q => (f q).collar)
    (fun q => localBase e Z q E) (fun q => (f q).separate)
    (fun q _ => (f q).contains (f q).empty_mem)
    (fun q _ => (f q).empty_mem) (fun q _ => (f q).contains)
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.1)
    (fun q _ => (f q).supported)
    (fun q hq x hx t ht =>
      (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.1 x hx t
        ((f q).supported t ht))
    (fun q hq => (parent_fibre_base c heX hXY hZ hE ((hi q).mp hq)).2.2.2)
    (fun q hq q' hq' hne t ht hm => parent_fibre_cross c hXY hZ
      ((hi q).mp hq) ((hi q').mp hq') hne (f q').supported ht hm)
  have htarget : parentOf X Y Z e E c.core ⊔
      fibreLayers (criticalPart e) (fun q => localBase e Z q E) is =
        parentOf X Y Z e E c.core := by
    apply sup_eq_left.mpr
    intro s hs
    obtain ⟨q,hq,x,hx,t,ht,rfl⟩ := (mem_fibreLayers _ _ _ _).mp hs
    have hqC := (hi q).mp hq
    have haX := (parent_fibre_base c heX hXY hZ hE hqC).1
    by_cases he : e ∈ q
    · have ht' : t ∈ E ∨ t ⊆ Z := by simpa [localBase,he] using ht
      rcases ht' with htE | htZ
      · exact Or.inr ⟨x,hx.trans haX,t,htE,rfl⟩
      · have hproper : x ⊂ q := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
          · have hh : criticalPart e q ⊆ q := by simp [criticalPart,he]
            exact hx.trans hh
          · intro h
            exact heX (haX (hx (h.symm ▸ he)))
        exact Or.inl (Or.inl ⟨x,⟨c.cells.boundary q hqC x hproper,hx.trans haX⟩,
          t,htZ,rfl⟩)
    · have ht' : t ∈ E ∧ t ⊆ Z := by simpa [localBase,he] using ht
      exact Or.inr ⟨x,hx.trans haX,t,ht'.1,rfl⟩
  change orderedPairs (T.1.cast
    (congrArg project (core_layers c f0 f1 is hi)).symm
    (congrArg project htarget)) = _
  rw [orderedPairs_cast]
  exact T.2

end D5.S3.Geometry.OriginalLabelTwoSum
