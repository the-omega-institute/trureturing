/- GID: D5/S3/Topology/DescendingClosureContiguity
   generality: G
   mirror-B: D5/B/S3/Topology/DescendingClosureContiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Chain, mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Ranked descending interpolation gives relative face-neighborhood contiguity and lifts simplicial contiguity to face posets. -/

module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import OmegaBuild.Commands

/-! Relative contiguity for a descending face-poset operator, using the
cardinality of a face as its strictly increasing rank. -/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.Topology.DescendingClosureContiguity

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q]

private def stage (rank : P → ℕ) (f g : P →o Q) (k : ℕ) (x : P) : Q :=
  if rank x < k then g x else f x

private theorem stage_mono (rank : P → ℕ) (hrank : StrictMono rank)
    (f g : P →o Q) (hle : ∀ x, g x ≤ f x) (k : ℕ) : Monotone (stage rank f g k) := by
  intro x y h
  have hr := hrank.monotone h
  by_cases hx : rank x < k <;> by_cases hy : rank y < k
  · simpa [stage, hx, hy] using g.monotone h
  · simpa [stage, hx, hy] using (hle x).trans (f.monotone h)
  · omega
  · simpa [stage, hx, hy] using f.monotone h

private theorem adjacent_cross (rank : P → ℕ) (hrank : StrictMono rank)
    (f g : P →o Q) (hle : ∀ x, g x ≤ f x) (k : ℕ) {x y : P} (h : x < y) :
    stage rank f g k x ≤ stage rank f g (k + 1) y ∧
      stage rank f g (k + 1) x ≤ stage rank f g k y := by
  have hr := hrank h
  constructor
  · by_cases hx : rank x < k <;> by_cases hy : rank y < k + 1
    · simpa [stage, hx, hy] using g.monotone h.le
    · simpa [stage, hx, hy] using (hle x).trans (f.monotone h.le)
    · omega
    · simpa [stage, hx, hy] using f.monotone h.le
  · by_cases hx : rank x < k + 1 <;> by_cases hy : rank y < k
    · simpa [stage, hx, hy] using g.monotone h.le
    · simpa [stage, hx, hy] using (hle x).trans (f.monotone h.le)
    · omega
    · simpa [stage, hx, hy] using f.monotone h.le

private theorem adjacent_same (rank : P → ℕ) (f g : P →o Q) (hle : ∀ x, g x ≤ f x)
    (k : ℕ) (x : P) : stage rank f g (k + 1) x ≤ stage rank f g k x := by
  by_cases h0 : rank x < k <;> by_cases h1 : rank x < k + 1
  · simp [stage, h0, h1]
  · omega
  · simpa [stage, h0, h1] using hle x
  · simp [stage, h0, h1]

/-- Two pointwise comparable order maps on a bounded ranked domain are joined by
a finite contiguity chain that fixes each vertex where they agree. Adjacent
stages send every chain to a common chain. -/
theorem exists_relative_contiguity_of_le (rank : P → ℕ) (hrank : StrictMono rank)
    (f g : P →o Q) (hle : ∀ x, g x ≤ f x) (bound : ℕ) (hbound : ∀ x, rank x ≤ bound) :
    ∃ F : ℕ → P →o Q,
      F 0 = f ∧ F (bound + 1) = g ∧
      (∀ k x, g x = f x → F k x = f x) ∧
      (∀ k x, g x ≤ F k x) ∧
      ∀ k (s : Set P), IsChain (· ≤ ·) s → IsChain (· ≤ ·) (F k '' s ∪ F (k + 1) '' s) := by
  let F (k : ℕ) : P →o Q := ⟨stage rank f g k, stage_mono rank hrank f g hle k⟩
  have happ (k : ℕ) (x : P) : F k x = stage rank f g k x := rfl
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [happ, stage]
  · ext x
    have h : rank x < bound + 1 := Nat.lt_succ_of_le (hbound x)
    simp [happ, stage, h]
  · intro k x hx
    simp [happ, stage, hx]
  · intro k x
    by_cases hx : rank x < k <;> simp [happ, stage, hx, hle]
  intro k s hs
  have mixed (x y : P) (hx : x ∈ s) (hy : y ∈ s) :
      F k x ≤ F (k + 1) y ∨ F (k + 1) y ≤ F k x := by
    by_cases h : x = y
    · subst y
      exact Or.inr (adjacent_same rank f g hle k x)
    rcases hs hx hy h with hxy | hyx
    · exact Or.inl (adjacent_cross rank hrank f g hle k (lt_of_le_of_ne hxy h)).1
    · exact Or.inr (adjacent_cross rank hrank f g hle k (lt_of_le_of_ne hyx (Ne.symm h))).2
  intro a ha b hb _
  rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;>
    rcases hb with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · by_cases h : x = y
    · subst y; exact Or.inl le_rfl
    · rcases hs hx hy h with hxy | hyx
      · exact Or.inl ((F k).monotone hxy)
      · exact Or.inr ((F k).monotone hyx)
  · exact mixed x y hx hy
  · exact (mixed y x hy hx).symm
  · by_cases h : x = y
    · subst y; exact Or.inl le_rfl
    · rcases hs hx hy h with hxy | hyx
      · exact Or.inl ((F (k + 1)).monotone hxy)
      · exact Or.inr ((F (k + 1)).monotone hyx)


section FaceNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices of the face-poset neighborhood of a vertex subset. -/
abbrev MeetingFace (K : PreAbstractSimplicialComplex V) (S : Finset V) :=
  {f : Finset V // f ∈ K ∧ (f ∩ S).Nonempty}

/-- Intersecting each face with the selected vertices retracts the neighborhood
onto the face poset of the induced subcomplex. -/
def intersectVertices (K : PreAbstractSimplicialComplex V) (S : Finset V) :
    MeetingFace K S →o MeetingFace K S where
  toFun f := ⟨f.val ∩ S,
    (K.isRelLowerSet_faces f.property.1).2 Finset.inter_subset_left f.property.2,
    by simpa only [Finset.inter_assoc, Finset.inter_self] using f.property.2⟩
  monotone' := fun _ _ h => Finset.inter_subset_inter h (Finset.Subset.refl _)

/-- The intersection deformation proceeds through contiguous simplicial maps,
keeping the entire induced face poset fixed, with length bounded by the
number of vertices of the original complex. -/
theorem face_neighborhood_relative_contiguity
    (K : PreAbstractSimplicialComplex V) (S : Finset V) :
    ∃ F : ℕ → MeetingFace K S →o MeetingFace K S,
      F 0 = OrderHom.id ∧ F (Fintype.card V + 1) = intersectVertices K S ∧
      (∀ k f, f.val ⊆ S → F k f = f) ∧
      ∀ k (C : Set (MeetingFace K S)), IsChain (· ≤ ·) C →
        IsChain (· ≤ ·) (F k '' C ∪ F (k + 1) '' C) := by
  let rank : MeetingFace K S → ℕ := fun f => f.val.card
  have hstrict : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hdesc (f : MeetingFace K S) : intersectVertices K S f ≤ f := Finset.inter_subset_left
  have hbound (f : MeetingFace K S) : rank f ≤ Fintype.card V := Finset.card_le_univ _
  obtain ⟨F, h0, h1, hfix, _, hchain⟩ :=
    exists_relative_contiguity_of_le rank hstrict OrderHom.id (intersectVertices K S) hdesc _ hbound
  refine ⟨F, h0, h1, ?_, hchain⟩
  intro k f hf
  exact hfix k f (Subtype.ext (Finset.inter_eq_left.mpr hf))

omit [Fintype V] in
/-- A cover of the vertices by two subsets gives a cover of the flags by
their face-poset neighborhoods. -/
theorem two_subsets_cover_face_flags (K : PreAbstractSimplicialComplex V)
    (A B : Finset V) (cover : ∀ v : V, v ∈ A ∨ v ∈ B)
    (C : Set {f : Finset V // f ∈ K}) (hC : IsChain (· ≤ ·) C) :
    (∀ f ∈ C, (f.val ∩ A).Nonempty) ∨ (∀ f ∈ C, (f.val ∩ B).Nonempty) := by
  by_cases hn : C.Nonempty
  · let rank : {f : Finset V // f ∈ K} → ℕ := fun f => f.val.card
    obtain ⟨f, hf, hmin⟩ := (measure rank).wf.has_min C hn
    have hleast (g) (hg : g ∈ C) : f ≤ g := by
      by_contra h
      have hne : f ≠ g := fun hfg => h (hfg.le)
      obtain hfg | hgf := hC hf hg hne
      · exact h hfg
      · have hproper : g < f := lt_of_le_of_ne hgf hne.symm
        exact hmin g hg (Finset.card_lt_card hproper)
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces f.property).1
    rcases cover v with ha | hb
    · exact Or.inl fun g hg => ⟨v, Finset.mem_inter.mpr ⟨hleast g hg hv, ha⟩⟩
    · exact Or.inr fun g hg => ⟨v, Finset.mem_inter.mpr ⟨hleast g hg hv, hb⟩⟩
  · exact Or.inl fun f hf => (hn ⟨f, hf⟩).elim

end FaceNeighborhood

section FaceImages

variable {V W : Type*} [Fintype V] [DecidableEq W]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

/-- Nonempty faces ordered by inclusion. -/
abbrev Faces (M : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ M}

/-- The map of nonempty face posets induced by a simplicial vertex map. -/
def faceImage (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) :
    Faces K →o Faces L where
  toFun s := ⟨s.val.image f, hf _ s.property⟩
  monotone' := fun _ _ h => Finset.image_subset_image h

private def unionFaceImages (f g : V → W)
    (hfg : ∀ s ∈ K, s.image f ∪ s.image g ∈ L) : Faces K →o Faces L where
  toFun s := ⟨s.val.image f ∪ s.val.image g, hfg _ s.property⟩
  monotone' := fun _ _ h =>
    Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

/-- Contiguity of two maps between complexes lifts to the contiguity class
of their induced maps between the order complexes of the face posets. -/
theorem faceImage_connected_by_contiguity (f g : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) (hg : ∀ s ∈ K, s.image g ∈ L)
    (hfg : ∀ s ∈ K, s.image f ∪ s.image g ∈ L) :
    Relation.ReflTransGen
      (fun (a b : Faces K →o Faces L) =>
        ∀ C : Set (Faces K), IsChain (· ≤ ·) C → IsChain (· ≤ ·) (a '' C ∪ b '' C))
      (faceImage f hf) (faceImage g hg) := by
  let R (a b : Faces K →o Faces L) :=
    ∀ C : Set (Faces K), IsChain (· ≤ ·) C → IsChain (· ≤ ·) (a '' C ∪ b '' C)
  let top := unionFaceImages f g hfg
  let rank : Faces K → ℕ := fun s => s.val.card
  have hRank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hBound (s : Faces K) : rank s ≤ Fintype.card V := Finset.card_le_univ _
  have reachable (u : Faces K →o Faces L) (hu : ∀ s, u s ≤ top s) :
      Relation.ReflTransGen R top u ∧ Relation.ReflTransGen R u top := by
    obtain ⟨F, h0, hlast, _, _, hstep⟩ :=
      exists_relative_contiguity_of_le rank hRank top u hu _ hBound
    have hc (k : ℕ) : R (F k) (F (k + 1)) := hstep k
    have both (k : ℕ) :
        Relation.ReflTransGen R (F 0) (F k) ∧ Relation.ReflTransGen R (F k) (F 0) := by
      induction k with
      | zero => exact ⟨.refl, .refl⟩
      | succ k ih =>
        have hRev : R (F (k + 1)) (F k) := by
          intro s hs
          simpa only [Set.union_comm] using hc k s hs
        exact ⟨ih.1.tail (hc k), (Relation.ReflTransGen.single hRev).trans ih.2⟩
    simpa only [h0, hlast] using both (Fintype.card V + 1)
  have lf : ∀ s, faceImage f hf s ≤ top s := fun _ => Finset.subset_union_left
  have lg : ∀ s, faceImage g hg s ≤ top s := fun _ => Finset.subset_union_right
  exact (reachable _ lf).2.trans (reachable _ lg).1

end FaceImages

end D5.S3.Topology.DescendingClosureContiguity
