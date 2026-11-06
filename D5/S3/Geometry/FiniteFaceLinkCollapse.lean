/- GID: D5/S3/Geometry/FiniteFaceLinkCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteFaceLinkCollapse
   mirror-E: none(waiver:finite-face-link-collapse)
   anchors: [mathlib/module/Mathlib.Data.List.Forall2]
   utility: none
   digest: Original-label nonempty-face link collapse preserves ordered pairs, every frame, and the whole antistar fixed set. -/
/- SOURCE DRAFT — UNCOMPILED.  No Lean/kernel, axiom-closure, gate, or
   project-acceptance result is claimed for this file.

   Frozen input baselines (read-only snapshots; final bindings are in
   source-repair-evidence.json):
   * FiniteElementaryCollapse.lean,
     SHA256 e236cddd69e50c23f2a500a0775c57c12123f92613c91cec29a61f191dae2c3f.
   * FiniteRelativeSimplicialCollapse.lean,
     SHA256 0e751c6d6b0dc309f20384f8051d19f31724e80e3fa4f85492b9c6d9177e1342.
   The relative source uses the frozen whole-cylinder bundle's public original
   FiniteConeCollapse.ConePair.cone_segment and the incremental owner patch
   exposing the original FiniteComponentClosure.vertexComplex.  This draft uses the name
   `vertexComplex` supplied by that owner and does not define a second one.

   This is the original-label finite-face lift.  It keeps the nonempty-face
   convention: the empty face occurs only through AugmentedFace and never as a
   point of a realization.  The last theorem is conditional on an actual
   Sequence on the original label type; no subtype homeomorphism transports a
   combinatorial sequence.
-/

import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import D5.S3.Geometry.FiniteComponentClosure.Models

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteFaceLinkCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse
open FiniteGraphVertexSubstitution
open FiniteComponentClosure (vertexComplex)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Disjointness is kept as a predicate on the original finite labels.  This
form avoids changing the carrier to a subtype. -/
def DisjointFrom (E s : Finset V) : Prop := ∀ x ∈ E, x ∉ s

/-- Disjointness is inherited by a smaller right-hand face. The former
`DisjointFrom E (E ∪ s)` conclusion was false for nonempty E. -/
private theorem disjointFrom_subset_right {E s t : Finset V}
    (h : DisjointFrom E s) (ht : t ⊆ s) : DisjointFrom E t := by
  intro x hxE hxt
  exact h x hxE (ht hxt)

private theorem disjointFrom_sdiff (E s : Finset V) :
    DisjointFrom E (s \ E) := by
  intro x hxE hx
  exact (Finset.mem_sdiff.mp hx).2 hxE

private theorem diff_union_disjoint {E s : Finset V}
    (h : DisjointFrom E s) : (E ∪ s) \ E = s := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1 with hxE | hxs
    · exact ((Finset.mem_sdiff.mp hx).2 hxE).elim
    · exact hxs
  · intro x hxs
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right E hxs, fun hxE => h x hxE hxs⟩

private theorem union_diff_of_subset {E s : Finset V} (h : E ⊆ s) :
    E ∪ (s \ E) = s := Finset.union_sdiff_of_subset h

private theorem union_subset_iff_diff {E a s : Finset V}
    (hdis : DisjointFrom E a) (hEs : E ⊆ s) :
    E ∪ a ⊆ s ↔ a ⊆ s \ E := by
  constructor
  · intro h x hx
    exact Finset.mem_sdiff.mpr
      ⟨h (Finset.mem_union_right E hx), fun hxE => hdis x hxE hx⟩
  · intro h
    exact Finset.union_subset hEs (fun x hx => (Finset.mem_sdiff.mp (h hx)).1)

/-- The nonempty face link of an arbitrary nonempty face. -/
def faceLink (K : PreAbstractSimplicialComplex V) (E : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ DisjointFrom E s ∧ E ∪ s ∈ K}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hdis, hKs⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, disjointFrom_subset_right hdis hts,
      (K.isRelLowerSet_faces hKs).2 (Finset.union_subset_union_left E hts)
        (ht.mono Finset.subset_union_right)⟩

/-- The exact antistar, on the same original label type. -/
def faceAntistar (K : PreAbstractSimplicialComplex V) (E : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ ¬ E ⊆ s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hns⟩
    refine ⟨(K.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    refine ⟨(K.isRelLowerSet_faces hs).2 hts ht, ?_⟩
    intro hEt
    exact hns (hEt.trans hts)

/-- Exact current frame.  Faces avoiding E stay forever; faces containing E
are controlled by the augmented current link. -/
def faceFrame (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (M : PreAbstractSimplicialComplex V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace M (s \ E))}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hframe⟩
    refine ⟨(K.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    refine ⟨(K.isRelLowerSet_faces hs).2 hts ht, ?_⟩
    by_cases hEt : E ⊆ t
    · right
      have hEs : E ⊆ s := hEt.trans hts
      have hM : AugmentedFace M (s \ E) := hframe.resolve_left (fun h => h hEs)
      apply augmented_downward hM
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hts (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    · exact Or.inl hEt

@[simp] theorem mem_faceLink (K : PreAbstractSimplicialComplex V) (E s : Finset V) :
    s ∈ faceLink K E ↔ s.Nonempty ∧ DisjointFrom E s ∧ E ∪ s ∈ K := Iff.rfl

@[simp] theorem mem_faceAntistar (K : PreAbstractSimplicialComplex V) (E s : Finset V) :
    s ∈ faceAntistar K E ↔ s ∈ K ∧ ¬ E ⊆ s := Iff.rfl

@[simp] theorem mem_faceFrame (K : PreAbstractSimplicialComplex V)
    (E : Finset V) (M : PreAbstractSimplicialComplex V) (s : Finset V) :
    s ∈ faceFrame K E M ↔ s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace M (s \ E)) := Iff.rfl

/-- The frame contains the antistar and is a subcomplex of K. -/
theorem faceAntistar_le_frame (K : PreAbstractSimplicialComplex V)
    (E : Finset V) (M : PreAbstractSimplicialComplex V) : faceAntistar K E ≤ faceFrame K E M := by
  intro s hs
  exact ⟨hs.1, Or.inl hs.2⟩

theorem faceFrame_le (K : PreAbstractSimplicialComplex V)
    (E : Finset V) (M : PreAbstractSimplicialComplex V) : faceFrame K E M ≤ K := fun _ hs => hs.1

/-- The initial frame is exactly K when M is the full nonempty link. -/
theorem faceFrame_link_eq (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (hE : E.Nonempty) : faceFrame K E (faceLink K E) = K := by
  apply le_antisymm
  · exact faceFrame_le K E _
  · intro s hs
    refine ⟨hs, ?_⟩
    by_cases hEs : E ⊆ s
    · right
      by_cases hdiff : s \ E = ∅
      · exact Or.inl hdiff
      · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr hdiff,
          disjointFrom_sdiff E s, by rw [union_diff_of_subset hEs]; exact hs⟩
    · exact Or.inl hEs

/-- Every face containing E is represented by an augmented link face. -/
theorem faceFrame_containing_iff (K : PreAbstractSimplicialComplex V)
    {E : Finset V} {M : PreAbstractSimplicialComplex V}
    (hM : M ≤ faceLink K E) {s : Finset V} (hs : s ∈ K) :
    E ⊆ s → (s ∈ faceFrame K E M ↔ AugmentedFace M (s \ E)) := by
  intro hEs
  change (s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace M (s \ E))) ↔ _
  simp only [hs, hEs, not_true_eq_false, false_or, true_and]

/-- The exact link of an intermediate frame, including all nonempty faces. -/
theorem faceFrame_link (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M : PreAbstractSimplicialComplex V} (hM : M ≤ faceLink K E) :
    faceLink (faceFrame K E M) E = M := by
  apply le_antisymm
  · intro s hs
    have hframe := hs.2.2
    have hMaug : AugmentedFace M ((E ∪ s) \ E) :=
      (faceFrame_containing_iff K hM hframe.1 Finset.subset_union_left).mp hframe
    rw [diff_union_disjoint hs.2.1] at hMaug
    rcases hMaug with hempty | hmem
    · exact (hs.1.ne_empty hempty).elim
    · exact hmem
  · intro s hs
    have hMs := hM hs
    refine ⟨hMs.1, hMs.2.1, hMs.2.2, Or.inr ?_⟩
    rw [diff_union_disjoint hMs.2.1]
    exact Or.inr hs

/-- Coface correspondence over the containing-E part of the frame.
The E-subset hypothesis is essential: the frame retains every antistar face. -/
theorem faceFrame_coface_iff (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M : PreAbstractSimplicialComplex V} (hM : M ≤ faceLink K E)
    {P : CollapsePair V} (hP : P.ambient = M)
    {s : Finset V} (hs : s ∈ faceFrame K E M) (hEs : E ⊆ s) :
    E ∪ P.lower ⊂ s ↔ P.lower ⊂ s \ E := by
  have hl : P.lower ∈ M := hP ▸ P.lower_mem
  have hdis := (hM hl).2.1
  rw [Finset.ssubset_iff_subset_ne, Finset.ssubset_iff_subset_ne,
    union_subset_iff_diff hdis hEs]
  apply and_congr_right
  intro _
  constructor
  · intro hne heq
    apply hne
    calc
      E ∪ P.lower = E ∪ (s \ E) := congrArg (fun t => E ∪ t) heq
      _ = s := union_diff_of_subset hEs
  · intro hne heq
    apply hne
    calc
      P.lower = (E ∪ P.lower) \ E := (diff_union_disjoint hdis).symm
      _ = s \ E := congrArg (fun t => t \ E) heq

/-- Freeness is checked in the original owner ambient after the exact
M-to-P.ambient equality transport. No new coface premise is assumed. -/
theorem lifted_pair_spec (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M : PreAbstractSimplicialComplex V} (hM : M ≤ faceLink K E)
    (P : CollapsePair V) (hP : P.ambient = M)
    (hPsub : M ≤ faceFrame K E M) :
    ∀ {s : Finset V}, s ∈ faceFrame K E M →
      E ∪ P.lower ⊂ s → s = E ∪ P.upper := by
  intro s hs hstrict
  have hEs : E ⊆ s := Finset.subset_union_left.trans hstrict.subset
  have hco := (faceFrame_coface_iff K E hM hP hs hEs).mp hstrict
  have hMface : s \ E ∈ M := by
    have hm := (faceFrame_containing_iff K hM hs.1 hEs).mp hs
    rcases hm with hempty | hm
    · exact (P.lower_nonempty.ne_empty
        (Finset.subset_empty.mp (by simpa only [hempty] using hco.subset))).elim
    · exact hm
  have heq := P.free (s \ E) (hP.symm ▸ hMface) hco
  calc
    s = E ∪ (s \ E) := (union_diff_of_subset hEs).symm
    _ = E ∪ P.upper := congrArg (fun t => E ∪ t) heq

/-- Singleton and insertion identities for the link. -/
theorem faceLink_singleton (K : PreAbstractSimplicialComplex V) (v : V) :
    faceLink K ({v} : Finset V) = link K v := by
  apply SetLike.coe_injective
  ext s
  change (s.Nonempty ∧ DisjointFrom {v} s ∧ {v} ∪ s ∈ K) ↔
    (s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K)
  simp [DisjointFrom]

theorem faceLink_insert (K : PreAbstractSimplicialComplex V)
    (v : V) (F : Finset V) (hvF : v ∉ F) :
    faceLink K (insert v F) = faceLink (link K v) F := by
  apply le_antisymm
  · intro s hs
    refine ⟨hs.1, ?_, ?_⟩
    · exact fun x hxF => hs.2.1 x (Finset.mem_insert_of_mem hxF)
    · refine ⟨hs.1.mono Finset.subset_union_right, ?_, ?_⟩
      · intro hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hvF hv
        · exact hs.2.1 v (Finset.mem_insert_self _ _) hv
      · simpa only [Finset.insert_union] using hs.2.2
  · intro s hs
    refine ⟨hs.1, ?_, ?_⟩
    · intro x hx hxS
      rcases Finset.mem_insert.mp hx with rfl | hxF
      · exact hs.2.2.2.1 (Finset.mem_union_right F hxS)
      · exact hs.2.1 x hxF hxS
    · simpa only [Finset.insert_union] using hs.2.2.2.2

/-- Singleton antistar is the existing whole deletion. -/
theorem faceAntistar_singleton (K : PreAbstractSimplicialComplex V) (v : V) :
    faceAntistar K ({v} : Finset V) = deletion K v := by
  apply SetLike.coe_injective
  ext s
  change (s ∈ K ∧ ¬ ({v} : Finset V) ⊆ s) ↔ (s ∈ K ∧ v ∉ s)
  rw [Finset.singleton_subset_iff]

private theorem insert_subset_erase_iff {v : V} {F s : Finset V}
    (hvF : v ∉ F) (hvs : v ∈ s) :
    insert v F ⊆ s ↔ F ⊆ s.erase v := by
  constructor
  · intro h x hx
    exact Finset.mem_erase.mpr
      ⟨fun he => hvF (he ▸ hx), h (Finset.mem_insert_of_mem hx)⟩
  · intro h
    exact Finset.insert_subset_iff.mpr
      ⟨hvs, h.trans (Finset.erase_subset _ _)⟩

private theorem sdiff_insert_eq_erase_sdiff (s F : Finset V) (v : V) :
    s \ insert v F = s.erase v \ F := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
  tauto

private theorem nonempty_not_subset_singleton {F : Finset V} {v : V}
    (hF : F.Nonempty) (hvF : v ∉ F) : ¬ F ⊆ ({v} : Finset V) := by
  intro h
  obtain ⟨x, hx⟩ := hF
  have he : x = v := Finset.mem_singleton.mp (h hx)
  exact hvF (he ▸ hx)

/-- The containing-v part of the insertion identity. The empty erased face
is treated explicitly; it contributes the existing vertex, not a new point. -/
private theorem frame_insert_containing (K : PreAbstractSimplicialComplex V)
    (v : V) (F : Finset V) (M : PreAbstractSimplicialComplex V)
    (hvF : v ∉ F) (hF : F.Nonempty) (hvK : ({v} : Finset V) ∈ K)
    {s : Finset V} (hvs : v ∈ s) :
    s ∈ faceFrame K (insert v F) M ↔
      AugmentedFace (faceFrame (link K v) F M) (s.erase v) := by
  by_cases he : s.erase v = ∅
  · have hs : s = {v} := by
      calc
        s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
        _ = {v} := by rw [he]; rfl
    have hn : ¬ insert v F ⊆ s := by
      rw [hs]
      exact fun h => nonempty_not_subset_singleton hF hvF
        ((Finset.subset_insert _ _).trans h)
    constructor
    · intro _; exact Or.inl he
    · intro _; exact ⟨by rw [hs]; exact hvK, Or.inl hn⟩
  · have ht : (s.erase v).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    constructor
    · intro hs
      refine Or.inr ⟨⟨ht, Finset.notMem_erase _ _, ?_⟩, ?_⟩
      · simpa only [Finset.insert_erase hvs] using hs.1
      · simpa only [insert_subset_erase_iff hvF hvs,
          sdiff_insert_eq_erase_sdiff] using hs.2
    · rintro (he' | hs)
      · exact (he he').elim
      · refine ⟨?_, ?_⟩
        · simpa only [Finset.insert_erase hvs] using hs.1.2.2
        · simpa only [insert_subset_erase_iff hvF hvs,
            sdiff_insert_eq_erase_sdiff] using hs.2

/-- Insertion frame identity with the actual vertex and a fresh insertion.
Both hypotheses are essential for arbitrary (possibly empty) current M. -/
theorem faceFrame_insert (K : PreAbstractSimplicialComplex V)
    (v : V) (F : Finset V) (M : PreAbstractSimplicialComplex V)
    (hM : M ≤ faceLink K (insert v F)) (hF : F.Nonempty)
    (hvF : v ∉ F) (hvK : ({v} : Finset V) ∈ K) :
    faceFrame K (insert v F) M =
      deletion K v ⊔ cone v (faceFrame (link K v) F M) := by
  apply le_antisymm
  · intro s hs
    by_cases hvs : v ∈ s
    · exact Or.inr ⟨(K.isRelLowerSet_faces hs.1).1,
        (frame_insert_containing K v F M hvF hF hvK hvs).mp hs⟩
    · exact Or.inl ⟨hs.1, hvs⟩
  · intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, Or.inl (fun h => hs.2 (h (Finset.mem_insert_self _ _)))⟩
    · by_cases hvs : v ∈ s
      · exact (frame_insert_containing K v F M hvF hF hvK hvs).mpr hs.2
      · have ht : s.erase v = s := Finset.erase_eq_of_notMem hvs
        rcases hs.2 with he | he
        · exact (hs.1.ne_empty (ht.symm.trans he)).elim
        · have hK : s ∈ K :=
            (K.isRelLowerSet_faces he.1.2.2).2
              (by rw [ht]; exact Finset.subset_insert _ _) hs.1
          exact ⟨hK, Or.inl (fun h => hvs (h (Finset.mem_insert_self _ _)))⟩

/-- The nonempty residual F makes the apex singleton an antistar face.
The insertion is fresh and the apex was already a vertex of K. -/
theorem faceAntistar_insert (K : PreAbstractSimplicialComplex V)
    (v : V) (F : Finset V) (hF : F.Nonempty) (hvK : ({v} : Finset V) ∈ K)
    (hvF : v ∉ F) :
    faceAntistar K (insert v F) =
      deletion K v ⊔ cone v (faceAntistar (link K v) F) := by
  apply le_antisymm
  · intro s hs
    by_cases hvs : v ∈ s
    · right
      refine ⟨(K.isRelLowerSet_faces hs.1).1, ?_⟩
      by_cases he : s.erase v = ∅
      · exact Or.inl he
      · exact Or.inr ⟨⟨Finset.nonempty_iff_ne_empty.mpr he,
          Finset.notMem_erase _ _, by simpa only [Finset.insert_erase hvs] using hs.1⟩,
          fun h => hs.2 ((insert_subset_erase_iff hvF hvs).mpr h)⟩
    · exact Or.inl ⟨hs.1, hvs⟩
  · intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, fun h => hs.2 (h (Finset.mem_insert_self _ _))⟩
    · rcases hs.2 with he | he
      · have hsub : s ⊆ ({v} : Finset V) := by
          intro x hx
          by_contra hn
          have hxv : x ≠ v := by simpa only [Finset.mem_singleton] using hn
          have hx' := Finset.mem_erase.mpr ⟨hxv, hx⟩
          simpa only [he, Finset.notMem_empty] using hx'
        exact ⟨(K.isRelLowerSet_faces hvK).2 hsub hs.1,
          fun h => nonempty_not_subset_singleton hF hvF
            (((Finset.subset_insert _ _).trans h).trans hsub)⟩
      · have hK : s ∈ K := (K.isRelLowerSet_faces he.1.2.2).2
            (Finset.insert_erase_subset _ _) hs.1
        refine ⟨hK, ?_⟩
        intro h
        exact he.2 ((insert_subset_erase_iff hvF
          (h (Finset.mem_insert_self _ _))).mp h)

theorem faceFrame_singleton (K : PreAbstractSimplicialComplex V) (v : V)
    (M : PreAbstractSimplicialComplex V) (hM : M ≤ link K v)
    (hvK : ({v} : Finset V) ∈ K) :
    faceFrame K ({v} : Finset V) M = deletion K v ⊔ cone v M := by
  have hdiff (s : Finset V) : s \ ({v} : Finset V) = s.erase v := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
    exact and_comm
  apply le_antisymm
  · intro s hs
    by_cases hvs : v ∈ s
    · right
      refine ⟨(K.isRelLowerSet_faces hs.1).1, ?_⟩
      have hm := hs.2.resolve_left (fun h => h (Finset.singleton_subset_iff.mpr hvs))
      simpa only [hdiff] using hm
    · exact Or.inl ⟨hs.1, hvs⟩
  · intro s hs
    have hK : s ∈ K := by
      rw [← deletion_union_link_cone K v hvK]
      exact (sup_le_sup_left (cone_mono v hM) (deletion K v)) hs
    refine ⟨hK, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl (fun h => hs.2 (Finset.singleton_subset_iff.mp h))
    · exact Or.inr (by simpa only [hdiff] using hs.2)

/-- The output of liftOver is the first pair in the relation; its source pair
is second.  This orientation matches `List.Forall₂ output source`. -/
def PairLiftedBy (D : PreAbstractSimplicialComplex V) (v : V)
    (P Q : CollapsePair V) : Prop :=
  ∃ (hQD : Q.ambient ≤ D) (hvD : Fresh v D),
    P = Pair.liftPairOver Q D v hQD hvD

theorem pairs_liftOver_forall2
    {M N D : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (v : V) (hMD : M ≤ D) (hvD : Fresh v D) :
    List.Forall₂ (PairLiftedBy D v)
      (S.liftOver D v hMD hvD).pairs S.pairs := by
  simpa [PairLiftedBy] using
    (Sequence.pairs_liftOver_forall2 S v hMD hvD)

/-- A pair relation after all insertions have been performed.  The output pair
is first, matching the chosen output prefix in `faceLinkCollapse_ordered_pairs`.
-/
def PairUnionSpec (E : Finset V) (d : V)
    (P Q : CollapsePair V) : Prop :=
  P.lower = E ∪ Q.lower ∧ P.apex = Q.apex ∧ P.upper = E ∪ Q.upper

/-- The singleton owner is reused exactly; the empty-F cone branch is never
used.  This helper is intentionally an actual Sequence, not a topological
existence statement. -/
def singletonFaceCollapse (K : PreAbstractSimplicialComplex V) (v d : V)
    (S : Sequence (faceLink K ({v} : Finset V)) (vertexComplex d)) :
    Sequence K (faceAntistar K ({v} : Finset V)) := by
  let S' : Sequence (link K v) (vertexComplex d) :=
    S.cast (faceLink_singleton K v) rfl
  exact (linkCollapseDeletion K v d S').cast rfl
    (faceAntistar_singleton K v).symm

/-- A link face already lies in the corresponding frame. -/
private theorem link_base_le_frame (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M : PreAbstractSimplicialComplex V} (hM : M ≤ faceLink K E) :
    M ≤ faceFrame K E M := by
  intro s hs
  have hm := hM hs
  have hK : s ∈ K := (K.isRelLowerSet_faces hm.2.2).2
    Finset.subset_union_right hm.1
  refine ⟨hK, Or.inr (Or.inr ?_)⟩
  have hd : s \ E = s := by
    ext x
    constructor
    · exact fun h => (Finset.mem_sdiff.mp h).1
    · intro hx
      exact Finset.mem_sdiff.mpr ⟨hx, fun hxE => hm.2.1 x hxE hx⟩
  rw [hd]
  exact hs

/-- Lift one original free pair, literally adjoining E to its lower and upper
faces. This constructs CollapsePair data and uses the original free-field API. -/
private def framePair (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (P : CollapsePair V) (hP : P.ambient ≤ faceLink K E) : CollapsePair V where
  ambient := faceFrame K E P.ambient
  lower := E ∪ P.lower
  apex := P.apex
  lower_nonempty := P.lower_nonempty.mono Finset.subset_union_right
  apex_notMem := by
    intro ha
    rcases Finset.mem_union.mp ha with haE | hal
    · exact (hP P.upper_mem).2.1 P.apex haE (Finset.mem_insert_self _ _)
    · exact P.apex_notMem hal
  upper_mem := by
    have hu := hP P.upper_mem
    have heq : insert P.apex (E ∪ P.lower) = E ∪ P.upper := by
      simp only [CollapsePair.upper, Finset.union_insert]
    rw [heq]
    refine ⟨hu.2.2, Or.inr ?_⟩
    rw [diff_union_disjoint hu.2.1]
    exact Or.inr P.upper_mem
  free := by
    intro s hs hstrict
    have he := lifted_pair_spec K E hP P rfl (link_base_le_frame K E hP) hs hstrict
    simpa only [CollapsePair.upper, Finset.union_insert] using he

private theorem framePair_retained (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (P : CollapsePair V) (hP : P.ambient ≤ faceLink K E) :
    (framePair K E P hP).retained = faceFrame K E P.retained := by
  apply SetLike.coe_injective
  ext s
  change ((s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace P.ambient (s \ E))) ∧
      ¬ E ∪ P.lower ⊆ s) ↔
    (s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace P.retained (s \ E)))
  by_cases hEs : E ⊆ s
  · rw [union_subset_iff_diff (hP P.lower_mem).2.1 hEs, augmented_retained]
    simp only [hEs, not_true_eq_false, false_or]
    exact and_assoc
  · have hn : ¬ E ∪ P.lower ⊆ s :=
      fun h => hEs (Finset.subset_union_left.trans h)
    simp only [hEs, not_false_eq_true, true_or, and_true, hn]

/-- Replay the source sequence in its exact frames, on the same finite label
carrier and in the same order. No additional Sequence owner is introduced. -/
private def replayFrames (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (hM : M ≤ faceLink K E) : Sequence (faceFrame K E M) (faceFrame K E N) := by
  revert hM
  induction S with
  | refl M => intro hM; exact .refl _
  | @step P N T ih =>
      intro hM
      let Q := framePair K E P hM
      have tail := ih (P.retained_le.trans hM)
      exact .step Q (tail.cast (framePair_retained K E P hM).symm rfl)

private theorem replayFrames_pairs (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (hM : M ≤ faceLink K E) (d : V) :
    List.Forall₂ (PairUnionSpec E d) (replayFrames K E S hM).pairs S.pairs := by
  revert hM
  induction S with
  | refl M => intro hM; exact .nil
  | @step P N T ih =>
      intro hM
      change List.Forall₂ (PairUnionSpec E d)
        (framePair K E P hM ::
          ((replayFrames K E T (P.retained_le.trans hM)).cast
            (framePair_retained K E P hM).symm rfl).pairs) (P :: T.pairs)
      rw [Sequence.pairs_cast]
      refine .cons ⟨rfl, rfl, ?_⟩ (ih (P.retained_le.trans hM))
      simp only [framePair, CollapsePair.upper, Finset.union_insert]

private theorem replayFrames_frames (K : PreAbstractSimplicialComplex V) (E : Finset V)
    {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (hM : M ≤ faceLink K E) :
    (replayFrames K E S hM).frames = S.frames.map (faceFrame K E) := by
  revert hM
  induction S with
  | refl M => intro hM; rfl
  | @step P N T ih =>
      intro hM
      change faceFrame K E P.ambient ::
          ((replayFrames K E T (P.retained_le.trans hM)).cast
            (framePair_retained K E P hM).symm rfl).frames =
        faceFrame K E P.ambient :: T.frames.map (faceFrame K E)
      rw [Sequence.frames_cast, ih (P.retained_le.trans hM)]

/-- The terminal label and edge are derived from the actual source sequence. -/
theorem terminal_data (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (d : V) (hE : E.Nonempty) (S : Sequence (faceLink K E) (vertexComplex d)) :
    d ∉ E ∧ E ∪ ({d} : Finset V) ∈ K := by
  have hd : ({d} : Finset V) ∈ faceLink K E := S.monotone rfl
  exact ⟨fun hde => hd.2.1 d hde (by simp), hd.2.2⟩

/-- The only faces in the terminal frame containing E are E and E∪{d}. -/
private def finalFacePair (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (d : V) (hE : E.Nonempty) (hd : d ∉ E)
    (hEd : E ∪ ({d} : Finset V) ∈ K) : CollapsePair V where
  ambient := faceFrame K E (vertexComplex d)
  lower := E
  apex := d
  lower_nonempty := hE
  apex_notMem := hd
  upper_mem := by
    have heq : insert d E = E ∪ ({d} : Finset V) := by simp
    rw [heq]
    refine ⟨hEd, Or.inr ?_⟩
    rw [diff_union_disjoint (show DisjointFrom E ({d} : Finset V) from by
      intro x hxE hxd
      exact hd (Finset.mem_singleton.mp hxd ▸ hxE))]
    exact Or.inr rfl
  free := by
    intro s hs hstrict
    have hEs := hstrict.subset
    have hm : AugmentedFace (vertexComplex d) (s \ E) :=
      hs.2.resolve_left (fun hn => hn hEs)
    rcases hm with he | he
    · have hsE : s = E := by
        calc
          s = E ∪ (s \ E) := (union_diff_of_subset hEs).symm
          _ = E := by rw [he]; simp
      exact (hstrict.ne hsE.symm).elim
    · change s \ E = {d} at he
      calc
        s = E ∪ (s \ E) := (union_diff_of_subset hEs).symm
        _ = insert d E := by rw [he]; simp

private theorem finalFacePair_retained (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (d : V) (hE : E.Nonempty) (hd : d ∉ E)
    (hEd : E ∪ ({d} : Finset V) ∈ K) :
    (finalFacePair K E d hE hd hEd).retained = faceAntistar K E := by
  apply SetLike.coe_injective
  ext s
  change ((s ∈ K ∧ (¬ E ⊆ s ∨ AugmentedFace (vertexComplex d) (s \ E))) ∧
    ¬ E ⊆ s) ↔ (s ∈ K ∧ ¬ E ⊆ s)
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, Or.inl h.2⟩, h.2⟩

private def finalFaceStep (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (d : V) (hE : E.Nonempty) (hd : d ∉ E)
    (hEd : E ∪ ({d} : Finset V) ∈ K) :
    Sequence (faceFrame K E (vertexComplex d)) (faceAntistar K E) :=
  (Sequence.step (finalFacePair K E d hE hd hEd)
    (Sequence.refl _)).cast rfl (finalFacePair_retained K E d hE hd hEd)

/-- The general nonempty-face constructor: replay every source pair in its
literal E-frame, then append the terminal pair. Singleton and larger faces use
the same existing relative Sequence/coordinate realization owner. -/
def faceLinkCollapse (K : PreAbstractSimplicialComplex V) (E : Finset V) (d : V)
    (hE : E.Nonempty) (hEK : E ∈ K)
    (S : Sequence (faceLink K E) (vertexComplex d)) :
    Sequence K (faceAntistar K E) :=
  let hd := terminal_data K E d hE S
  ((replayFrames K E S le_rfl).append
    (finalFaceStep K E d hE hd.1 hd.2)).cast (faceFrame_link_eq K E hE) rfl

theorem faceLinkCollapse_pair_count (K : PreAbstractSimplicialComplex V)
    (E : Finset V) (d : V) (hE : E.Nonempty) (hEK : E ∈ K)
    (S : Sequence (faceLink K E) (vertexComplex d)) :
    (faceLinkCollapse K E d hE hEK S).pairs.length = S.pairs.length + 1 := by
  have hlen := (replayFrames_pairs K E S le_rfl d).length_eq
  simp only [faceLinkCollapse, Sequence.pairs_cast, Sequence.pairs_append,
    List.length_append, finalFaceStep, Sequence.pairs, List.length_cons,
    List.length_nil, hlen]

/-- Every output prefix pair matches the corresponding source pair; the exact
terminal pair is appended last. The relation is output-first/source-second. -/
theorem faceLinkCollapse_ordered_pairs
    (K : PreAbstractSimplicialComplex V) (E : Finset V) (d : V)
    (hE : E.Nonempty) (hEK : E ∈ K)
    (S : Sequence (faceLink K E) (vertexComplex d)) :
    ∃ qs q,
      (faceLinkCollapse K E d hE hEK S).pairs = qs ++ [q] ∧
      List.Forall₂ (PairUnionSpec E d) qs S.pairs ∧
      q.lower = E ∧ q.apex = d ∧ q.upper = E ∪ ({d} : Finset V) := by
  let hd := terminal_data K E d hE S
  refine ⟨(replayFrames K E S le_rfl).pairs,
    finalFacePair K E d hE hd.1 hd.2, ?_,
    replayFrames_pairs K E S le_rfl d, rfl, rfl, ?_⟩
  · simp only [faceLinkCollapse, finalFaceStep, Sequence.pairs_cast,
      Sequence.pairs_append, Sequence.pairs]
  · change insert d E = E ∪ ({d} : Finset V)
    simp

/-- Exact source-indexed n+1 frame specification; the additional output
endpoint is the full antistar, as fixed by the final Sequence type. -/
theorem faceLinkCollapse_frames
    (K : PreAbstractSimplicialComplex V) (E : Finset V) (d : V)
    (hE : E.Nonempty) (hEK : E ∈ K)
    (S : Sequence (faceLink K E) (vertexComplex d)) :
    ∀ i < S.pairs.length + 1,
      (faceLinkCollapse K E d hE hEK S).frames.getD i K =
        faceFrame K E (S.frames.getD i (faceLink K E)) := by
  intro i hi
  let hd := terminal_data K E d hE S
  let T := replayFrames K E S le_rfl
  let U := finalFaceStep K E d hE hd.1 hd.2
  have hlen : T.pairs.length = S.pairs.length :=
    (replayFrames_pairs K E S le_rfl d).length_eq
  have hiT : i < T.pairs.length + 1 := by rw [hlen]; exact hi
  have hp := Sequence.frames_append_getD_lt T U hiT
  rw [replayFrames_frames] at hp
  have hmap := Sequence.list_getD_map (faceFrame K E) S.frames i (faceLink K E)
  rw [faceFrame_link_eq K E hE] at hp hmap
  simpa only [faceLinkCollapse, Sequence.frames_cast, T, U] using hp.trans hmap

/-- The exact link/coface specification consumed by the sequence result. -/
structure FaceLinkLiftResult (K : PreAbstractSimplicialComplex V) (E : Finset V)
    (d : V) (S : Sequence (faceLink K E) (vertexComplex d)) where
  sequence : Sequence K (faceAntistar K E)
  d_not_mem : d ∉ E
  terminal_face : E ∪ ({d} : Finset V) ∈ K
  pair_count : sequence.pairs.length = S.pairs.length + 1
  ordered_pairs : ∃ qs q,
    sequence.pairs = qs ++ [q] ∧
    List.Forall₂ (PairUnionSpec E d) qs S.pairs ∧
    q.lower = E ∧ q.apex = d ∧ q.upper = E ∪ ({d} : Finset V)
  frame_spec : ∀ i < S.pairs.length + 1,
    sequence.frames.getD i K = faceFrame K E (S.frames.getD i (faceLink K E))
  link_spec : ∀ {M : PreAbstractSimplicialComplex V}, M ∈ S.frames →
    faceLink (faceFrame K E M) E = M
  fixed_antistar : ∀ (t : I) (x : Space K),
    x.val ∈ realization (faceAntistar K E) →
      sequence.collapseHomotopy (t, x) = x

/-- Package all exact specifications with the actual sequence. -/
def faceLinkLift
    (K : PreAbstractSimplicialComplex V) (E : Finset V) (d : V)
    (hE : E.Nonempty) (hEK : E ∈ K)
    (S : Sequence (faceLink K E) (vertexComplex d)) :
    FaceLinkLiftResult K E d S := by
  let T := faceLinkCollapse K E d hE hEK S
  have hd := terminal_data K E d hE S
  refine ⟨T, hd.1, hd.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact faceLinkCollapse_pair_count K E d hE hEK S
  · exact faceLinkCollapse_ordered_pairs K E d hE hEK S
  · exact faceLinkCollapse_frames K E d hE hEK S
  · intro M hM
    exact faceFrame_link K E (S.frames_le_source M hM)
  · intro t x hx
    exact Sequence.collapseHomotopy_fixed T t x hx

/-- Reusable immediate consequences: the whole antistar realization is fixed,
and every original deletion contained in it is fixed through the same actual
coordinate inclusion. -/
theorem fixed_faceAntistar
    (R : FaceLinkLiftResult K E d S) (t : I) (x : Space K)
    (hx : x.val ∈ realization (faceAntistar K E)) :
    R.sequence.collapseHomotopy (t, x) = x := R.fixed_antistar t x hx

theorem deletion_le_faceAntistar {E : Finset V} {K : PreAbstractSimplicialComplex V}
    {e : V} (he : e ∈ E) : deletion K e ≤ faceAntistar K E := by
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro hEs
  exact hs.2 (hEs he)

theorem fixed_whole_deletion
    (R : FaceLinkLiftResult K E d S) (e : V) (he : e ∈ E) (t : I)
    (x : Space (deletion K e)) :
    R.sequence.collapseHomotopy
      (t, realizationInclusion (deletion_le K e) x) =
      realizationInclusion (deletion_le K e) x := by
  apply R.fixed_antistar
  exact realization_mono (deletion_le_faceAntistar he) x.property

/-- Original-label residual predicate for a graph face link. -/
def residualPredicate (G : SimpleGraph V) (E : Finset V) : V → Prop :=
  fun x => x ∉ E ∧ ∀ e ∈ E, ¬ G.Adj e x

theorem graph_faceLink_eq_restricted (G : SimpleGraph V) (E : Finset V)
    (hE : E.Nonempty) (hInd : G.IsIndepSet (E : Set V)) :
    faceLink (independenceComplex G).toPreAbstractSimplicialComplex E =
      restricted G (residualPredicate G E) := by
  apply SetLike.coe_injective
  ext s
  change (s.Nonempty ∧ DisjointFrom E s ∧
      (E ∪ s).Nonempty ∧ G.IsIndepSet ((E ∪ s : Finset V) : Set V)) ↔
    (s.Nonempty ∧ G.IsIndepSet (s : Set V) ∧
      ∀ x ∈ s, x ∉ E ∧ ∀ e ∈ E, ¬ G.Adj e x)
  constructor
  · rintro ⟨hs, hdis, _, hIs⟩
    refine ⟨hs, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hIs (Finset.mem_union_right E hx) (Finset.mem_union_right E hy) hxy
    · intro x hx
      refine ⟨fun hxE => hdis x hxE hx, ?_⟩
      intro e heE
      have hne : e ≠ x := by
        intro heq
        subst x
        exact hdis e heE hx
      exact hIs (Finset.mem_union_left s heE) (Finset.mem_union_right E hx) hne
  · rintro ⟨hs, hIs, hp⟩
    refine ⟨hs, ?_, hs.mono Finset.subset_union_right, ?_⟩
    · intro e heE hes
      exact (hp e hes).1 heE
    · intro x hx y hy hxy hadj
      rcases Finset.mem_union.mp hx with hxE | hxs <;>
        rcases Finset.mem_union.mp hy with hyE | hys
      · exact hInd hxE hyE hxy hadj
      · exact (hp y hys).2 x hxE hadj
      · exact (hp x hxs).2 y hyE hadj.symm
      · exact hIs hxs hys hxy hadj

/-- For an independent nonadjacent edge, the residual predicate is exactly the
literal original-label predicate requested by the graph consumer. -/
def edgeResidualPredicate (G : SimpleGraph V) (b c : V) : V → Prop :=
  fun x => x ≠ b ∧ x ≠ c ∧ ¬ G.Adj b x ∧ ¬ G.Adj c x

theorem edge_residualPredicate_eq (G : SimpleGraph V) {b c : V}
    (hbc : b ≠ c) :
    residualPredicate G ({b, c} : Finset V) = edgeResidualPredicate G b c := by
  funext x
  apply propext
  constructor
  · rintro ⟨hx, hp⟩
    have hxb : x ≠ b := fun h => hx (by simp [h])
    have hxc : x ≠ c := fun h => hx (by simp [h])
    exact ⟨hxb, hxc, hp b (by simp) , hp c (by simp)⟩
  · rintro ⟨hxb, hxc, hbp, hcp⟩
    refine ⟨?_, ?_⟩
    · simpa [hxb, hxc]
    · intro e he xeq
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hbp xeq
      · have hec : e = c := Finset.mem_singleton.mp he
        subst e
        exact hcp xeq

/-- The antistar of an edge is the UNION of the two whole original deletions.
This equality is on face collections, not merely on vertex sets. -/
theorem edge_antistar_union_deletions (K : PreAbstractSimplicialComplex V)
    (b c : V) :
    faceAntistar K ({b, c} : Finset V) = deletion K b ⊔ deletion K c := by
  apply SetLike.coe_injective
  ext s
  by_cases hbs : b ∈ s <;> by_cases hcs : c ∈ s <;>
    simp [faceAntistar, deletion, hbs, hcs]

/-- A graph consumer takes a Sequence already on the original-label restricted
complex.  The only transport is equality cast; mapHomeomorph is a realization
transport and is deliberately not used to invent a combinatorial sequence. -/
def graph_edge_faceLinkLift
    (G : SimpleGraph V) {b c d : V} (hbc : b ≠ c)
    (hInd : G.IsIndepSet ({b, c} : Set V))
    (S : Sequence
      (restricted G (edgeResidualPredicate G b c)) (vertexComplex d))
    (hface : ({b, c} : Finset V) ∈
      (independenceComplex G).toPreAbstractSimplicialComplex)
    (hres : faceLink (independenceComplex G).toPreAbstractSimplicialComplex
      ({b, c} : Finset V) = restricted G (edgeResidualPredicate G b c)) :
    FaceLinkLiftResult
      (independenceComplex G).toPreAbstractSimplicialComplex
      ({b, c} : Finset V) d (S.cast hres.symm rfl) := by
  exact faceLinkLift _ _ d (Finset.insert_nonempty _ _) hface
    (S.cast hres.symm rfl)

end D5.S3.Geometry.FiniteFaceLinkCollapse
