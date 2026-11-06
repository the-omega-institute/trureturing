/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Rename
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Rename
   mirror-E: none(waiver:original-label-two-sum-rename)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Injective original-label transport reuses mathlib complex maps and transports actual native pairs, sequences and fillings. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates

/-! UNCOMPILED. The raw map is the direct image of the EXISTING downward face
family, including its actual empty membership. Native transport uses mathlib's
PreAbstractSimplicialComplex.map and the existing CollapsePair/Sequence. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Direct image of raw faces, without adjoining empty to a VOID source. -/
def renameFamily (f : U → V) (K : Family U) : Family V where
  carrier := {s | ∃ t ∈ K, t.image f = s}
  lower' := by
    rintro s t h ⟨u,hu,rfl⟩
    obtain ⟨v,hvu,rfl⟩ := Finset.subset_image_iff.mp h
    exact ⟨v,K.lower hvu hu,rfl⟩

/-- Projection agrees exactly with the pinned mathlib image-complex API. -/
theorem project_rename (f : U → V) (K : Family U) :
    project (renameFamily f K) = (project K).map f := by
  ext s
  change (s.Nonempty ∧ ∃ t ∈ K, t.image f = s) ↔
    ∃ t, (t.Nonempty ∧ t ∈ K) ∧ t.image f = s
  constructor
  · rintro ⟨hn,t,ht,rfl⟩
    exact ⟨t,⟨Finset.image_nonempty.mp hn,ht⟩,rfl⟩
  · rintro ⟨t,⟨hn,ht⟩,rfl⟩
    exact ⟨Finset.image_nonempty.mpr hn,t,ht,rfl⟩

/-- Ordinary free pairs transport through an injective label map. Freeness is
proved on all cofaces of the mapped ambient, rather than postulated. -/
def renamePair (f : U ↪ V) (P : CollapsePair U) : CollapsePair V where
  ambient := P.ambient.map f
  lower := P.lower.image f
  apex := f P.apex
  lower_nonempty := Finset.image_nonempty.mpr P.lower_nonempty
  apex_notMem := by
    intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact P.apex_notMem (f.injective he ▸ hx)
  upper_mem := by
    exact ⟨P.upper,P.upper_mem,by simp [CollapsePair.upper]⟩
  free := by
    rintro s ⟨t,ht,rfl⟩ hsub
    have hlt : P.lower ⊂ t := Finset.ssubset_iff_subset_ne.mpr
      ⟨(Finset.image_subset_image_iff f.injective).mp hsub.1,fun h =>
        hsub.ne (congrArg (fun z : Finset U => z.image f) h)⟩
    rw [P.free t ht hlt]
    simp [CollapsePair.upper]

private theorem renamePair_retained (f : U ↪ V) (P : CollapsePair U) :
    (renamePair f P).retained = P.retained.map f := by
  ext s
  change ((∃ t, t ∈ P.ambient ∧ t.image f = s) ∧ ¬ P.lower.image f ⊆ s) ↔
    ∃ t, (t ∈ P.ambient ∧ ¬ P.lower ⊆ t) ∧ t.image f = s
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,hn⟩
    exact ⟨t,⟨ht,fun h => hn ((Finset.image_subset_image_iff f.injective).mpr h)⟩,rfl⟩
  · rintro ⟨t,⟨ht,hn⟩,rfl⟩
    exact ⟨⟨t,ht,rfl⟩,fun h => hn ((Finset.image_subset_image_iff f.injective).mp h)⟩

/-- Recursive transport of the ACTUAL native list. -/
def renameSequence (f : U ↪ V) {M N : PreAbstractSimplicialComplex U}
    (S : Sequence M N) : Sequence (M.map f) (N.map f) := by
  induction S with
  | refl M => exact Sequence.refl _
  | step P T ih =>
    exact Sequence.step (renamePair f P)
      (ih.cast (renamePair_retained f P).symm rfl)

/-- Exact ordered coverage of the transported ordinary pairs. -/
theorem renameSequence_pairs (f : U ↪ V) {M N : PreAbstractSimplicialComplex U}
    (S : Sequence M N) :
    (renameSequence f S).pairs.map (fun P => (P.lower,P.upper)) =
      S.pairs.map (fun P => (P.lower.image f,P.upper.image f)) := by
  induction S with
  | refl M => rfl
  | step P T ih =>
    simp only [renameSequence,Sequence.pairs,List.map_cons]
    erw [Sequence.pairs_cast]
    simpa only [renamePair,CollapsePair.upper,Finset.image_insert] using
      congrArg (List.cons (P.lower.image f,P.upper.image f)) ih

/-- Simplex, intersections and endpoint families are transported literally. -/
theorem rename_operations (f : U ↪ V) (W : Finset U) (A B : Family U)
    (C : Finset (Finset U)) :
    renameFamily f (delta W) = delta (W.image f) ∧
    renameFamily f (A ⊔ B) = renameFamily f A ⊔ renameFamily f B ∧
    renameFamily f (A ⊓ B) = renameFamily f A ⊓ renameFamily f B ∧
    renameFamily f (endpoint A C) =
      endpoint (renameFamily f A) (C.image (fun t => t.image f)) := by
  have hd : renameFamily f (delta W) = delta (W.image f) := by
    apply SetLike.ext
    intro s
    exact Finset.subset_image_iff.symm
  have hu : renameFamily f (A ⊔ B) = renameFamily f A ⊔ renameFamily f B := by
    apply SetLike.ext
    intro s
    change (∃ t, (t ∈ A ∨ t ∈ B) ∧ t.image f = s) ↔
      (∃ t ∈ A, t.image f = s) ∨ (∃ t ∈ B, t.image f = s)
    aesop
  have hi : renameFamily f (A ⊓ B) = renameFamily f A ⊓ renameFamily f B := by
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨t,⟨ha,hb⟩,rfl⟩
      exact ⟨⟨t,ha,rfl⟩,⟨t,hb,rfl⟩⟩
    · rintro ⟨⟨t,ha,he⟩,⟨u,hb,he'⟩⟩
      have heq := Finset.image_injective f.injective (he.trans he'.symm)
      exact ⟨t,⟨ha,heq.symm ▸ hb⟩,he⟩
  refine ⟨hd,hu,hi,?_⟩
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨t,(ht | ⟨q,hq,htq⟩),rfl⟩
    · exact Or.inl ⟨t,ht,rfl⟩
    · exact Or.inr ⟨q.image f,Finset.mem_image.mpr ⟨q,hq,rfl⟩,
        Finset.image_subset_image htq⟩
  · rintro (⟨t,ht,rfl⟩ | ⟨q,hq,hsq⟩)
    · exact ⟨t,Or.inl ht,rfl⟩
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨t,htu,rfl⟩ := Finset.subset_image_iff.mp hsq
      exact ⟨t,Or.inr ⟨u,hu,htu⟩,rfl⟩

private theorem critical_rename (f : U ↪ V) {B : Family U} {C : Finset (Finset U)}
    (h : CriticalData B C) :
    CriticalData (renameFamily f B) (C.image (fun t => t.image f)) := by
  constructor
  · intro s hs
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.image_nonempty.mpr (h.nonempty q hq)
  · intro s hs ⟨t,ht,he⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    exact h.absent q hq ((Finset.image_injective f.injective he) ▸ ht)
  · intro s hs t hts
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u,hu,rfl⟩ := Finset.subset_image_iff.mp hts.1
    refine ⟨u,h.boundary q hq u (Finset.ssubset_iff_subset_ne.mpr ⟨hu,?_⟩),rfl⟩
    intro he
    exact hts.ne (congrArg (fun s : Finset U => s.image f) he)
  · intro s hs t ht hst
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp ht
    rw [h.antichain q hq q' hq' ((Finset.image_subset_image_iff f.injective).mp hst)]

/-- A local filling can be installed on any fresh original labels. -/
def renameFilling (f : U ↪ V) {W : Finset U} {A : Family U} (g : Filling W A) :
    Filling (W.image f) (renameFamily f A) where
  empty_mem := ⟨∅,g.empty_mem,by simp⟩
  collar := renameFamily f g.collar
  critical := g.critical.image (fun t => t.image f)
  contains := by rintro s ⟨t,ht,rfl⟩; exact ⟨t,g.contains ht,rfl⟩
  supported := by
    rintro s ⟨t,ht,rfl⟩
    exact Finset.image_subset_image (g.supported t ht)
  critical_supported := by
    intro s hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.image_subset_image (g.critical_supported t ht)
  cells := critical_rename f g.cells
  main := (renameSequence f g.main).cast
    (by rw [← project_rename,(rename_operations f W A A g.critical).1])
    (by rw [← project_rename,(rename_operations f W g.collar A g.critical).2.2.2])
  separate := (renameSequence f g.separate).cast
    (project_rename f g.collar).symm (project_rename f A).symm

/-- Absolute certificates transport with every original ground/ghost label. -/
def renameCertificate (f : U ↪ V) {W : Finset U} {K : Family U}
    (c : Certificate W K) : Certificate (W.image f) (renameFamily f K) where
  supported := by
    rintro s ⟨t,ht,rfl⟩
    exact Finset.image_subset_image (c.supported t ht)
  core := renameFamily f c.core
  critical := c.critical.image (fun t => t.image f)
  vertex := f c.vertex
  vertex_mem := ⟨{c.vertex},c.vertex_mem,by simp⟩
  core_supported := by
    rintro s ⟨t,ht,rfl⟩
    exact Finset.image_subset_image (c.core_supported t ht)
  critical_supported := by
    intro s hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.image_subset_image (c.critical_supported t ht)
  cells := critical_rename f c.cells
  main := (renameSequence f c.main).cast (project_rename f K).symm
    (by rw [← project_rename,(rename_operations f W c.core K c.critical).2.2.2])
  separate := (renameSequence f c.separate).cast (project_rename f c.core).symm
    (by rw [← project_rename,(rename_operations f {c.vertex} K K c.critical).1,
      Finset.image_singleton])

end D5.S3.Geometry.OriginalLabelTwoSum
