/- GID: D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/WheelSupplier
   mirror-E: none(waiver:original-label-two-sum-wheel-supplier)
   anchors: [mathlib/module/Mathlib.Data.Finset.Image]
   utility: none
   digest: Fresh original wheel labels instantiate the native Gamma/two-filling compiler and preserve critical count with size increment two. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Compiler
import D5.S3.Geometry.OriginalLabelTwoSum.Rename
import D5.S3.Geometry.OriginalLabelTwoSum.Wheel
import D5.S3.Geometry.OriginalLabelTwoSum.CellLabels

/-! UNCOMPILED. This supplies a full native certificate for the literal parent
formula, for ANY retained interface, including the current core vertex. The
general graph/path binding is NOT supplied by this algebraic theorem. f(0)=e is
only an ambient label: 0 is outside the right ground and e is outside the parent
ground. It is never a retained fake tree coordinate. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem image_supported (f : Wheel.Label ↪ V) :
    Supported (Wheel.Y.image f) (renameFamily f Wheel.E) := by
  rintro s ⟨t,ht,rfl⟩
  exact Finset.image_subset_image (Wheel.certificate.core_supported t ht)

private theorem zero_outside (f : Wheel.Label ↪ V) : f 0 ∉ Wheel.Y.image f := by
  intro h
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
  have hz : i = 0 := f.injective he
  subst i
  exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) hi

private def retargetFilling {W : Finset V} {A B : Family V}
    (g : Filling W A) (h : A = B) : Filling W B where
  empty_mem := h ▸ g.empty_mem
  collar := g.collar
  critical := g.critical
  contains := by rw [← h]; exact g.contains
  supported := g.supported
  critical_supported := g.critical_supported
  cells := g.cells
  main := g.main
  separate := g.separate.cast rfl (congrArg project h)

private theorem image_interfaces (f : Wheel.Label ↪ V) :
    Wheel.Z.image f = Wheel.Y.image f \ Wheel.R.image f ∧
    renameFamily f Wheel.A0 = renameFamily f Wheel.E ⊓ delta (Wheel.Z.image f) ∧
    renameFamily f Wheel.A1 = renameFamily f Wheel.E ⊔ delta (Wheel.Z.image f) := by
  refine ⟨?_,?_,?_⟩
  · rw [Wheel.interface_equations.1,Finset.image_sdiff _ _ f.injective]
  · rw [Wheel.interface_equations.2.1,
      (rename_operations f Wheel.Z Wheel.E (delta Wheel.Z) ∅).2.2.1,
      (rename_operations f Wheel.Z Wheel.E Wheel.E ∅).1]
  · rw [Wheel.interface_equations.2.2,
      (rename_operations f Wheel.Z Wheel.E (delta Wheel.Z) ∅).2.1,
      (rename_operations f Wheel.Z Wheel.E Wheel.E ∅).1]

/-- Witness the right Gamma permission by the original four pairs, install both
filling records and the separate 13/123 collar on fresh labels, then RUN the
parent compiler. Its Prop-valued permission makes a classical Gamma choice; the
exact expansion below records that choice, without identifying it with its witness.
There is no restriction excluding e=current core vertex. -/
def oneStep {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    Certificate (X ∪ Wheel.Y.image f)
      (parentOf X (Wheel.Y.image f) (Wheel.Z.image f) e (renameFamily f Wheel.E) K) := by
  let g0 : Filling (Wheel.Z.image f)
      (renameFamily f Wheel.E ⊓ delta (Wheel.Z.image f)) :=
    retargetFilling (renameFilling f Wheel.fill0) (image_interfaces f).2.1
  let g1 : Filling (Wheel.Y.image f)
      (renameFamily f Wheel.E ⊔ delta (Wheel.Z.image f)) :=
    retargetFilling (renameFilling f Wheel.fill1) (image_interfaces f).2.2
  let G : Sequence (project (delta (Wheel.Y.image f)))
      (project (renameFamily f Wheel.E)) :=
    (renameSequence f Wheel.gamma).cast
      (by rw [← project_rename,(rename_operations f Wheel.Y Wheel.E Wheel.E ∅).1])
      (project_rename f Wheel.E).symm
  have heY : e ∉ Wheel.Y.image f := hf0 ▸ zero_outside f
  have hr : Wheel.R.image f ⊆ Wheel.Y.image f :=
    Finset.image_subset_image (by decide : Wheel.R ⊆ Wheel.Y)
  have hrne : (Wheel.R.image f).Nonempty :=
    Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)
  exact compileParent c g0 g1 heX heY hXY hr hrne (image_interfaces f).1
    (image_supported f) (Or.inl ⟨G⟩)

/-- The computed critical family has the exact original two-branch transform. -/
theorem oneStep_critical {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    (oneStep c f hf0 heX hXY).critical =
      c.critical.image (wheelCell e (f 1) (f 3) (f 4)) := by
  unfold oneStep
  dsimp only
  erw [compileParent_critical]
  change parentCritical e c.critical
    (Wheel.fill0.critical.image (fun t => t.image f))
    (Wheel.fill1.critical.image (fun t => t.image f)) = _
  simp only [Wheel.fill0,Wheel.fill1,Finset.image_singleton,
    Finset.image_insert,Finset.image_empty]
  ext s
  rw [mem_parentCritical]
  constructor
  · rintro (⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩)
    · have ht' : t = {f 3,f 4} := Finset.mem_singleton.mp ht
      subst t
      exact Finset.mem_image.mpr ⟨q,hq,by simp [wheelCell,he]⟩
    · have ht' : t = {f 1,f 3,f 4} := Finset.mem_singleton.mp ht
      subst t
      exact Finset.mem_image.mpr ⟨q,hq,by simp [wheelCell,he]⟩
  · intro hs
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    by_cases he : e ∈ q
    · exact Or.inr ⟨q,hq,he,{f 1,f 3,f 4},by simp,by simp [wheelCell,he]⟩
    · exact Or.inl ⟨q,hq,he,{f 3,f 4},by simp,by simp [wheelCell,he]⟩

private theorem fresh {X : Finset V} {e : V} (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (hXY : Disjoint X (Wheel.Y.image f))
    {i : Wheel.Label} (hi : i ∈ Wheel.Y) : f i ∉ insert e X := by
  intro h
  rcases Finset.mem_insert.mp h with he | hx
  · have hi0 : i = 0 := f.injective (he.trans hf0.symm)
    subst i
    exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) hi
  · exact Finset.disjoint_left.mp hXY hx (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

/-- The native one-step supplier preserves the number of critical faces and
increases the size of EACH by exactly two, also when the interface is a critical
singleton or the current core vertex. -/
theorem oneStep_statistics {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    (oneStep c f hf0 heX hXY).critical.card = c.critical.card ∧
    ∀ q ∈ c.critical, (wheelCell e (f 1) (f 3) (f 4) q).card = q.card + 2 := by
  have h1 : f 1 ∉ insert e X := fresh f hf0 hXY (by decide)
  have h3 : f 3 ∉ insert e X := fresh f hf0 hXY (by decide)
  have h4 : f 4 ∉ insert e X := fresh f hf0 hXY (by decide)
  have h13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Wheel.Label) ≠ 3) (f.injective h)
  have h14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Wheel.Label) ≠ 4) (f.injective h)
  have h34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Wheel.Label) ≠ 4) (f.injective h)
  constructor
  · rw [oneStep_critical]
    exact wheelCell_count (insert e X) c.critical e (f 1) (f 3) (f 4)
      c.critical_supported (Finset.mem_insert_self _ _) h1 h3 h4 h13 h14
  · intro q hq
    exact wheelCell_card (insert e X) q e (f 1) (f 3) (f 4)
      (c.critical_supported q hq) h1 h3 h4 h13 h14 h34


/-- Raw-face main substitution. Only previous pair data and critical labels
are inputs; filling lists are the actual renamed original wheel operations. -/
def oneStepMainFrom (e : V) (f : Wheel.Label ↪ V)
    (critical : Finset (Finset V)) (previous : List (Finset V × Finset V)) :
    List (Finset V × Finset V) := by
  let g0 := retargetFilling (renameFilling f Wheel.fill0) (image_interfaces f).2.1
  let g1 := retargetFilling (renameFilling f Wheel.fill1) (image_interfaces f).2.2
  exact previous.flatMap (fun P =>
      replayFacePairs (Wheel.Y.image f) (Wheel.Z.image f) e
        (renameFamily f Wheel.E) P
        (rightGammaPairs (Wheel.Y.image f) (renameFamily f Wheel.E))) ++
    (fibres critical).flatMap (fun q =>
      (selectFilling e g0 g1 q).main.pairs.map
        (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper)))

/-- Raw-face separate substitution: standalone collars, previous core faces,
then the full-ground terminal formula. No previous certificate is consulted. -/
def oneStepSeparateFrom (X : Finset V) (e : V) (f : Wheel.Label ↪ V)
    (critical : Finset (Finset V)) (vertex : V)
    (previous : List (Finset V × Finset V)) : List (Finset V × Finset V) := by
  let g0 := retargetFilling (renameFilling f Wheel.fill0) (image_interfaces f).2.1
  let g1 := retargetFilling (renameFilling f Wheel.fill1) (image_interfaces f).2.2
  exact (fibres critical).flatMap (fun q =>
      (selectFilling e g0 g1 q).separate.pairs.map
        (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) ++
    previous.flatMap (fun P =>
      replayFacePairs (Wheel.Y.image f) (Wheel.Z.image f) e
        (renameFamily f Wheel.E) P
        (rightGammaPairs (Wheel.Y.image f) (renameFamily f Wheel.E))) ++
    finishFacePairs X (Wheel.Y.image f) (Wheel.Z.image f) (Wheel.R.image f)
      e vertex (renameFamily f Wheel.E)
      (Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty))
      (rightGammaPairs (Wheel.Y.image f) (renameFamily f Wheel.E))

/-- The compiler instance of the main raw-face substitution. -/
def oneStepMainSchedule {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    List (Finset V × Finset V) :=
  oneStepMainFrom e f c.critical (orderedPairs c.main)

/-- The compiler instance of the separate raw-face substitution. -/
def oneStepSeparateSchedule {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    List (Finset V × Finset V) :=
  oneStepSeparateFrom X e f c.critical c.vertex (orderedPairs c.separate)

private theorem flatMap_faces (ps : List (CollapsePair V))
    (F : (Finset V × Finset V) → List (Finset V × Finset V)) :
    ps.flatMap (fun P => F (orderedPair P)) = (ps.map orderedPair).flatMap F := by
  induction ps with
  | nil => rfl
  | cons P ps ih =>
    change F (orderedPair P) ++ _ = F (orderedPair P) ++ _
    exact congrArg (List.append (F (orderedPair P))) ih

/-- Both one-step formulas use the Gamma actually chosen by the existing
Prop-valued compiler permission, rather than identifying choice with its witness. -/
theorem oneStep_main_orderedPairs {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    orderedPairs (oneStep c f hf0 heX hXY).main =
      oneStepMainSchedule c f hf0 heX hXY := by
  classical
  let g0 := retargetFilling (renameFilling f Wheel.fill0) (image_interfaces f).2.1
  let g1 := retargetFilling (renameFilling f Wheel.fill1) (image_interfaces f).2.2
  let G := (renameSequence f Wheel.gamma).cast
    (by rw [← project_rename,(rename_operations f Wheel.Y Wheel.E Wheel.E ∅).1])
    (project_rename f Wheel.E).symm
  have heY : e ∉ Wheel.Y.image f := hf0 ▸ zero_outside f
  have hr : Wheel.R.image f ⊆ Wheel.Y.image f :=
    Finset.image_subset_image (by decide : Wheel.R ⊆ Wheel.Y)
  have hrne : (Wheel.R.image f).Nonempty :=
    Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)
  have h := compileParent_consumed_expansion c g0 g1 heX heY hXY hr hrne
    (image_interfaces f).1 (image_supported f) (Or.inl ⟨G⟩)
  simpa only [oneStep, oneStepMainSchedule, oneStepMainFrom,
    g0, g1, orderedPairs, List.flatMap_map] using h.1

 theorem oneStep_separate_orderedPairs {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    orderedPairs (oneStep c f hf0 heX hXY).separate =
      oneStepSeparateSchedule c f hf0 heX hXY := by
  classical
  let g0 := retargetFilling (renameFilling f Wheel.fill0) (image_interfaces f).2.1
  let g1 := retargetFilling (renameFilling f Wheel.fill1) (image_interfaces f).2.2
  let G := (renameSequence f Wheel.gamma).cast
    (by rw [← project_rename,(rename_operations f Wheel.Y Wheel.E Wheel.E ∅).1])
    (project_rename f Wheel.E).symm
  have heY : e ∉ Wheel.Y.image f := hf0 ▸ zero_outside f
  have hr : Wheel.R.image f ⊆ Wheel.Y.image f :=
    Finset.image_subset_image (by decide : Wheel.R ⊆ Wheel.Y)
  have hrne : (Wheel.R.image f).Nonempty :=
    Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)
  have h := compileParent_consumed_expansion c g0 g1 heX heY hXY hr hrne
    (image_interfaces f).1 (image_supported f) (Or.inl ⟨G⟩)
  simpa only [oneStep, oneStepSeparateSchedule, oneStepSeparateFrom,
    g0, g1, orderedPairs, List.flatMap_map, finishPairSchedule_faces] using h.2

/-- The exact terminal choice used by the independent row vertex recursion. -/
theorem oneStep_vertex {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X (Wheel.Y.image f)) :
    (oneStep c f hf0 heX hXY).vertex =
      finishVertex X (Wheel.R.image f) e c.vertex
        (Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)) := by
  unfold oneStep
  dsimp only
  erw [compileParent_vertex]

end D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier
