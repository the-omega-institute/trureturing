/- GID: D5/S3/Topology/StableCategory/MovingAnchorMixedCone
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/MovingAnchorMixedCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A deformation on the second trace gives a cone cover with exact old intersections. -/

import D5.S3.Topology.StableCategory.InheritedDepthConeAttachment

/-!
# Moving the anchor on a cone attachment

Omega original. The second retained piece can move its exclusive base faces
inside the actual cone base before admitting one terminal anchor.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

open BarycentricGraphDistance (Face)
open RelativeCoverNecessity (FixedOrderMaps RelativeOrderFence)
open ConnectedCategoryGraft (Categorical)
open PartialOrder (NonemptyFiniteChains)
open Relation (EqvGen)

open private categorical_of_meeting map_fence from D5.S3.Topology.SubdivisionCategoricalCover
open private liftedRegion liftedRegion_lower from
  D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision
open private allowedChains trim_flags from D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

variable {P V : Type*} [PartialOrder P] [DecidableEq V]

namespace Attachment

open private pointPiece_inter_old pointPiece_fence trace_iff_retained trace_singleton_of_mem
  from D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

variable (d : Attachment P V)

private theorem exterior_point_cover
    (E : Bool → Set P) (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i) :
    ∀ x, ∃ i, x ∈ d.pointPiece (E i) (d.exteriorPiece (E false) i) := by
  classical
  intro x
  by_cases hx : x ∈ d.retained
  · obtain ⟨i, hi⟩ := oldCover _ (d.retractLand ⟨x, hx⟩)
    exact ⟨i, Or.inl ⟨hx, hi⟩⟩
  · let s := d.faceIso.symm ⟨x, (d.cover x).resolve_left hx⟩
    have he : (d.faceIso s).val = x :=
      congrArg Subtype.val (d.faceIso.apply_symm_apply ⟨x, (d.cover x).resolve_left hx⟩)
    have hu : d.apex ∈ s.val := by
      by_contra h
      exact hx (he ▸ (d.base_iff s).mpr h)
    by_cases ht : ∃ v ∈ s.val, d.trace (E false) ({v} : Finset V)
    · exact ⟨false, Or.inr ⟨s, ⟨hu, ⟨fun _ => rfl, fun _ => ht⟩⟩, he⟩⟩
    · refine ⟨true, Or.inr ⟨s, ⟨hu, ?_⟩, he⟩⟩
      simp [ht]

private theorem first_pointPiece_fence
    (E : Bool → Set P) (hE : E false ⊆ d.old) (lower₀ : IsLowerSet (E false))
    (full : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, d.trace (E false) ({v} : Finset V)) → d.trace (E false) s.val) :
    RelativeOrderFence (d.pointPiece (E false) (d.exteriorPiece (E false) false))
      (E false) := by
  classical
  let cut : Finset V →o Finset V :=
    ⟨fun s => s.filter (fun v => d.trace (E false) ({v} : Finset V)),
      fun _ _ h => Finset.filter_subset_filter _ h⟩
  let middle : Finset V →o Finset V :=
    ⟨fun s => insert d.apex (cut s), fun _ _ h =>
      Finset.insert_subset_insert _ (cut.monotone h)⟩
  have cutTrace (s : Face d.cone) (hs : s ∈ d.exteriorPiece (E false) false) :
      d.trace (E false) (cut s.val) := by
    obtain ⟨v, hv, hTrace⟩ := hs.2.mpr rfl
    have hsub : cut s.val ⊆ s.val := Finset.filter_subset _ _
    have hn : (cut s.val).Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hTrace⟩⟩
    let t : Face d.cone := ⟨cut s.val, (d.cone.isRelLowerSet_faces s.property).2 hsub hn⟩
    apply full t
    · intro hu
      have h := (Finset.mem_filter.mp hu).2
      obtain ⟨_, hNot, _⟩ := h
      exact hNot (Finset.mem_singleton_self d.apex)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
  refine pointPiece_fence d hE (D := d.exteriorPiece (E false) false)
    (fun _ hs => hs.1) middle cut
    (fun s hs => d.insert_apex ⟨cut s.val, (cutTrace s hs).choose⟩) cutTrace
    (fun _ _ _ hx => Finset.mem_insert_of_mem hx) (Or.inl ?_) ?_
  · intro s hs x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hs.1
    · exact (Finset.mem_filter.mp hx).1
  · intro b hb s _ hbs v hv
    exact Finset.mem_filter.mpr ⟨hbs hv, trace_singleton_of_mem d lower₀ hb hv⟩

/-- A nonempty cone base face supported entirely outside the first trace. -/
def IsExclusiveBase (E₀ : Set P) (s : Face d.cone) : Prop :=
  d.apex ∉ s.val ∧ ∀ v ∈ s.val, ¬ d.trace E₀ ({v} : Finset V)

private theorem exclusive_mem_retainedPiece (E : Bool → Set P)
    (lower₀ : IsLowerSet (E false)) (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i)
    (s : Face d.cone) (hs : d.IsExclusiveBase (E false) s) :
    (d.faceIso s).val ∈ d.retainedPiece (E true) := by
  let x : d.retained := ⟨(d.faceIso s).val, (d.base_iff s).mpr hs.1⟩
  obtain ⟨i, hi⟩ := oldCover _ (d.retractLand x)
  cases i with
  | false =>
    have ht := (trace_iff_retained d (E false) s hs.1).mpr ⟨x.property, hi⟩
    obtain ⟨v, hv⟩ := (d.cone.isRelLowerSet_faces s.property).1
    exact (hs.2 v hv (trace_singleton_of_mem d lower₀ ht hv)).elim
  | true => exact ⟨x.property, hi⟩

/-- A retained order map whose image of each exclusive base face stays in
the actual cone base. The codomain enforces preservation of the retained piece. -/
abbrev MovingAnchorRow (E : Bool → Set P) :=
  {f : d.retainedPiece (E true) →o d.retainedPiece (E true) //
    ∀ s : Face d.cone, d.IsExclusiveBase (E false) s →
      ∀ hs : (d.faceIso s).val ∈ d.retainedPiece (E true),
        (f ⟨(d.faceIso s).val, hs⟩).val ∈ d.coneRegion}

/-- The identity is a valid row for any pair of traces. -/
def movingAnchorIdentity (E : Bool → Set P) : d.MovingAnchorRow E :=
  ⟨OrderHom.id, fun s _ _ => (d.faceIso s).property⟩

/-- Read a moved base face via the inverse of the attachment's chart. -/
def movingBaseImage {E : Bool → Set P} (f : d.MovingAnchorRow E)
    (s : Face d.cone) (hs : d.IsExclusiveBase (E false) s)
    (hA : (d.faceIso s).val ∈ d.retainedPiece (E true)) : Face d.cone :=
  d.faceIso.symm ⟨(f.val ⟨(d.faceIso s).val, hA⟩).val, f.property s hs hA⟩

private theorem movingBaseImage_chart {E : Bool → Set P} (f : d.MovingAnchorRow E)
    (s : Face d.cone) (hs : d.IsExclusiveBase (E false) s)
    (hA : (d.faceIso s).val ∈ d.retainedPiece (E true)) :
    (d.faceIso (d.movingBaseImage f s hs hA)).val = (f.val ⟨(d.faceIso s).val, hA⟩).val :=
  congrArg Subtype.val (d.faceIso.apply_symm_apply _)

/-- A fence on the second retained piece and an anchor spanning the terminal
images of its exclusive base faces. -/
structure MovingAnchorCertificate (E : Bool → Set P) where
  last : d.MovingAnchorRow E
  fence : EqvGen (· ≤ ·) (d.movingAnchorIdentity E) last
  anchor : V
  anchorTrace : d.trace (E true) ({anchor} : Finset V)
  span : ∀ (s : Face d.cone) (hs : d.IsExclusiveBase (E false) s)
    (hA : (d.faceIso s).val ∈ d.retainedPiece (E true)),
      d.trace (E true) (insert anchor (d.movingBaseImage last s hs hA).val)

/-- Extend the retained fence over the exterior faces of the second piece.
Insert the terminal anchor while keeping the apex, then remove the apex. -/
theorem moving_anchor_endpoint_fence
    (E : Bool → Set P) (lower₀ : IsLowerSet (E false))
    (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i) (c : d.MovingAnchorCertificate E) :
    let W := d.pointPiece (E true) (d.exteriorPiece (E false) true)
    ∃ f : W →o P, EqvGen (· ≤ ·) (OrderEmbedding.subtype W).toOrderHom f ∧
      ∀ x, f x ∈ d.retainedPiece (E true) := by
  classical
  dsimp only
  let A := d.retainedPiece (E true)
  let D := d.exteriorPiece (E false) true
  let W := d.pointPiece (E true) D
  let erased (s : D) := s.val.val.erase d.apex
  let base (s : D) (h : (erased s).Nonempty) : Face d.cone :=
    ⟨erased s, (d.cone.isRelLowerSet_faces s.val.property).2 (Finset.erase_subset _ _) h⟩
  have exclusive (s : D) (h : (erased s).Nonempty) : d.IsExclusiveBase (E false) (base s h) := by
    refine ⟨Finset.notMem_erase _ _, ?_⟩
    intro v hv ht
    have bad : true = false := s.property.2.mp ⟨v, (Finset.mem_erase.mp hv).2, ht⟩
    cases bad
  have inA (s : D) (h : (erased s).Nonempty) : (d.faceIso (base s h)).val ∈ A :=
    d.exclusive_mem_retainedPiece E lower₀ oldCover (base s h) (exclusive s h)
  let retainedBase (s : D) (h : (erased s).Nonempty) : A :=
    ⟨(d.faceIso (base s h)).val, inA s h⟩
  let moved (g : d.MovingAnchorRow E) (s : D) (hs : (erased s).Nonempty) : Face d.cone :=
    d.movingBaseImage g (base s hs) (exclusive s hs) (inA s hs)
  let image (g : d.MovingAnchorRow E) (s : D) : Finset V :=
    if hs : (erased s).Nonempty then (moved g s hs).val else ∅
  have image_of_nonempty (g : d.MovingAnchorRow E) (s : D) (hs : (erased s).Nonempty) :
      image g s = (moved g s hs).val := dite_eq_left hs
  have image_of_empty (g : d.MovingAnchorRow E) (s : D) (hs : ¬ (erased s).Nonempty) :
      image g s = ∅ := dite_eq_right hs
  have image_mono (g : d.MovingAnchorRow E) : Monotone (image g) := by
    intro s t hst
    have he : erased s ⊆ erased t := Finset.erase_subset_erase _ hst
    by_cases hs : (erased s).Nonempty
    · have ht : (erased t).Nonempty := Finset.Nonempty.mono he hs
      rw [image_of_nonempty g s hs, image_of_nonempty g t ht]
      have hbase : retainedBase s hs ≤ retainedBase t ht :=
        d.faceIso.monotone (show base s hs ≤ base t ht from he)
      exact (show moved g s hs ≤ moved g t ht from
        d.faceIso.symm.monotone (g.val.monotone hbase))
    · rw [image_of_empty g s hs]
      exact Finset.empty_subset _
  have image_compare (g h : d.MovingAnchorRow E) (hgh : g ≤ h) (s : D) :
      image g s ⊆ image h s := by
    by_cases hs : (erased s).Nonempty
    · rw [image_of_nonempty g s hs, image_of_nonempty h s hs]
      have hle : g.val ≤ h.val := hgh
      exact (show moved g s hs ≤ moved h s hs from
        d.faceIso.symm.monotone (OrderHom.le_def.mp hle (retainedBase s hs)))
    · simpa only [image_of_empty g s hs, image_of_empty h s hs] using
        (Finset.empty_subset (∅ : Finset V))
  have image_identity (s : D) : image (d.movingAnchorIdentity E) s = erased s := by
    by_cases hs : (erased s).Nonempty
    · rw [image_of_nonempty _ s hs]
      change (d.faceIso.symm (d.faceIso (base s hs))).val = erased s
      rw [d.faceIso.symm_apply_apply]
    · rw [image_of_empty _ s hs, Finset.not_nonempty_iff_eq_empty.mp hs]

  -- Lowerness of the cone puts any retained point below a coned face in
  -- the chart. Its apex-free support then lies below the erased base.
  have below_base (x : A) (s : D) (hx : x.val ≤ (d.faceIso s.val).val) :
      ∃ hs : (erased s).Nonempty, x.val ≤ (d.faceIso (base s hs)).val := by
    let xC : d.coneRegion := ⟨x.val, d.coneLower hx (d.faceIso s.val).property⟩
    let b := d.faceIso.symm xC
    have hb : (d.faceIso b).val = x.val :=
      congrArg Subtype.val (d.faceIso.apply_symm_apply xC)
    have hbA : d.apex ∉ b.val := (d.base_iff b).mp (hb.symm ▸ x.property.choose)
    have hbs : b ≤ s.val := d.faceIso.le_iff_le.mp (show
      (d.faceIso b).val ≤ (d.faceIso s.val).val by simpa only [hb] using hx)
    have he : b.val ⊆ erased s := by
      intro v hv
      exact Finset.mem_erase.mpr ⟨fun h => hbA (h ▸ hv), hbs hv⟩
    obtain ⟨v, hv⟩ := (d.cone.isRelLowerSet_faces b.property).1
    let hs : (erased s).Nonempty := ⟨v, he hv⟩
    refine ⟨hs, ?_⟩
    rw [← hb]
    exact d.faceIso.monotone (show b ≤ base s hs from he)

  have witness (x : W) (hx : x.val ∉ A) : ∃ s ∈ D, (d.faceIso s).val = x.val :=
    (show x.val ∈ A ∨ ∃ s ∈ D, (d.faceIso s).val = x.val from x.property).resolve_left hx
  let exterior (x : W) (hx : x.val ∉ A) : D :=
    ⟨(witness x hx).choose, (witness x hx).choose_spec.1⟩
  have exterior_eq (x : W) (hx : x.val ∉ A) :
      (d.faceIso (exterior x hx).val).val = x.val := (witness x hx).choose_spec.2
  let extend (g : d.MovingAnchorRow E) (F : D → Finset V) (hF : Monotone F)
      (faces : ∀ s, F s ∈ d.cone) (contains : ∀ s, image g s ⊆ F s) : W →o P :=
    { toFun := fun x => if hx : x.val ∈ A then (g.val ⟨x.val, hx⟩).val
        else (d.faceIso ⟨F (exterior x hx), faces (exterior x hx)⟩).val
      monotone' := by
        intro x y hxy
        have hxy' : x.val ≤ y.val := hxy
        by_cases hx : x.val ∈ A <;> by_cases hy : y.val ∈ A
        · simp only [dite_eq_left hx, dite_eq_left hy]
          exact g.val.monotone hxy
        · simp only [dite_eq_left hx, dite_eq_right hy]
          let s := exterior y hy
          obtain ⟨hs, hbelow⟩ := below_base ⟨x.val, hx⟩ s ((exterior_eq y hy).symm ▸ hxy')
          have hg : (g.val ⟨x.val, hx⟩).val ≤ (d.faceIso (moved g s hs)).val := by
            have himage : (d.faceIso (moved g s hs)).val = (g.val (retainedBase s hs)).val :=
              d.movingBaseImage_chart g (base s hs) (exclusive s hs) (inA s hs)
            rw [himage]
            exact g.val.monotone hbelow
          have hsub : moved g s hs ≤ (⟨F s, faces s⟩ : Face d.cone) := by
            change (moved g s hs).val ⊆ F s
            rw [← image_of_nonempty g s hs]
            exact contains s
          exact hg.trans (d.faceIso.monotone hsub)
        · exfalso
          have hxA : x.val ∈ d.retained := d.retainedLower hxy' hy.choose
          exact (d.base_iff (exterior x hx).val).mp ((exterior_eq x hx).symm ▸ hxA)
            (exterior x hx).property.1
        · simp only [dite_eq_right hx, dite_eq_right hy]
          have hst : exterior x hx ≤ exterior y hy := d.faceIso.le_iff_le.mp (show
            (d.faceIso (exterior x hx).val).val ≤ (d.faceIso (exterior y hy).val).val by
              simpa only [exterior_eq] using hxy')
          exact d.faceIso.monotone (show
            (⟨F (exterior x hx), faces (exterior x hx)⟩ : Face d.cone) ≤
              ⟨F (exterior y hy), faces (exterior y hy)⟩ from hF hst) }
  have extend_at (g : d.MovingAnchorRow E) (F : D → Finset V) (hF : Monotone F)
      (faces : ∀ s, F s ∈ d.cone) (contains : ∀ s, image g s ⊆ F s) (x : W) :
      extend g F hF faces contains x = (if hx : x.val ∈ A then (g.val ⟨x.val, hx⟩).val
        else (d.faceIso ⟨F (exterior x hx), faces (exterior x hx)⟩).val) := rfl
  have extend_le (g h : d.MovingAnchorRow E) (F G : D → Finset V)
      (hF : Monotone F) (hG : Monotone G) (fF : ∀ s, F s ∈ d.cone)
      (fG : ∀ s, G s ∈ d.cone) (iF : ∀ s, image g s ⊆ F s)
      (iG : ∀ s, image h s ⊆ G s) (hgh : g.val ≤ h.val) (hFG : ∀ s, F s ⊆ G s) :
      extend g F hF fF iF ≤ extend h G hG fG iG := by
    intro x
    by_cases hx : x.val ∈ A
    · have hle : (g.val ⟨x.val, hx⟩).val ≤ (h.val ⟨x.val, hx⟩).val :=
        OrderHom.le_def.mp hgh ⟨x.val, hx⟩
      simpa only [extend_at, dite_eq_left hx] using hle
    · simp only [extend_at, dite_eq_right hx]
      exact d.faceIso.monotone (show
        (⟨F (exterior x hx), fF (exterior x hx)⟩ : Face d.cone) ≤
          ⟨G (exterior x hx), fG (exterior x hx)⟩ from hFG (exterior x hx))

  let keep (g : d.MovingAnchorRow E) (s : D) := insert d.apex (image g s)
  have keep_face (g : d.MovingAnchorRow E) (s : D) : keep g s ∈ d.cone := by
    change insert d.apex (image g s) ∈ d.cone
    by_cases hs : (erased s).Nonempty
    · rw [image_of_nonempty g s hs]
      exact d.insert_apex (moved g s hs)
    · rw [image_of_empty g s hs, Finset.insert_empty]
      exact (d.cone.isRelLowerSet_faces s.val.property).2
        (Finset.singleton_subset_iff.mpr s.property.1) (Finset.singleton_nonempty _)
  have keep_mono (g : d.MovingAnchorRow E) : Monotone (keep g) :=
    fun _ _ h => Finset.insert_subset_insert _ (image_mono g h)
  have keep_contains (g : d.MovingAnchorRow E) (s : D) : image g s ⊆ keep g s :=
    Finset.subset_insert _ _
  let lift (g : d.MovingAnchorRow E) : W →o P :=
    extend g (keep g) (keep_mono g) (keep_face g) (keep_contains g)
  have lift_id : lift (d.movingAnchorIdentity E) = (OrderEmbedding.subtype W).toOrderHom := by
    apply OrderHom.ext
    funext x
    by_cases hx : x.val ∈ A
    · simp only [lift, extend_at, dite_eq_left hx] <;> rfl
    · simp only [lift, extend_at, dite_eq_right hx]
      have hface : (⟨keep (d.movingAnchorIdentity E) (exterior x hx),
          keep_face _ _⟩ : Face d.cone) = (exterior x hx).val := by
        apply Subtype.ext
        change insert d.apex (image (d.movingAnchorIdentity E) (exterior x hx)) = _
        rw [image_identity]
        exact Finset.insert_erase (exterior x hx).property.1
      rw [hface]
      exact exterior_eq x hx
  have path : EqvGen (· ≤ ·) (OrderEmbedding.subtype W).toOrderHom (lift c.last) := by
    rw [← lift_id]
    exact map_fence lift (fun g h hgh => .rel _ _
      (extend_le g h (keep g) (keep h) (keep_mono g) (keep_mono h) (keep_face g)
        (keep_face h) (keep_contains g) (keep_contains h) hgh
        (fun s => Finset.insert_subset_insert _ (image_compare g h hgh s)))) c.fence

  let anchored (s : D) := insert c.anchor (image c.last s)
  have anchored_trace (s : D) : d.trace (E true) (anchored s) := by
    change d.trace (E true) (insert c.anchor (image c.last s))
    by_cases hs : (erased s).Nonempty
    · rw [image_of_nonempty c.last s hs]
      exact c.span (base s hs) (exclusive s hs) (inA s hs)
    · rw [image_of_empty c.last s hs, Finset.insert_empty]
      exact c.anchorTrace
  have anchored_mono : Monotone anchored :=
    fun _ _ h => Finset.insert_subset_insert _ (image_mono c.last h)
  let mid (s : D) := insert d.apex (anchored s)
  have mid_face (s : D) : mid s ∈ d.cone :=
    d.insert_apex ⟨anchored s, (anchored_trace s).choose⟩
  have mid_mono : Monotone mid :=
    fun _ _ h => Finset.insert_subset_insert _ (anchored_mono h)
  have anchored_contains (s : D) : image c.last s ⊆ anchored s := Finset.subset_insert _ _
  have mid_contains (s : D) : image c.last s ⊆ mid s :=
    (anchored_contains s).trans (Finset.subset_insert _ _)
  let middle := extend c.last mid mid_mono mid_face mid_contains
  have last_face (s : D) : anchored s ∈ d.cone := (anchored_trace s).choose
  let last := extend c.last anchored anchored_mono last_face anchored_contains
  have add_anchor : lift c.last ≤ middle :=
    extend_le c.last c.last (keep c.last) mid (keep_mono c.last) mid_mono
      (keep_face c.last) mid_face (keep_contains c.last) mid_contains le_rfl
      (fun s => Finset.insert_subset_insert _ (anchored_contains s))
  have drop_apex : last ≤ middle :=
    extend_le c.last c.last anchored mid anchored_mono mid_mono
      last_face mid_face anchored_contains mid_contains le_rfl (fun _ => Finset.subset_insert _ _)
  refine ⟨last, .trans _ _ _ path
    (.trans _ _ _ (.rel _ _ add_anchor) (.symm _ _ (.rel _ _ drop_apex))), ?_⟩
  intro x
  by_cases hx : x.val ∈ A
  · simpa only [last, extend_at, dite_eq_left hx] using (c.last.val ⟨x.val, hx⟩).property
  · simp only [last, extend_at, dite_eq_right hx]
    let s := exterior x hx
    let t : Face d.cone := ⟨anchored s, last_face s⟩
    exact (trace_iff_retained d (E true) t (anchored_trace s).choose_spec.choose).mp
      (anchored_trace s)

private theorem categorical_of_endpoint {R T : Set P} {f : R →o P}
    (path : EqvGen (· ≤ ·) (OrderEmbedding.subtype R).toOrderHom f)
    (lands : ∀ x, f x ∈ T) (hT : Categorical T) : Categorical R := by
  obtain ⟨c, hc⟩ := hT
  let r : R →o T := ⟨fun x => ⟨f x, lands x⟩, f.monotone⟩
  have rest : EqvGen (· ≤ ·) f (OrderHom.const R c) :=
    map_fence (fun g => g.comp r)
      (fun _ _ h => .rel _ _ (fun x => OrderHom.le_def.mp h (r x))) hc
  exact ⟨c, .trans _ _ _ path rest⟩

private theorem retainedPiece_categorical {E : Set P} (hE : Categorical E) :
    Categorical (d.retainedPiece E) := by
  let A := d.retainedPiece E
  let inc : A →o d.retained := ⟨fun x => ⟨x.val, x.property.choose⟩, fun _ _ h => h⟩
  let append (g : FixedOrderMaps d.retained d.old) : A →o P := g.val.comp inc
  have path : EqvGen (· ≤ ·) (OrderEmbedding.subtype A).toOrderHom (append d.retract) :=
    map_fence append (fun g h hgh => .rel _ _ (fun x =>
      (OrderHom.le_def.mp (show g.val ≤ h.val from hgh)) (inc x))) d.retractFence
  exact categorical_of_endpoint path (fun x => x.property.choose_spec) hE

/-- A full first trace and a moving anchor on the second piece give a
categorical point cover with both exact old intersections. -/
theorem moving_anchor_point_cover
    (E : Bool → Set P) (hE : ∀ i, E i ⊆ d.old) (lower₀ : IsLowerSet (E false))
    (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i) (oldCat : ∀ i, Categorical (E i))
    (full : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, d.trace (E false) ({v} : Finset V)) → d.trace (E false) s.val)
    (c : d.MovingAnchorCertificate E) :
    let W := fun i => d.pointPiece (E i) (d.exteriorPiece (E false) i)
    (∀ x, ∃ i, x ∈ W i) ∧ (∀ i, W i ∩ d.old = E i) ∧ (∀ i, Categorical (W i)) := by
  dsimp only
  refine ⟨d.exterior_point_cover E oldCover,
    fun i => pointPiece_inter_old d (hE i) (fun _ hs => hs.1), ?_⟩
  intro i
  cases i with
  | false =>
    let W₀ := d.pointPiece (E false) (d.exteriorPiece (E false) false)
    obtain ⟨f, hf, lands⟩ := d.first_pointPiece_fence E (hE false) lower₀ full
    have path : EqvGen (· ≤ ·) (OrderEmbedding.subtype W₀).toOrderHom f.val :=
      map_fence (fun g : FixedOrderMaps W₀ (E false) => g.val)
        (fun _ _ h => .rel _ _ h) hf
    exact categorical_of_endpoint path lands (oldCat false)
  | true =>
    obtain ⟨f, hf, lands⟩ := d.moving_anchor_endpoint_fence E lower₀ oldCover c
    exact categorical_of_endpoint hf lands (d.retainedPiece_categorical (oldCat true))

end Attachment

private theorem allowed_cover_exact [Finite P] {I : Type*} {Q : Set P} {E W : I → Set P}
    (hE : ∀ i, IsLowerSet (E i)) (oldCover : ∀ x ∈ Q, ∃ i, x ∈ E i)
    (pointCover : ∀ x, ∃ i, x ∈ W i) (exactOld : ∀ i, W i ∩ Q = E i) :
    let U := fun i => liftedRegion (allowedChains Q (E i) (W i))
    (∀ s, ∃ i, s ∈ U i) ∧ (∀ i, U i ∩ flagRegion Q = flagRegion (E i)) := by
  classical
  have sub (i : I) {x : P} (hx : x ∈ E i) : x ∈ W i ∧ x ∈ Q := by
    rw [← exactOld i] at hx
    exact hx
  refine ⟨?_, ?_⟩
  · intro s
    obtain ⟨m, hm⟩ := s.finset.exists_minimal s.nonempty
    have hmle (t : NonemptyFiniteChains P) (ht : t ∈ s.finset) : m ≤ t :=
      (s.comparable ⟨m, hm.1⟩ ⟨t, ht⟩).elim id (fun h => hm.2 ht h)
    let O := s.finset.filter (· ∈ liftedRegion Q)
    by_cases hO : O.Nonempty
    · obtain ⟨b, hb⟩ := O.exists_maximal hO
      have hb' := Finset.mem_filter.mp hb.1
      obtain ⟨y, hy⟩ := b.finset.exists_maximal b.nonempty
      obtain ⟨i, hi⟩ := oldCover y (hb'.2 y hy.1)
      have oldInE (t : NonemptyFiniteChains P) (ht : t ∈ s.finset)
          (htQ : t ∈ liftedRegion Q) : t ∈ liftedRegion (E i) := by
        have htb : t ≤ b := (s.comparable ⟨t, ht⟩ ⟨b, hb'.1⟩).elim id
          (fun h => hb.2 (Finset.mem_filter.mpr ⟨ht, htQ⟩) h)
        intro v hv
        have hvb : v ∈ b.finset := htb hv
        have hvy : v ≤ y := (b.comparable ⟨v, hvb⟩ ⟨y, hy.1⟩).elim id (fun h => hy.2 hvb h)
        exact hE i hvy hi
      have hmOld : m ∈ liftedRegion Q := liftedRegion_lower Q (hmle b hb'.1) hb'.2
      obtain ⟨z, hz⟩ := m.nonempty
      exact ⟨i, fun t ht => ⟨⟨z, hmle t ht hz, (sub i (oldInE m hm.1 hmOld z hz)).1⟩,
        oldInE t ht⟩⟩
    · obtain ⟨z, hz⟩ := m.nonempty
      obtain ⟨i, hi⟩ := pointCover z
      exact ⟨i, fun t ht => ⟨⟨z, hmle t ht hz, hi⟩, fun htOld =>
        (hO ⟨t, Finset.mem_filter.mpr ⟨ht, htOld⟩⟩).elim⟩⟩
  · intro i
    ext s
    constructor
    · rintro ⟨hs, ho⟩ t ht
      exact (hs t ht).2 (ho t ht)
    · intro hs
      refine ⟨?_, fun t ht v hv => (sub i (hs t ht v hv)).2⟩
      intro t ht
      obtain ⟨x, hx⟩ := t.nonempty
      exact ⟨⟨x, hx, (sub i (hs t ht x hx)).1⟩, fun _ => hs t ht⟩

/-- Categorical point regions with exact old intersections give categorical lower
regions with the same subdivided intersections. The contractions of the point
regions can move points of the specified old pieces. -/
theorem categorical_lower_cover_double_subdivision [Finite P] {I : Type*}
    {Q : Set P} {E W : I → Set P}
    (lower : ∀ i, IsLowerSet (E i)) (oldCover : ∀ x ∈ Q, ∃ i, x ∈ E i)
    (pointCover : ∀ x, ∃ i, x ∈ W i) (exactOld : ∀ i, W i ∩ Q = E i)
    (categorical : ∀ i, Categorical (W i)) :
    ∃ U : I → Set (NonemptyFiniteChains (NonemptyFiniteChains P)), (∀ s, ∃ i, s ∈ U i) ∧
      ∀ i, IsLowerSet (U i) ∧ Categorical (U i) ∧
        U i ∩ flagRegion Q = flagRegion (E i) := by
  classical
  let := Fintype.ofFinite P
  let : Finite (NonemptyFiniteChains P) :=
    Finite.of_injective (fun s : NonemptyFiniteChains P => s.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)
  let U (i : I) := liftedRegion (allowedChains Q (E i) (W i))
  obtain ⟨cover, old⟩ := allowed_cover_exact lower oldCover pointCover exactOld
  refine ⟨U, cover, fun i => ⟨liftedRegion_lower _, ?_, old i⟩⟩
  have hchains : Categorical (liftedRegion (W i)) := by
    apply categorical_of_meeting (categorical i)
    intro s
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  have hflags : Categorical (flagRegion (W i)) := by
    apply categorical_of_meeting hchains
    intro s
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  obtain ⟨c, hc⟩ := hflags
  obtain ⟨cut, hcut, lands⟩ := trim_flags Q (E i) (W i)
  let r : U i →o flagRegion (W i) := ⟨fun s => ⟨cut.val s, lands s⟩, cut.val.monotone⟩
  have first : EqvGen (· ≤ ·) (OrderEmbedding.subtype (U i)).toOrderHom cut.val :=
    map_fence (fun f => f.val) (fun _ _ h => .rel _ _ h) hcut
  have rest : EqvGen (· ≤ ·) cut.val (OrderHom.const (U i) c) :=
    map_fence (fun f => f.comp r) (fun _ _ h => .rel _ _ (fun x => OrderHom.le_def.mp h (r x))) hc
  exact ⟨c, .trans _ _ _ first rest⟩

/-- The moving-anchor point cover gives a categorical lower two-cover after
two subdivisions, with both prescribed old intersections. -/
theorem Attachment.moving_anchor_exact_two_cover [Finite P] (d : Attachment P V)
    (E : Bool → Set P) (hE : ∀ i, E i ⊆ d.old) (lower : ∀ i, IsLowerSet (E i))
    (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i) (oldCat : ∀ i, Categorical (E i))
    (full : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, d.trace (E false) ({v} : Finset V)) → d.trace (E false) s.val)
    (c : d.MovingAnchorCertificate E) :
    ∃ U : Bool → Set (NonemptyFiniteChains (NonemptyFiniteChains P)),
      (∀ s, ∃ i, s ∈ U i) ∧
      ∀ i, IsLowerSet (U i) ∧ Categorical (U i) ∧
        U i ∩ flagRegion d.old = flagRegion (E i) := by
  obtain ⟨points, old, categorical⟩ :=
    d.moving_anchor_point_cover E hE (lower false) oldCover oldCat full c
  exact categorical_lower_cover_double_subdivision lower oldCover points old categorical


end D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

namespace D5.S3.Topology.StableCategory.InheritedDepthConeAttachment.ConeDecomposition

open OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open PartialOrder (NonemptyFiniteChains)
open BarycentricGraphDistance (Face)
open ConnectedCategoryGraft (Categorical)
open TrimmedAnchorMixedCone (flagRegion)

open private finiteAtDepth finiteChains from
  D5.S3.Topology.StableCategory.InheritedDepthConeAttachment

local notation "S" => NonemptyFiniteChains

variable {X : Type} [PartialOrder X]

/-- On the actual attachment chart at positive depth, a moving anchor
transports both old intersections across the next two subdivisions. -/
theorem moving_anchor_exact_two_cover_of_adjoined_maximum [Finite X] {Q₀ : Set X}
    (t : X) (hQ : IsLowerSet Q₀) (ht : t ∉ Q₀) (hcover : ∀ x : X, x ∈ Q₀ ∨ x = t)
    (n : ℕ) :
    let P := finiteSpaceSubdivision X n
    letI : PartialOrder P.1 := P.2
    ∀ [DecidableEq P.1],
    let a := ((ofAdjoinedMaximum t hQ ht hcover).iterate n).attachment
    ∀ (E : Bool → Set (S P.1)),
      (∀ i, E i ⊆ a.old) → (∀ i, IsLowerSet (E i)) →
      (∀ x ∈ a.old, ∃ i, x ∈ E i) → (∀ i, Categorical (E i)) →
      (∀ s : Face a.cone, a.apex ∉ s.val →
        (∀ v ∈ s.val, a.trace (E false) {v}) → a.trace (E false) s.val) →
      a.MovingAnchorCertificate E →
      ∃ U : Bool → Set (S (S (S P.1))), (∀ s, ∃ i, s ∈ U i) ∧
        ∀ i, IsLowerSet (U i) ∧ Categorical (U i) ∧
          U i ∩ flagRegion a.old = flagRegion (E i) := by
  dsimp only
  intro dec E hE lower cover cat full c
  let P := finiteSpaceSubdivision X n
  let : PartialOrder P.1 := P.2
  let : Finite P.1 := finiteAtDepth n
  let : Finite (S P.1) := finiteChains
  exact ((ofAdjoinedMaximum t hQ ht hcover).iterate n).attachment.moving_anchor_exact_two_cover
    E hE lower cover cat full c

end D5.S3.Topology.StableCategory.InheritedDepthConeAttachment.ConeDecomposition
