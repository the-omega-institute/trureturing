/- GID: D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/TrimmedAnchorMixedCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A vertex spanning one exclusive trace transports a relative two-cover over a cone. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.BarycentricGraphDistance
import D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision

/-!
# Relative covers of a cone attachment

Omega original. A full trace allows a face to be trimmed to its trace vertices.
An anchor on the other side handles faces supported entirely on exclusive vertices.
The resulting relative point cover becomes a lower cover after two subdivisions.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

open BarycentricGraphDistance (Face)
open RelativeCoverNecessity (FixedOrderMaps RelativeOrderFence)
open Relation (EqvGen)

open private map_fence from D5.S3.Topology.SubdivisionCategoricalCover

variable {P V : Type*} [PartialOrder P] [DecidableEq V]

/-- A cone face poset chart on one of two lower regions. The base is identified
with its actual old image by the specified relative retraction. -/
structure Attachment (P V : Type*) [PartialOrder P] [DecidableEq V] where
  cone : PreAbstractSimplicialComplex V
  apex : V
  retained : Set P
  coneRegion : Set P
  old : Set P
  interface : Set P
  faceIso : Face cone ≃o coneRegion
  retainedLower : IsLowerSet retained
  coneLower : IsLowerSet coneRegion
  cover : ∀ x, x ∈ retained ∨ x ∈ coneRegion
  oldSubset : old ⊆ retained
  base_iff : ∀ s : Face cone, (faceIso s).val ∈ retained ↔ apex ∉ s.val
  insert_apex : ∀ s : Face cone, insert apex s.val ∈ cone
  retract : FixedOrderMaps retained old
  retractFence : EqvGen (fun f g : FixedOrderMaps retained old => f.val ≤ g.val)
    (FixedOrderMaps.inclusion retained old) retract
  retractLand : ∀ x : retained, retract.val x ∈ old
  interfaceIso : {s : Face cone // apex ∉ s.val} ≃o interface
  interface_eq : ∀ s : Face cone, ∀ h : apex ∉ s.val,
    (interfaceIso ⟨s, h⟩).val = retract.val ⟨(faceIso s).val, (base_iff s).mpr h⟩

namespace Attachment

variable (d : Attachment P V)

/-- A finite vertex set is in the trace when it is a base face identified
with a point of the prescribed old region. -/
def trace (E : Set P) (s : Finset V) : Prop :=
  ∃ hs : s ∈ d.cone, ∃ hu : d.apex ∉ s,
    (d.interfaceIso ⟨⟨s, hs⟩, hu⟩).val ∈ E

/-- The inverse image of an old region under the retained retraction. -/
def retainedPiece (E : Set P) : Set P :=
  {x | ∃ hx : x ∈ d.retained, d.retract.val ⟨x, hx⟩ ∈ E}

private theorem trace_iff_retained (E : Set P) (s : Face d.cone) (hs : d.apex ∉ s.val) :
    d.trace E s.val ↔ (d.faceIso s).val ∈ d.retainedPiece E := by
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨(d.base_iff s).mpr hs, (d.interface_eq s hs) ▸ h⟩
  · rintro ⟨_, h⟩
    exact ⟨s.property, hs, (d.interface_eq s hs).symm ▸ h⟩

private theorem trace_mono_down {E : Set P} (hE : IsLowerSet E)
    {s t : Face d.cone} (hst : s ≤ t) (ht : d.trace E t.val) :
    d.trace E s.val := by
  have htBase : d.apex ∉ t.val := ht.choose_spec.choose
  have hsBase : d.apex ∉ s.val := fun h => htBase (hst h)
  obtain ⟨_, htE⟩ := (d.trace_iff_retained E t htBase).mp ht
  apply (d.trace_iff_retained E s hsBase).mpr
  refine ⟨(d.base_iff s).mpr hsBase, hE ?_ htE⟩
  exact d.retract.val.monotone (show
    (⟨(d.faceIso s).val, (d.base_iff s).mpr hsBase⟩ : d.retained) ≤
      ⟨(d.faceIso t).val, (d.base_iff t).mpr htBase⟩ from d.faceIso.monotone hst)

private theorem trace_singleton_of_mem {E : Set P} (hE : IsLowerSet E)
    {s : Face d.cone} (hs : d.trace E s.val) {v : V} (hv : v ∈ s.val) :
    d.trace E ({v} : Finset V) := by
  have hsub : ({v} : Finset V) ⊆ s.val := Finset.singleton_subset_iff.mpr hv
  let vertex : Face d.cone :=
    ⟨{v}, (d.cone.isRelLowerSet_faces s.property).2 hsub (Finset.singleton_nonempty v)⟩
  exact d.trace_mono_down hE (s := vertex) (t := s) hsub hs

/-- The point region obtained by adding the specified cone faces to a retained piece. -/
def pointPiece (E : Set P) (D : Set (Face d.cone)) : Set P :=
  {x | x ∈ d.retainedPiece E ∨ ∃ s ∈ D, (d.faceIso s).val = x}

private theorem pointPiece_inter_old {E : Set P} (hE : E ⊆ d.old)
    {D : Set (Face d.cone)} (hD : ∀ s ∈ D, d.apex ∈ s.val) :
    d.pointPiece E D ∩ d.old = E := by
  ext x
  constructor
  · rintro ⟨hx, hOld⟩
    rcases hx with ⟨hxA, hxE⟩ | ⟨s, hs, rfl⟩
    · have hfix : d.retract.val ⟨x, hxA⟩ = x := d.retract.property ⟨x, hxA⟩ hOld
      rw [hfix] at hxE
      exact hxE
    · exact ((d.base_iff s).mp (d.oldSubset hOld) (hD s hs)).elim
  · intro hx
    have hOld : x ∈ d.old := hE hx
    have hxA : x ∈ d.retained := d.oldSubset hOld
    exact ⟨Or.inl ⟨hxA, (d.retract.property ⟨x, hxA⟩ hOld).symm ▸ hx⟩, hOld⟩

/-- Extend two cone rows by the identity on the retained piece, then append
the specified retraction fence. Only base faces below an exterior face
need to be preserved in the two cone rows. -/
private theorem pointPiece_fence {E : Set P} (hE : E ⊆ d.old)
    {D : Set (Face d.cone)} (hD : ∀ s ∈ D, d.apex ∈ s.val)
    (middle last : Finset V →o Finset V)
    (hMiddle : ∀ s ∈ D, middle s.val ∈ d.cone)
    (hLast : ∀ s ∈ D, d.trace E (last s.val))
    (hLastMiddle : ∀ s ∈ D, last s.val ≤ middle s.val)
    (hFirst : (∀ s ∈ D, middle s.val ≤ s.val) ∨ (∀ s ∈ D, s.val ≤ middle s.val))
    (hKeep : ∀ (b : Face d.cone), d.trace E b.val →
      ∀ s ∈ D, b ≤ s → b.val ≤ last s.val) :
    RelativeOrderFence (d.pointPiece E D) E := by
  classical
  let R := d.retainedPiece E
  let W := d.pointPiece E D
  have hRetained (x : P) (hx : x ∈ E) : x ∈ R := by
    have hxA := d.oldSubset (hE hx)
    exact ⟨hxA, (d.retract.property ⟨x, hxA⟩ (hE hx)).symm ▸ hx⟩
  have witness (x : W) (hx : x.val ∉ R) : ∃ s ∈ D, (d.faceIso s).val = x.val :=
    (show x.val ∈ R ∨ ∃ s ∈ D, (d.faceIso s).val = x.val from x.property).resolve_left hx
  let exterior (x : W) (hx : x.val ∉ R) : Face d.cone := (witness x hx).choose
  have exterior_spec (x : W) (hx : x.val ∉ R) :
      exterior x hx ∈ D ∧ (d.faceIso (exterior x hx)).val = x.val :=
    (witness x hx).choose_spec
  let row (f : Finset V →o Finset V) (hf : ∀ s ∈ D, f s.val ∈ d.cone)
      (keep : ∀ (b : Face d.cone), d.trace E b.val →
        ∀ s ∈ D, b ≤ s → b.val ≤ f s.val) : FixedOrderMaps W E :=
    ⟨{ toFun := fun x => if hx : x.val ∈ R then x.val else
          (d.faceIso ⟨f (exterior x hx).val, hf _ (exterior_spec x hx).1⟩).val
       monotone' := by
        intro x y hxy
        have hxy' : x.val ≤ y.val := hxy
        by_cases hx : x.val ∈ R <;> by_cases hy : y.val ∈ R
        · simpa only [dite_eq_left hx, dite_eq_left hy] using hxy'
        · simp only [dite_eq_left hx, dite_eq_right hy]
          let s := exterior y hy
          have he : (d.faceIso s).val = y.val := (exterior_spec y hy).2
          have hxC : x.val ∈ d.coneRegion :=
            d.coneLower hxy' (he ▸ (d.faceIso s).property)
          let b := d.faceIso.symm ⟨x.val, hxC⟩
          have hb : (d.faceIso b).val = x.val :=
            congrArg Subtype.val (d.faceIso.apply_symm_apply ⟨x.val, hxC⟩)
          have hbA : (d.faceIso b).val ∈ d.retained := hb.symm ▸ hx.choose
          have hbTrace := (d.trace_iff_retained E b ((d.base_iff b).mp hbA)).mpr (hb.symm ▸ hx)
          have hbs : b ≤ s := d.faceIso.le_iff_le.mp (show
            (d.faceIso b).val ≤ (d.faceIso s).val by simpa only [hb, he] using hxy')
          have hbf : b ≤ (⟨f s.val, hf s (exterior_spec y hy).1⟩ : Face d.cone) :=
            keep b hbTrace s (exterior_spec y hy).1 hbs
          exact hb ▸ (show (d.faceIso b).val ≤
            (d.faceIso ⟨f s.val, hf s (exterior_spec y hy).1⟩).val from d.faceIso.monotone hbf)
        · exfalso
          let s := exterior x hx
          have hxA : x.val ∈ d.retained := d.retainedLower hxy' hy.choose
          exact (d.base_iff s).mp ((exterior_spec x hx).2.symm ▸ hxA)
            (hD s (exterior_spec x hx).1)
        · simp only [dite_eq_right hx, dite_eq_right hy]
          let s := exterior x hx
          let t := exterior y hy
          have hs : (d.faceIso s).val = x.val := (exterior_spec x hx).2
          have ht : (d.faceIso t).val = y.val := (exterior_spec y hy).2
          have hst : s ≤ t := d.faceIso.le_iff_le.mp (show
            (d.faceIso s).val ≤ (d.faceIso t).val by simpa only [hs, ht] using hxy')
          exact d.faceIso.monotone (show
            (⟨f s.val, hf s (exterior_spec x hx).1⟩ : Face d.cone) ≤
              ⟨f t.val, hf t (exterior_spec y hy).1⟩ from f.monotone hst) },
      fun x hx => dite_eq_left (hRetained x.val hx)⟩
  have middleKeep (b : Face d.cone) (hb : d.trace E b.val)
      (s : Face d.cone) (hs : s ∈ D) (hbs : b ≤ s) : b.val ≤ middle s.val :=
    (hKeep b hb s hs hbs).trans (hLastMiddle s hs)
  let M := row middle hMiddle middleKeep
  have hLastFace : ∀ s ∈ D, last s.val ∈ d.cone := fun s hs => (hLast s hs).choose
  let L := row last hLastFace hKeep
  have row_retained (f) (hf) (keep) (x : W) (hx : x.val ∈ R) :
      (row f hf keep).val x = x.val := by
    change (if h : x.val ∈ R then x.val else
      (d.faceIso ⟨f (exterior x h).val, hf _ (exterior_spec x h).1⟩).val) = x.val
    rw [dite_eq_left hx]
  have row_exterior (f) (hf) (keep) (x : W) (hx : x.val ∉ R) :
      (row f hf keep).val x =
        (d.faceIso ⟨f (exterior x hx).val, hf _ (exterior_spec x hx).1⟩).val := by
    change (if h : x.val ∈ R then x.val else
      (d.faceIso ⟨f (exterior x h).val, hf _ (exterior_spec x h).1⟩).val) = _
    rw [dite_eq_right hx]
  have hML : L.val ≤ M.val := by
    intro x
    by_cases hx : x.val ∈ R
    · dsimp only [L, M]
      rw [row_retained last hLastFace hKeep x hx, row_retained middle hMiddle middleKeep x hx]
    · dsimp only [L, M]
      rw [row_exterior last hLastFace hKeep x hx, row_exterior middle hMiddle middleKeep x hx]
      exact d.faceIso.monotone (show (⟨last (exterior x hx).val, _⟩ : Face d.cone) ≤
        ⟨middle (exterior x hx).val, _⟩ from hLastMiddle _ (exterior_spec x hx).1)
  have before : EqvGen (fun f g : FixedOrderMaps W E => f.val ≤ g.val)
      (FixedOrderMaps.inclusion W E) M := by
    rcases hFirst with h | h
    · apply EqvGen.symm
      apply EqvGen.rel
      intro x
      change (row middle hMiddle middleKeep).val x ≤ x.val
      by_cases hx : x.val ∈ R
      · rw [row_retained middle hMiddle middleKeep x hx]
      · rw [row_exterior middle hMiddle middleKeep x hx]
        have hle : (⟨middle (exterior x hx).val, hMiddle _ (exterior_spec x hx).1⟩ :
            Face d.cone) ≤ exterior x hx := h _ (exterior_spec x hx).1
        have hmap : (d.faceIso _).val ≤ (d.faceIso (exterior x hx)).val :=
          d.faceIso.monotone hle
        exact hmap.trans (exterior_spec x hx).2.le
    · apply EqvGen.rel
      intro x
      change x.val ≤ (row middle hMiddle middleKeep).val x
      by_cases hx : x.val ∈ R
      · rw [row_retained middle hMiddle middleKeep x hx]
      · rw [row_exterior middle hMiddle middleKeep x hx]
        have hle : exterior x hx ≤
            (⟨middle (exterior x hx).val, hMiddle _ (exterior_spec x hx).1⟩ : Face d.cone) :=
          h _ (exterior_spec x hx).1
        exact (exterior_spec x hx).2.symm.le.trans (d.faceIso.monotone hle)
  have land (x : W) : L.val x ∈ R := by
    dsimp only [L]
    by_cases hx : x.val ∈ R
    · rwa [row_retained last hLastFace hKeep x hx]
    · rw [row_exterior last hLastFace hKeep x hx]
      have ht := hLast (exterior x hx) (exterior_spec x hx).1
      let t : Face d.cone := ⟨last (exterior x hx).val, hLastFace _ (exterior_spec x hx).1⟩
      exact (d.trace_iff_retained E t ht.choose_spec.choose).mp ht
  let lift : W →o d.retained :=
    ⟨fun x => ⟨L.val x, (land x).choose⟩, fun _ _ h => L.val.monotone h⟩
  let append (f : FixedOrderMaps d.retained d.old) : FixedOrderMaps W E :=
    ⟨f.val.comp lift, by
      intro x hx
      have he : (lift x).val = x.val := L.property x hx
      exact (f.property (lift x) (he.symm ▸ hE hx)).trans he⟩
  have hStart : append (FixedOrderMaps.inclusion d.retained d.old) = L := by
    apply Subtype.ext
    apply OrderHom.ext
    funext x
    rfl
  have after : EqvGen (fun f g : FixedOrderMaps W E => f.val ≤ g.val) L (append d.retract) := by
    rw [← hStart]
    exact map_fence append (fun f g h => .rel _ _ (fun x =>
      (OrderHom.le_def.mp (show f.val ≤ g.val from h)) (lift x))) d.retractFence
  refine ⟨append d.retract, .trans _ _ _ before (.trans _ _ _ (.symm _ _ (.rel _ _ hML)) after), ?_⟩
  intro x
  exact (land x).choose_spec

/-- The first color takes exactly the exterior faces with a vertex of its
inherited trace. The second takes the apex and the exterior faces whose
base vertices are all exclusive to the second color. -/
def exteriorPiece (E₀ : Set P) (color : Bool) : Set (Face d.cone) :=
  {s | d.apex ∈ s.val ∧ ((∃ v ∈ s.val, d.trace E₀ ({v} : Finset V)) ↔ color = false)}

/-- One anchor spanning the base faces on exclusive vertices is sufficient
when the first trace is full. Both order fences fix the prescribed old
points throughout. -/
theorem trimmed_anchor_point_cover
    (E : Bool → Set P) (hE : ∀ i, E i ⊆ d.old) (lower₀ : IsLowerSet (E false))
    (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i)
    (full : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, d.trace (E false) ({v} : Finset V)) → d.trace (E false) s.val)
    (a : V) (anchor : d.trace (E true) ({a} : Finset V))
    (span : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, ¬ d.trace (E false) ({v} : Finset V)) →
      d.trace (E true) (insert a s.val)) :
    let W := fun i => d.pointPiece (E i) (d.exteriorPiece (E false) i)
    (∀ x, ∃ i, x ∈ W i) ∧
      (∀ i, W i ∩ d.old = E i) ∧ (∀ i, RelativeOrderFence (W i) (E i)) := by
  classical
  dsimp only
  have exterior (i : Bool) : ∀ s ∈ d.exteriorPiece (E false) i, d.apex ∈ s.val :=
    fun _ hs => hs.1
  refine ⟨?_, fun i => d.pointPiece_inter_old (hE i) (exterior i), ?_⟩
  · intro x
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
  · intro i
    cases i with
    | false =>
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
      refine d.pointPiece_fence (hE false) (exterior false) middle cut
        (fun s hs => d.insert_apex ⟨cut s.val, (cutTrace s hs).choose⟩) cutTrace
        (fun _ _ _ hx => Finset.mem_insert_of_mem hx) (Or.inl ?_) ?_
      · intro s hs x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact exterior false s hs
        · exact (Finset.mem_filter.mp hx).1
      · intro b hb s _ hbs v hv
        exact Finset.mem_filter.mpr ⟨hbs hv, d.trace_singleton_of_mem lower₀ hb hv⟩
    | true =>
      let last : Finset V →o Finset V :=
        ⟨fun s => insert a (s.erase d.apex), fun _ _ h =>
          Finset.insert_subset_insert _ (Finset.erase_subset_erase _ h)⟩
      let middle : Finset V →o Finset V :=
        ⟨fun s => insert d.apex (last s), fun _ _ h =>
          Finset.insert_subset_insert _ (last.monotone h)⟩
      have insertedTrace (s : Face d.cone) (hs : s ∈ d.exteriorPiece (E false) true) :
          d.trace (E true) (last s.val) := by
        by_cases hn : (s.val.erase d.apex).Nonempty
        · let t : Face d.cone := ⟨s.val.erase d.apex,
            (d.cone.isRelLowerSet_faces s.property).2 (Finset.erase_subset _ _) hn⟩
          apply span t
          · exact Finset.notMem_erase _ _
          · intro v hv hTrace
            have bad : true = false := hs.2.mp ⟨v, (Finset.mem_erase.mp hv).2, hTrace⟩
            cases bad
        · have hempty : s.val.erase d.apex = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
          change d.trace (E true) (insert a (s.val.erase d.apex))
          simpa only [hempty, Finset.insert_empty] using anchor
      refine d.pointPiece_fence (hE true) (exterior true) middle last
        (fun s hs => d.insert_apex ⟨last s.val, (insertedTrace s hs).choose⟩) insertedTrace
        (fun _ _ _ hx => Finset.mem_insert_of_mem hx) (Or.inr ?_) ?_
      · intro s _ v hv
        by_cases hu : v = d.apex
        · exact Finset.mem_insert.mpr (Or.inl hu)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hu, hv⟩))
      · intro b hb s _ hbs v hv
        have hBase : d.apex ∉ b.val := hb.choose_spec.choose
        have hvApex : v ≠ d.apex := fun h => hBase (h ▸ hv)
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvApex, hbs hv⟩)

end Attachment

section DoubleSubdivision

open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open private restrictChains unionMap from D5.S3.Topology.SubdivisionCategoricalCover
open private liftedRegion liftedRegion_lower relative_fence_of_comparison
  from D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision

/-- The flags of nonempty chains supported on a prescribed point region. -/
def flagRegion (U : Set P) : Set (NonemptyFiniteChains (NonemptyFiniteChains P)) :=
  liftedRegion (liftedRegion U)

private theorem mem_restriction {X : Type*} [PartialOrder X]
    {U : Set X} {S : Set (NonemptyFiniteChains X)}
    (meet : ∀ s : S, ∃ x ∈ s.val.finset, x ∈ U) (s : S) (x : U) :
    x ∈ (restrictChains U meet s).finset ↔ x.val ∈ s.val.finset := by
  classical
  change x ∈ s.val.finset.subtype (· ∈ U) ↔ _
  exact Finset.mem_subtype

/-- Lift a fence once, retaining agreement on every chain of fixed points. -/
private theorem lift_relative_fence {X : Type*} [PartialOrder X] [Finite X]
    {R E : Set X} (h : RelativeOrderFence R E) :
    RelativeOrderFence (liftedRegion R) (liftedRegion E) := by
  classical
  let := Fintype.ofFinite R
  let A := liftedRegion R
  let T := liftedRegion E
  let meet (s : A) : ∃ x ∈ s.val.finset, x ∈ R := by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  let lift : A →o NonemptyFiniteChains R := restrictChains R meet
  have image_eq (f : R →o X) (s : A)
      (hf : ∀ x ∈ (lift s).finset, f x = x.val) : (lift s).map f = s.val := by
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro x
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hf y hy]
      exact (mem_restriction meet s y).mp hy
    · intro hx
      let y : R := ⟨x, s.property x hx⟩
      have hy := (mem_restriction meet s y).mpr hx
      exact ⟨y, hy, hf y hy⟩
  let row (f : FixedOrderMaps R E) : FixedOrderMaps A T :=
    ⟨(orderHomMap f.val).comp lift, fun s hs =>
      image_eq f.val s (fun x hx => f.property x (hs x.val ((mem_restriction meet s x).mp hx)))⟩
  have start : row (FixedOrderMaps.inclusion R E) = FixedOrderMaps.inclusion A T := by
    apply Subtype.ext
    apply OrderHom.ext
    funext s
    exact image_eq _ s (fun _ _ => rfl)
  let down (x : R) : Finset R := Finset.univ.filter (· ≤ x)
  let rank (x : R) : ℕ := (down x).card
  have mem_down (x y : R) : y ∈ down x ↔ y ≤ x := by simp [down]
  have strict : StrictMono rank := by
    intro x y hxy
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz =>
      (mem_down y z).mpr (((mem_down x z).mp hz).trans hxy.le), ?_⟩
    intro eq
    exact hxy.not_ge ((mem_down x y).mp (eq.symm ▸ (mem_down y y).mpr le_rfl))
  have bound (x : R) : rank x ≤ Fintype.card R := Finset.card_le_univ _
  have step (f g : FixedOrderMaps R E) (hfg : f ≤ g) :
      EqvGen (fun f g : FixedOrderMaps A T => f.val ≤ g.val) (row f) (row g) := by
    have leRows : f.val ≤ g.val := hfg
    obtain ⟨F, hzero, hlast, hfix, _, hstep⟩ :=
      exists_relative_contiguity_of_le rank strict g.val f.val
        (OrderHom.le_def.mp leRows) (Fintype.card R) bound
    have hF (k : ℕ) (x : R) (hx : x.val ∈ E) : F k x = x.val := by
      rw [hfix k x ((f.property x hx).trans (g.property x hx).symm), g.property x hx]
    let r (k : ℕ) : FixedOrderMaps A T := row ⟨F k, hF k⟩
    let bridge (k : ℕ) : FixedOrderMaps A T :=
      ⟨(unionMap (F k) (F (k + 1)) (hstep k)).comp lift, by
        intro s hs
        apply NonemptyFiniteChains.ext
        change ((r k).val s).finset ∪ ((r (k + 1)).val s).finset = s.val.finset
        rw [(r k).property s hs, (r (k + 1)).property s hs, Finset.union_idempotent]⟩
    have path (k : ℕ) : EqvGen (fun f g : FixedOrderMaps A T => f.val ≤ g.val) (r 0) (r k) := by
      induction k with
      | zero => exact .refl _
      | succ k ih =>
        have hk : (r k).val ≤ (bridge k).val := fun _ => Finset.subset_union_left
        have hks : (r (k + 1)).val ≤ (bridge k).val := fun _ => Finset.subset_union_right
        exact .trans _ _ _ ih (.trans _ _ _ (.rel _ _ hk) (.symm _ _ (.rel _ _ hks)))
    have first : r 0 = row g := by
      have eq : (⟨F 0, hF 0⟩ : FixedOrderMaps R E) = g := Subtype.ext hzero
      exact congrArg row eq
    have last : r (Fintype.card R + 1) = row f := by
      have eq : (⟨F (Fintype.card R + 1), hF _⟩ : FixedOrderMaps R E) = f :=
        Subtype.ext hlast
      exact congrArg row eq
    have hp := path (Fintype.card R + 1)
    rw [first, last] at hp
    exact .symm _ _ hp
  obtain ⟨f, hf, hland⟩ := h
  refine ⟨row f, ?_, ?_⟩
  · rw [← start]
    exact map_fence row step hf
  · intro s y hy
    obtain ⟨x, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hy
    exact hland x

private def allowedChains (Q E W : Set P) : Set (NonemptyFiniteChains P) :=
  {s | (∃ x ∈ s.finset, x ∈ W) ∧ (s ∈ liftedRegion Q → s ∈ liftedRegion E)}

private theorem trim_flags [Finite P] (Q E W : Set P) :
    RelativeOrderFence (liftedRegion (allowedChains Q E W)) (flagRegion W) := by
  classical
  let := Fintype.ofFinite P
  let M := allowedChains Q E W
  let A := liftedRegion M
  let meet (s : A) : ∃ x ∈ s.val.finset, x ∈ M := by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  let lift : A →o NonemptyFiniteChains M := restrictChains M meet
  let pointMeet (s : M) : ∃ x ∈ s.val.finset, x ∈ W := s.property.1
  let cut : M →o NonemptyFiniteChains W := restrictChains W pointMeet
  let f : M →o NonemptyFiniteChains P :=
    (orderHomMap (OrderEmbedding.subtype W).toOrderHom).comp cut
  let g : M →o NonemptyFiniteChains P := (OrderEmbedding.subtype M).toOrderHom
  have mem_cut (s : M) (x : P) : x ∈ (f s).finset ↔ x ∈ s.val.finset ∧ x ∈ W := by
    change x ∈ ((cut s).map (OrderEmbedding.subtype W).toOrderHom).finset ↔ _
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_restriction pointMeet s y).mp hy, y.property⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨x, hxW⟩, (mem_restriction pointMeet s ⟨x, hxW⟩).mpr hx, rfl⟩
  have hfg : f ≤ g := fun s _ hx => ((mem_cut s _).mp hx).1
  let rank (s : M) : ℕ := s.val.finset.card
  refine relative_fence_of_comparison lift hfg (rank := rank) (fun _ _ h => Finset.card_lt_card h)
    (Fintype.card P) (fun _ => Finset.card_le_univ _) ?_ ?_ ?_
  · intro s
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro x
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_restriction meet s y).mp hy
    · intro hx
      let y : M := ⟨x, s.property x hx⟩
      exact ⟨y, (mem_restriction meet s y).mpr hx, rfl⟩
  · intro s hs x hx
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro y
    exact (mem_cut x y).trans ⟨And.left, fun hy =>
      ⟨hy, hs x.val ((mem_restriction meet s x).mp hx) y hy⟩⟩
  · intro s x hx y hy
    obtain ⟨z, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hx
    exact ((mem_cut z y).mp hy).2

/-- A relative point cover yields an exact lower cover after two subdivisions. -/
theorem exact_lower_cover_double_subdivision [Finite P] {I : Type*}
    {Q : Set P} {E W : I → Set P}
    (hE : ∀ i, IsLowerSet (E i)) (oldCover : ∀ x ∈ Q, ∃ i, x ∈ E i)
    (pointCover : ∀ x, ∃ i, x ∈ W i)
    (exactOld : ∀ i, W i ∩ Q = E i) (fences : ∀ i, RelativeOrderFence (W i) (E i)) :
    ∃ U : I → Set (NonemptyFiniteChains (NonemptyFiniteChains P)),
      (∀ i, IsLowerSet (U i)) ∧ (∀ s, ∃ i, s ∈ U i) ∧
      (∀ i, U i ∩ flagRegion Q = flagRegion (E i)) ∧
      ∀ i, RelativeOrderFence (U i) (flagRegion (E i)) := by
  classical
  let := Fintype.ofFinite P
  let : Finite (NonemptyFiniteChains P) :=
    Finite.of_injective (fun s : NonemptyFiniteChains P => s.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)
  let U (i : I) := liftedRegion (allowedChains Q (E i) (W i))
  have sub (i : I) {x : P} (hx : x ∈ E i) : x ∈ W i ∧ x ∈ Q := by
    rw [← exactOld i] at hx
    exact hx
  refine ⟨U, fun _ => liftedRegion_lower _, ?_, ?_, ?_⟩
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
  · intro i
    let S := flagRegion (W i)
    let T := flagRegion (E i)
    have hTS : T ⊆ S := fun _ hs t ht x hx => (sub i (hs t ht x hx)).1
    obtain ⟨cut, hcut, hlands⟩ := trim_flags Q (E i) (W i)
    have one : RelativeOrderFence (liftedRegion (W i)) (liftedRegion (E i)) :=
      lift_relative_fence (fences i)
    obtain ⟨f, hf, hland⟩ := lift_relative_fence one
    let lift : U i →o S :=
      ⟨fun s => ⟨cut.val s, hlands s⟩, fun _ _ h => cut.val.monotone h⟩
    let narrow (g : FixedOrderMaps (U i) S) : FixedOrderMaps (U i) T :=
      ⟨g.val, fun x hx => g.property x (hTS hx)⟩
    let append (g : FixedOrderMaps S T) : FixedOrderMaps (U i) T :=
      ⟨g.val.comp lift, by
        intro x hx
        have he : (lift x).val = x.val := cut.property x (hTS hx)
        exact (g.property (lift x) (he.symm ▸ hx)).trans he⟩
    have first : EqvGen (fun a b : FixedOrderMaps (U i) T => a.val ≤ b.val)
        (FixedOrderMaps.inclusion (U i) T) (narrow cut) :=
      map_fence narrow (fun _ _ h => .rel _ _ h) hcut
    have last : EqvGen (fun a b : FixedOrderMaps (U i) T => a.val ≤ b.val)
        (narrow cut) (append f) :=
      map_fence append (fun a b h => .rel _ _ (fun x =>
        (OrderHom.le_def.mp (show a.val ≤ b.val from h)) (lift x))) hf
    exact ⟨append f, .trans _ _ _ first last, fun x => hland (lift x)⟩

open ConnectedCategoryGraft (Categorical)
open private categorical_of_meeting from D5.S3.Topology.SubdivisionCategoricalCover

/-- A full first trace and an anchor spanning its exclusive complement give
a categorical lower two-cover two subdivisions later, with both prescribed
old traces and both relative retraction fences. -/
theorem Attachment.trimmed_anchor_exact_two_cover [Finite P] (d : Attachment P V)
    (E : Bool → Set P) (hE : ∀ i, E i ⊆ d.old) (lower : ∀ i, IsLowerSet (E i))
    (oldCover : ∀ x ∈ d.old, ∃ i, x ∈ E i) (oldCat : ∀ i, Categorical (E i))
    (full : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, d.trace (E false) ({v} : Finset V)) → d.trace (E false) s.val)
    (a : V) (anchor : d.trace (E true) ({a} : Finset V))
    (span : ∀ s : Face d.cone, d.apex ∉ s.val →
      (∀ v ∈ s.val, ¬ d.trace (E false) ({v} : Finset V)) →
      d.trace (E true) (insert a s.val)) :
    ∃ U : Bool → Set (NonemptyFiniteChains (NonemptyFiniteChains P)),
      (∀ s, ∃ i, s ∈ U i) ∧
      ∀ i, IsLowerSet (U i) ∧ Categorical (U i) ∧
        U i ∩ flagRegion d.old = flagRegion (E i) ∧
          RelativeOrderFence (U i) (flagRegion (E i)) := by
  classical
  let := Fintype.ofFinite P
  let : Finite (NonemptyFiniteChains P) :=
    Finite.of_injective (fun s : NonemptyFiniteChains P => s.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)
  obtain ⟨points, old, fences⟩ :=
    d.trimmed_anchor_point_cover E hE (lower false) oldCover full a anchor span
  obtain ⟨U, hU, cover, traces, paths⟩ :=
    exact_lower_cover_double_subdivision lower oldCover points old fences
  refine ⟨U, cover, fun i => ⟨hU i, ?_, traces i, paths i⟩⟩
  have hchain : Categorical (liftedRegion (E i)) := by
    apply categorical_of_meeting (oldCat i)
    intro s
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  have hflag : Categorical (flagRegion (E i)) := by
    apply categorical_of_meeting hchain
    intro s
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩
  obtain ⟨c, hc⟩ := hflag
  obtain ⟨last, path, land⟩ := paths i
  let r : U i →o flagRegion (E i) := ⟨fun s => ⟨last.val s, land s⟩, last.val.monotone⟩
  have first : EqvGen (· ≤ ·) (OrderEmbedding.subtype (U i)).toOrderHom last.val :=
    map_fence (fun f : FixedOrderMaps (U i) (flagRegion (E i)) => f.val)
      (fun _ _ h => .rel _ _ h) path
  have rest : EqvGen (· ≤ ·) last.val (OrderHom.const (U i) c) :=
    map_fence (fun f => f.comp r)
      (fun _ _ h => .rel _ _ (fun s => OrderHom.le_def.mp h (r s))) hc
  exact ⟨c, .trans _ _ _ first rest⟩

end DoubleSubdivision

end D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone
