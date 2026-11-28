/- GID: D5/S3/Topology/StableCategory/InheritedDepthConeAttachment
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/InheritedDepthConeAttachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attachment retains a relative retraction and its exact cone base under subdivision. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
import D5.S3.Topology.StableCategory.TrimmedAnchorMixedCone

/-!
# Cone attachments at inherited subdivision depth

Omega original. A fixed-relative retraction on one side of a lower cover survives ordinary
chain subdivision when the other side is a cone with its exact base as interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Topology.StableCategory.InheritedDepthConeAttachment

open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open RelativeCoverNecessity (FixedOrderMaps RelativeOrderFence singletonChain isMin_singletonChain)
open Relation (EqvGen)

open private restrictChains unionMap map_fence from D5.S3.Topology.SubdivisionCategoricalCover
open private chainsCongr homOfIso from D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
open private liftedRegion liftedRegion_lower relative_fence_of_comparison from
  D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision

local notation "S" => NonemptyFiniteChains
local notation "SB" => liftedRegion

variable {P X Y : Type} [PartialOrder P] [PartialOrder X] [PartialOrder Y]

private theorem finiteChains [Finite P] : Finite (S P) := by
  classical
  let := Fintype.ofFinite P
  exact Finite.of_injective (fun s : S P => s.finset) (fun _ _ h => NonemptyFiniteChains.ext h)

private theorem finiteAtDepth [Finite X] (n : ℕ) : Finite (finiteSpaceSubdivision X n).1 := by
  induction n with
  | zero => exact inferInstanceAs (Finite X)
  | succ n ih =>
    let P := finiteSpaceSubdivision X n
    let : PartialOrder P.1 := P.2
    let : Finite P.1 := ih
    exact finiteChains

private def inclusion (U : Set P) : U →o P :=
  (OrderEmbedding.subtype U).toOrderHom

private def onRegion (U : Set P) : SB U →o S U :=
  restrictChains U fun s => by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩

private theorem mem_onRegion {U : Set P} (s : SB U) (x : U) :
    x ∈ (onRegion U s).finset ↔ x.val ∈ s.val.finset := by
  classical
  change x ∈ s.val.finset.subtype (· ∈ U) ↔ _
  exact Finset.mem_subtype

private def liftMap {U : Set P} (f : U →o Y) : SB U →o S Y :=
  (orderHomMap f).comp (onRegion U)

private theorem mem_liftMap {U : Set P} (f : U →o Y) (s : SB U) (y : Y) :
    y ∈ (liftMap f s).finset ↔ ∃ x : U, x.val ∈ s.val.finset ∧ f x = y := by
  change y ∈ ((onRegion U s).map f).finset ↔ _
  rw [NonemptyFiniteChains.mem_map_iff]
  exact exists_congr (fun x => (mem_onRegion s x).and Iff.rfl)

private theorem liftMap_fixed {U E : Set P} (f : U →o P)
    (hf : ∀ x : U, x.val ∈ E → f x = x.val)
    (s : SB U) (hs : s.val ∈ SB E) : liftMap f s = s.val := by
  apply NonemptyFiniteChains.ext
  apply Finset.ext
  intro y
  rw [mem_liftMap]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ((hf x (hs x.val hx)).symm.trans hxy) ▸ hx
  · intro hy
    exact ⟨⟨y, s.property y hy⟩, hy, hf _ (hs y hy)⟩

private def regionChains (U : Set P) : SB U ≃o S U where
  toFun := onRegion U
  invFun s := ⟨s.map (inclusion U), by
    intro y hy
    obtain ⟨x, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hy
    exact x.property⟩
  left_inv s := Subtype.ext (liftMap_fixed (E := U) (inclusion U) (fun _ _ => rfl) s s.property)
  right_inv s := by
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro x
    rw [mem_onRegion]
    change x.val ∈ (s.map (inclusion U)).finset ↔ _
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      exact (Subtype.ext h : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  map_rel_iff' := by
    intro s t
    change (onRegion U s).finset ⊆ (onRegion U t).finset ↔ s.val.finset ⊆ t.val.finset
    constructor
    · intro h x hx
      exact (mem_onRegion t ⟨x, s.property x hx⟩).mp
        (h ((mem_onRegion s ⟨x, s.property x hx⟩).mpr hx))
    · intro h
      exact (onRegion U).monotone (show s ≤ t from h)

private theorem lift_mono {U V : Set P} (h : U ⊆ V) : SB U ⊆ SB V :=
  fun _ hs x hx => h (hs x hx)

private theorem lift_inter (U V : Set P) : SB U ∩ SB V = SB (U ∩ V) := by
  ext s
  exact ⟨fun h x hx => ⟨h.1 x hx, h.2 x hx⟩,
    fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩⟩

private theorem chain_compare (s : S P) {x y : P} (hx : x ∈ s.finset) (hy : y ∈ s.finset) :
    x ≤ y ∨ y ≤ x :=
  s.comparable ⟨x, hx⟩ ⟨y, hy⟩

private theorem lift_union_of_lower {U V : Set P} (hU : IsLowerSet U) (hV : IsLowerSet V)
    (hcover : ∀ x : P, x ∈ U ∨ x ∈ V) (s : S P) : s ∈ SB U ∨ s ∈ SB V := by
  classical
  obtain ⟨m, hm⟩ := s.finset.exists_maximal s.nonempty
  have hle : ∀ x ∈ s.finset, x ≤ m := fun x hx =>
    (chain_compare s hx hm.1).elim id (hm.2 hx)
  rcases hcover m with h | h
  · exact Or.inl (fun x hx => hU (hle x hx) h)
  · exact Or.inr (fun x hx => hV (hle x hx) h)

/-- The endpoints of a fence are specified, and its full sequence fixes
the prescribed points as in `RelativeOrderFence`. -/
abbrev FixedFence {A E : Set P} (f g : FixedOrderMaps A E) : Prop :=
  EqvGen (fun a b : FixedOrderMaps A E => a.val ≤ b.val) f g

private theorem fixedFence_map {A E : Set P} {B F : Set Y}
    (m : FixedOrderMaps A E → FixedOrderMaps B F)
    (hm : ∀ f g, f.val ≤ g.val → (m f).val ≤ (m g).val)
    {f g : FixedOrderMaps A E} (h : FixedFence f g) : FixedFence (m f) (m g) :=
  map_fence m (fun _ _ hle => .rel _ _ (hm _ _ hle)) h

section LiftFence

variable {U : Set P} {D E : Set (S Y)}

/-- Endpoint-preserving form of the comparison lift in
`RelativeMaximaDoubleSubdivision`. It keeps the
two chain-image rows explicit so that the last row can be used in a second
fence or restricted to an interface. -/
private theorem lift_comparison (lift : D →o S U) {f g : U →o Y} (hfg : f ≤ g)
    (rank : U → ℕ) (hrank : StrictMono rank) (bound : ℕ) (hbound : ∀ x, rank x ≤ bound)
    (hf : ∀ s : D, s.val ∈ E → (lift s).map f = s.val)
    (hg : ∀ s : D, s.val ∈ E → (lift s).map g = s.val)
    (hagree : ∀ (s : D), s.val ∈ E → ∀ x ∈ (lift s).finset, f x = g x) :
    FixedFence (⟨(orderHomMap g).comp lift, hg⟩ : FixedOrderMaps D E)
      ⟨(orderHomMap f).comp lift, hf⟩ := by
  classical
  obtain ⟨F, hzero, hlast, hfix, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank g f (OrderHom.le_def.mp hfg) bound hbound
  have fixed (k : ℕ) (s : D) (hs : s.val ∈ E) : (lift s).map (F k) = s.val := by
    calc
      (lift s).map (F k) = (lift s).map g := by
        apply NonemptyFiniteChains.ext
        exact Finset.image_congr (fun x hx => hfix k x (hagree s hs x hx))
      _ = s.val := hg s hs
  let row (k : ℕ) : FixedOrderMaps D E := ⟨(orderHomMap (F k)).comp lift, fixed k⟩
  let bridge (k : ℕ) : FixedOrderMaps D E :=
    ⟨(unionMap (F k) (F (k + 1)) (hstep k)).comp lift, by
      intro s hs
      apply NonemptyFiniteChains.ext
      change ((lift s).map (F k)).finset ∪ ((lift s).map (F (k + 1))).finset = s.val.finset
      rw [fixed k s hs, fixed (k + 1) s hs, Finset.union_idempotent]⟩
  have path (k : ℕ) : FixedFence (row 0) (row k) := by
    induction k with
    | zero => exact .refl _
    | succ k ih =>
      have hup : (row k).val ≤ (bridge k).val := fun _ => Finset.subset_union_left
      have hdown : (row (k + 1)).val ≤ (bridge k).val := fun _ => Finset.subset_union_right
      exact .trans _ _ _ ih (.trans _ _ _ (.rel _ _ hup) (.symm _ _ (.rel _ _ hdown)))
  have hstart : row 0 = (⟨(orderHomMap g).comp lift, hg⟩ : FixedOrderMaps D E) :=
    Subtype.ext (congrArg (fun m => (orderHomMap m).comp lift) hzero)
  have hend : row (bound + 1) = (⟨(orderHomMap f).comp lift, hf⟩ : FixedOrderMaps D E) :=
    Subtype.ext (congrArg (fun m => (orderHomMap m).comp lift) hlast)
  rw [← hstart, ← hend]
  exact path (bound + 1)

end LiftFence

private def liftRow {U E : Set P} (f : FixedOrderMaps U E) :
    FixedOrderMaps (SB U) (SB E) :=
  ⟨liftMap f.val, liftMap_fixed f.val f.property⟩

private theorem liftRow_inclusion (U E : Set P) :
    liftRow (FixedOrderMaps.inclusion U E) = FixedOrderMaps.inclusion (SB U) (SB E) := by
  apply Subtype.ext
  apply OrderHom.ext
  funext s
  exact liftMap_fixed (E := U) (inclusion U) (fun _ _ => rfl) s s.property

private theorem lift_fixedFence {U E : Set (S P)} [Finite P]
    {f g : FixedOrderMaps U E} (path : FixedFence f g) :
    FixedFence (liftRow f) (liftRow g) := by
  classical
  let := Fintype.ofFinite P
  induction path with
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  | rel f g hfg =>
    refine .symm _ _ (lift_comparison (onRegion U) hfg
      (fun x : U => x.val.finset.card) (fun _ _ h => Finset.card_lt_card h)
      (Fintype.card P) (fun _ => Finset.card_le_univ _)
      (liftRow f).property (liftRow g).property ?_)
    intro s hs x hx
    have hxE := hs x.val ((mem_onRegion s x).mp hx)
    exact (f.property x hxE).trans (g.property x hxE).symm

private theorem liftMap_lands {U : Set P} {E : Set Y} (f : U →o Y)
    (hf : ∀ x, f x ∈ E) (s : SB U) : liftMap f s ∈ SB E := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := (mem_liftMap f s y).mp hy
  exact hf x

private def glueInclusion {A B E F : Set P} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hE : E ⊆ A) (hF : A ∩ B ⊆ F) (f : FixedOrderMaps B F) :
    FixedOrderMaps (A ∪ B) E := by
  classical
  let g (s : (A ∪ B : Set P)) : P :=
    if hs : s.val ∈ A then s.val else
      f.val ⟨s.val, (show s.val ∈ A ∨ s.val ∈ B from s.property).resolve_left hs⟩
  have onB (s : (A ∪ B : Set P)) (hs : s.val ∈ B) : g s = f.val ⟨s.val, hs⟩ := by
    by_cases ha : s.val ∈ A
    · simpa only [g, dite_eq_left ha] using (f.property ⟨s.val, hs⟩ (hF ⟨ha, hs⟩)).symm
    · simp only [g, dite_eq_right ha]
  refine ⟨⟨g, ?_⟩, fun s hs => dite_eq_left (hE hs)⟩
  intro s t h
  have hst : s.val ≤ t.val := h
  by_cases ht : t.val ∈ A
  · have hs := hA hst ht
    simpa only [g, dite_eq_left hs, dite_eq_left ht] using hst
  · have htB := (show t.val ∈ A ∨ t.val ∈ B from t.property).resolve_left ht
    have hsB := hB hst htB
    rw [onB s hsB, onB t htB]
    exact f.val.monotone (show (⟨s.val, hsB⟩ : B) ≤ ⟨t.val, htB⟩ from hst)

private theorem glue_on_left {A B E F : Set P} {hA : IsLowerSet A} {hB : IsLowerSet B}
    {hE : E ⊆ A} {hF : A ∩ B ⊆ F} (f : FixedOrderMaps B F)
    (s : (A ∪ B : Set P)) (hs : s.val ∈ A) : (glueInclusion hA hB hE hF f).val s = s.val := by
  unfold glueInclusion
  exact dite_eq_left hs

private theorem glue_on_right {A B E F : Set P} {hA : IsLowerSet A} {hB : IsLowerSet B}
    {hE : E ⊆ A} {hF : A ∩ B ⊆ F} (f : FixedOrderMaps B F)
    (s : (A ∪ B : Set P)) (hs : s.val ∈ B) :
    (glueInclusion hA hB hE hF f).val s = f.val ⟨s.val, hs⟩ := by
  classical
  change (if h : s.val ∈ A then s.val else
    f.val ⟨s.val, (show s.val ∈ A ∨ s.val ∈ B from s.property).resolve_left h⟩) =
      f.val ⟨s.val, hs⟩
  by_cases ha : s.val ∈ A
  · rw [dite_eq_left ha]
    exact (f.property ⟨s.val, hs⟩ (hF ⟨ha, hs⟩)).symm
  · rw [dite_eq_right ha]

private theorem glue_inclusion {A B E F : Set P} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hE : E ⊆ A) (hF : A ∩ B ⊆ F) :
    glueInclusion hA hB hE hF (FixedOrderMaps.inclusion B F) =
      FixedOrderMaps.inclusion (A ∪ B) E := by
  apply Subtype.ext
  apply OrderHom.ext
  funext s
  change (glueInclusion hA hB hE hF (FixedOrderMaps.inclusion B F)).val s = s.val
  rcases s.property with hs | hs
  · exact glue_on_left _ s hs
  · exact glue_on_right _ s hs

private theorem glue_fence {A B E F : Set P} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hE : E ⊆ A) (hF : A ∩ B ⊆ F)
    {f g : FixedOrderMaps B F} (h : FixedFence f g) :
    FixedFence (glueInclusion hA hB hE hF f) (glueInclusion hA hB hE hF g) := by
  apply fixedFence_map (glueInclusion hA hB hE hF) _ h
  intro f g hfg s
  rcases s.property with hs | hs
  · rw [glue_on_left f s hs, glue_on_left g s hs]
  · rw [glue_on_right f s hs, glue_on_right g s hs]
    exact OrderHom.le_def.mp hfg _

private def insertChain (a : P) (s : S P) (h : ∀ x ∈ s.finset, a ≤ x ∨ x ≤ a) : S P := by
  classical
  refine ⟨insert a s.finset, ⟨a, Finset.mem_insert_self _ _⟩, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  change x ≤ y ∨ y ≤ x
  rcases Finset.mem_insert.mp hx with he | hx
  · rw [he]
    rcases Finset.mem_insert.mp hy with he' | hy
    · exact Or.inl he'.symm.le
    · exact h y hy
  · rcases Finset.mem_insert.mp hy with he | hy
    · rw [he]
      exact (h x hx).symm
    · exact chain_compare s hx hy

open Classical in
private def eraseChain (a : P) (s : S P) (h : (s.finset.erase a).Nonempty) : S P := by
  classical
  exact ⟨s.finset.erase a, h, fun x y =>
    chain_compare s (Finset.mem_erase.mp x.property).2 (Finset.mem_erase.mp y.property).2⟩

open Classical in
/-- The cone apex belongs only to the cone side. Its base consists exactly of
the overlap, and the retained retraction identifies that overlap with the horn. -/
structure ConeDecomposition (X : Type) [PartialOrder X] (Q H : Set (S X)) where
  A : Set (S X)
  C : Set (S X)
  lowerA : IsLowerSet A
  lowerC : IsLowerSet C
  cover : ∀ s, s ∈ A ∨ s ∈ C
  old_subset : Q ⊆ A
  apex : X
  apex_mem : singletonChain apex ∈ C
  base_exact : ∀ s, s ∈ A ∩ C ↔ s ∈ C ∧ apex ∉ s.finset
  cone : ∀ s ∈ C, ∃ t ∈ C, t.finset = insert apex s.finset
  retract : FixedOrderMaps A Q
  fence : FixedFence (FixedOrderMaps.inclusion A Q) retract
  lands : ∀ s : A, retract.val s ∈ Q
  baseIso : (A ∩ C : Set (S X)) ≃o H
  baseIso_eq : ∀ b, (baseIso b).val = retract.val ⟨b.val, b.property.1⟩

namespace ConeDecomposition

variable {Q H : Set (S X)} (d : ConeDecomposition X Q H)

private def M : Set (S X) := {s | s ∈ d.C ∧ s ≠ singletonChain d.apex}

private def N : Set (S X) := {s | s ∈ d.C ∧ d.apex ∈ s.finset}

private theorem tip_le {s : S X} (hs : s ∈ d.N) : singletonChain d.apex ≤ s :=
  Finset.singleton_subset_iff.mpr hs.2

private theorem split (s : S (S X)) (hs : s ∈ SB d.C) : s ∈ SB d.M ∨ s ∈ SB d.N := by
  by_cases ht : singletonChain d.apex ∈ s.finset
  · refine Or.inr (fun x hx => ⟨hs x hx, ?_⟩)
    have hle : singletonChain d.apex ≤ x :=
      (chain_compare s ht hx).elim id (fun h => isMin_singletonChain d.apex h)
    exact hle (Finset.mem_singleton_self _)
  · exact Or.inl (fun x hx => ⟨hs x hx, fun h => ht (h ▸ hx)⟩)

private theorem old_inter_M : d.A ∩ d.M = d.A ∩ d.C := by
  ext s
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · intro hs
    refine ⟨hs.1, hs.2, fun he => ((d.base_exact s).mp hs).2 ?_⟩
    rw [he]
    exact Finset.mem_singleton_self _

private theorem old_disjoint_N {s : S X} (ha : s ∈ d.A) (hn : s ∈ d.N) : False :=
  ((d.base_exact s).mp ⟨ha, hn.1⟩).2 hn.2

open Classical in
private theorem erased_nonempty (s : d.M) : (s.val.finset.erase d.apex).Nonempty := by
  classical
  by_contra hn
  apply s.property.2
  apply NonemptyFiniteChains.ext
  change s.val.finset = {d.apex}
  have hsub : s.val.finset ⊆ {d.apex} := by
    intro x hx
    apply Finset.mem_singleton.mpr
    by_contra hne
    exact hn ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩⟩
  obtain ⟨x, hx⟩ := s.val.nonempty
  have he := Finset.mem_singleton.mp (hsub hx)
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (he ▸ hx))

open Classical in
private def eraseApex : d.M →o S X where
  toFun s := eraseChain d.apex s.val (d.erased_nonempty s)
  monotone' := fun _ _ h => Finset.erase_subset_erase _ h

open Classical in
private theorem erase_le (s : d.M) : d.eraseApex s ≤ s.val :=
  Finset.erase_subset _ _

open Classical in
private theorem erase_lands (s : d.M) : d.eraseApex s ∈ d.A ∩ d.C := by
  apply (d.base_exact _).mpr
  exact ⟨d.lowerC (d.erase_le s) s.property.1, fun ht => (Finset.mem_erase.mp ht).1 rfl⟩

private theorem erase_fixed (s : d.M) (hs : s.val ∈ d.A ∩ d.C) :
    d.eraseApex s = s.val := by
  classical
  apply NonemptyFiniteChains.ext
  exact Finset.erase_eq_of_notMem ((d.base_exact _).mp hs).2

private def coneFace (s : (d.A ∩ d.C : Set (S X))) : S X := (d.cone s.val s.property.2).choose

private theorem coneFace_mem (s : (d.A ∩ d.C : Set (S X))) : d.coneFace s ∈ d.C :=
  (d.cone s.val s.property.2).choose_spec.1

open Classical in
private theorem coneFace_finset (s : (d.A ∩ d.C : Set (S X))) :
    (d.coneFace s).finset = insert d.apex s.val.finset :=
  (d.cone s.val s.property.2).choose_spec.2

open Classical in
private def interfaceIso : (d.M ∩ d.N : Set (S X)) ≃o (d.A ∩ d.C : Set (S X)) where
  toFun s := ⟨d.eraseApex ⟨s.val, s.property.1⟩, d.erase_lands ⟨s.val, s.property.1⟩⟩
  invFun s := ⟨d.coneFace s, by
    have hC := d.coneFace_mem s
    have hfin := d.coneFace_finset s
    refine ⟨⟨hC, ?_⟩, hC, ?_⟩
    · intro he
      obtain ⟨x, hx⟩ := s.val.nonempty
      have hne : x ≠ d.apex := fun h => ((d.base_exact _).mp s.property).2 (h ▸ hx)
      have hmem : x ∈ insert d.apex s.val.finset := Finset.mem_insert_of_mem hx
      rw [← hfin, he] at hmem
      exact hne (Finset.mem_singleton.mp hmem)
    · rw [hfin]
      exact Finset.mem_insert_self _ _⟩
  left_inv s := by
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    change (d.coneFace ⟨d.eraseApex ⟨s.val, s.property.1⟩,
      d.erase_lands ⟨s.val, s.property.1⟩⟩).finset = s.val.finset
    rw [d.coneFace_finset]
    exact Finset.insert_erase s.property.2.2
  right_inv s := by
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    change (d.coneFace s).finset.erase d.apex = s.val.finset
    rw [d.coneFace_finset]
    exact Finset.erase_insert ((d.base_exact _).mp s.property).2
  map_rel_iff' := by
    classical
    intro s t
    change s.val.finset.erase d.apex ⊆ t.val.finset.erase d.apex ↔ s.val.finset ⊆ t.val.finset
    constructor
    · intro h x hx
      by_cases he : x = d.apex
      · exact he.symm ▸ t.property.2.2
      · exact (Finset.mem_erase.mp (h (Finset.mem_erase.mpr ⟨he, hx⟩))).2
    · exact Finset.erase_subset_erase _

private theorem subdivided_interface (s : S (S X)) :
    s ∈ (SB d.A ∪ SB d.M) ∩ SB d.N ↔
      s ∈ SB d.N ∧ singletonChain d.apex ∉ s.finset := by
  constructor
  · rintro ⟨ha | hm, hn⟩
    · obtain ⟨x, hx⟩ := s.nonempty
      exact (d.old_disjoint_N (ha x hx) (hn x hx)).elim
    · exact ⟨hn, fun ht => (hm _ ht).2 rfl⟩
  · rintro ⟨hn, ht⟩
    exact ⟨Or.inr (fun x hx => ⟨(hn x hx).1, fun h => ht (h ▸ hx)⟩), hn⟩

private theorem subdivided_interface_eq :
    (SB d.A ∪ SB d.M) ∩ SB d.N = SB (d.M ∩ d.N) := by
  ext s
  rw [d.subdivided_interface s, ← lift_inter]
  exact ⟨fun h => ⟨fun x hx => ⟨(h.1 x hx).1, fun he => h.2 (he ▸ hx)⟩, h.1⟩,
    fun h => ⟨h.2, fun ht => (h.1 _ ht).2 rfl⟩⟩

private def subdividedBaseIso :
    ((SB d.A ∪ SB d.M) ∩ SB d.N : Set (S (S X))) ≃o SB H :=
  let h := d.subdivided_interface_eq
  let relabel : ((SB d.A ∪ SB d.M) ∩ SB d.N : Set (S (S X))) ≃o SB (d.M ∩ d.N) :=
    { toFun := fun s => ⟨s.val, h ▸ s.property⟩
      invFun := fun s => ⟨s.val, h.symm ▸ s.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_rel_iff' := Iff.rfl }
  relabel.trans ((regionChains (d.M ∩ d.N)).trans
    ((chainsCongr (d.interfaceIso.trans d.baseIso)).trans (regionChains H).symm))

private theorem mem_subdividedBaseIso
    (s : ((SB d.A ∪ SB d.M) ∩ SB d.N : Set (S (S X)))) (y : S X) :
    y ∈ (d.subdividedBaseIso s).val.finset ↔
      ∃ x : (d.M ∩ d.N : Set (S X)), x.val ∈ s.val.finset ∧
        (d.baseIso (d.interfaceIso x)).val = y := by
  change y ∈ (((onRegion (d.M ∩ d.N) ⟨s.val, d.subdivided_interface_eq ▸ s.property⟩).map
    (homOfIso (d.interfaceIso.trans d.baseIso))).map (inclusion H)).finset ↔ _
  simp only [NonemptyFiniteChains.mem_map_iff, mem_onRegion]
  constructor
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d.baseIso (d.interfaceIso x), ⟨x, hx, rfl⟩, rfl⟩

/-- Ordinary chain subdivision preserves the cone decomposition, including
the fixed-relative retraction and the order isomorphism on its exact base. -/
def subdivide [Finite X] : ConeDecomposition (S X) (SB Q) (SB H) := by
  classical
  let U := SB d.A
  let V := SB d.M
  let E := SB Q
  let F := SB (d.A ∩ d.C)
  have hU : IsLowerSet U := liftedRegion_lower _
  have hV : IsLowerSet V := liftedRegion_lower _
  have hE : E ⊆ U := lift_mono d.old_subset
  have hF : U ∩ V ⊆ F := by
    change SB d.A ∩ SB d.M ⊆ _
    rw [lift_inter, d.old_inter_M]
  let strip : FixedOrderMaps d.M (d.A ∩ d.C) := ⟨d.eraseApex, d.erase_fixed⟩
  have strip_path : FixedFence (FixedOrderMaps.inclusion V F) (liftRow strip) := by
    rw [← liftRow_inclusion]
    apply lift_fixedFence
    exact .symm _ _ (.rel _ _ d.erase_le)
  let stripped := glueInclusion hU hV hE hF (liftRow strip)
  have stripped_path : FixedFence (FixedOrderMaps.inclusion (U ∪ V) E) stripped := by
    rw [← glue_inclusion hU hV hE hF]
    exact glue_fence hU hV hE hF strip_path
  have stripped_lands (s : (U ∪ V : Set (S (S X)))) : stripped.val s ∈ U := by
    rcases s.property with hs | hs
    · rw [glue_on_left _ s hs]
      exact hs
    · rw [glue_on_right _ s hs]
      exact liftMap_lands d.eraseApex (fun x => (d.erase_lands x).1) ⟨s.val, hs⟩
  let intoU : (U ∪ V : Set (S (S X))) →o U :=
    ⟨fun s => ⟨stripped.val s, stripped_lands s⟩, stripped.val.monotone⟩
  let extend (f : FixedOrderMaps U E) : FixedOrderMaps (U ∪ V) E :=
    ⟨f.val.comp intoU, by
      intro s hs
      have he : (intoU s).val = s.val := stripped.property s hs
      have hfixed : (intoU s).val ∈ E := he.symm ▸ hs
      exact (f.property (intoU s) hfixed).trans he⟩
  have extend_start : extend (FixedOrderMaps.inclusion U E) = stripped := by
    apply Subtype.ext
    apply OrderHom.ext
    funext s
    rfl
  have path_on_U : FixedFence (FixedOrderMaps.inclusion U E) (liftRow d.retract) := by
    rw [← liftRow_inclusion]
    exact lift_fixedFence d.fence
  have extend_path : FixedFence stripped (extend (liftRow d.retract)) := by
    rw [← extend_start]
    exact fixedFence_map extend (fun _ _ h s => OrderHom.le_def.mp h (intoU s)) path_on_U
  refine
    { A := U ∪ V
      C := SB d.N
      lowerA := fun _ _ h hs => hs.elim (fun hu => Or.inl (hU h hu))
        (fun hv => Or.inr (hV h hv))
      lowerC := liftedRegion_lower _
      cover := ?_
      old_subset := fun _ hs => Or.inl (hE hs)
      apex := singletonChain d.apex
      apex_mem := ?_
      base_exact := d.subdivided_interface
      cone := ?_
      retract := extend (liftRow d.retract)
      fence := .trans _ _ _ stripped_path extend_path
      lands := fun s => liftMap_lands d.retract.val d.lands (intoU s)
      baseIso := d.subdividedBaseIso
      baseIso_eq := ?_ }
  · intro s
    rcases lift_union_of_lower d.lowerA d.lowerC d.cover s with ha | hc
    · exact Or.inl (Or.inl ha)
    · rcases d.split s hc with hm | hn
      · exact Or.inl (Or.inr hm)
      · exact Or.inr hn
  · intro x hx
    have hx' : x = singletonChain d.apex := Finset.mem_singleton.mp hx
    subst x
    exact ⟨d.apex_mem, Finset.mem_singleton_self _⟩
  · intro s hs
    let tip := singletonChain d.apex
    let t := insertChain tip s (fun x hx => Or.inl (d.tip_le (hs x hx)))
    refine ⟨t, ?_, rfl⟩
    intro x hx
    change x ∈ insert tip s.finset at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨d.apex_mem, Finset.mem_singleton_self _⟩
    · exact hs x hx
  · intro s
    let v : (U ∪ V : Set (S (S X))) := ⟨s.val, s.property.1⟩
    have hJ : s.val ∈ SB (d.M ∩ d.N) := d.subdivided_interface_eq ▸ s.property
    have hV' : s.val ∈ V := fun x hx => (hJ x hx).1
    have hv : (intoU v).val = liftMap d.eraseApex ⟨s.val, hV'⟩ :=
      glue_on_right _ v hV'
    change (d.subdividedBaseIso s).val = liftMap d.retract.val (intoU v)
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro y
    rw [d.mem_subdividedBaseIso, mem_liftMap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      let b : (d.A ∩ d.C : Set (S X)) := d.interfaceIso x
      refine ⟨⟨b.val, b.property.1⟩, ?_, (d.baseIso_eq b).symm⟩
      rw [hv, mem_liftMap]
      exact ⟨⟨x.val, x.property.1⟩, hx, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [hv, mem_liftMap] at hb
      obtain ⟨x, hx, he⟩ := hb
      let z : (d.M ∩ d.N : Set (S X)) := ⟨x.val, hJ x.val hx⟩
      let c : (d.A ∩ d.C : Set (S X)) := d.interfaceIso z
      have hc : (⟨c.val, c.property.1⟩ : d.A) = b := Subtype.ext he
      exact ⟨z, hx, (d.baseIso_eq c).trans (congrArg d.retract.val hc)⟩

end ConeDecomposition

/-- At depth one, the chains of the retained region and the chains below or
through the new maximum form the initial cone decomposition. -/
def ConeDecomposition.ofAdjoinedMaximum {Q : Set P} (t : P)
    (hQ : IsLowerSet Q) (ht : t ∉ Q) (hcover : ∀ x : P, x ∈ Q ∨ x = t) :
    ConeDecomposition P (SB Q) (SB (Set.Iio t)) := by
  classical
  let H := Set.Iio t
  let T : Set P := Set.Iic t
  have hH : H ⊆ Q := by
    intro x hx
    exact (hcover x).resolve_right (ne_of_lt hx)
  have hbase (s : S P) : s ∈ SB Q ∩ SB T ↔ s ∈ SB T ∧ t ∉ s.finset := by
    constructor
    · exact fun h => ⟨h.2, fun hs => ht (h.1 t hs)⟩
    · rintro ⟨hT, hs⟩
      exact ⟨fun x hx => (hcover x).resolve_right (fun he => hs (he ▸ hx)), hT⟩
  have htrace (s : S P) : s ∈ SB Q ∩ SB T ↔ s ∈ SB H := by
    constructor
    · intro hs x hx
      exact lt_of_le_of_ne (hs.2 x hx) (fun he => ht (he ▸ hs.1 x hx))
    · exact fun hs => ⟨fun x hx => hH (hs x hx), fun x hx => (hs x hx).le⟩
  refine
    { A := SB Q
      C := SB T
      lowerA := liftedRegion_lower _
      lowerC := liftedRegion_lower _
      cover := ?_
      old_subset := fun _ h => h
      apex := t
      apex_mem := ?_
      base_exact := hbase
      cone := ?_
      retract := FixedOrderMaps.inclusion _ _
      fence := .refl _
      lands := fun s => s.property
      baseIso :=
        { toFun := fun s => ⟨s.val, (htrace s.val).mp s.property⟩
          invFun := fun s => ⟨s.val, (htrace s.val).mpr s.property⟩
          left_inv := fun s => Subtype.ext rfl
          right_inv := fun s => Subtype.ext rfl
          map_rel_iff' := Iff.rfl }
      baseIso_eq := fun _ => rfl }
  · intro s
    refine lift_union_of_lower hQ (fun _ _ h hy => h.trans hy) ?_ s
    intro x
    exact (hcover x).imp id (fun h => h.le)
  · intro x hx
    exact (Finset.mem_singleton.mp hx).le
  · intro s hs
    let u := insertChain t s (fun x hx => Or.inr (hs x hx))
    refine ⟨u, ?_, rfl⟩
    intro x hx
    change x ∈ insert t s.finset at hx
    exact (Finset.mem_insert.mp hx).elim (fun h => h.le) (fun h => hs x h)

/-- The ordinary subdivision of a region in the ambient chain poset. -/
def iteratedRegion (U : Set (S X)) :
    (n : ℕ) → (let P := finiteSpaceSubdivision X n
               letI : PartialOrder P.1 := P.2
               Set (S P.1))
  | 0 => U
  | n + 1 =>
    let P := finiteSpaceSubdivision X n
    letI : PartialOrder P.1 := P.2
    show Set (S (S P.1)) from @liftedRegion (S P.1) inferInstance (iteratedRegion U n)

/-- The retained side and the cone with its exact base persist through any
number of further ordinary subdivisions. -/
def ConeDecomposition.iterate [Finite X] {Q H : Set (S X)}
    (d : ConeDecomposition X Q H) (n : ℕ) :
    let P := finiteSpaceSubdivision X n
    letI : PartialOrder P.1 := P.2
    ConeDecomposition P.1 (iteratedRegion Q n) (iteratedRegion H n) := by
  induction n with
  | zero => exact d
  | succ n ih =>
    let P := finiteSpaceSubdivision X n
    letI : PartialOrder P.1 := P.2
    letI : Finite P.1 := finiteAtDepth n
    exact ih.subdivide

namespace ConeDecomposition

open TrimmedAnchorMixedCone (Attachment flagRegion)
open BarycentricGraphDistance (Face)
open ConnectedCategoryGraft (Categorical)

variable {Q H : Set (S X)} (d : ConeDecomposition X Q H)

/-- The simplicial complex whose faces are the supports of chains in the cone region. -/
def complex : PreAbstractSimplicialComplex X where
  faces := {σ | ∃ s : d.C, s.val.finset = σ}
  isRelLowerSet_faces := by
    rintro σ ⟨s, rfl⟩
    refine ⟨s.val.nonempty, fun τ hτ hn => ?_⟩
    let t : S X := ⟨τ, hn, fun x y => chain_compare s.val (hτ x.property) (hτ y.property)⟩
    exact ⟨⟨t, d.lowerC (show t ≤ s.val from hτ) s.property⟩, rfl⟩

/-- A face of the cone complex is the corresponding chain of the cone region. -/
def chart : Face d.complex ≃o d.C where
  toFun s := s.property.choose
  invFun s := ⟨s.val.finset, ⟨s, rfl⟩⟩
  left_inv s := Subtype.ext s.property.choose_spec
  right_inv s := Subtype.ext (NonemptyFiniteChains.ext
    ((show ∃ t : d.C, t.val.finset = s.val.finset from ⟨s, rfl⟩).choose_spec))
  map_rel_iff' := by
    intro s t
    change s.property.choose.val.finset ⊆ t.property.choose.val.finset ↔ s.val ⊆ t.val
    rw [s.property.choose_spec, t.property.choose_spec]

private theorem chart_support (s : Face d.complex) : (d.chart s).val.finset = s.val :=
  s.property.choose_spec

private def chartBase : {s : Face d.complex // d.apex ∉ s.val} ≃o (d.A ∩ d.C : Set (S X)) where
  toFun s := ⟨(d.chart s.val).val, (d.base_exact _).mpr
    ⟨(d.chart s.val).property, fun h => s.property (d.chart_support s.val ▸ h)⟩⟩
  invFun s := ⟨d.chart.symm ⟨s.val, s.property.2⟩, (d.base_exact _).mp s.property |>.2⟩
  left_inv s := Subtype.ext (d.chart.symm_apply_apply s.val)
  right_inv s := by
    apply Subtype.ext
    exact congrArg (fun z : d.C => z.val) (d.chart.apply_symm_apply ⟨s.val, s.property.2⟩)
  map_rel_iff' := d.chart.le_iff_le

/-- Read the cone decomposition as an attachment chart over its actual old interface. -/
def attachment [DecidableEq X] : Attachment (S X) X where
  cone := d.complex
  apex := d.apex
  retained := d.A
  coneRegion := d.C
  old := Q
  interface := H
  faceIso := d.chart
  retainedLower := d.lowerA
  coneLower := d.lowerC
  cover := d.cover
  oldSubset := d.old_subset
  base_iff s := by
    rw [← d.chart_support s]
    exact ⟨fun ha => ((d.base_exact _).mp ⟨ha, (d.chart s).property⟩).2,
      fun hn => ((d.base_exact _).mpr ⟨(d.chart s).property, hn⟩).1⟩
  insert_apex s := by
    obtain ⟨t, ht, h⟩ := d.cone _ (d.chart s).property
    refine ⟨⟨t, ht⟩, ?_⟩
    change t.finset = insert d.apex s.val
    apply Finset.ext
    intro x
    rw [h]
    simp only [Finset.mem_insert, d.chart_support s]
  retract := d.retract
  retractFence := d.fence
  retractLand := d.lands
  interfaceIso := d.chartBase.trans d.baseIso
  interface_eq s hs := d.baseIso_eq (d.chartBase ⟨s, hs⟩)

/-- At any fixed positive depth, two further subdivisions transport a categorical
two-cover under the full-trace and exclusive-anchor conditions. The base chart
is identified by the retained retraction with the actual subdivided strict lower
set of the adjoined maximum. -/
theorem exact_two_cover_of_adjoined_maximum [Finite X] {Q₀ : Set X}
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
      ∀ v : P.1, a.trace (E true) {v} →
      (∀ s : Face a.cone, a.apex ∉ s.val →
        (∀ u ∈ s.val, ¬ a.trace (E false) {u}) → a.trace (E true) (insert v s.val)) →
      ∃ U : Bool → Set (S (S (S P.1))), (∀ s, ∃ i, s ∈ U i) ∧
        ∀ i, IsLowerSet (U i) ∧ Categorical (U i) ∧
          U i ∩ flagRegion a.old = flagRegion (E i) ∧
          RelativeOrderFence (U i) (flagRegion (E i)) := by
  dsimp only
  intro dec E hE lower cover cat full v hv span
  let P := finiteSpaceSubdivision X n
  let : PartialOrder P.1 := P.2
  let : Finite P.1 := finiteAtDepth n
  let : Finite (S P.1) := finiteChains
  exact ((ofAdjoinedMaximum t hQ ht hcover).iterate n).attachment.trimmed_anchor_exact_two_cover
    E hE lower cover cat full v hv span

end ConeDecomposition

end D5.S3.Topology.StableCategory.InheritedDepthConeAttachment
