/- GID: D5/S3/Geometry/Gluing/TruncatedTetrahedronRelativeCW
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/TruncatedTetrahedronRelativeCW
   mirror-E: none(waiver:relative-cw-topological-construction)
   anchors: [mathlib/module/Mathlib.Topology.CWComplex.Classical.Finite]
   utility: none
   digest: Finite raw tetrahedron pairings carry actual relative cells above their closed face skeleton. -/

import D5.S3.Geometry.Gluing.RawFaceLinkPathConnected
import D5.S3.Geometry.Gluing.ActualLinkAffineFan
import D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

open Set Metric Topology
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan
  (TruncatedTetrahedron TruncatedPoint)
open D5.S3.Geometry.Gluing.RawFaceLinkPathConnected (sigma frame chi)
open D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
open private paired_twice from D5.S3.Geometry.Gluing.RawFaceLinkPathConnected

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

private theorem frame_at (f : Fin 4) : frame f f = none := by
  change (Equiv.optionCongr (chi f)) ((finSuccEquiv' f) f) = none
  exact congrArg (Equiv.optionCongr (chi f)) (finSuccEquiv'_at f)

private theorem sigma_face (P : RawFacePairing T) (x : T × Fin 4) :
    sigma P x x.2 = (P.facePair x).2 := by
  apply (frame (P.facePair x).2).injective
  change (frame (P.facePair x).2)
    ((frame (P.facePair x).2).symm
      ((Equiv.optionCongr (P.faceMap x)) (frame x.2 x.2))) = _
  simpa only [Equiv.apply_symm_apply, frame_at]

private theorem sigma_inverse (P : RawFacePairing T) (x : T × Fin 4) :
    sigma P (P.facePair x) = (sigma P x).symm := by
  have hm : P.faceMap (P.facePair x) = (P.faceMap x).symm := by
    apply Equiv.ext
    intro n
    have h := P.mapInverse x ((P.faceMap x).symm n)
    simpa using h
  ext i
  simp [sigma, paired_twice P x, hm]

/-- The coordinate transport on the unchanged retained tetrahedra. -/
def truncatedMove (P : RawFacePairing T) (f : Fin 4) (a : TruncatedPoint T) :
    TruncatedPoint T :=
  ((P.facePair (a.1,f)).1, ⟨fun i => a.2.val ((sigma P (a.1,f)).symm i),
    (fun i => a.2.property.1 _),
    ((sigma P (a.1,f)).symm.sum_comp a.2.val).trans a.2.property.2⟩)

/-- Only zero coordinates enable original face identifications. -/
def TruncatedStep (P : RawFacePairing T) (a b : TruncatedPoint T) : Prop :=
  ∃ f : Fin 4, a.2.val f = 0 ∧ b = truncatedMove P f a

/-- The full original equivalence closure, with its quotient topology. -/
abbrev TruncatedQuotient (P : RawFacePairing T) :=
  Quotient (Relation.EqvGen.setoid (TruncatedStep P))

@[reducible] def q (P : RawFacePairing T) : TruncatedPoint T → TruncatedQuotient P :=
  @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P))

private theorem continuous_q (P : RawFacePairing T) : Continuous (q P) :=
  continuous_quotient_mk'

private theorem truncated_move_inverse (P : RawFacePairing T)
    (a : TruncatedPoint T) (f : Fin 4) :
    truncatedMove P (P.facePair (a.1,f)).2 (truncatedMove P f a) = a := by
  have ht : ((P.facePair (a.1,f)).1, (P.facePair (a.1,f)).2) = P.facePair (a.1,f) := rfl
  apply Prod.ext
  · change (P.facePair ((P.facePair (a.1,f)).1, (P.facePair (a.1,f)).2)).1 = a.1
    rw [ht, paired_twice]
  · apply Subtype.ext
    funext i
    change a.2.val ((sigma P (a.1,f)).symm
      ((sigma P ((P.facePair (a.1,f)).1, (P.facePair (a.1,f)).2)).symm i)) = a.2.val i
    rw [ht, sigma_inverse]
    simp

private theorem truncated_step_symmetric (P : RawFacePairing T)
    {a b : TruncatedPoint T} (h : TruncatedStep P a b) : TruncatedStep P b a := by
  obtain ⟨f,hf,rfl⟩ := h
  refine ⟨(P.facePair (a.1,f)).2, ?_, (truncated_move_inverse P a f).symm⟩
  change a.2.val ((sigma P (a.1,f)).symm (P.facePair (a.1,f)).2) = 0
  rw [← sigma_face P (a.1,f), Equiv.symm_apply_apply]
  exact hf

private theorem original_truncated_relation_closed (P : RawFacePairing T) :
    IsClosed {ab : TruncatedPoint T × TruncatedPoint T |
      Relation.EqvGen (TruncatedStep P) ab.1 ab.2} := by
  let S : Set (Fin 4 → ℝ) := {a |
    (∀ i, 0 ≤ a i ∧ a i ≤ 3/4) ∧ (∑ i, a i) = 1}
  have hI : ∀ (rho : Equiv.Perm (Fin 4)) (z : Fin 4 → ℝ),
      z ∈ S → (fun i => z (rho.symm i)) ∈ S := by
    intro rho z hz
    exact ⟨fun i => hz.1 _, (rho.symm.sum_comp z).trans hz.2⟩
  exact (uniform_transport_and_closed_relation S hI
    (fun x : T × Fin 4 => (P.facePair x).1) (sigma P)).2.2

private theorem closed_quotient_map {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hR : IsClosed {ab : X × X | r ab.1 ab.2}) :
    IsClosedMap (@Quotient.mk' X r) := by
  intro C hC
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have he : (@Quotient.mk' X r) ⁻¹' ((@Quotient.mk' X r) '' C) =
      Prod.fst '' ({ab : X × X | r ab.1 ab.2} ∩ Prod.snd ⁻¹' C) := by
    ext x
    constructor
    · rintro ⟨z,hz,heq⟩
      exact ⟨(x,z),⟨Quotient.exact heq.symm,hz⟩,rfl⟩
    · rintro ⟨⟨x',z⟩,⟨hr,hz⟩,heq⟩
      dsimp at heq
      subst x'
      exact ⟨z,hz,Quotient.sound (r.symm hr)⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ (hR.inter (hC.preimage continuous_snd))

private theorem compact_closed_quotient_t2 {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (r : Setoid X)
    (hR : IsClosed {ab : X × X | r ab.1 ab.2}) : T2Space (Quotient r) := by
  let q : X → Quotient r := @Quotient.mk' X r
  have hc : IsClosedMap q := closed_quotient_map r hR
  refine ⟨?_⟩
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  have hx : IsClosed {z : X | r z x} :=
    hR.preimage (continuous_id.prodMk continuous_const)
  have hy : IsClosed {z : X | r z y} :=
    hR.preimage (continuous_id.prodMk continuous_const)
  have hd : Disjoint {z : X | r z x} {z : X | r z y} := by
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hxy (Quotient.sound (r.trans (r.symm hzx) hzy))
  obtain ⟨U,V,hU,hV,hxU,hyV,hUV⟩ := normal_separation hx hy hd
  refine ⟨(q '' Uᶜ)ᶜ,(q '' Vᶜ)ᶜ,(hc _ hU.isClosed_compl).isOpen_compl,
    (hc _ hV.isClosed_compl).isOpen_compl,?_,?_,?_⟩
  · rintro ⟨z,hz,he⟩
    exact hz (hxU (Quotient.exact he))
  · rintro ⟨z,hz,he⟩
    exact hz (hyV (Quotient.exact he))
  · apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨w,rfl⟩ := Quotient.mk'_surjective z
    have hwU : w ∈ U := by
      by_contra h
      exact hzU ⟨w,h,rfl⟩
    have hwV : w ∈ V := by
      by_contra h
      exact hzV ⟨w,h,rfl⟩
    exact Set.disjoint_left.mp hUV hwU hwV


private theorem original_truncated_compact : CompactSpace (TruncatedPoint T) := by
  let S : Set (Fin 4 → ℝ) := {a |
    (∀ i, 0 ≤ a i ∧ a i ≤ 3/4) ∧ (∑ i, a i) = 1}
  have hB : IsClosed {a : Fin 4 → ℝ | ∀ i, 0 ≤ a i ∧ a i ≤ 3/4} := by
    have he : {a : Fin 4 → ℝ | ∀ i, 0 ≤ a i ∧ a i ≤ 3/4} =
        ⋂ i : Fin 4, {a : Fin 4 → ℝ | 0 ≤ a i ∧ a i ≤ 3/4} := by ext a; simp
    rw [he]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  have hS : IsClosed S := hB.inter (isClosed_eq (by fun_prop) continuous_const)
  have hK : IsCompact S :=
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 4 => (0 : ℝ))
      (fun _ : Fin 4 => (3/4 : ℝ)))).of_isClosed_subset hS (by
        intro a ha
        exact ⟨fun i => (ha.1 i).1,fun i => (ha.1 i).2⟩)
  letI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hK
  exact inferInstanceAs (CompactSpace (T × ↥S))

private theorem original_truncated_quotient_t2 (P : RawFacePairing T) :
    T2Space (TruncatedQuotient P) := by
  letI : CompactSpace (TruncatedPoint T) := original_truncated_compact
  exact compact_closed_quotient_t2 _ (original_truncated_relation_closed P)

local instance (P : RawFacePairing T) : T2Space (TruncatedQuotient P) :=
  original_truncated_quotient_t2 P

def Interior (a : TruncatedPoint T) : Prop := ∀ i, a.2.val i ≠ 0

def FaceInterior (a : TruncatedPoint T) (f : Fin 4) : Prop :=
  a.2.val f = 0 ∧ ∀ g, a.2.val g = 0 → g = f

private theorem step_unique (P : RawFacePairing T) {a b c : TruncatedPoint T} {f : Fin 4}
    (ha : FaceInterior a f) (hab : TruncatedStep P a b) (hac : TruncatedStep P a c) :
    b = c := by
  obtain ⟨g,hg,rfl⟩ := hab
  obtain ⟨k,hk,rfl⟩ := hac
  rw [ha.2 g hg,ha.2 k hk]

private theorem step_face (P : RawFacePairing T) {a b : TruncatedPoint T} {f : Fin 4}
    (ha : FaceInterior a f) (hab : TruncatedStep P a b) :
    FaceInterior b (P.facePair (a.1,f)).2 := by
  obtain ⟨g,hg,rfl⟩ := hab
  have hgf := ha.2 g hg
  subst g
  constructor
  · change a.2.val ((sigma P (a.1,f)).symm (P.facePair (a.1,f)).2) = 0
    rw [← sigma_face P (a.1,f),Equiv.symm_apply_apply]
    exact ha.1
  · intro g hg
    change a.2.val ((sigma P (a.1,f)).symm g) = 0 at hg
    have hh := ha.2 _ hg
    calc g = sigma P (a.1,f) ((sigma P (a.1,f)).symm g) :=
           (Equiv.apply_symm_apply _ _).symm
         _ = sigma P (a.1,f) f := congrArg (sigma P _) hh
         _ = (P.facePair (a.1,f)).2 := sigma_face P _

private theorem face_chain_normal_form (P : RawFacePairing T)
    (a b : TruncatedPoint T) (f : Fin 4) (ha : FaceInterior a f) :
    Relation.EqvGen (TruncatedStep P) a b ↔ b = a ∨ TruncatedStep P a b := by
  have forward {x y : TruncatedPoint T} (hxy : TruncatedStep P x y)
      (hx : x = a ∨ TruncatedStep P a x) : y = a ∨ TruncatedStep P a y := by
    rcases hx with rfl | hx
    · exact Or.inr hxy
    · exact Or.inl (step_unique P (step_face P ha hx) hxy (truncated_step_symmetric P hx))
  have inv : ∀ {x y : TruncatedPoint T}, Relation.EqvGen (TruncatedStep P) x y →
      ((x = a ∨ TruncatedStep P a x) ↔ (y = a ∨ TruncatedStep P a y)) := by
    intro x y h
    induction h with
    | rel x y h => exact ⟨forward h,forward (truncated_step_symmetric P h)⟩
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · intro h
    exact (inv h).mp (Or.inl rfl)
  · rintro (rfl | h)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h

private theorem interior_normal_form (P : RawFacePairing T)
    (a b : TruncatedPoint T) (ha : Interior a) :
    Relation.EqvGen (TruncatedStep P) a b ↔ b = a := by
  have forward {x y : TruncatedPoint T} (hxy : TruncatedStep P x y)
      (hx : x = a) : y = a := by
    subst x
    obtain ⟨f,hf,_⟩ := hxy
    exact False.elim (ha f hf)
  have inv : ∀ {x y : TruncatedPoint T}, Relation.EqvGen (TruncatedStep P) x y →
      (x = a ↔ y = a) := by
    intro x y h
    induction h with
    | rel x y h => exact ⟨forward h,forward (truncated_step_symmetric P h)⟩
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · intro h
    exact (inv h).mp rfl
  · intro h
    subst b
    exact Relation.EqvGen.refl _

private theorem paired_face_distinct (P : RawFacePairing T) (a : TruncatedPoint T)
    (f : Fin 4) (ha : FaceInterior a f) : truncatedMove P f a ≠ a := by
  intro he
  have hs : TruncatedStep P a (truncatedMove P f a) := ⟨f,ha.1,rfl⟩
  have hb := step_face P ha hs
  rw [he] at hb
  have hg := ha.2 _ hb.1
  have ht : (P.facePair (a.1,f)).1 = a.1 := congrArg Prod.fst he
  exact P.pairFixedFree (a.1,f) (Prod.ext ht hg)

private theorem actual_face_classification (P : RawFacePairing T)
    (a b : TruncatedPoint T) (f : Fin 4) (ha : FaceInterior a f) :
    truncatedMove P f a ≠ a ∧
      (Relation.EqvGen (TruncatedStep P) a b ↔ b = a ∨ b = truncatedMove P f a) := by
  refine ⟨paired_face_distinct P a f ha,?_⟩
  rw [face_chain_normal_form P a b f ha]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (step_unique P ha h ⟨f,ha.1,rfl⟩)
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨f,ha.1,rfl⟩

section CompactOpenChart

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

/-- A continuous map of a compact space embeds an open subset if every fiber
meeting that subset is a singleton. No restricted-quotient assertion is used. -/
private theorem compact_open_isEmbedding (f : X → Y) (hf : Continuous f)
    (U : Set X) (hU : IsOpen U)
    (hfiber : ∀ (x : X), x ∈ U → ∀ y : X, f y = f x → y = x) :
    IsEmbedding (fun x : U => f x.val) := by
  let g : U → ↥(f '' U) := fun x => ⟨f x.val, x.val, x.property, rfl⟩
  have hgcont : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hginj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact hfiber y.val y.property x.val (congrArg Subtype.val h)
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgopen : IsOpenMap g := by
    intro V hV
    let W : Set X := Subtype.val '' V
    have hW : IsOpen W := hU.isOpenMap_subtype_val V hV
    have hclosed : IsClosed (f '' Wᶜ) := hf.isClosedMap _ hW.isClosed_compl
    have heq : g '' V =
        (Subtype.val : ↥(f '' U) → Y) ⁻¹' (f '' Wᶜ)ᶜ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
        have hyx := hfiber x.val x.property y he
        exact hy (hyx.symm ▸ (show x.val ∈ W from ⟨x, hx, rfl⟩))
      · intro hz
        obtain ⟨x, hx, hfx⟩ := z.property
        have hxW : x ∈ W := by
          by_contra hn
          exact hz ⟨x, hn, hfx⟩
        obtain ⟨v, hv, hvx⟩ := hxW
        refine ⟨v, hv, Subtype.ext ?_⟩
        change f v.val = z.val
        rw [hvx]
        exact hfx
    rw [heq]
    exact hclosed.isOpen_compl.preimage continuous_subtype_val
  have hg : IsHomeomorph g := ⟨hgcont, hgopen, hginj, hgsurj⟩
  exact IsEmbedding.subtypeVal.comp hg.isEmbedding

end CompactOpenChart

section BallCharacteristic

variable {d : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]

abbrev Disk (d : ℕ) := ↥(closedBall (0 : Fin d → ℝ) 1)
private abbrev OpenDisk (d : ℕ) := ↥(ball (0 : Fin d → ℝ) 1)

/-- The open ball as an open subset of the closed ball, with both inherited
topologies. This contains no assertion about the quotient. -/
private def openDiskInDisk (d : ℕ) : OpenDisk d ≃ₜ
    {x : Disk d // x.val ∈ ball (0 : Fin d → ℝ) 1} where
  toFun x := ⟨⟨x.val, ball_subset_closedBall x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def diskExtend (f : Disk d → Y) : (Fin d → ℝ) → Y :=
  Function.extend Subtype.val f (fun _ => f ⟨0, by simp⟩)

@[simp] private theorem diskExtend_coe (f : Disk d → Y) (x : Disk d) :
    diskExtend f x.val = f x :=
  Subtype.val_injective.extend_apply _ _ x

private theorem continuousOn_diskExtend (f : Disk d → Y) (hf : Continuous f) :
    ContinuousOn (diskExtend f) (closedBall 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (closedBall (0 : Fin d → ℝ) 1).domRestrict (diskExtend f) = f := by
    funext x
    exact diskExtend_coe f x
  rw [he]
  exact hf

private theorem disk_open_isEmbedding (f : Disk d → Y) (hf : Continuous f)
    (hfiber : ∀ (x y : Disk d), x.val ∈ ball 0 1 → f y = f x → y = x) :
    IsEmbedding (fun x : OpenDisk d => diskExtend f x.val) := by
  letI : CompactSpace (Disk d) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have he := compact_open_isEmbedding f hf
    {x : Disk d | x.val ∈ ball 0 1}
    (isOpen_ball.preimage continuous_subtype_val)
    (fun x hx y h => hfiber x y hx h)
  convert he.comp (openDiskInDisk d).isEmbedding using 1
  funext x
  exact diskExtend_coe f ⟨x.val, ball_subset_closedBall x.property⟩

private theorem diskExtend_injOn (f : Disk d → Y) (hf : Continuous f)
    (hfiber : ∀ (x y : Disk d), x.val ∈ ball 0 1 → f y = f x → y = x) :
    InjOn (diskExtend f) (ball 0 1) := by
  intro x hx y hy h
  exact congrArg Subtype.val
    ((disk_open_isEmbedding f hf hfiber).injective
      (show (fun x : OpenDisk d => diskExtend f x.val) ⟨x, hx⟩ =
        (fun x : OpenDisk d => diskExtend f x.val) ⟨y, hy⟩ from h))

/-- The required PartialEquiv, without requiring a closed-cell embedding. -/
private def diskPartial (f : Disk d → Y) (hf : Continuous f)
    (hfiber : ∀ (x y : Disk d), x.val ∈ ball 0 1 → f y = f x → y = x) :
    PartialEquiv (Fin d → ℝ) Y :=
  (diskExtend_injOn f hf hfiber).toPartialEquiv (diskExtend f) (ball 0 1)

private theorem diskPartial_continuousOn (f : Disk d → Y) (hf : Continuous f)
    (hfiber : ∀ (x y : Disk d), x.val ∈ ball 0 1 → f y = f x → y = x) :
    ContinuousOn (diskPartial f hf hfiber) (closedBall 0 1) :=
  continuousOn_diskExtend f hf

private theorem diskPartial_continuousOn_symm (f : Disk d → Y) (hf : Continuous f)
    (hfiber : ∀ (x y : Disk d), x.val ∈ ball 0 1 → f y = f x → y = x) :
    ContinuousOn (diskPartial f hf hfiber).symm (diskPartial f hf hfiber).target := by
  let e := diskPartial f hf hfiber
  let g : OpenDisk d → Y := fun x => e x.val
  have hg : IsEmbedding g := disk_open_isEmbedding f hf hfiber
  let inv : e.target → OpenDisk d := fun y =>
    ⟨e.symm y.val, e.map_target y.property⟩
  have heq : g ∘ inv = (Subtype.val : e.target → Y) := by
    funext y
    exact e.right_inv y.property
  have hi : Continuous inv := hg.continuous_iff.mpr (by
    rw [heq]
    exact continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hi)

end BallCharacteristic

/- Affine-coordinate models. In dimension d we keep d coordinates and recover
   the last coordinate from the actual sum. All interiors below are in R^d. -/

private def residual {d : ℕ} (mass : ℝ) (x : Fin d → ℝ) : ℝ := mass - ∑ i, x i

private def poly (d : ℕ) (mass cap : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ cap) ∧
    0 ≤ residual mass x ∧ residual mass x ≤ cap}

private def strictPoly (d : ℕ) (mass cap : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 < x i ∧ x i < cap) ∧
    0 < residual mass x ∧ residual mass x < cap}

private theorem continuous_residual (d : ℕ) (mass : ℝ) :
    Continuous (residual (d := d) mass) := by unfold residual; fun_prop

private theorem poly_closed (d : ℕ) (mass cap : ℝ) : IsClosed (poly d mass cap) := by
  have hcoords : IsClosed {x : Fin d → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ cap} := by
    have he : {x : Fin d → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ cap} =
        ⋂ i : Fin d, {x | 0 ≤ x i ∧ x i ≤ cap} := by ext x; simp
    rw [he]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  exact hcoords.inter
    ((isClosed_le continuous_const (continuous_residual d mass)).inter
      (isClosed_le (continuous_residual d mass) continuous_const))

private theorem poly_compact (d : ℕ) (mass cap : ℝ) : IsCompact (poly d mass cap) :=
  (isCompact_Icc : IsCompact (Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => cap))).of_isClosed_subset
    (poly_closed d mass cap) (fun _ hx => ⟨fun i => (hx.1 i).1, fun i => (hx.1 i).2⟩)

private theorem poly_convex (d : ℕ) (mass cap : ℝ) : Convex ℝ (poly d mass cap) := by
  intro x hx y hy a b ha hb hab
  have hcap : a * cap + b * cap = cap := by rw [← add_mul, hab, one_mul]
  have hr : residual mass (a • x + b • y) =
      a * residual mass x + b * residual mass y := by
    simp only [residual, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    have hm : a * mass + b * mass = mass := by rw [← add_mul, hab, one_mul]
    nlinarith only [hm]
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ cap
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1)
    · nlinarith only [hcap, mul_le_mul_of_nonneg_left (hx.1 i).2 ha,
        mul_le_mul_of_nonneg_left (hy.1 i).2 hb]
  · rw [hr]
    constructor
    · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
    · nlinarith only [hcap, mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]

private def sumLinear (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

private def massReflection (mass : ℝ) : ℝ ≃ₜ ℝ where
  toFun x := mass - x
  invFun x := mass - x
  left_inv x := by ring
  right_inv x := by ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem residual_open (d : ℕ) [NeZero d] (mass : ℝ) :
    IsOpenMap (residual (d := d) mass) := by
  have hs : Function.Surjective (sumLinear d) := by
    intro r
    refine ⟨Pi.single (0 : Fin d) r, ?_⟩
    simp [sumLinear]
  exact (massReflection mass).isOpenMap.comp
    ((sumLinear d).isOpenMap_of_finiteDimensional hs)

private theorem strictPoly_open (d : ℕ) (mass cap : ℝ) : IsOpen (strictPoly d mass cap) := by
  have he : strictPoly d mass cap =
      (⋂ i : Fin d, {x : Fin d → ℝ | 0 < x i ∧ x i < cap}) ∩
      (residual mass ⁻¹' Ioo 0 cap) := by ext x; simp [strictPoly]
  rw [he]
  exact (isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)).inter
    (isOpen_Ioo.preimage (continuous_residual d mass))

private theorem poly_interior (d : ℕ) [NeZero d] (mass cap : ℝ) :
    interior (poly d mass cap) = strictPoly d mass cap := by
  apply subset_antisymm
  · intro x hx
    constructor
    · intro i
      have hi : x ∈ interior ((fun y : Fin d → ℝ => y i) ⁻¹' Icc 0 cap) :=
        interior_mono (fun y hy => hy.1 i) hx
      have hj := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa only [interior_Icc, mem_preimage, mem_Ioo] using hj
    · have hi : x ∈ interior (residual mass ⁻¹' Icc 0 cap) :=
        interior_mono (fun y hy => hy.2) hx
      have hj := (residual_open d mass).interior_preimage_subset_preimage_interior hi
      simpa only [interior_Icc, mem_preimage, mem_Ioo] using hj
  · apply interior_maximal _ (strictPoly_open d mass cap)
    intro x hx
    exact ⟨fun i => ⟨(hx.1 i).1.le, (hx.1 i).2.le⟩, hx.2.1.le, hx.2.2.le⟩

private inductive Model where
  | bulk | hex | cap

@[reducible] private def dim : Model → ℕ | .bulk => 3 | .hex => 2 | .cap => 2
@[reducible] private def mass : Model → ℝ | .bulk => 1 | .hex => 1 | .cap => 1 / 4
@[reducible] private def modelPoly (k : Model) := poly (dim k) (mass k) (3 / 4)

private theorem model_interior_nonempty (k : Model) : (interior (modelPoly k)).Nonempty := by
  cases k
  · refine ⟨fun _ => (1 / 4 : ℝ), ?_⟩
    rw [modelPoly, poly_interior]
    norm_num [strictPoly, residual, dim, mass, Fin.sum_univ_succ]
  · refine ⟨fun _ => (1 / 3 : ℝ), ?_⟩
    rw [modelPoly, poly_interior]
    norm_num [strictPoly, residual, dim, mass, Fin.sum_univ_succ]
  · refine ⟨fun _ => (1 / 12 : ℝ), ?_⟩
    rw [modelPoly, poly_interior]
    norm_num [strictPoly, residual, dim, mass, Fin.sum_univ_succ]

private theorem model_gauge_exists (k : Model) :
    ∃ h : (Fin (dim k) → ℝ) ≃ₜ (Fin (dim k) → ℝ),
      h '' interior (modelPoly k) = ball 0 1 ∧
      h '' modelPoly k = closedBall 0 1 ∧
      h '' frontier (modelPoly k) = sphere 0 1 := by
  obtain ⟨h, hi, hc, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (poly_convex (dim k) (mass k) (3 / 4))
      (model_interior_nonempty k)
      (poly_compact (dim k) (mass k) (3 / 4)).isBounded
  have hclosed : IsClosed (modelPoly k) := poly_closed (dim k) (mass k) (3 / 4)
  change h '' closure (modelPoly k) = closedBall 0 1 at hc
  rw [hclosed.closure_eq] at hc
  exact ⟨h, hi, hc, hf⟩

private def gauge (k : Model) := Classical.choose (model_gauge_exists k)
private theorem gauge_spec (k : Model) :
    gauge k '' interior (modelPoly k) = ball 0 1 ∧
    gauge k '' modelPoly k = closedBall 0 1 ∧
    gauge k '' frontier (modelPoly k) = sphere 0 1 :=
  Classical.choose_spec (model_gauge_exists k)

private def polyBall (k : Model) : ↥(modelPoly k) ≃ₜ Disk (dim k) :=
  ((gauge k).image (modelPoly k)).trans (Homeomorph.setCongr (gauge_spec k).2.1)

@[simp] private theorem polyBall_val (k : Model) (x : ↥(modelPoly k)) :
    (polyBall k x).val = gauge k x.val := rfl

private theorem polyBall_interior_iff (k : Model) (x : ↥(modelPoly k)) :
    x.val ∈ interior (modelPoly k) ↔ (polyBall k x).val ∈ ball 0 1 := by
  rw [polyBall_val, ← (gauge_spec k).1]
  constructor
  · exact mem_image_of_mem (gauge k)
  · rintro ⟨y, hy, he⟩
    exact (gauge k).injective he ▸ hy

private theorem polyBall_symm_interior_iff (k : Model) (x : Disk (dim k)) :
    ((polyBall k).symm x).val ∈ interior (modelPoly k) ↔ x.val ∈ ball 0 1 := by
  rw [polyBall_interior_iff, (polyBall k).apply_symm_apply]

private theorem polyBall_symm_frontier (k : Model) (x : Disk (dim k))
    (hx : x.val ∈ sphere 0 1) : ((polyBall k).symm x).val ∈ frontier (modelPoly k) := by
  have hi : gauge k ((polyBall k).symm x).val = x.val :=
    congrArg Subtype.val ((polyBall k).apply_symm_apply x)
  have hm : gauge k ((polyBall k).symm x).val ∈ gauge k '' frontier (modelPoly k) := by
    rw [(gauge_spec k).2.2, hi]
    exact hx
  obtain ⟨y, hy, he⟩ := hm
  exact (gauge k).injective he ▸ hy


variable (P : RawFacePairing T)

/- Actual affine realizations into the four retained coordinates. -/

private def bulkCoords (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![x 0, x 1, x 2, residual 1 x]

private theorem bulkCoords_sum (x : Fin 3 → ℝ) : ∑ i, bulkCoords x i = 1 := by
  simp [bulkCoords, residual, Fin.sum_univ_succ] <;> ring

private def bulkRealize (x : ↥(modelPoly .bulk)) : TruncatedTetrahedron :=
  ⟨bulkCoords x.val, (by
    intro i
    fin_cases i
    · exact x.property.1 0
    · exact x.property.1 1
    · exact x.property.1 2
    · exact x.property.2), bulkCoords_sum x.val⟩

private theorem bulkRealize_injective : Function.Injective bulkRealize := by
  intro x y h
  apply Subtype.ext
  funext i
  have hh := congrArg (fun z : TruncatedTetrahedron => z.val i.castSucc) h
  fin_cases i <;> exact hh

private def bulkExtract (a : TruncatedTetrahedron) : ↥(modelPoly .bulk) :=
  ⟨![a.val 0, a.val 1, a.val 2], (by
    constructor
    · intro i
      fin_cases i
      · exact a.property.1 0
      · exact a.property.1 1
      · exact a.property.1 2
    · have hs : a.val 0 + a.val 1 + a.val 2 + a.val 3 = 1 := by
        simpa only [Fin.sum_univ_four] using a.property.2
      have he : residual 1 (![a.val 0, a.val 1, a.val 2] : Fin 3 → ℝ) = a.val 3 := by
        simp [residual, Fin.sum_univ_succ]
        linarith
      rw [he]
      exact a.property.1 3)⟩

private theorem bulkRealize_extract (a : TruncatedTetrahedron) :
    bulkRealize (bulkExtract a) = a := by
  apply Subtype.ext
  funext i
  have hs : a.val 0 + a.val 1 + a.val 2 + a.val 3 = 1 := by
    simpa only [Fin.sum_univ_four] using a.property.2
  fin_cases i <;> simp [bulkRealize, bulkExtract, bulkCoords, residual, Fin.sum_univ_succ] <;>
    linarith

private def bulkHomeomorph : ↥(modelPoly .bulk) ≃ₜ TruncatedTetrahedron where
  toFun := bulkRealize
  invFun := bulkExtract
  left_inv x := bulkRealize_injective (bulkRealize_extract (bulkRealize x))
  right_inv := bulkRealize_extract
  continuous_toFun := by
    have hc (i : Fin 3) : Continuous (fun x : ↥(modelPoly .bulk) => x.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact (continuous_residual 3 1).comp continuous_subtype_val
  continuous_invFun := by
    have hc (i : Fin 4) : Continuous (fun a : TruncatedTetrahedron => a.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact hc 0
    · exact hc 1
    · exact hc 2

private theorem bulkRealize_strict_iff (x : ↥(modelPoly .bulk)) :
    x.val ∈ interior (modelPoly .bulk) ↔
      ∀ i, 0 < (bulkRealize x).val i ∧ (bulkRealize x).val i < 3 / 4 := by
  have hi : interior (modelPoly .bulk) = strictPoly 3 1 (3 / 4) :=
    poly_interior 3 1 (3 / 4)
  rw [hi]
  constructor
  · intro hx i
    fin_cases i
    · exact hx.1 0
    · exact hx.1 1
    · exact hx.1 2
    · exact hx.2
  · intro hx
    refine ⟨?_, hx 3⟩
    intro i
    fin_cases i
    · exact hx 0
    · exact hx 1
    · exact hx 2

inductive FaceShape where
  | hex | cap

private def faceMass : FaceShape → ℝ | .hex => 1 | .cap => 1 / 4
private def faceFixed : FaceShape → ℝ | .hex => 0 | .cap => 3 / 4
private def facePoly : FaceShape → Set (Fin 2 → ℝ)
  | .hex => modelPoly .hex | .cap => modelPoly .cap

private theorem facePoly_eq (k : FaceShape) : facePoly k = poly 2 (faceMass k) (3 / 4) := by
  cases k <;> rfl

private def faceBall : (k : FaceShape) → ↥(facePoly k) ≃ₜ Disk 2
  | .hex => polyBall .hex | .cap => polyBall .cap

private theorem faceBall_symm_interior_iff (k : FaceShape) (x : Disk 2) :
    ((faceBall k).symm x).val ∈ interior (facePoly k) ↔ x.val ∈ ball 0 1 := by
  cases k
  · exact polyBall_symm_interior_iff .hex x
  · exact polyBall_symm_interior_iff .cap x

private def faceFrame (j : Fin 4) : Equiv.Perm (Fin 4) := Equiv.swap j 3

@[simp] private theorem faceFrame_last (j : Fin 4) : faceFrame j 3 = j := by
  simp [faceFrame]

private theorem faceFrame_ne (j : Fin 4) (i : Fin 4) (hi : i ≠ 3) : faceFrame j i ≠ j := by
  intro h
  exact hi ((faceFrame j).injective (h.trans (faceFrame_last j).symm))

private def faceCoords (k : FaceShape) (j : Fin 4) (x : Fin 2 → ℝ) : Fin 4 → ℝ :=
  fun i => (![x 0, x 1, residual (faceMass k) x, faceFixed k] : Fin 4 → ℝ)
    ((faceFrame j).symm i)

private theorem faceCoords_values (k : FaceShape) (j : Fin 4) (x : Fin 2 → ℝ) :
    faceCoords k j x (faceFrame j 0) = x 0 ∧
    faceCoords k j x (faceFrame j 1) = x 1 ∧
    faceCoords k j x (faceFrame j 2) = residual (faceMass k) x ∧
    faceCoords k j x j = faceFixed k := by
  have hv (i : Fin 4) : faceCoords k j x (faceFrame j i) =
      (![x 0, x 1, residual (faceMass k) x, faceFixed k] : Fin 4 → ℝ) i := by
    change (![x 0, x 1, residual (faceMass k) x, faceFixed k] : Fin 4 → ℝ)
      ((faceFrame j).symm (faceFrame j i)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨hv 0, hv 1, hv 2, ?_⟩
  calc
    faceCoords k j x j = faceCoords k j x (faceFrame j 3) :=
      congrArg (faceCoords k j x) (faceFrame_last j).symm
    _ = faceFixed k := hv 3

private theorem faceCoords_sum (k : FaceShape) (j : Fin 4) (x : Fin 2 → ℝ) :
    ∑ i, faceCoords k j x i = 1 := by
  unfold faceCoords
  rw [Equiv.sum_comp]
  cases k <;> simp [residual, faceMass, faceFixed, Fin.sum_univ_succ] <;> ring

private def faceRealize (k : FaceShape) (t : T) (j : Fin 4)
    (x : ↥(facePoly k)) : TruncatedPoint T :=
  (t, ⟨faceCoords k j x.val, (by
    have hx : x.val ∈ poly 2 (faceMass k) (3 / 4) := (facePoly_eq k) ▸ x.property
    have hb : ∀ n : Fin 4,
        0 ≤ (![x.val 0, x.val 1, residual (faceMass k) x.val, faceFixed k] :
          Fin 4 → ℝ) n ∧
        (![x.val 0, x.val 1, residual (faceMass k) x.val, faceFixed k] :
          Fin 4 → ℝ) n ≤ 3 / 4 := by
      intro n
      fin_cases n
      · exact hx.1 0
      · exact hx.1 1
      · exact hx.2
      · cases k <;> norm_num [faceFixed]
    intro i
    exact hb ((faceFrame j).symm i)), faceCoords_sum k j x.val⟩)

private theorem faceRealize_fixed (k : FaceShape) (t : T) (j : Fin 4)
    (x : ↥(facePoly k)) : (faceRealize k t j x).2.val j = faceFixed k :=
  (faceCoords_values k j x.val).2.2.2

private theorem faceRealize_injective (k : FaceShape) (t : T) (j : Fin 4) :
    Function.Injective (faceRealize k t j) := by
  intro x y h
  have h0 := congrArg (fun a : TruncatedPoint T => a.2.val (faceFrame j 0)) h
  have h1 := congrArg (fun a : TruncatedPoint T => a.2.val (faceFrame j 1)) h
  apply Subtype.ext
  funext i
  fin_cases i
  · exact ((faceCoords_values k j x.val).1.symm.trans h0).trans
      (faceCoords_values k j y.val).1
  · exact ((faceCoords_values k j x.val).2.1.symm.trans h1).trans
      (faceCoords_values k j y.val).2.1

private theorem continuous_faceRealize (k : FaceShape) (t : T) (j : Fin 4) :
    Continuous (faceRealize k t j) := by
  have hc (i : Fin 2) : Continuous (fun x : ↥(facePoly k) => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  apply Continuous.prodMk continuous_const
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : ↥(facePoly k) => faceCoords k j x.val i)
  unfold faceCoords
  generalize (faceFrame j).symm i = n
  fin_cases n
  · exact hc 0
  · exact hc 1
  · exact (continuous_residual 2 (faceMass k)).comp continuous_subtype_val
  · exact continuous_const

def faceCarrier (k : FaceShape) (t : T) (j : Fin 4) : Set (TruncatedPoint T) :=
  {a | a.1 = t ∧ a.2.val j = faceFixed k}

/-- Reconstruction in R^2 of every point of the entire original closed face. -/
private theorem faceRealize_surj (k : FaceShape) (t : T) (j : Fin 4)
    (a : TruncatedPoint T) (ha : a ∈ faceCarrier k t j) :
    ∃ x : ↥(facePoly k), faceRealize k t j x = a := by
  let e := faceFrame j
  let x : Fin 2 → ℝ := ![a.2.val (e 0), a.2.val (e 1)]
  have hs : ∑ i, a.2.val (e i) = 1 :=
    (Equiv.sum_comp e a.2.val).trans a.2.property.2
  have hj : a.2.val (e 3) = faceFixed k := by simpa [e] using ha.2
  have hr : residual (faceMass k) x = a.2.val (e 2) := by
    rw [Fin.sum_univ_four] at hs
    have hm : faceMass k + faceFixed k = 1 := by
      cases k <;> norm_num [faceMass, faceFixed]
    simp [residual, x, Fin.sum_univ_succ]
    linarith
  have hx : x ∈ facePoly k := by
    rw [facePoly_eq]
    constructor
    · intro i
      fin_cases i
      · exact a.2.property.1 (e 0)
      · exact a.2.property.1 (e 1)
    · rw [hr]
      exact a.2.property.1 (e 2)
  refine ⟨⟨x, hx⟩, Prod.ext ha.1.symm (Subtype.ext ?_)⟩
  funext i
  obtain ⟨n, rfl⟩ := e.surjective i
  fin_cases n
  · exact (faceCoords_values k j x).1
  · exact (faceCoords_values k j x).2.1
  · exact (faceCoords_values k j x).2.2.1.trans hr
  · change faceCoords k j x (e 3) = a.2.val (e 3)
    rw [show e 3 = j from faceFrame_last j]
    exact (faceCoords_values k j x).2.2.2.trans ha.2.symm

/-- This is a homeomorphism to the closed face in the original retained carrier,
before quotienting. It asserts no closed-cell embedding after quotienting. -/
private def faceHomeomorph (k : FaceShape) (t : T) (j : Fin 4) :
    ↥(facePoly k) ≃ₜ ↥(faceCarrier k t j) := by
  letI : CompactSpace ↥(facePoly k) :=
    isCompact_iff_compactSpace.mp (by rw [facePoly_eq]; exact poly_compact _ _ _)
  let f : ↥(facePoly k) → ↥(faceCarrier k t j) := fun x =>
    ⟨faceRealize k t j x, rfl, faceRealize_fixed k t j x⟩
  have hf : IsHomeomorph f := isHomeomorph_iff_continuous_bijective.mpr
    ⟨(continuous_faceRealize k t j).subtype_mk _,
      (fun x y h => faceRealize_injective k t j (congrArg Subtype.val h)), by
        rintro ⟨a, ha⟩
        obtain ⟨x, hx⟩ := faceRealize_surj k t j a ha
        exact ⟨x, Subtype.ext hx⟩⟩
  exact hf.homeomorph f

private theorem faceRealize_strict_iff (k : FaceShape) (t : T) (j : Fin 4)
    (x : ↥(facePoly k)) :
    x.val ∈ interior (facePoly k) ↔
      ∀ i, i ≠ j → 0 < (faceRealize k t j x).2.val i ∧
        (faceRealize k t j x).2.val i < 3 / 4 := by
  have hi : interior (facePoly k) = strictPoly 2 (faceMass k) (3 / 4) := by
    rw [facePoly_eq, poly_interior]
  rw [hi]
  constructor
  · intro hx i hij
    obtain ⟨n, rfl⟩ := (faceFrame j).surjective i
    fin_cases n
    · change 0 < faceCoords k j x.val (faceFrame j 0) ∧
        faceCoords k j x.val (faceFrame j 0) < 3 / 4
      rw [(faceCoords_values k j x.val).1]
      exact hx.1 0
    · change 0 < faceCoords k j x.val (faceFrame j 1) ∧
        faceCoords k j x.val (faceFrame j 1) < 3 / 4
      rw [(faceCoords_values k j x.val).2.1]
      exact hx.1 1
    · change 0 < faceCoords k j x.val (faceFrame j 2) ∧
        faceCoords k j x.val (faceFrame j 2) < 3 / 4
      rw [(faceCoords_values k j x.val).2.2.1]
      exact hx.2
    · exact (hij (faceFrame_last j)).elim
  · intro hx
    have h0 := hx (faceFrame j 0) (faceFrame_ne j 0 (by decide))
    have h1 := hx (faceFrame j 1) (faceFrame_ne j 1 (by decide))
    have h2 := hx (faceFrame j 2) (faceFrame_ne j 2 (by decide))
    change 0 < faceCoords k j x.val (faceFrame j 0) ∧
      faceCoords k j x.val (faceFrame j 0) < 3 / 4 at h0
    change 0 < faceCoords k j x.val (faceFrame j 1) ∧
      faceCoords k j x.val (faceFrame j 1) < 3 / 4 at h1
    change 0 < faceCoords k j x.val (faceFrame j 2) ∧
      faceCoords k j x.val (faceFrame j 2) < 3 / 4 at h2
    rw [(faceCoords_values k j x.val).1] at h0
    rw [(faceCoords_values k j x.val).2.1] at h1
    rw [(faceCoords_values k j x.val).2.2.1] at h2
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · exact h1
    · exact h2

private theorem capRealize_interior (t : T) (j : Fin 4) (x : ↥(facePoly .cap))
    (hx : x.val ∈ interior (facePoly .cap)) : Interior (faceRealize .cap t j x) := by
  intro i
  by_cases hi : i = j
  · subst i
    rw [faceRealize_fixed]
    norm_num [faceFixed]
  · exact ne_of_gt ((faceRealize_strict_iff .cap t j x).mp hx i hi).1

private theorem hexRealize_faceInterior (t : T) (j : Fin 4) (x : ↥(facePoly .hex))
    (hx : x.val ∈ interior (facePoly .hex)) : FaceInterior (faceRealize .hex t j x) j := by
  refine ⟨faceRealize_fixed .hex t j x, ?_⟩
  intro i hi
  by_contra hij
  exact (ne_of_gt ((faceRealize_strict_iff .hex t j x).mp hx i hij).1) hi

/- Full EqvGen, including self-pairings, is used in the next two facts. -/

private theorem hex_same_face_fiber (a b : TruncatedPoint T) (f : Fin 4)
    (ha : FaceInterior a f) (hb : b.1 = a.1) (hbzero : b.2.val f = 0)
    (h : Relation.EqvGen (TruncatedStep P) a b) : b = a := by
  rcases ((actual_face_classification P a b f ha).2.mp h) with he | he
  · exact he
  · have hs : TruncatedStep P a b := ⟨f, ha.1, he⟩
    have hbf := step_face P ha hs
    have hf : f = (P.facePair (a.1, f)).2 := hbf.2 f hbzero
    have ht : b.1 = (P.facePair (a.1, f)).1 :=
      congrArg (fun z : TruncatedPoint T => z.1) he
    exact (P.pairFixedFree (a.1, f) (Prod.ext (ht.symm.trans hb) hf.symm)).elim

def bulkDiskPoint (t : T) (x : Disk 3) : TruncatedPoint T :=
  (t, bulkRealize ((polyBall .bulk).symm x))

def faceDiskPoint (k : FaceShape) (t : T) (j : Fin 4) (x : Disk 2) :
    TruncatedPoint T := (faceHomeomorph k t j ((faceBall k).symm x)).val

def topCharacteristic (t : T) : Disk 3 → (TruncatedQuotient P) := (q P) ∘ bulkDiskPoint t
def faceCharacteristic (k : FaceShape) (t : T) (j : Fin 4) : Disk 2 → (TruncatedQuotient P) :=
  (q P) ∘ faceDiskPoint k t j

private theorem continuous_bulkDiskPoint (t : T) : Continuous (bulkDiskPoint t) :=
  continuous_const.prodMk (bulkHomeomorph.continuous.comp (polyBall .bulk).symm.continuous)

private theorem continuous_faceDiskPoint (k : FaceShape) (t : T) (j : Fin 4) :
    Continuous (faceDiskPoint k t j) :=
  (continuous_subtype_val.comp (faceHomeomorph k t j).continuous).comp
    (faceBall k).symm.continuous

private theorem continuous_topCharacteristic (t : T) : Continuous (topCharacteristic P t) :=
  (continuous_q P).comp (continuous_bulkDiskPoint t)

private theorem continuous_faceCharacteristic (k : FaceShape) (t : T) (j : Fin 4) :
    Continuous (faceCharacteristic P k t j) :=
  (continuous_q P).comp (continuous_faceDiskPoint k t j)

private theorem topCharacteristic_fiber (t : T) (x y : Disk 3)
    (hx : x.val ∈ ball 0 1) (h : topCharacteristic P t y = topCharacteristic P t x) : y = x := by
  have hi := (polyBall_symm_interior_iff .bulk x).mpr hx
  have hs := (bulkRealize_strict_iff ((polyBall .bulk).symm x)).mp hi
  have ha : Interior (bulkDiskPoint t x) := fun i => ne_of_gt (hs i).1
  have he : bulkDiskPoint t y = bulkDiskPoint t x :=
    (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h.symm)
  exact (polyBall .bulk).symm.injective
    (bulkRealize_injective (congrArg Prod.snd he))

private theorem faceCharacteristic_fiber (k : FaceShape) (t : T) (j : Fin 4) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) (h : faceCharacteristic P k t j y = faceCharacteristic P k t j x) :
    y = x := by
  have hi := (faceBall_symm_interior_iff k x).mpr hx
  have hr : Relation.EqvGen (TruncatedStep P)
      (faceDiskPoint k t j x) (faceDiskPoint k t j y) := Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h.symm
  have he : faceDiskPoint k t j y = faceDiskPoint k t j x := by
    cases k
    · exact hex_same_face_fiber P _ _ j (hexRealize_faceInterior t j _ hi) rfl
        (faceRealize_fixed .hex t j _) hr
    · exact (interior_normal_form P _ _ (capRealize_interior t j _ hi)).mp hr
  exact (faceBall k).symm.injective (faceRealize_injective k t j he)

/-- Three-dimensional characteristic maps in the full quotient. -/
def topCell (t : T) : PartialEquiv (Fin 3 → ℝ) (TruncatedQuotient P) :=
  diskPartial (topCharacteristic P t) (continuous_topCharacteristic P t) (topCharacteristic_fiber P t)

/-- Directed face maps retain the entire closed cap or original zero face. -/
def directedFaceCell (k : FaceShape) (t : T) (j : Fin 4) :
    PartialEquiv (Fin 2 → ℝ) (TruncatedQuotient P) :=
  diskPartial (faceCharacteristic P k t j) (continuous_faceCharacteristic P k t j)
    (faceCharacteristic_fiber P k t j)

@[simp] private theorem topCell_source (t : T) : (topCell P t).source = ball 0 1 := rfl
private theorem topCell_continuousOn (t : T) : ContinuousOn (topCell P t) (closedBall 0 1) :=
  diskPartial_continuousOn _ _ _
private theorem topCell_continuousOn_symm (t : T) :
    ContinuousOn (topCell P t).symm (topCell P t).target :=
  diskPartial_continuousOn_symm _ _ _
private theorem directedFaceCell_continuousOn (k : FaceShape) (t : T) (j : Fin 4) :
    ContinuousOn (directedFaceCell P k t j) (closedBall 0 1) :=
  diskPartial_continuousOn _ _ _
private theorem directedFaceCell_continuousOn_symm (k : FaceShape) (t : T) (j : Fin 4) :
    ContinuousOn (directedFaceCell P k t j).symm (directedFaceCell P k t j).target :=
  diskPartial_continuousOn_symm _ _ _

@[simp] private theorem topCell_coe_disk (t : T) (x : Disk 3) :
    topCell P t x.val = (q P) (bulkDiskPoint t x) := diskExtend_coe _ x

@[simp] private theorem directedFaceCell_coe_disk (k : FaceShape) (t : T) (j : Fin 4)
    (x : Disk 2) : directedFaceCell P k t j x.val = (q P) (faceDiskPoint k t j x) :=
  diskExtend_coe _ x

private theorem topCell_closed_image (t : T) :
    topCell P t '' closedBall 0 1 = (q P) '' {a : TruncatedPoint T | a.1 = t} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨bulkDiskPoint t ⟨x, hx⟩, rfl, (topCell_coe_disk P t ⟨x, hx⟩).symm⟩
  · rintro ⟨a, ha, rfl⟩
    let x : Disk 3 := polyBall .bulk (bulkExtract a.2)
    refine ⟨x.val, x.property, ?_⟩
    rw [topCell_coe_disk P]
    apply congrArg (q P)
    change (t, bulkRealize ((polyBall .bulk).symm (polyBall .bulk (bulkExtract a.2)))) = a
    rw [(polyBall .bulk).symm_apply_apply, bulkRealize_extract]
    exact Prod.ext ha.symm rfl

private theorem directedFaceCell_closed_image (k : FaceShape) (t : T) (j : Fin 4) :
    directedFaceCell P k t j '' closedBall 0 1 = (q P) '' faceCarrier k t j := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨faceDiskPoint k t j ⟨x, hx⟩,
      ⟨rfl, faceRealize_fixed k t j _⟩, ?_⟩
    exact (directedFaceCell_coe_disk P k t j ⟨x, hx⟩).symm
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨p, hp⟩ := faceRealize_surj k t j a ha
    let x : Disk 2 := faceBall k p
    refine ⟨x.val, x.property, ?_⟩
    rw [directedFaceCell_coe_disk P]
    apply congrArg (q P)
    change faceRealize k t j ((faceBall k).symm (faceBall k p)) = a
    rw [(faceBall k).symm_apply_apply]
    exact hp

private theorem topCell_open_disjoint (t s : T) (hts : t ≠ s) :
    Disjoint (topCell P t '' ball 0 1) (topCell P s '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 3 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 3 := ⟨y, ball_subset_closedBall hy⟩
  have hq : (q P) (bulkDiskPoint t xd) = (q P) (bulkDiskPoint s yd) := by
    rw [← topCell_coe_disk P t xd, ← topCell_coe_disk P s yd]
    exact hxz.trans hyz.symm
  have hs := (bulkRealize_strict_iff ((polyBall .bulk).symm xd)).mp
    ((polyBall_symm_interior_iff .bulk xd).mpr hx)
  have ha : Interior (bulkDiskPoint t xd) := fun i => ne_of_gt (hs i).1
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) hq)
  exact hts (congrArg (fun z : TruncatedPoint T => z.1) he).symm

private theorem topCell_closed_cover : (⋃ t : T, topCell P t '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨a, rfl⟩ :=
    @Quotient.mk'_surjective _ (Relation.EqvGen.setoid (TruncatedStep P)) z
  apply mem_iUnion.mpr
  refine ⟨a.1, ?_⟩
  rw [topCell_closed_image P]
  exact ⟨a, rfl, rfl⟩


/-- Two directed faces belong to the same free-involution orbit. -/
def pairedFaceSetoid (P : RawFacePairing T) : Setoid (T × Fin 4) where
  r x y := y = x ∨ y = P.facePair x
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (paired_twice P x).symm
    · intro x y z hxy hyz
      rcases hxy with rfl | rfl
      · exact hyz
      · rcases hyz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (paired_twice P x)

abbrev PairedFace (P : RawFacePairing T) := Quotient (pairedFaceSetoid P)

/-- A closed original face selected from each actual pairing orbit. -/
def faceRep (r : PairedFace P) : T × Fin 4 := r.out

private theorem face_representatives_separate (r s : PairedFace P)
    (h : faceRep P s = faceRep P r ∨ faceRep P s = P.facePair (faceRep P r)) : s = r := by
  have he : Quotient.mk (pairedFaceSetoid P) (faceRep P r) =
      Quotient.mk (pairedFaceSetoid P) (faceRep P s) := Quotient.sound h
  simpa only [faceRep, Quotient.out_eq] using he.symm

private theorem face_representatives_cover (x : T × Fin 4) :
    ∃ r : PairedFace P, x = faceRep P r ∨ x = P.facePair (faceRep P r) := by
  let r : PairedFace P := Quotient.mk _ x
  exact ⟨r, Quotient.exact (Quotient.out_eq r)⟩

/-- Cap faces are indexed by original corners; zero faces by actual pairing orbits. -/
abbrev SurfaceCell := (T × Fin 4) ⊕ PairedFace P

def surfaceCell : SurfaceCell P → PartialEquiv (Fin 2 → ℝ) (TruncatedQuotient P)
  | .inl (t,j) => directedFaceCell P .cap t j
  | .inr r => directedFaceCell P .hex (faceRep P r).1 (faceRep P r).2

private def surfaceDiskPoint : SurfaceCell P → Disk 2 → TruncatedPoint T
  | .inl (t,j) => faceDiskPoint .cap t j
  | .inr r => faceDiskPoint .hex (faceRep P r).1 (faceRep P r).2

@[simp] private theorem surfaceCell_coe_disk (c : SurfaceCell P) (x : Disk 2) :
    surfaceCell P c x.val = (q P) (surfaceDiskPoint P c x) := by
  cases c with
  | inl tj => exact directedFaceCell_coe_disk P .cap tj.1 tj.2 x
  | inr r => exact directedFaceCell_coe_disk P .hex _ _ x

@[simp] private theorem surfaceCell_source (c : SurfaceCell P) : (surfaceCell P c).source = ball 0 1 := by
  cases c <;> rfl

private theorem surfaceCell_continuousOn (c : SurfaceCell P) :
    ContinuousOn (surfaceCell P c) (closedBall 0 1) := by
  cases c
  · exact directedFaceCell_continuousOn P .cap _ _
  · exact directedFaceCell_continuousOn P .hex _ _

private theorem surfaceCell_continuousOn_symm (c : SurfaceCell P) :
    ContinuousOn (surfaceCell P c).symm (surfaceCell P c).target := by
  cases c
  · exact directedFaceCell_continuousOn_symm P .cap _ _
  · exact directedFaceCell_continuousOn_symm P .hex _ _

private theorem hex_open_pair_tag (a b : TruncatedPoint T) (f g : Fin 4)
    (ha : FaceInterior a f) (hb : FaceInterior b g)
    (h : Relation.EqvGen (TruncatedStep P) a b) :
    (b.1, g) = (a.1, f) ∨ (b.1, g) = P.facePair (a.1, f) := by
  rcases (actual_face_classification P a b f ha).2.mp h with he | he
  · left
    have hbf : b.2.val f = 0 := by rw [he]; exact ha.1
    have hg : g = f := (hb.2 f hbf).symm
    have ht : b.1 = a.1 := congrArg (fun z : TruncatedPoint T => z.1) he
    exact Prod.ext ht hg
  · right
    have hb' := step_face P ha
      (show TruncatedStep P a b from ⟨f, ha.1, he⟩)
    have hbzero : b.2.val (P.facePair (a.1, f)).2 = 0 := hb'.1
    have hg : g = (P.facePair (a.1, f)).2 := (hb.2 _ hbzero).symm
    have ht : b.1 = (P.facePair (a.1, f)).1 :=
      congrArg (fun z : TruncatedPoint T => z.1) he
    exact Prod.ext ht hg

private theorem cap_open_tag (t s : T) (j l : Fin 4)
    (x y : Disk 2) (hx : x.val ∈ ball 0 1)
    (h : (q P) (faceDiskPoint .cap t j x) = (q P) (faceDiskPoint .cap s l y)) :
    (s, l) = (t, j) := by
  have hi := (faceBall_symm_interior_iff .cap x).mpr hx
  have ha := capRealize_interior t j ((faceBall .cap).symm x) hi
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
  have hj : l = j := by
    by_contra hlj
    have hl := ((faceRealize_strict_iff .cap t j _).mp hi l hlj).2
    have hy : (faceDiskPoint .cap s l y).2.val l = 3 / 4 :=
      faceRealize_fixed .cap s l _
    rw [he] at hy
    linarith
  have ht : s = t := congrArg (fun z : TruncatedPoint T => z.1) he
  exact Prod.ext ht hj

private theorem cap_hex_open_ne (t s : T) (j l : Fin 4) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) :
    (q P) (faceDiskPoint .cap t j x) ≠ (q P) (faceDiskPoint .hex s l y) := by
  intro h
  have ha := capRealize_interior t j ((faceBall .cap).symm x)
    ((faceBall_symm_interior_iff .cap x).mpr hx)
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
  have hz : (faceDiskPoint .hex s l y).2.val l = 0 := faceRealize_fixed .hex s l _
  rw [he] at hz
  exact ha l hz

private theorem surface_open_index (c d : SurfaceCell P) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) (hy : y.val ∈ ball 0 1)
    (h : (q P) (surfaceDiskPoint P c x) = (q P) (surfaceDiskPoint P d y)) : c = d := by
  cases c with
  | inl tj =>
    cases d with
    | inl sl => exact congrArg Sum.inl (cap_open_tag P tj.1 sl.1 tj.2 sl.2 x y hx h).symm
    | inr r => exact (cap_hex_open_ne P tj.1 _ tj.2 _ x y hx h).elim
  | inr r =>
    cases d with
    | inl sl => exact (cap_hex_open_ne P sl.1 _ sl.2 _ y x hy h.symm).elim
    | inr s =>
      have ha := hexRealize_faceInterior
        (faceRep P r).1 (faceRep P r).2
        ((faceBall .hex).symm x) ((faceBall_symm_interior_iff .hex x).mpr hx)
      have hb := hexRealize_faceInterior
        (faceRep P s).1 (faceRep P s).2
        ((faceBall .hex).symm y) ((faceBall_symm_interior_iff .hex y).mpr hy)
      have ht := hex_open_pair_tag P _ _ _ _ ha hb (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
      have hr : s = r := face_representatives_separate P r s (by
        simpa only [faceRealize] using ht)
      exact congrArg Sum.inr hr.symm

private theorem surfaceCell_open_disjoint (c d : SurfaceCell P) (hcd : c ≠ d) :
    Disjoint (surfaceCell P c '' ball 0 1) (surfaceCell P d '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 2 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 2 := ⟨y, ball_subset_closedBall hy⟩
  apply hcd
  apply surface_open_index P c d xd yd hx hy
  rw [← surfaceCell_coe_disk P c xd, ← surfaceCell_coe_disk P d yd]
  exact hxz.trans hyz.symm

/-- Actual geometric two-dimensional subset; no CW structure on it is assumed. -/
def faceSkeleton : Set (TruncatedQuotient P) := ⋃ c : SurfaceCell P, surfaceCell P c '' closedBall 0 1

private theorem faceSkeleton_closed : IsClosed (faceSkeleton P) :=
  isClosed_iUnion_of_finite fun c =>
    ((isCompact_closedBall _ _).image_of_continuousOn (surfaceCell_continuousOn P c)).isClosed

private theorem top_surface_open_closed_disjoint (t : T) (c : SurfaceCell P) :
    Disjoint (topCell P t '' ball 0 1) (surfaceCell P c '' closedBall 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 3 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 2 := ⟨y, hy⟩
  have hq : (q P) (bulkDiskPoint t xd) = (q P) (surfaceDiskPoint P c yd) := by
    rw [← topCell_coe_disk P t xd, ← surfaceCell_coe_disk P c yd]
    exact hxz.trans hyz.symm
  have hs := (bulkRealize_strict_iff ((polyBall .bulk).symm xd)).mp
    ((polyBall_symm_interior_iff .bulk xd).mpr hx)
  have ha : Interior (bulkDiskPoint t xd) := fun i => ne_of_gt (hs i).1
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) hq)
  cases c with
  | inl tj =>
    have hcap : (surfaceDiskPoint P (.inl tj) yd).2.val tj.2 = 3 / 4 :=
      faceRealize_fixed .cap tj.1 tj.2 _
    rw [he] at hcap
    exact (ne_of_lt (hs tj.2).2) hcap
  | inr r =>
    have hz : (surfaceDiskPoint P (.inr r) yd).2.val (faceRep P r).2 = 0 :=
      faceRealize_fixed .hex _ _ _
    rw [he] at hz
    exact ha _ hz

private theorem topCell_disjoint_faceSkeleton (t : T) :
    Disjoint (topCell P t '' ball 0 1) (faceSkeleton P) := by
  rw [faceSkeleton, disjoint_iUnion_right]
  exact top_surface_open_closed_disjoint P t


private theorem zero_face_mem_faceSkeleton (a : TruncatedPoint T) (j : Fin 4)
    (hz : a.2.val j = 0) : q P a ∈ (faceSkeleton P) := by
  obtain ⟨r, hr | hr⟩ := face_representatives_cover P (a.1,j)
  · apply mem_iUnion.mpr
    refine ⟨Sum.inr r, ?_⟩
    change q P a ∈ directedFaceCell P .hex _ _ '' closedBall 0 1
    rw [directedFaceCell_closed_image P]
    exact ⟨a, ⟨congrArg Prod.fst hr, (congrArg Prod.snd hr) ▸ hz⟩, rfl⟩
  · let b := truncatedMove P j a
    have hp : P.facePair (a.1,j) = faceRep P r := by
      rw [hr]
      exact paired_twice P _
    have hb : b ∈ faceCarrier .hex (faceRep P r).1 (faceRep P r).2 := by
      constructor
      · exact congrArg Prod.fst hp
      · change a.2.val ((sigma P (a.1,j)).symm (faceRep P r).2) = 0
        rw [← hp, ← sigma_face P (a.1,j), Equiv.symm_apply_apply]
        exact hz
    have hab : q P a = q P b := Quotient.sound
      (s := Relation.EqvGen.setoid (TruncatedStep P))
      (Relation.EqvGen.rel _ _ (show TruncatedStep P a b from ⟨j,hz,rfl⟩))
    rw [hab]
    apply mem_iUnion.mpr
    refine ⟨Sum.inr r, ?_⟩
    change q P b ∈ directedFaceCell P .hex _ _ '' closedBall 0 1
    rw [directedFaceCell_closed_image P]
    exact ⟨b,hb,rfl⟩

private theorem cap_face_mem_faceSkeleton (a : TruncatedPoint T) (j : Fin 4)
    (hc : a.2.val j = 3 / 4) : (q P) a ∈ (faceSkeleton P) := by
  apply mem_iUnion.mpr
  refine ⟨Sum.inl (a.1, j), ?_⟩
  change (q P) a ∈ directedFaceCell P .cap a.1 j '' closedBall 0 1
  rw [directedFaceCell_closed_image P]
  exact ⟨a, ⟨rfl, hc⟩, rfl⟩

private theorem top_sphere_has_boundary_coordinate (t : T) (x : Disk 3)
    (hx : x.val ∈ sphere 0 1) :
    ∃ j : Fin 4, (bulkDiskPoint t x).2.val j = 0 ∨
      (bulkDiskPoint t x).2.val j = 3 / 4 := by
  classical
  by_contra hn
  have hs : ∀ j, 0 < (bulkDiskPoint t x).2.val j ∧
      (bulkDiskPoint t x).2.val j < 3 / 4 := by
    intro j
    have hb := (bulkDiskPoint t x).2.property.1 j
    have h0 : (bulkDiskPoint t x).2.val j ≠ 0 := fun he => hn ⟨j, Or.inl he⟩
    have hc : (bulkDiskPoint t x).2.val j ≠ 3 / 4 := fun he => hn ⟨j, Or.inr he⟩
    constructor
    · by_contra hbad
      exact h0 (by linarith)
    · by_contra hbad
      exact hc (by linarith)
  have hi := (bulkRealize_strict_iff ((polyBall .bulk).symm x)).mpr hs
  exact disjoint_left.mp disjoint_interior_frontier hi (polyBall_symm_frontier .bulk x hx)

/-- Each original three-cell sphere maps into the actual closed face skeleton. -/
private theorem topCell_sphere_mapsTo (t : T) : MapsTo (topCell P t) (sphere 0 1) (faceSkeleton P) := by
  intro x hx
  let xd : Disk 3 := ⟨x, sphere_subset_closedBall hx⟩
  rw [topCell_coe_disk P t xd]
  obtain ⟨j, hj | hj⟩ := top_sphere_has_boundary_coordinate t xd hx
  · exact zero_face_mem_faceSkeleton P _ j hj
  · exact cap_face_mem_faceSkeleton P _ j hj

def HigherCell (n : ℕ) := {t : T // n = 3}

def higherMap (n : ℕ) (i : HigherCell (T := T) n) : PartialEquiv (Fin n → ℝ) (TruncatedQuotient P) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell P t

private theorem higher_finite_cell (n : ℕ) : Finite (HigherCell (T := T) n) := by
  unfold HigherCell
  infer_instance

private theorem higher_eventually_empty : ∀ᶠ n in Filter.atTop, IsEmpty (HigherCell (T := T) n) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨4, ?_⟩
  intro n hn
  refine ⟨?_⟩
  rintro ⟨t, ht⟩
  omega

private theorem higher_source (n : ℕ) (i : HigherCell (T := T) n) : (higherMap P n i).source = ball 0 1 := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_source P t

private theorem higher_continuousOn (n : ℕ) (i : HigherCell (T := T) n) :
    ContinuousOn (higherMap P n i) (closedBall 0 1) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_continuousOn P t

private theorem higher_continuousOn_symm (n : ℕ) (i : HigherCell (T := T) n) :
    ContinuousOn (higherMap P n i).symm (higherMap P n i).target := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_continuousOn_symm P t

private theorem higher_pairwiseDisjoint :
    (univ : Set (Σ n, HigherCell (T := T) n)).PairwiseDisjoint
      (fun ni => higherMap P ni.1 ni.2 '' ball 0 1) := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
  rintro ⟨n, ⟨t, ht⟩⟩ _ ⟨m, ⟨s, hs⟩⟩ _ hne
  subst n
  subst m
  apply topCell_open_disjoint P t s
  intro hts
  apply hne
  subst s
  rfl

private theorem higher_disjointBase (n : ℕ) (i : HigherCell (T := T) n) :
    Disjoint (higherMap P n i '' ball 0 1) (faceSkeleton P) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_disjoint_faceSkeleton P t

private theorem higher_mapsTo (n : ℕ) (i : HigherCell (T := T) n) :
    MapsTo (higherMap P n i) (sphere 0 1)
      ((faceSkeleton P) ∪ ⋃ (m < n) (j : HigherCell (T := T) m), higherMap P m j '' closedBall 0 1) := by
  rcases i with ⟨t, h⟩
  subst n
  intro x hx
  exact Or.inl (topCell_sphere_mapsTo P t hx)

private theorem higher_union :
    (faceSkeleton P) ∪ ⋃ (n : ℕ) (i : HigherCell (T := T) n), higherMap P n i '' closedBall 0 1 = univ := by
  apply eq_univ_of_forall
  intro z
  right
  have hz : z ∈ ⋃ t : T, topCell P t '' closedBall 0 1 := by rw [topCell_closed_cover P]; trivial
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨3, mem_iUnion.mpr ⟨⟨t, rfl⟩, ht⟩⟩

/-- The original retained quotient as a finite relative CW complex above its closed faces. -/
def relativeCW : RelCWComplex (univ : Set (TruncatedQuotient P)) (faceSkeleton P) :=
  RelCWComplex.mkFinite univ (faceSkeleton P) (HigherCell (T := T)) (higherMap P)
    (higher_eventually_empty (T := T)) (higher_finite_cell (T := T)) (higher_source P) (higher_continuousOn P)
    (higher_continuousOn_symm P) (higher_pairwiseDisjoint P) (higher_disjointBase P)
    (higher_mapsTo P) (faceSkeleton_closed P) (higher_union P)

private theorem relativeCW_finite :
    letI := relativeCW P
    RelCWComplex.Finite (univ : Set (TruncatedQuotient P)) :=
  RelCWComplex.finite_mkFinite univ (faceSkeleton P) (HigherCell (T := T)) (higherMap P)
    (higher_eventually_empty (T := T)) (higher_finite_cell (T := T)) (higher_source P) (higher_continuousOn P)
    (higher_continuousOn_symm P) (higher_pairwiseDisjoint P) (higher_disjointBase P)
    (higher_mapsTo P) (faceSkeleton_closed P) (higher_union P)

/-- Boundary strata of the retained tetrahedra, including every closed-face tie. -/
def retainedBoundary : Set (TruncatedPoint T) :=
  {a | ∃ j : Fin 4, a.2.val j = 0 ∨ a.2.val j = 3 / 4}

private theorem faceSkeleton_eq_boundaryImage :
    faceSkeleton P = q P '' retainedBoundary (T := T) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    cases c with
    | inl tj =>
      change z ∈ directedFaceCell P .cap tj.1 tj.2 '' closedBall 0 1 at hc
      rw [directedFaceCell_closed_image P] at hc
      obtain ⟨a,ha,he⟩ := hc
      exact ⟨a, ⟨tj.2, Or.inr ha.2⟩, he⟩
    | inr r =>
      change z ∈ directedFaceCell P .hex (faceRep P r).1 (faceRep P r).2 '' closedBall 0 1 at hc
      rw [directedFaceCell_closed_image P] at hc
      obtain ⟨a,ha,he⟩ := hc
      exact ⟨a, ⟨(faceRep P r).2, Or.inl ha.2⟩, he⟩
  · rintro ⟨a,⟨j,hj | hj⟩,rfl⟩
    · exact zero_face_mem_faceSkeleton P a j hj
    · exact cap_face_mem_faceSkeleton P a j hj

/-- Geometry of the original full quotient and its actual upper-dimensional cells.
The projection argument identifies the ambient quotient observations used by
these maps. The relative complex adds the original three-cells to the closed
face skeleton. -/
structure UpperGeometry (projection : TruncatedPoint T → TruncatedQuotient P) : Prop where
  interior_fibers : ∀ (a b : TruncatedPoint T), Interior a →
    (projection a = projection b ↔ b = a)
  face_fibers : ∀ (a b : TruncatedPoint T) (f : Fin 4), FaceInterior a f →
    truncatedMove P f a ≠ a ∧
      (projection a = projection b ↔ b = a ∨ b = truncatedMove P f a)
  top_characteristic : ∀ t : T,
    Continuous (topCharacteristic P t) ∧
    (∀ x : Disk 3, topCell P t x.val = projection (bulkDiskPoint t x)) ∧
    (∀ (x y : Disk 3), x.val ∈ ball 0 1 →
      topCharacteristic P t y = topCharacteristic P t x → y = x)
  face_characteristic : ∀ (k : FaceShape) (t : T) (j : Fin 4),
    Continuous (faceCharacteristic P k t j) ∧
    (∀ x : Disk 2, directedFaceCell P k t j x.val = projection (faceDiskPoint k t j x)) ∧
    (∀ (x y : Disk 2), x.val ∈ ball 0 1 →
      faceCharacteristic P k t j y = faceCharacteristic P k t j x → y = x)
  top_charts : ∀ t : T, (topCell P t).source = ball 0 1 ∧
    ContinuousOn (topCell P t) (closedBall 0 1) ∧
    ContinuousOn (topCell P t).symm (topCell P t).target
  face_charts : ∀ c : SurfaceCell P, (surfaceCell P c).source = ball 0 1 ∧
    ContinuousOn (surfaceCell P c) (closedBall 0 1) ∧
    ContinuousOn (surfaceCell P c).symm (surfaceCell P c).target
  top_closed_image : ∀ t : T,
    topCell P t '' closedBall 0 1 = projection '' {a : TruncatedPoint T | a.1 = t}
  directed_face_closed_image : ∀ (k : FaceShape) (t : T) (j : Fin 4),
    directedFaceCell P k t j '' closedBall 0 1 = projection '' faceCarrier k t j
  top_open_disjoint : ∀ (t s : T), t ≠ s →
    Disjoint (topCell P t '' ball 0 1) (topCell P s '' ball 0 1)
  face_open_disjoint : ∀ (c d : SurfaceCell P), c ≠ d →
    Disjoint (surfaceCell P c '' ball 0 1) (surfaceCell P d '' ball 0 1)
  top_closed_cover : (⋃ t : T, topCell P t '' closedBall 0 1) = univ
  skeleton_image : faceSkeleton P = projection '' retainedBoundary (T := T)
  skeleton_closed : IsClosed (faceSkeleton P)
  top_disjoint_skeleton : ∀ t : T,
    Disjoint (topCell P t '' ball 0 1) (faceSkeleton P)
  sphere_attaching : ∀ t : T,
    MapsTo (topCell P t) (sphere 0 1) (faceSkeleton P)
  finite_relative : letI := relativeCW P
    RelCWComplex.Finite (univ : Set (TruncatedQuotient P))

/-- Every finite discrete raw tetrahedron pairing has genuine characteristic
maps on its original retained quotient and a finite relative CW structure above
the actual closed face skeleton. Pairing orbits index the zero faces. -/
theorem upper_geometry : UpperGeometry P (q P) where
  interior_fibers a b ha := by
    rw [← interior_normal_form P a b ha]
    exact ⟨fun h => Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h,
      fun h => Quotient.sound (s := Relation.EqvGen.setoid (TruncatedStep P)) h⟩
  face_fibers a b f ha := by
    obtain ⟨hd,h⟩ := actual_face_classification P a b f ha
    exact ⟨hd, ⟨fun he => h.mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) he),
      fun he => Quotient.sound (s := Relation.EqvGen.setoid (TruncatedStep P)) (h.mpr he)⟩⟩
  top_characteristic t := ⟨continuous_topCharacteristic P t,
    topCell_coe_disk P t, topCharacteristic_fiber P t⟩
  face_characteristic k t j := ⟨continuous_faceCharacteristic P k t j,
    directedFaceCell_coe_disk P k t j, faceCharacteristic_fiber P k t j⟩
  top_charts t := ⟨topCell_source P t, topCell_continuousOn P t, topCell_continuousOn_symm P t⟩
  face_charts c := ⟨surfaceCell_source P c,
    surfaceCell_continuousOn P c, surfaceCell_continuousOn_symm P c⟩
  top_closed_image := topCell_closed_image P
  directed_face_closed_image := directedFaceCell_closed_image P
  top_open_disjoint := topCell_open_disjoint P
  face_open_disjoint := surfaceCell_open_disjoint P
  top_closed_cover := topCell_closed_cover P
  skeleton_image := faceSkeleton_eq_boundaryImage P
  skeleton_closed := faceSkeleton_closed P
  top_disjoint_skeleton := topCell_disjoint_faceSkeleton P
  sphere_attaching := topCell_sphere_mapsTo P
  finite_relative := relativeCW_finite P

end D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
