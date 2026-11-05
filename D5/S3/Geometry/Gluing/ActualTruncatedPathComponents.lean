/- GID: D5/S3/Geometry/Gluing/ActualTruncatedPathComponents
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualTruncatedPathComponents
   mirror-E: none(waiver:arbitrary-discrete-action-path-component-classification)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.PathConnected,mathlib/module/Mathlib.Topology.Connected.TotallyDisconnected]
   utility: none
   digest: Paths in the original full retained quotient detect exactly generated tag orbits. -/

import D5.S3.Geometry.Gluing.ActualLinkAffineFan
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order

/-! # Path components of the original full retained quotient -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.ActualTruncatedPathComponents

open D5.S3.Geometry.Gluing.ActualLinkAffineFan
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (faceWord)
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits (act act_one act_mul)

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

private abbrev project (u v : G) : TruncatedPoint Ω → TruncatedQuotient u v Ω :=
  @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v))

/-- All four original cap inequalities and the original affine mass equation. -/
private theorem retained_convex : Convex ℝ
    {p : Fin 4 → ℝ | (∀ i, 0 ≤ p i ∧ p i ≤ 3/4) ∧ (∑ i, p i) = 1} := by
  have hsum : IsLinearMap ℝ (fun p : Fin 4 → ℝ => ∑ i, p i) := {
    map_add := by intro p r; simp only [Pi.add_apply, Finset.sum_add_distrib]
    map_smul := by intro s p; simp only [Pi.smul_apply, Finset.smul_sum] }
  have he : {p : Fin 4 → ℝ | (∀ i, 0 ≤ p i ∧ p i ≤ 3/4) ∧ (∑ i, p i) = 1} =
      Set.Icc (0 : Fin 4 → ℝ) (fun _ => (3/4 : ℝ)) ∩
        {p : Fin 4 → ℝ | (∑ i, p i) = 1} := by
    ext p
    exact ⟨fun hp => ⟨⟨fun i => (hp.1 i).1, fun i => (hp.1 i).2⟩, hp.2⟩,
      fun hp => ⟨fun i => ⟨hp.1.1 i, hp.1.2 i⟩, hp.2⟩⟩
  rw [he]
  exact (convex_Icc (𝕜 := ℝ) _ _).inter (convex_hyperplane hsum 1)

/-- The complete zero face is nonempty inside the original capped carrier. -/
private def facePoint (x : Ω) (f : Fin 4) : TruncatedPoint Ω :=
  (x, ⟨fun i => if i = f then 0 else 1/3, by
    constructor
    · intro i
      dsimp only
      split_ifs <;> norm_num
    · fin_cases f <;> norm_num [Fin.sum_univ_succ]⟩)

variable [TopologicalSpace Ω]

private theorem same_tag_joined (u v : G) (a b : TruncatedPoint Ω)
    (htag : a.1 = b.1) : Joined (project u v a) (project u v b) := by
  rcases a with ⟨x,p⟩
  rcases b with ⟨y,r⟩
  change x = y at htag
  subst y
  have hj : Joined p r :=
    ((retained_convex.isPathConnected ⟨p.val,p.property⟩).joinedIn
      p.val p.property r.val r.property).joined_subtype
  have hi : Continuous (fun z : TruncatedTetrahedron => project u v (x,z)) :=
    continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
  exact hj.map hi

private theorem across_face_joined (u v : G) (f : Fin 4)
    (a b : TruncatedPoint Ω) (htag : b.1 = act a.1 (faceWord u v f)) :
    Joined (project u v a) (project u v b) := by
  let z := facePoint a.1 f
  have hstep : TruncatedStep u v z (truncatedMove u v f z) :=
    ⟨f, by simp [z,facePoint], rfl⟩
  have he : project u v z = project u v (truncatedMove u v f z) :=
    Quotient.sound (Relation.EqvGen.rel _ _ hstep)
  have ha : Joined (project u v a) (project u v z) :=
    same_tag_joined u v a z rfl
  have hb : Joined (project u v (truncatedMove u v f z)) (project u v b) :=
    same_tag_joined u v _ b htag.symm
  exact ha.trans (by rw [he]; exact hb)

private theorem generated_joined (u v : G) (g : G)
    (hg : g ∈ Subgroup.closure ({u,v} : Set G)) :
    ∀ (a b : TruncatedPoint Ω), act a.1 g = b.1 →
      Joined (project u v a) (project u v b) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hgu | hgv
    · subst g
      intro a b hab
      exact across_face_joined u v 0 a b (by simpa [faceWord] using hab.symm)
    · subst g
      intro a b hab
      exact across_face_joined u v 1 a b (by simpa [faceWord] using hab.symm)
  | one =>
    intro a b hab
    exact same_tag_joined u v a b (by simpa using hab)
  | mul g h hg hh ihg ihh =>
    intro a b hab
    let c : TruncatedPoint Ω := (act a.1 g,a.2)
    exact (ihg a c rfl).trans (ihh c b ((act_mul a.1 g h).trans hab))
  | inv g hg ih =>
    intro a b hab
    apply Joined.symm
    apply ih b a
    rw [← hab, act_mul]
    simp

private theorem faceWord_mem (u v : G) (f : Fin 4) :
    faceWord u v f ∈ Subgroup.closure ({u,v} : Set G) := by
  have hu : u ∈ Subgroup.closure ({u,v} : Set G) := Subgroup.subset_closure (by simp)
  have hv : v ∈ Subgroup.closure ({u,v} : Set G) := Subgroup.subset_closure (by simp)
  fin_cases f
  · simpa [faceWord] using hu
  · simpa [faceWord] using hv
  · simpa [faceWord] using (Subgroup.closure ({u,v} : Set G)).inv_mem hv
  · simpa [faceWord] using (Subgroup.closure ({u,v} : Set G)).inv_mem hu

variable [DiscreteTopology Ω]

/-- A generated-orbit characteristic descends through the full original EqvGen. -/
private theorem joined_implies_orbit (u v : G) (a b : TruncatedPoint Ω)
    (hj : Joined (project u v a) (project u v b)) :
    ∃ g ∈ Subgroup.closure ({u,v} : Set G), act a.1 g = b.1 := by
  classical
  let H := Subgroup.closure ({u,v} : Set G)
  let P : Ω → Prop := fun y => ∃ g ∈ H, act a.1 g = y
  have transport (x : Ω) (g : G) (hg : g ∈ H) : P x ↔ P (act x g) := by
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨k*g,H.mul_mem hk hg,(act_mul a.1 k g).symm⟩
    · rintro ⟨k,hk,he⟩
      refine ⟨k*g⁻¹,H.mul_mem hk (H.inv_mem hg),?_⟩
      rw [← act_mul, he, act_mul]
      simp
  have invariant (c d : TruncatedPoint Ω)
      (h : Relation.EqvGen (TruncatedStep u v) c d) : P c.1 ↔ P d.1 := by
    induction h with
    | rel c d h =>
      obtain ⟨f,_,rfl⟩ := h
      exact transport c.1 (faceWord u v f) (faceWord_mem u v f)
    | refl c => rfl
    | symm c d h ih => exact ih.symm
    | trans c d e hcd hde ihcd ihde => exact ihcd.trans ihde
  let label : TruncatedPoint Ω → Bool := fun c => if P c.1 then true else false
  have hlabel (c d : TruncatedPoint Ω)
      (h : Relation.EqvGen (TruncatedStep u v) c d) : label c = label d := by
    dsimp only [label]
    rw [invariant c d h]
  let L : TruncatedQuotient u v Ω → Bool := Quotient.lift label hlabel
  have hc : Continuous label :=
    (continuous_of_discreteTopology : Continuous
      (fun x : Ω => if P x then true else false)).comp continuous_fst
  have hL : Continuous L := hc.quotient_lift hlabel
  obtain ⟨p⟩ := hj.map hL
  have he : p 0 = p 1 :=
    PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval) p.continuous
  rw [p.source,p.target] at he
  change (if P a.1 then true else false) = (if P b.1 then true else false) at he
  have ha : P a.1 := ⟨1,H.one_mem,act_one a.1⟩
  change P b.1
  by_contra hb
  simp [ha,hb] at he

/-- Path components of the original full retained quotient are precisely the
orbits of the subgroup generated by u and v on the original tags. The carrier
contains every cap; the relation is the full face-guarded EqvGen and the topology
is its original quotient topology. No finiteness or nonemptiness is assumed. -/
theorem actual_truncated_joined_iff (u v : G) (a b : TruncatedPoint Ω) :
    Joined (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep u v)) a)
      (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep u v)) b) ↔
    ∃ g ∈ Subgroup.closure ({u,v} : Set G), act a.1 g = b.1 := by
  constructor
  · exact joined_implies_orbit u v a b
  · rintro ⟨g,hg,hab⟩
    exact generated_joined u v g hg a b hab

end D5.S3.Geometry.Gluing.ActualTruncatedPathComponents
