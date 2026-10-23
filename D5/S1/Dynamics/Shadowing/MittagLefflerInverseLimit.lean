/- GID: D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/MittagLefflerInverseLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-cover shadowing passes to compact Hausdorff Mittag-Leffler limits. -/

import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Sets.OpenCover

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/-- Successive errors lie in single members of the control cover. -/
def PseudoOrbit {X : Type*} [TopologicalSpace X] (f : X → X)
    (C : Finset (Opens X)) (x : ℕ → X) : Prop :=
  ∀ n, ∃ U ∈ C, f (x n) ∈ U ∧ x (n + 1) ∈ U

/-- One orbit follows a sequence at every natural time, including zero. -/
def Shadows {X : Type*} [TopologicalSpace X] (f : X → X)
    (C : Finset (Opens X)) (x : ℕ → X) (z : X) : Prop :=
  ∀ n, ∃ U ∈ C, f^[n] z ∈ U ∧ x n ∈ U

/-- Shadowing with respect to every finite open cover; empty spaces are permitted. -/
def HasShadowing {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ C : Finset (Opens X), IsOpenCover (fun U : C => U.1) →
    ∃ D : Finset (Opens X), IsOpenCover (fun U : D => U.1) ∧
      ∀ x : ℕ → X, PseudoOrbit f D x → ∃ z, Shadows f C x z

variable {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{max u v})

private instance limit_compact [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    CompactSpace (TopCat.limitCone F).pt := by
  have h : IsClosed {x : ∀ j, F.obj j | ∀ {i j} (f : i ⟶ j), F.map f (x i) = x j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun f =>
      isClosed_eq ((F.map f).hom.continuous.comp (continuous_apply i)) (continuous_apply j)
  exact h.isClosedEmbedding_subtypeVal.compactSpace

/-- A natural continuous endomorphism acts coordinatewise on the concrete limit. -/
def limitDynamics (d : F ⟶ F) : C((TopCat.limitCone F).pt, (TopCat.limitCone F).pt) where
  toFun x := ⟨fun j => d.app j (x.1 j), fun {i j} f => by
    have h := ConcreteCategory.congr_hom (d.naturality f) (x.1 i)
    change d.app j (F.map f (x.1 i)) = F.map f (d.app i (x.1 i)) at h
    rw [← h, x.2 f]⟩
  continuous_toFun := (continuous_pi fun j =>
    (d.app j).hom.continuous.comp ((continuous_apply j).comp continuous_subtype_val)).subtype_mk _

private theorem projection_iterate (d : F ⟶ F) (j : J) (n : ℕ)
    (x : (TopCat.limitCone F).pt) :
    ((limitDynamics F d)^[n] x).1 j = (d.app j)^[n] (x.1 j) := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [iterate_succ_apply', limitDynamics]
      exact congrArg (d.app j) hn

/-- Every point in all incoming images lifts to a full compatible thread. -/
theorem compact_projection_image [IsCofiltered J] [Quiver.IsThin J]
    [∀ j, Nonempty (F.obj j)] [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (i : J) :
    range ((TopCat.limitCone F).π.app i) = (F ⋙ forget TopCat).eventualRange i := by
  classical
  apply Set.ext
  intro a
  constructor
  · rintro ⟨x, rfl⟩
    exact (Functor.mem_eventualRange_iff _).2 fun j f => ⟨x.1 j, x.2 f⟩
  · intro ha
    let A := Option (Σ r s : J, r ⟶ s)
    let t : A → Set (∀ j, F.obj j) := fun e => match e with
      | none => {x | x i = a}
      | some e => {x | F.map e.2.2 (x e.1) = x e.2.1}
    have ht : ∀ e, IsClosed (t e) := by
      intro e
      cases e with
      | none => exact isClosed_eq (continuous_apply i) continuous_const
      | some e =>
          exact isClosed_eq
            ((F.map e.2.2).hom.continuous.comp (continuous_apply e.1)) (continuous_apply e.2.1)
    have hfin : ∀ s : Finset A, (⋂ e ∈ s, t e).Nonempty := by
      intro s
      let G : Finset J := insert i (s.biUnion fun e => match e with
        | none => {i}
        | some e => {e.1, e.2.1})
      obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists G
      let p : ∀ j ∈ G, k ⟶ j := fun j hj => (hk hj).some
      obtain ⟨b, hb⟩ := (Functor.mem_eventualRange_iff _).1 ha (p i (Finset.mem_insert_self _ _))
      let x : ∀ j, F.obj j := fun j => if hj : j ∈ G then F.map (p j hj) b
        else Classical.choice (inferInstance : Nonempty (F.obj j))
      refine ⟨x, ?_⟩
      simp only [mem_iInter]
      intro e he
      cases e with
      | none => simpa [t, x, G] using hb
      | some e =>
        have hr : e.1 ∈ G := Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨some e, he, by simp⟩)
        have hs : e.2.1 ∈ G := Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨some e, he, by simp⟩)
        change F.map e.2.2 (x e.1) = x e.2.1
        dsimp only [x]
        rw [dif_pos hr, dif_pos hs]
        have hp : p e.1 hr ≫ e.2.2 = p e.2.1 hs := Subsingleton.elim _ _
        have hm := ConcreteCategory.congr_hom (F.map_comp (p e.1 hr) e.2.2) b
        simpa [hp] using hm.symm
    obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty ht hfin
    have hxi : x i = a := (mem_iInter.mp hx) none
    refine ⟨⟨x, fun {r s} f => (mem_iInter.mp hx) (some ⟨r, s, f⟩)⟩, hxi⟩

private theorem cover_of_pointwise {X : Type*} [TopologicalSpace X]
    (C : Finset (Opens X)) (h : ∀ x, ∃ U ∈ C, x ∈ U) :
    IsOpenCover (fun U : C => U.1) := by
  rw [IsOpenCover, eq_top_iff]
  intro x _
  obtain ⟨U, hU, hx⟩ := h x
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

/-- A finite cover of the limit is refined by finitely many opens at one stage,
covering the actual projection image rather than the whole stage. -/
theorem finite_cover_descent [IsCofiltered J]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (C : Finset (Opens (TopCat.limitCone F).pt))
    (hC : IsOpenCover (fun U : C => U.1)) :
    ∃ (i : J) (V : Finset (Opens (F.obj i))),
      (∀ a ∈ range ((TopCat.limitCone F).π.app i), ∃ U ∈ V, a ∈ U) ∧
      (∀ U ∈ V, ∃ W ∈ C, ((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i)) ⊆
        (W : Set (TopCat.limitCone F).pt)) := by
  classical
  let L := TopCat.limitCone F
  let : CompactSpace L.pt := limit_compact F
  have hb := TopCat.isTopologicalBasis_cofiltered_limit F L (TopCat.limitConeIsLimit F)
    (fun j => {U : Set (F.obj j) | IsOpen U})
    (fun _ => isTopologicalBasis_opens) (fun _ => isOpen_univ)
    (fun _ _ _ h h' => h.inter h') (fun _ _ f _ h => h.preimage (F.map f).hom.continuous)
  have hn : ∀ x : L.pt, ∃ (j : J) (U : Opens (F.obj j)),
      x ∈ (L.π.app j) ⁻¹' (U : Set _) ∧
        ∃ W ∈ C, (L.π.app j) ⁻¹' (U : Set (F.obj j)) ⊆ (W : Set L.pt) := by
    intro x
    obtain ⟨W, hxW⟩ := hC.exists_mem x
    obtain ⟨B, ⟨j, U, hU, rfl⟩, hxB, hBW⟩ := hb.exists_subset_of_mem_open hxW W.1.isOpen
    exact ⟨j, ⟨U, hU⟩, hxB, W.1, W.2, hBW⟩
  choose j U hxU hUC using hn
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (univ : Set L.pt)).elim_finite_subcover
    (fun x => (L.π.app (j x)) ⁻¹' (U x : Set _))
    (fun x => (U x).isOpen.preimage (L.π.app (j x)).hom.continuous)
    (by intro x _; exact mem_iUnion.mpr ⟨x, hxU x⟩)
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (s.image j)
  let q : ∀ x ∈ s, i ⟶ j x := fun x hx => (hi (Finset.mem_image.mpr ⟨x, hx, rfl⟩)).some
  let V : s → Opens (F.obj i) := fun x => (U x.1).comap (F.map (q x.1 x.2)).hom
  refine ⟨i, s.attach.image V, ?_, ?_⟩
  · rintro a ⟨x, rfl⟩
    have hx := hs (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨y, hys, hxy⟩ := hx
    refine ⟨V ⟨y, hys⟩, Finset.mem_image.mpr ⟨⟨y, hys⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    change F.map (q y hys) (x.1 i) ∈ U y
    rwa [x.2 (q y hys)]
  · intro B hB
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨W, hW, hUW⟩ := hUC x.1
    refine ⟨W, hW, fun y hy => hUW ?_⟩
    change y.1 (j x.1) ∈ U x.1
    change F.map (q x.1 x.2) (y.1 i) ∈ U x.1 at hy
    rwa [y.2 (q x.1 x.2)] at hy

private theorem bonding_iterate (d : F ⟶ F) {i k : J} (p : k ⟶ i)
    (n : ℕ) (x : F.obj k) :
    F.map p ((d.app k)^[n] x) = (d.app i)^[n] (F.map p x) := by
  have h := ConcreteCategory.congr_hom (d.naturality p)
  have he : Semiconj (F.map p) (d.app k) (d.app i) := fun x => (h x).symm
  exact he.iterate_right n x

/-- Finite-cover shadowing passes to a compact Hausdorff cofiltered thin ML limit.
The shadowing point is chosen in the entire finer stage and lifted only after
projection to the stabilized coarse image. -/
theorem shadowing_inverse_limit_of_mittag_leffler [IsCofiltered J] [Quiver.IsThin J]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (d : F ⟶ F) (hML : (F ⋙ forget TopCat).IsMittagLeffler)
    (hshadow : ∀ j, HasShadowing (d.app j)) :
    HasShadowing (limitDynamics F d) := by
  classical
  by_cases hne : ∀ j, Nonempty (F.obj j)
  · let : ∀ j, Nonempty (F.obj j) := hne
    intro C hC
    obtain ⟨i, V, hV, hVC⟩ := finite_cover_descent F C hC
    obtain ⟨k, p, hp⟩ := (Functor.isMittagLeffler_iff_eventualRange _).1 hML i
    let B : Finset (Opens (F.obj k)) := V.image fun U => U.comap (F.map p).hom
    have hB : IsOpenCover (fun U : B => U.1) := by
      apply cover_of_pointwise
      intro x
      have hx : F.map p x ∈ range ((TopCat.limitCone F).π.app i) := by
        rw [compact_projection_image F i, hp]
        exact ⟨x, rfl⟩
      obtain ⟨U, hU, hxU⟩ := hV _ hx
      exact ⟨U.comap (F.map p).hom, Finset.mem_image.mpr ⟨U, hU, rfl⟩, hxU⟩
    obtain ⟨W, hW, htrace⟩ := hshadow k B hB
    let D : Finset (Opens (TopCat.limitCone F).pt) :=
      W.image fun U => U.comap ((TopCat.limitCone F).π.app k).hom
    refine ⟨D, cover_of_pointwise D ?_, ?_⟩
    · intro x
      obtain ⟨U, hxU⟩ := hW.exists_mem (x.1 k)
      exact ⟨U.1.comap ((TopCat.limitCone F).π.app k).hom,
        Finset.mem_image.mpr ⟨U.1, U.2, rfl⟩, hxU⟩
    · intro x hx
      have hxk : PseudoOrbit (d.app k) W (fun n => (x n).1 k) := by
        intro n
        obtain ⟨U, hU, hf, hx'⟩ := hx n
        change U ∈ W.image _ at hU
        obtain ⟨U, hUW, rfl⟩ := Finset.mem_image.mp hU
        exact ⟨U, hUW, hf, hx'⟩
      obtain ⟨b, hb⟩ := htrace _ hxk
      have ha : F.map p b ∈ range ((TopCat.limitCone F).π.app i) := by
        rw [compact_projection_image F i, hp]
        exact ⟨b, rfl⟩
      obtain ⟨z, hz⟩ := ha
      change z.1 i = F.map p b at hz
      refine ⟨z, fun n => ?_⟩
      obtain ⟨U, hU, hbn, hxn⟩ := hb n
      change U ∈ V.image _ at hU
      obtain ⟨U, hUV, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨T, hT, hUT⟩ := hVC U hUV
      refine ⟨T, hT, hUT ?_, hUT ?_⟩
      · change ((limitDynamics F d)^[n] z).1 i ∈ U
        rw [projection_iterate, hz, ← bonding_iterate F d p]
        exact hbn
      · change (x n).1 i ∈ U
        rw [← (x n).2 p]
        exact hxn
  · obtain ⟨j, hj⟩ := not_forall.mp hne
    have he : IsEmpty (F.obj j) := not_nonempty_iff.mp hj
    let := he
    intro C _
    refine ⟨∅, cover_of_pointwise ∅ ?_, ?_⟩
    · intro x; exact isEmptyElim (x.1 j)
    · intro x _; exact isEmptyElim ((x 0).1 j)

end D5.S1.Dynamics.Shadowing
