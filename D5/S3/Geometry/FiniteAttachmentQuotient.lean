/- GID: D5/S3/Geometry/FiniteAttachmentQuotient
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteAttachmentQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite closed cover gives the canonical quotient of its attachments. -/
import D5.S3.Geometry.FiniteConeUnionWedge

/-! A common collapsed core identifies exactly the points over that core. -/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace D5.S3.Geometry.FiniteAttachmentQuotient

open FiniteConeUnionWedge

variable {X I : Type*} {D : I → Type*} [TopologicalSpace X]
  [∀ i, TopologicalSpace (D i)]

/-- The added point and every point of a summand lying over the core. -/
def attachingSet (f : ∀ i, C(D i, X)) (core : Set X) : Set (Unit ⊕ Σ i, D i) :=
  {s | Sum.elim (fun _ => True) (fun p => f p.1 p.2 ∈ core) s}

/-- The quotient that identifies all these points, including the added point. -/
abbrev AttachedQuotient (f : ∀ i, C(D i, X)) (core : Set X) :=
  Collapse (attachingSet f core)

private def rawMap (f : ∀ i, C(D i, X)) {core : Set X} (p : core) :
    C(Unit ⊕ Σ i, D i, Collapse core) :=
  ⟨Sum.elim (fun _ => collapseMap core p) (fun a => collapseMap core (f a.1 a.2)),
    continuous_const.sumElim
      (continuous_sigma fun i => (collapseMap core).continuous.comp (f i).continuous)⟩

private theorem rawMap_isQuotientMap [Finite I] [CompactSpace X] [T2Space X]
    [∀ i, CompactSpace (D i)] (f : ∀ i, C(D i, X)) {core : Set X} (p : core)
    (hc : IsClosed core) (cover : ∀ x, x ∈ core ∨ ∃ i d, f i d = x) :
    IsQuotientMap (rawMap f p) := by
  let _ : CompactSpace core := isCompact_iff_compactSpace.mp hc.isCompact
  let incl : core ⊕ (Σ i, D i) → X :=
    Sum.elim Subtype.val (fun z => f z.1 z.2)
  have hIncl : Continuous incl :=
    continuous_subtype_val.sumElim (continuous_sigma fun i => (f i).continuous)
  have hSurj : Function.Surjective incl := by
    intro x
    rcases cover x with h | ⟨i, d, hd⟩
    · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, d⟩, hd⟩
  let replaceCore : core ⊕ (Σ i, D i) → Unit ⊕ (Σ i, D i) :=
    Sum.map (fun _ => ()) id
  have hReplace : Continuous replaceCore := continuous_const.sumMap continuous_id
  apply IsQuotientMap.of_comp hReplace (rawMap f p).continuous
  have he : rawMap f p ∘ replaceCore = collapseMap core ∘ incl := by
    funext z
    rcases z with z | z
    · exact Quotient.sound (Or.inr ⟨p.property, z.property⟩)
    · rfl
  rw [he]
  exact isQuotientMap_quotient_mk'.comp (hIncl.isClosedMap.isQuotientMap hIncl hSurj)

private theorem rawMap_kernel (f : ∀ i, C(D i, X)) {core : Set X} (p : core)
    (hinj : ∀ i, Function.Injective (f i))
    (hoverlap : ∀ ⦃i j⦄, i ≠ j → ∀ (d : D i) (e : D j), f i d = f j e → f i d ∈ core)
    (s t : Unit ⊕ Σ i, D i) :
    (subsetSetoid (attachingSet f core)).r s t ↔ rawMap f p s = rawMap f p t := by
  classical
  constructor
  · rintro (rfl | ⟨hs, ht⟩)
    · rfl
    · have collapse_eq_core (z : Unit ⊕ Σ i, D i) (hz : z ∈ attachingSet f core) :
          rawMap f p z = collapseMap core p := by
        rcases z with _ | ⟨i, d⟩
        · rfl
        · exact Quotient.sound (Or.inr ⟨hz, p.property⟩)
      exact (collapse_eq_core s hs).trans (collapse_eq_core t ht).symm
  · intro h
    rcases s with _ | ⟨i, d⟩ <;> rcases t with _ | ⟨j, e⟩
    · exact Or.inr ⟨trivial, trivial⟩
    · have ht : f j e ∈ core := (Quotient.exact h).elim
        (fun he => he ▸ p.property) And.right
      exact Or.inr ⟨trivial, ht⟩
    · have hs : f i d ∈ core := (Quotient.exact h).elim
        (fun he => he.symm ▸ p.property) And.left
      exact Or.inr ⟨hs, trivial⟩
    · rcases Quotient.exact h with he | hcore
      · change f i d = f j e at he
        by_cases hij : i = j
        · subst j
          have hde := hinj i he
          subst e
          exact Or.inl rfl
        · have hd := hoverlap hij d e he
          refine Or.inr ⟨hd, ?_⟩
          change f j e ∈ core
          exact he ▸ hd
      · exact Or.inr hcore

/-- The canonical homeomorphism maps each summand using its injection and sends the added
point to the common core class. The index type and attaching sets may be empty. -/
theorem exists_homeomorph [Finite I] [CompactSpace X] [T2Space X]
    [∀ i, CompactSpace (D i)] (f : ∀ i, C(D i, X)) {core : Set X} (p : core)
    (hc : IsClosed core) (cover : ∀ x, x ∈ core ∨ ∃ i d, f i d = x)
    (hinj : ∀ i, Function.Injective (f i))
    (hoverlap : ∀ ⦃i j⦄, i ≠ j → ∀ (d : D i) (e : D j), f i d = f j e → f i d ∈ core) :
    ∃ e : AttachedQuotient f core ≃ₜ Collapse core,
      e (collapseMap (attachingSet f core) (Sum.inl ())) = collapseMap core p ∧
      ∀ i d, e (collapseMap (attachingSet f core) (Sum.inr ⟨i, d⟩)) =
        collapseMap core (f i d) := by
  let g := rawMap f p
  let e := (Homeomorph.Quotient.congrRight (rawMap_kernel f p hinj hoverlap)).trans
    (Topology.IsQuotientMap.homeomorph (f := g) (rawMap_isQuotientMap f p hc cover))
  exact ⟨e, rfl, fun _ _ => rfl⟩

end D5.S3.Geometry.FiniteAttachmentQuotient
