/- GID: D5/S3/ObserverMemory/Refinement/FactorizationCategory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/FactorizationCategory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement factorization data composes, is reflexive, and carries both preorder and categorical readings. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.FactorizationCategory

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

universe u

/- A readout keeps the source object type and its actual codomain together. -/
structure Readout (X : Type u) where
  codomain : Type u
  readout : Concept X codomain

/- An isomorphism of codomains is the witness used by the quotient reading. -/
structure CodomainIso (B₁ B₂ : Type*) where
  forward : B₁ → B₂
  backward : B₂ → B₁
  left_inv : Function.LeftInverse backward forward
  right_inv : Function.RightInverse backward forward

def CodomainIso.refl (B : Type*) : CodomainIso B B :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def CodomainIso.symm {B₁ B₂ : Type*} (e : CodomainIso B₁ B₂) : CodomainIso B₂ B₁ :=
  ⟨e.backward, e.forward, e.right_inv, e.left_inv⟩

def CodomainIso.trans {B₁ B₂ B₃ : Type*}
    (e₁ : CodomainIso B₁ B₂) (e₂ : CodomainIso B₂ B₃) : CodomainIso B₁ B₃ :=
  ⟨e₂.forward ∘ e₁.forward, e₁.backward ∘ e₂.backward,
    fun x =>
      (congrArg e₁.backward (e₂.left_inv (e₁.forward x))).trans (e₁.left_inv x),
    fun x =>
      (congrArg e₂.forward (e₁.right_inv (e₂.backward x))).trans (e₂.right_inv x)⟩

/- The source Sigma type: a factor map and its pointwise commuting proof. -/
structure Refines {X B' B : Type*} (q' : Concept X B') (q : Concept X B) where
  factor : B' → B
  commutes : ∀ x : X, q x = factor (q' x)

def identityRefinement {X B : Type*} (q : Concept X B) : Refines q q :=
  ⟨id, fun _ => rfl⟩

def composeRefinement {X B'' B' B : Type*}
    {q'' : Concept X B''} {q' : Concept X B'} {q : Concept X B}
    (h' : Refines q' q) (h'' : Refines q'' q') : Refines q'' q :=
  ⟨h'.factor ∘ h''.factor, fun x =>
    (h'.commutes x).trans (congrArg h'.factor (h''.commutes x))⟩

private theorem refines_ext {X B' B : Type*} {q' : Concept X B'} {q : Concept X B}
    (h₁ h₂ : Refines q' q) (hf : h₁.factor = h₂.factor) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hf
  rfl

def isoEquivalent {X : Type*} (r₁ r₂ : Readout X) : Prop :=
  ∃ e : CodomainIso r₁.codomain r₂.codomain,
    ∀ x : X, r₂.readout x = e.forward (r₁.readout x)

theorem isoEquivalent_refl {X : Type*} (r : Readout X) : isoEquivalent r r := by
  exact ⟨CodomainIso.refl r.codomain, fun _ => rfl⟩

theorem isoEquivalent_symm {X : Type*} {r₁ r₂ : Readout X}
    (h : isoEquivalent r₁ r₂) : isoEquivalent r₂ r₁ := by
  rcases h with ⟨e, h⟩
  refine ⟨e.symm, ?_⟩
  intro x
  calc
    r₁.readout x = e.backward (e.forward (r₁.readout x)) := (e.left_inv _).symm
    _ = e.backward (r₂.readout x) := congrArg e.backward (h x).symm

theorem isoEquivalent_trans {X : Type*} {r₁ r₂ r₃ : Readout X}
    (h₁₂ : isoEquivalent r₁ r₂) (h₂₃ : isoEquivalent r₂ r₃) :
    isoEquivalent r₁ r₃ := by
  rcases h₁₂ with ⟨e₁, h₁₂⟩
  rcases h₂₃ with ⟨e₂, h₂₃⟩
  refine ⟨e₁.trans e₂, ?_⟩
  intro x
  calc
    r₃.readout x = e₂.forward (r₂.readout x) := h₂₃ x
    _ = e₂.forward (e₁.forward (r₁.readout x)) := congrArg e₂.forward (h₁₂ x)
    _ = (e₁.trans e₂).forward (r₁.readout x) := rfl

def readoutSetoid (X : Type*) : Setoid (Readout X) where
  r := isoEquivalent
  iseqv := ⟨isoEquivalent_refl, isoEquivalent_symm, isoEquivalent_trans⟩

abbrev QuotientCodomainClass (X : Type*) := Quotient (readoutSetoid X)

private noncomputable def transport_refinement {X : Type*} {r₁ r₂ s₁ s₂ : Readout X}
    (h₁ : isoEquivalent r₁ s₁) (h₂ : isoEquivalent r₂ s₂)
    (h : Refines r₁.readout r₂.readout) : Refines s₁.readout s₂.readout := by
  let e₁ := Classical.choose h₁
  let e₂ := Classical.choose h₂
  have he₁ := Classical.choose_spec h₁
  have he₂ := Classical.choose_spec h₂
  let factor := e₂.forward ∘ h.factor ∘ e₁.backward
  refine ⟨factor, ?_⟩
  intro x
  have hx : r₁.readout x = e₁.backward (s₁.readout x) := by
    calc
      r₁.readout x = e₁.backward (e₁.forward (r₁.readout x)) := (e₁.left_inv _).symm
      _ = e₁.backward (s₁.readout x) := congrArg e₁.backward (he₁ x).symm
  calc
    s₂.readout x = e₂.forward (r₂.readout x) := he₂ x
    _ = e₂.forward (h.factor (r₁.readout x)) := congrArg e₂.forward (h.commutes x)
    _ = e₂.forward (h.factor (e₁.backward (s₁.readout x))) :=
      congrArg (fun y => e₂.forward (h.factor y)) hx
    _ = factor (s₁.readout x) := rfl

private theorem refinement_iff_of_iso {X : Type*} {r₁ r₂ s₁ s₂ : Readout X}
    (h₁ : isoEquivalent r₁ s₁) (h₂ : isoEquivalent r₂ s₂) :
    Nonempty (Refines r₁.readout r₂.readout) ↔
      Nonempty (Refines s₁.readout s₂.readout) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨transport_refinement h₁ h₂ h⟩
  · rintro ⟨h⟩
    exact ⟨transport_refinement (isoEquivalent_symm h₁) (isoEquivalent_symm h₂) h⟩

def classRefinementRelation {X : Type*} :
    QuotientCodomainClass X → QuotientCodomainClass X → Prop :=
  fun a b => Quotient.liftOn₂ a b
    (fun r₁ r₂ => Nonempty (Refines r₁.readout r₂.readout))
    (fun r₁ r₂ s₁ s₂ h₁ h₂ => propext (refinement_iff_of_iso h₁ h₂))

structure PreorderWitness (α : Type*) where
  relation : α → α → Prop
  reflexive : ∀ a, relation a a
  transitive : ∀ {a b c}, relation a b → relation b c → relation a c

def quotientCodomainPreorder {X : Type*} :
    PreorderWitness (QuotientCodomainClass X) where
  relation := classRefinementRelation
  reflexive := by
    intro a
    refine Quotient.inductionOn a ?_
    intro r
    exact ⟨identityRefinement r.readout⟩
  transitive := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro r₀ r₁ r₂ h₀ h₁
    rcases h₀ with ⟨h₀⟩
    rcases h₁ with ⟨h₁⟩
    exact ⟨composeRefinement h₁ h₀⟩

structure FactorizationCategoryReading (X : Type*) where
  identity : ∀ r : Readout X, Refines r.readout r.readout
  compose : ∀ {r₀ r₁ r₂ : Readout X},
    Refines r₀.readout r₁.readout → Refines r₁.readout r₂.readout →
      Refines r₀.readout r₂.readout
  left_identity : ∀ {r₀ r₁ : Readout X} (h : Refines r₀.readout r₁.readout),
    compose (identity r₀) h = h
  right_identity : ∀ {r₀ r₁ : Readout X} (h : Refines r₀.readout r₁.readout),
    compose h (identity r₁) = h
  associative : ∀ {r₀ r₁ r₂ r₃ : Readout X}
    (h₀ : Refines r₀.readout r₁.readout)
    (h₁ : Refines r₁.readout r₂.readout)
    (h₂ : Refines r₂.readout r₃.readout),
    compose (compose h₀ h₁) h₂ = compose h₀ (compose h₁ h₂)

def fixedCodomainFactorizationCategory {X : Type*} :
    FactorizationCategoryReading X where
  identity := fun r => identityRefinement r.readout
  compose := fun h₀ h₁ => composeRefinement h₁ h₀
  left_identity := by
    intro r₀ r₁ h
    apply refines_ext _ _
    funext x
    rfl
  right_identity := by
    intro r₀ r₁ h
    apply refines_ext _ _
    funext x
    rfl
  associative := by
    intro r₀ r₁ r₂ r₃ h₀ h₁ h₂
    apply refines_ext _ _
    funext x
    rfl

theorem refinement_factorization_structure
    {X B'' B' B : Type*}
    (q'' : Concept X B'') (q' : Concept X B') (q : Concept X B) :
    (Nonempty (Refines q q) ∧
      (Nonempty (Refines q' q) → Nonempty (Refines q'' q') →
        Nonempty (Refines q'' q))) ∧
      Nonempty (PreorderWitness (QuotientCodomainClass X)) ∧
      Nonempty (FactorizationCategoryReading X) := by
  refine ⟨?_, ⟨quotientCodomainPreorder⟩, ⟨fixedCodomainFactorizationCategory⟩⟩
  refine ⟨⟨identityRefinement q⟩, ?_⟩
  intro h₁ h₂
  rcases h₁ with ⟨h₁⟩
  rcases h₂ with ⟨h₂⟩
  exact ⟨composeRefinement h₁ h₂⟩

#print axioms refinement_factorization_structure

end D5.S3.ObserverMemory.Refinement.FactorizationCategory
