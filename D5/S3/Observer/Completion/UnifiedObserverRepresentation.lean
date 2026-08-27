/- GID: D5/S3/Observer/Completion/UnifiedObserverRepresentation
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/UnifiedObserverRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The complete protocol signature has a canonical quotient-range representation and universal factorization tests. -/

import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.UnifiedObserverRepresentation

theorem unified_observer_representation
    {X Protocol Law Interface : Type*}
    (law : Protocol → X → Law) (r : X → Interface) :
    (ExistsUnique fun equivalence :
        Quotient (Setoid.ker (fun x p => law p x)) ≃
          Set.range (fun x p => law p x) =>
      ∀ x, equivalence (Quotient.mk'' x) =
        ⟨(fun p => law p x), ⟨x, rfl⟩⟩) ∧
      ((∀ p, ∃ factor : Set.range r → Law,
          law p = factor ∘ Set.rangeFactorization r) ↔
        ∀ x y, r x = r y → ∀ p, law p x = law p y) ∧
      ((∀ x y, r x = r y → ∀ p, law p x = law p y) ↔
        ExistsUnique fun factor : Set.range r →
            Set.range (fun x p => law p x) =>
          Set.rangeFactorization (fun x p => law p x) =
              factor ∘ Set.rangeFactorization r) := by
  constructor
  · refine ⟨Setoid.quotientKerEquivRange (fun x p => law p x), ?_, ?_⟩
    · intro x
      rfl
    · intro other hother
      apply Equiv.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      exact (hother x).trans rfl
  constructor
  · constructor
    · rintro h x y hxy p
      obtain ⟨factor, factorization⟩ := h p
      calc
        law p x = factor (Set.rangeFactorization r x) :=
          congrFun factorization x
        _ = factor (Set.rangeFactorization r y) :=
          congrArg factor (Subtype.ext hxy)
        _ = law p y := (congrFun factorization y).symm
    · intro h p
      let factor : Set.range r → Law := fun state =>
        law p (Classical.choose state.property)
      refine ⟨factor, ?_⟩
      funext x
      change law p x = law p (Classical.choose (Set.rangeFactorization r x).property)
      exact (h (Classical.choose (Set.rangeFactorization r x).property) x
        ((Classical.choose_spec (Set.rangeFactorization r x).property).trans rfl) p).symm
  · constructor
    · intro h
      let factor : Set.range r → Set.range (fun x p => law p x) := fun state =>
        ⟨(fun p => law p (Classical.choose state.property)),
          ⟨Classical.choose state.property, rfl⟩⟩
      refine ⟨factor, ?_, ?_⟩
      · funext x
        apply Subtype.ext
        funext p
        change law p x = law p (Classical.choose (Set.rangeFactorization r x).property)
        exact (h (Classical.choose (Set.rangeFactorization r x).property) x
          ((Classical.choose_spec (Set.rangeFactorization r x).property).trans rfl) p).symm
      · intro other other_factorization
        apply Set.rangeFactorization_surjective.injective_comp_right
        exact other_factorization.symm.trans (by
          funext x
          apply Subtype.ext
          funext p
          change law p x = law p (Classical.choose (Set.rangeFactorization r x).property)
          exact (h (Classical.choose (Set.rangeFactorization r x).property) x
            ((Classical.choose_spec (Set.rangeFactorization r x).property).trans rfl) p).symm)
    · rintro ⟨factor, factorization, _⟩ x y hxy p
      have pointwise :
          (fun p => law p x) = factor (Set.rangeFactorization r x) := by
        have equality := congrArg Subtype.val (congrFun factorization x)
        change (fun p => law p x) = (factor (Set.rangeFactorization r x) :
          Protocol → Law) at equality
        exact equality
      have pointwise' :
          factor (Set.rangeFactorization r y) = (fun p => law p y) := by
        have equality := congrArg Subtype.val (congrFun factorization y)
        change (Set.rangeFactorization (fun x p => law p x) y :
          Protocol → Law) = (factor (Set.rangeFactorization r y) : Protocol → Law) at equality
        exact equality.symm
      have equalFactor :
          factor (Set.rangeFactorization r x) =
            factor (Set.rangeFactorization r y) :=
        congrArg factor (Subtype.ext hxy)
      have equalSignature :
          (fun p => law p x) = (fun p => law p y) := by
        calc
          (fun p => law p x) = (factor (Set.rangeFactorization r x) : Protocol → Law) := pointwise
          _ = (factor (Set.rangeFactorization r y) : Protocol → Law) :=
            congrArg Subtype.val equalFactor
          _ = (fun p => law p y) := pointwise'
      exact congrFun equalSignature p

#print axioms unified_observer_representation

end D5.S3.Observer.Completion.UnifiedObserverRepresentation
