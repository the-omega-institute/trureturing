/- GID: D5/S3/ArithUnits/FiniteAddActionCardinality
   generality: G
   mirror-B: D5/B/S3/ArithUnits/FiniteAddActionCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A free finite additive action forces the acting group order to divide the state-space cardinality, while a pretransitive invariant support is empty or full. -/

import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.FiniteAddActionCardinality

/-! An invariant finite support is a union of additive orbits.  The first theorem
records the extreme case where the action has one orbit; the second extracts
the arithmetic consequence of freeness from Burnside's decomposition. -/

theorem invariant_finset_empty_or_univ_of_pretransitive
    {G X : Type*} [AddGroup G] [AddAction G X]
    [AddAction.IsPretransitive G X] [Fintype X] [DecidableEq X]
    (D : Finset X)
    (hD : ∀ g : G, D.image (fun x => g +ᵥ x) = D) :
    D = ∅ ∨ D = Finset.univ := by
  classical
  rcases D.eq_empty_or_nonempty with hD0 | hDpos
  · exact Or.inl hD0
  · right
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨x₀, hx₀⟩ := hDpos
    obtain ⟨g, hg⟩ := AddAction.exists_vadd_eq G x₀ x
    have hx' : g +ᵥ x₀ ∈ D.image (fun y => g +ᵥ y) := by
      exact Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩
    rw [hD g] at hx'
    simpa [hg] using hx'

theorem card_addGroup_dvd_of_free_finite_action
    {G X : Type*} [AddGroup G] [AddAction G X]
    [Fintype G] [Fintype X]
    (hfree : ∀ g : G, g ≠ 0 → ∀ x : X, g +ᵥ x ≠ x) :
    Fintype.card G ∣ Fintype.card X := by
  classical
  have hsum :
      (∑ g : G, Fintype.card (AddAction.fixedBy X g)) = Fintype.card X := by
    rw [Finset.sum_eq_single 0]
    · let e : AddAction.fixedBy X (0 : G) ≃ X :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, by simp [AddAction.fixedBy]⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      simpa using (Fintype.card_congr e)
    · intro b hb hne
      apply Fintype.card_eq_zero_iff.mpr
      letI : IsEmpty (AddAction.fixedBy X b) :=
        ⟨fun x => hfree b hne x x.property⟩
      exact inferInstance
    · simp
  have hburn :=
    AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup G X
  rw [hsum] at hburn
  exact ⟨Fintype.card (AddAction.orbitRel.Quotient G X), by
    simpa [Nat.mul_comm] using hburn⟩

/-! The same orbit-counting argument applies directly to a finite invariant
support.  This is the bridge used by affine commutators: once the commutator
has supplied a free translation action on the support, its cardinality inherits
the group-order divisibility. -/

theorem card_addGroup_dvd_of_invariant_finset_of_free_action
    {G X : Type*} [AddGroup G] [AddAction G X]
    [Fintype G] [Fintype X] [DecidableEq X] (D : Finset X)
    (hD : ∀ g : G, D.image (fun x => g +ᵥ x) = D)
    (hfree : ∀ g : G, g ≠ 0 → ∀ x : X, g +ᵥ x ≠ x) :
    Fintype.card G ∣ D.card := by
  classical
  have hmem (g : G) {x : X} (hx : x ∈ D) : g +ᵥ x ∈ D := by
    have hx' : g +ᵥ x ∈ D.image (fun y => g +ᵥ y) := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [hD g] at hx'
    exact hx'
  letI : AddAction G D :=
    { vadd := fun g x => ⟨g +ᵥ (x : X), hmem g x.property⟩
      zero_vadd := fun x => Subtype.ext (zero_vadd _ x.val)
      add_vadd := fun g h x => Subtype.ext (add_vadd g h x.val) }
  have hfree' : ∀ g : G, g ≠ 0 → ∀ x : D, g +ᵥ x ≠ x := by
    intro g hg x hfix
    apply hfree g hg (x : X)
    exact congrArg Subtype.val hfix
  have hcard : Fintype.card G ∣ Fintype.card D :=
    card_addGroup_dvd_of_free_finite_action (G := G) (X := D) hfree'
  simpa only [Fintype.card_coe] using hcard

#print axioms invariant_finset_empty_or_univ_of_pretransitive
#print axioms card_addGroup_dvd_of_free_finite_action
#print axioms card_addGroup_dvd_of_invariant_finset_of_free_action

end D5.S3.ArithUnits.FiniteAddActionCardinality
