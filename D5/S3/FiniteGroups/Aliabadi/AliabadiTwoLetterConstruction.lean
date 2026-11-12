/- GID: D5/S3/FiniteGroups/Aliabadi/AliabadiTwoLetterConstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Aliabadi/AliabadiTwoLetterConstruction
   mirror-E: none(waiver:pure-finite-group-theorem)
   anchors: []
   utility: none
   digest: A nonidentity group element generates a permutation whose right quotients use exactly two letters and whose support has the element order. -/

import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.FiniteGroups.Aliabadi.AliabadiTwoLetterConstruction

/--
For every nonidentity element of a finite group, left multiplication on its cyclic
subgroup and the identity outside that subgroup gives a permutation with the
prescribed two-letter right-quotient alphabet.  The moved points are exactly the
cyclic subgroup, so their number is the element order.
-/
theorem exists_rightQuotient_perm_of_ne_one {G : Type u} [Group G] [Fintype G]
    [DecidableEq G] (a : G) (ha : a ≠ 1) :
    ∃ σ : Equiv.Perm G,
      σ.support.card = orderOf a ∧
        ∀ x : G, σ x * x⁻¹ = a ∨ σ x * x⁻¹ = 1 := by
  classical
  let H : Subgroup G := Subgroup.zpowers a
  let f : G → G := fun x => if x ∈ H then a * x else x
  have haH : a ∈ H := by
    exact Subgroup.mem_zpowers a
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
    · simpa [f, hx, hy] using hxy
    · have hxy' : a * x = y := by simpa [f, hx, hy] using hxy
      have hyH : y ∈ H := by
        rw [← hxy']
        exact H.mul_mem haH hx
      exact (hy hyH).elim
    · have hxy' : x = a * y := by simpa [f, hx, hy] using hxy
      have hxH : x ∈ H := by
        rw [hxy']
        exact H.mul_mem haH hy
      exact (hx hxH).elim
    · simpa [f, hx, hy] using hxy
  have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  let σ : Equiv.Perm G := Equiv.ofBijective f hf_bij
  let T : Finset G := (H : Set G).toFinset
  have hsupport : σ.support = T := by
    ext x
    rw [Equiv.Perm.mem_support]
    by_cases hx : x ∈ H
    · have hax : a * x ≠ x := by
        intro hax
        apply ha
        have hmul := congrArg (fun z : G => z * x⁻¹) hax
        simpa [mul_assoc] using hmul
      simp [σ, f, T, hx, hax]
    · simp [σ, f, T, hx]
  have hcard : T.card = orderOf a := by
    dsimp [T]
    rw [Set.toFinset_card]
    exact Fintype.card_zpowers
  refine ⟨σ, hsupport ▸ hcard, ?_⟩
  intro x
  by_cases hx : x ∈ H
  · left
    simp [σ, f, hx]
  · right
    simp [σ, f, hx]

#print axioms exists_rightQuotient_perm_of_ne_one

end D5.S3.FiniteGroups.Aliabadi.AliabadiTwoLetterConstruction
