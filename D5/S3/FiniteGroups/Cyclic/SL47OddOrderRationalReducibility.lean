/- GID: D5/S3/FiniteGroups/Cyclic/SL47OddOrderRationalReducibility
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/SL47OddOrderRationalReducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-order subgroups of SL₂(F₄₇) have reducible faithful rational actions in dimension 48. -/

import D5.S3.FiniteGroups.Cyclic.SL47OrderThreeConjugacy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The odd-image branch of the finite-group P48q obstruction. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace ExtremalC48

open private exists_normal_zpowers_of_dvd exists_invariant_subspace_of_card_lt
  exists_invariant_subspace_of_normal_zpowers from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
open private card_SL47 from D5.S3.FiniteGroups.Cyclic.SL47OrderThreeConjugacy

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Every faithful rational action of an odd-order subgroup of `SL₂(F₄₇)` in
dimension `48` has a nonzero proper invariant subspace. -/
theorem sl47_odd_order_exists_invariant_subspace
    (H : Subgroup SL47) (hH : ¬ 2 ∣ Nat.card H)
    (ρ : Representation ℚ H V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank ℚ V = 48) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  have hSL : Nat.card SL47 = 2 ^ 5 * (3 * 23 * 47) :=
    card_SL47.trans (by decide)
  have hcard₀ : Nat.card H ∣ 2 ^ 5 * (3 * 23 * 47) := hSL ▸ H.card_subgroup_dvd_card
  have hcop32 := Nat.prime_two.coprime_pow_of_not_dvd (m := 5) hH
  have hcard : Nat.card H ∣ 3 * 23 * 47 := hcop32.dvd_of_dvd_mul_left hcard₀
  by_cases h47 : 47 ∣ Nat.card H
  · obtain ⟨x, hx, hnormal⟩ := exists_normal_zpowers_of_dvd 47 69 hcard h47
      (by decide) (by decide)
    let := hnormal
    exact exists_invariant_subspace_of_normal_zpowers ρ hρ x 47 hx
      (hdim.symm ▸ (by decide))
  · have hcop47 : Nat.Coprime (Nat.card H) 47 :=
      ((show (47 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h47).symm
    have hcard' : Nat.card H ∣ 3 * 23 :=
      hcop47.dvd_of_dvd_mul_right hcard
    by_cases h23 : 23 ∣ Nat.card H
    · obtain ⟨x, hx, hnormal⟩ := exists_normal_zpowers_of_dvd 23 3 hcard' h23
        (by decide) (by decide)
      let := hnormal
      exact exists_invariant_subspace_of_normal_zpowers ρ hρ x 23 hx
        (hdim.symm ▸ (by decide))
    · have hcop23 : Nat.Coprime (Nat.card H) 23 :=
        ((show (23 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h23).symm
      have hcard'' : Nat.card H ∣ 3 :=
        hcop23.dvd_of_dvd_mul_right hcard'
      apply exists_invariant_subspace_of_card_lt ρ
      have hle : Nat.card H ≤ 3 := Nat.le_of_dvd (by decide) hcard''
      omega

#print axioms sl47_odd_order_exists_invariant_subspace

end ExtremalC48
