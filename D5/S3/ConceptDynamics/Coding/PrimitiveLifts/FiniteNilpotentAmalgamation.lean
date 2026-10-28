/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteNilpotentAmalgamation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteNilpotentAmalgamation
   mirror-E: none(waiver:symbolic-structural-theorem)
   anchors: []
   utility: none
   digest: Amalgamation of every prescribed coprime equal-power pair forces a finite group to be nilpotent. -/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Factorization.Basic

/-! The prescribed roots, rather than just the existence of roots of their common
power, determine coprime-order commutation. The finite Sylow argument uses
Mathlib's classical Sylow and nilpotence theory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation

variable {G : Type*} [Group G]

private theorem commute_of_amalgamation
    (h : ∀ x y : G, ∀ m n : ℕ, Nat.Coprime m n → x ^ m = y ^ n →
      ∃ z : G, x = z ^ n ∧ y = z ^ m)
    {x y : G} (hxy : Nat.Coprime (orderOf x) (orderOf y)) : Commute x y := by
  obtain ⟨z, hx, hy⟩ := h x y (orderOf x) (orderOf y) hxy
    ((pow_orderOf_eq_one x).trans (pow_orderOf_eq_one y).symm)
  rw [hx, hy]
  exact Commute.pow_pow_self z _ _

private theorem sylow_le_normalizer_of_coprime_commutation [Finite G]
    (h : ∀ x y : G, Nat.Coprime (orderOf x) (orderOf y) → Commute x y)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (P : Sylow p G) (Q : Sylow q G) :
    (Q : Subgroup G) ≤ (P : Subgroup G).normalizer := by
  have hcard := IsPGroup.coprime_card_of_ne p q hpq
    (P : Subgroup G) (Q : Subgroup G) P.isPGroup' Q.isPGroup'
  apply Subgroup.le_normalizer_iff.mpr
  intro y hy x hx
  have hxy := h x y (hcard.of_dvd
    ((P : Subgroup G).orderOf_dvd_natCard hx)
    ((Q : Subgroup G).orderOf_dvd_natCard hy))
  simpa only [← hxy.eq, mul_assoc, mul_inv_cancel, mul_one] using hx

private theorem sylow_normal_of_coprime_commutation [Finite G]
    (h : ∀ x y : G, Nat.Coprime (orderOf x) (orderOf y) → Commute x y)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : (P : Subgroup G).Normal := by
  classical
  apply Subgroup.normalizer_eq_top_iff.mp
  apply Subgroup.eq_top_of_card_eq
  apply Nat.dvd_antisymm
  · exact Subgroup.card_subgroup_dvd_card _
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro q k hq hqk
    letI : Fact q.Prime := ⟨hq⟩
    by_cases hpq : p = q
    · subst q
      exact dvd_trans (P.pow_dvd_card_of_pow_dvd_card hqk)
        ((P : Subgroup G).card_dvd_of_le Subgroup.le_normalizer)
    · let Q : Sylow q G := Classical.arbitrary _
      exact dvd_trans (Q.pow_dvd_card_of_pow_dvd_card hqk)
        ((Q : Subgroup G).card_dvd_of_le
          (sylow_le_normalizer_of_coprime_commutation h hpq P Q))

/-- In a finite group, a common root for every prescribed coprime equal-power
pair forces nilpotence. The exponents range over all naturals, including zero;
neither uniqueness of the common root nor commutativity is assumed. -/
theorem nilpotent_of_coprime_power_amalgamation [Finite G]
    (h : ∀ x y : G, ∀ m n : ℕ, Nat.Coprime m n → x ^ m = y ^ n →
      ∃ z : G, x = z ^ n ∧ y = z ^ m) : Group.IsNilpotent G := by
  apply (Group.isNilpotent_of_finite_tfae (G := G)).out 3 0 |>.mp
  intro p hp P
  letI := hp
  exact sylow_normal_of_coprime_commutation
    (fun _ _ hxy => commute_of_amalgamation h hxy) P

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation
