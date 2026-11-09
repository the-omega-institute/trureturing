/- GID: D5/S3/Combinatorics/CayleySumCodes/Regularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/Regularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact degree and square-set dichotomy for finite regular Cayley sum graphs. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.Regularity

open scoped Classical

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

private noncomputable def neighborEquiv (Y : Set G) (hn : NormalSubset Y) (g : G) :
    (sumGraph Y hn).neighborSet g ≃ ↥(Y \ {g * g}) where
  toFun h := ⟨g * h.1, h.2.2, by
    intro he
    have eqh : h.1 = g := mul_left_cancel (Set.mem_singleton_iff.mp he)
    exact h.2.1 eqh.symm⟩
  invFun y := ⟨g⁻¹ * y.1, by
    refine ⟨?_, ?_⟩
    · intro he
      apply y.2.2
      apply Set.mem_singleton_iff.mpr
      have hh := congrArg (fun z : G => g * z) he
      simpa using hh.symm
    · simpa using y.2.1⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

/-- Every vertex has |Y| neighbors except that its own square, when present
in Y, removes exactly one open neighbor. The graph is the actual loopless
sum graph and the bijection is h maps to g*h. -/
theorem degree_card [Finite G] (Y : Set G) (hn : NormalSubset Y) (g : G) :
    Nat.card ((sumGraph Y hn).neighborSet g) =
      Nat.card Y - if g * g ∈ Y then 1 else 0 := by
  classical
  rw [Nat.card_congr (neighborEquiv Y hn g)]
  change (Y \ {g * g}).ncard = Y.ncard - if g * g ∈ Y then 1 else 0
  by_cases hm : g * g ∈ Y
  · rw [if_pos hm]
    have he := Set.ncard_sdiff_singleton_add_one hm
    omega
  · rw [if_neg hm, Nat.sub_zero]
    congr 1
    exact Set.sdiff_singleton_eq_self hm

/-- Full finite-group regularity dichotomy. Equality of the actual neighbor
cardinality at every vertex with its value at 1 is precisely regularity:
the group is nonempty, and that common value is its regular degree. -/
theorem result [Finite G] (Y : Set G) (hn : NormalSubset Y) :
    (∀ g : G, Nat.card ((sumGraph Y hn).neighborSet g) =
      Nat.card ((sumGraph Y hn).neighborSet 1)) ↔
    Y ∩ squares (⊤ : Subgroup G) = ∅ ∨ squares (⊤ : Subgroup G) ⊆ Y := by
  classical
  have positive (x : G) (hx : x ∈ Y) : 0 < Nat.card Y := by
    letI : Nonempty Y := ⟨⟨x, hx⟩⟩
    exact Nat.card_pos
  constructor
  · intro hreg
    by_cases h1 : (1 : G) ∈ Y
    · right
      rintro z ⟨g, _, rfl⟩
      by_contra hn
      have he := hreg g
      rw [degree_card, degree_card] at he
      simp only [one_mul, if_neg hn, if_pos h1, Nat.sub_zero] at he
      have hp := positive 1 h1
      omega
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, g, _, rfl⟩
      have he := hreg g
      rw [degree_card, degree_card] at he
      simp only [one_mul, if_pos hz, if_neg h1, Nat.sub_zero] at he
      have hp := positive (g * g) hz
      omega
  · rintro (hfree | hall) g
    · have hsq (x : G) : x * x ∉ Y := by
        intro hx
        have hm : x * x ∈ Y ∩ squares (⊤ : Subgroup G) := ⟨hx, x, by trivial, rfl⟩
        rw [hfree] at hm
        exact hm
      rw [degree_card, degree_card]
      simp only [ite_eq_right (hsq g), ite_eq_right (hsq 1)]
    · have hsq (x : G) : x * x ∈ Y := hall ⟨x, by trivial, rfl⟩
      rw [degree_card, degree_card]
      simp only [ite_eq_left (hsq g), ite_eq_left (hsq 1)]

#print axioms degree_card
#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.Regularity
