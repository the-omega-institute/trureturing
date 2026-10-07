/- GID: D5/S3/FiniteGroups/NikolovSegal/UniformTwistedSmallLarge
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/UniformTwistedSmallLarge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded small-simple coverage and conditional uniform small-large extension. -/

import D5.S3.FiniteGroups.NikolovSegal.TwistedProductPadding
import D5.S3.FiniteGroups.NikolovSegal.PartIILemma41

set_option autoImplicit false

namespace NikolovSegal.SmallTwistedProduct
open Equation47WordCoupling
universe u

/-- At a fixed cutoff and scalar length, combine the genuine bounded-small
theorem with the owner's Lemma4.1. The only coverage premise is the literal
large-simple q=1 scalar PRODUCT input, including its pre-target corrections. -/
theorem uniform_twisted_at_max_of_large_scalar_one (M C : ℕ)
    (scalar : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      ¬IsMulCommutative S → C < Nat.card S →
      ∀ beta : Fin M → MulAut S, PartIIScalarProductInput 1 M beta (fun _ => 1)) :
    ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      ¬IsMulCommutative S → PartIITwistedProductInput S (max M (C+1)) := by
  intro S _ _ _ hn
  by_cases hsmall : Nat.card S ≤ C
  · exact twisted_input_mono (le_max_right M (C+1))
      (bounded_small_simple_twisted_input C hn hsmall)
  · have hlarge : C < Nat.card S := Nat.lt_of_not_ge hsmall
    exact twisted_input_mono (le_max_left M (C+1))
      (NikolovSegal.twisted_input_of_scalar_one (scalar S hn hlarge))

/-- Literal all-simple uniform twisted PRODUCT existence, conditional only
on the single still-open uniform large-simple q=1 scalar PRODUCT theorem.
The resulting common length is positive and is fixed before group, tuple,
and target. This is not a proof of the scalar premise. -/
theorem uniform_all_simple_twisted_of_large_scalar_one
    (scalar : ∃ M C : ℕ,
      ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
        ¬IsMulCommutative S → C < Nat.card S →
        ∀ beta : Fin M → MulAut S, PartIIScalarProductInput 1 M beta (fun _ => 1)) :
    ∃ D : ℕ, 0 < D ∧
      ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
        ¬IsMulCommutative S → PartIITwistedProductInput S D := by
  obtain ⟨M,C,hscalar⟩ := scalar
  refine ⟨max M (C+1),?_,uniform_twisted_at_max_of_large_scalar_one M C hscalar⟩
  exact (Nat.zero_lt_succ C).trans_le (le_max_right M (C+1))

end NikolovSegal.SmallTwistedProduct
