/- GID: D5/S3/Observer/GoldenCoding/ModFiveCharacterWordQuotient
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/ModFiveCharacterWordQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct directed mod-five character words have the same scalar product. -/

import Mathlib.Tactic
import Mathlib.Tactic.NormNum.LegendreSymbol

/- Library-search audit trail (2026-09-03):
   * D5 searches for character words, scalar products, mod-five characters,
     noninjectivity, and permutation products found no theorem on the explicit
     residue-word carrier below. `holFive_perm` instead has prime words as its
     carrier, and `golden_scalar_dihedrally_blind` concerns completed worlds.
   * Pinned Mathlib provides the Legendre symbol computation, finite images,
     and `Set.InjOn`, but no exact theorem identifying these two words and the
     five-element refinement image.
   * Body-shape searches for paired `legendreSym 5` values and product maps
     found no existing D5 primitive definition to import. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.ModFiveCharacterWordQuotient

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- For offsets zero and two, the two directed mixed-sign character words are
distinct, but their scalar products coincide. The complete five-residue image
is recorded explicitly, and pair multiplication is not injective on it. -/
theorem mod_five_character_word_scalar_quotient :
    let characterWord : ZMod 5 -> Int × Int := fun n =>
      (legendreSym 5 n.val, legendreSym 5 (n + 2).val)
    let scalarProduct : Int × Int -> Int := fun word => word.1 * word.2
    let validWords : Finset (Int × Int) := Finset.univ.image characterWord
    characterWord 1 = (1, -1) ∧
      characterWord 2 = (-1, 1) ∧
      characterWord 1 ≠ characterWord 2 ∧
      scalarProduct (characterWord 1) = -1 ∧
      scalarProduct (characterWord 2) = -1 ∧
      scalarProduct (characterWord 1) = scalarProduct (characterWord 2) ∧
      validWords = {(0, -1), (1, -1), (-1, 1), (-1, 0), (1, 1)} ∧
      ¬ Set.InjOn scalarProduct (validWords : Set (Int × Int)) := by
  dsimp only
  let characterWord : ZMod 5 -> Int × Int := fun n =>
    (legendreSym 5 n.val, legendreSym 5 (n + 2).val)
  let scalarProduct : Int × Int -> Int := fun word => word.1 * word.2
  let validWords : Finset (Int × Int) := Finset.univ.image characterWord
  have hForward : characterWord 1 = (1, -1) := by
    decide
  have hReverse : characterWord 2 = (-1, 1) := by
    decide
  have hDistinct : characterWord 1 ≠ characterWord 2 := by
    decide
  have hForwardProduct : scalarProduct (characterWord 1) = -1 := by
    decide
  have hReverseProduct : scalarProduct (characterWord 2) = -1 := by
    decide
  have hSameProduct :
      scalarProduct (characterWord 1) = scalarProduct (characterWord 2) := by
    decide
  have hRange :
      validWords = {(0, -1), (1, -1), (-1, 1), (-1, 0), (1, 1)} := by
    decide
  refine ⟨hForward, hReverse, hDistinct, hForwardProduct, hReverseProduct,
    hSameProduct, hRange, ?_⟩
  intro hInjective
  have hForwardMem : characterWord 1 ∈ validWords := by
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  have hReverseMem : characterWord 2 ∈ validWords := by
    exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  exact hDistinct (hInjective hForwardMem hReverseMem hSameProduct)

/-- The residue carrier used by the character-word construction is inhabited. -/
example : ZMod 5 := 0

#print axioms mod_five_character_word_scalar_quotient

end D5.S3.Observer.GoldenCoding.ModFiveCharacterWordQuotient
