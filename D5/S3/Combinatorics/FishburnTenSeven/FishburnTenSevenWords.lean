/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords
   mirror-E: none(waiver:reversal-interchange-language-bijection)
   anchors: [mathlib/module/Mathlib.Data.List.Chain, mathlib/module/Mathlib.Data.Set.Basic]
   utility: none
   digest: Reversal and interchange give an involutive bijection of the two word languages. -/

import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords

inductive Letter where
  | d
  | i
  | j
  deriving DecidableEq

open Letter

def Before (earlier later : Letter) (word : List Letter) : Prop :=
  word.Pairwise (fun left right => left ≠ later ∨ right ≠ earlier)

def languageA (size : ℕ) : Set (List Letter) :=
  {word | word.length = size ∧
    word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before j d word}

def languageC (size : ℕ) : Set (List Letter) :=
  {word | word.length = size ∧
    word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before d i word}

def swap : Letter → Letter
  | d => d
  | i => j
  | j => i

def phi (word : List Letter) : List Letter := (word.map swap).reverse

theorem word_bijection (size : ℕ) :
    Function.Involutive phi ∧
    (∀ word, word ∈ languageA size ↔ phi word ∈ languageC size) ∧
    ∃ correspondence : languageA size ≃ languageC size,
      ∀ word, (correspondence word).val = phi word.val := by
  have hswap (letter : Letter) : swap (swap letter) = letter := by
    cases letter <;> rfl
  have hinverse : Function.Involutive phi := by
    intro word
    simp only [phi, List.map_reverse, List.reverse_reverse, List.map_map]
    simp only [Function.comp_def, hswap]
    exact List.map_id word
  have hchain (left right : Letter) :
      (swap right ≠ j ∨ swap left ≠ i) ↔ (left ≠ j ∨ right ≠ i) := by
    cases left <;> cases right <;> simp [swap]
  have horder (left right : Letter) :
      (swap right ≠ i ∨ swap left ≠ d) ↔ (left ≠ d ∨ right ≠ j) := by
    cases left <;> cases right <;> simp [swap]
  have hforward (word : List Letter) :
      word ∈ languageA size ↔ phi word ∈ languageC size := by
    simp only [languageA, languageC, Set.mem_ofPred_eq, phi, List.length_reverse,
      List.length_map, List.isChain_reverse, List.isChain_map, Before,
      List.pairwise_reverse, List.pairwise_map]
    simp_rw [hchain, horder]
  refine ⟨hinverse, hforward, ?_⟩
  refine ⟨{
    toFun := fun word => ⟨phi word.val, (hforward word.val).mp word.property⟩
    invFun := fun word => ⟨phi word.val, (hforward (phi word.val)).mpr ?_⟩
    left_inv := ?_
    right_inv := ?_ }, fun _ => rfl⟩
  · simpa only [hinverse word.val] using word.property
  · intro word
    exact Subtype.ext (hinverse word.val)
  · intro word
    exact Subtype.ext (hinverse word.val)

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords
