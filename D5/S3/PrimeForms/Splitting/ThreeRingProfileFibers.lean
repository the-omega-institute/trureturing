/- GID: D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/ThreeRingProfileFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Gaussian, Eisenstein, and golden residue readings on units modulo sixty realize all eight split-inert profiles, each on exactly two unit classes. -/

import Mathlib

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'tri_ring_image_surjective_with_fibers_of_card_two' D5
     Golden/Frozen/accepted` returned no matches.
   * Searches for `ZMod 60`, `threeRingProfile_fiber_card_two`, `Sigma3`, and
     `barSigma` returned no Lean declarations in `D5`; there are no public or
     private exact local hits.
   * The source definitions are explicit residue tests. The public local theorems
     `EisensteinCriterion.neg_three_isSquare_iff` and
     `GoldenPrimeClassification.five_is_square_mod_prime_iff_mod_five_eq_one_or_four`
     justify the Eisenstein and golden prime readings, but are not needed to check
     the already-factored map on `(ZMod 60)ˣ`.
   * Mathlib searches found `ZMod.unitsEquivCoprime`,
     `ZMod.card_units_eq_totient`, `Nat.totient`, and general fiber-cardinality
     lemmas, but no theorem computing this three-coordinate map. The proof below
     uses finite kernel evaluation of the source's residue predicates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

-- Lean 4.33's stricter type check breaks mathlib's `Fintype` deriving handler.
section
set_option backward.isDefEq.respectTransparency.types false

/-- A non-ramified quadratic splitting reading. -/
inductive SplitReading where
  | split
  | inert
  deriving DecidableEq, Fintype, Repr

/-- The three coordinates of the Gaussian, Eisenstein, and golden splitting profile. -/
structure ThreeRingProfile where
  gaussian : SplitReading
  eisenstein : SplitReading
  golden : SplitReading
  deriving DecidableEq, Fintype, Repr

end

/-- The Gaussian reading is split exactly on the unit class `1 mod 4`. -/
def gaussianReading (u : (ZMod 60)ˣ) : SplitReading :=
  if u.val.val % 4 = 1 then .split else .inert

/-- The Eisenstein reading is split exactly on the unit class `1 mod 3`. -/
def eisensteinReading (u : (ZMod 60)ˣ) : SplitReading :=
  if u.val.val % 3 = 1 then .split else .inert

/-- The golden reading is split exactly on the square unit classes modulo five. -/
def goldenReading (u : (ZMod 60)ˣ) : SplitReading :=
  if u.val.val % 5 = 1 ∨ u.val.val % 5 = 4 then .split else .inert

/-- The three-ring image induced by the source's Gaussian, Eisenstein, and golden tests. -/
def triRingImage (u : (ZMod 60)ˣ) : ThreeRingProfile :=
  ⟨gaussianReading u, eisensteinReading u, goldenReading u⟩

/-- The three-ring image is onto, and every split-inert profile has exactly two preimages. -/
theorem tri_ring_image_surjective_with_fibers_of_card_two :
    Function.Surjective triRingImage ∧
      ∀ t, Fintype.card {u : (ZMod 60)ˣ // triRingImage u = t} = 2 := by
  letI : DecidableEq SplitReading := fun a b => by
    cases a <;> cases b <;> infer_instance
  letI : DecidableEq ThreeRingProfile := fun x y => by
    rcases x with ⟨a, b, c⟩
    rcases y with ⟨a', b', c'⟩
    cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;>
      infer_instance
  letI : Fintype SplitReading := ⟨{.split, .inert}, by
    intro x
    cases x <;> simp⟩
  letI : Fintype ThreeRingProfile := ⟨
    {⟨.split, .split, .split⟩, ⟨.split, .split, .inert⟩,
     ⟨.split, .inert, .split⟩, ⟨.split, .inert, .inert⟩,
     ⟨.inert, .split, .split⟩, ⟨.inert, .split, .inert⟩,
     ⟨.inert, .inert, .split⟩, ⟨.inert, .inert, .inert⟩}, by
    intro x
    rcases x with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> simp⟩
  set_option maxRecDepth 100000 in
    constructor
    · intro t
      rcases t with ⟨a, b, c⟩
      cases a <;> cases b <;> cases c <;> decide
    · intro t
      rcases t with ⟨a, b, c⟩
      cases a <;> cases b <;> cases c <;> decide

example :
    triRingImage (1 : (ZMod 60)ˣ) =
      ⟨SplitReading.split, SplitReading.split, SplitReading.split⟩ := by
    decide

#print axioms tri_ring_image_surjective_with_fibers_of_card_two

end D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers
