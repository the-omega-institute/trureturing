/- GID: D5/S3/Arith/Constellations/FiniteBlockingCriterion
   generality: G
   mirror-B: D5/B/S3/Arith/Constellations/FiniteBlockingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite constellation cannot cover a prime residue space larger than its size. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * Repository searches for forbidden residue images, local residue counts, finite blocking,
     and complete residue coverage found no declaration defining or proving this source atom.
   * Pinned Mathlib supplies the exact cardinality bound `Finset.card_image_le`; `ZMod` and
     `Nat.Primes` supply the concrete residue and prime carriers used below.
   * Loogle returned `Finset.card_image_le`. GitHub Lean searches found no source-specific
     theorem. `AxiomMath/PrimeGapsLib.Finset.admissible_iff_le_card` is over `Finset Nat`,
     uses a different missed-residue definition, and states the later admissibility reduction;
     it is not an exact carrier or theorem-type match and is not imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Constellations.FiniteBlockingCriterion

/-- The forbidden residue set `R_p(H) = {-h mod p | h in H}` from source lines 656-662. -/
def forbiddenResidues (p : Nat.Primes) (H : Finset Int) : Finset (ZMod p.1) :=
  H.image fun h : Int => -(h : ZMod p.1)

/-- The local residue count `nu_p(H) = |R_p(H)|` from source lines 664-668. -/
def localResidueCount (p : Nat.Primes) (H : Finset Int) : Nat :=
  (forbiddenResidues p H).card

/-- Source lines 670-676: a constellation is admissible when every prime residue space
has strictly more classes than the corresponding forbidden residue set. -/
def IsAdmissible (H : Finset Int) : Prop :=
  forall p : Nat.Primes, localResidueCount p H < p.1

/-- Source lines 678-684 (Theorem 10.1). If `H` has `k` elements, then at every
prime `p > k` its forbidden residue image has at most `k` elements, and `k < p`. -/
theorem finite_blocking_criterion
    (H : Finset Int) (k : Nat) (card_eq : H.card = k) :
    forall p : Nat.Primes, k < p.1 ->
      localResidueCount p H <= k ∧ k < p.1 := by
  intro p prime_above_card
  constructor
  · unfold localResidueCount forbiddenResidues
    simpa [card_eq] using
      (Finset.card_image_le
        (s := H) (f := fun h : Int => -(h : ZMod p.1)))
  · exact prime_above_card

#print axioms finite_blocking_criterion

section FidelityProbes

/-- Reverse probe for both source leaves: together they force the forbidden image below `p`. -/
example (H : Finset Int) (k : Nat) (card_eq : H.card = k)
    (p : Nat.Primes) (prime_above_card : k < p.1) :
    localResidueCount p H < p.1 := by
  obtain ⟨image_le, card_lt_prime⟩ :=
    finite_blocking_criterion H k card_eq p prime_above_card
  exact image_le.trans_lt card_lt_prime

-- The source permits the empty constellation; its forbidden image is observably empty.
example (p : Nat.Primes) : localResidueCount p (∅ : Finset Int) = 0 := by
  simp [localResidueCount, forbiddenResidues]

-- A nonempty concrete image shows that the local definitions do not collapse to the empty set.
example :
    localResidueCount (⟨3, Nat.prime_three⟩ : Nat.Primes) ({0, 1} : Finset Int) = 2 := by
  decide

-- A1 does not imply A2: at `k = p = 2`, the image bound holds but the strict bound does not.
example :
    localResidueCount (⟨2, Nat.prime_two⟩ : Nat.Primes) ({0, 1} : Finset Int) <= 2 ∧
      ¬2 < (2 : Nat) := by
  decide

-- A2 does not imply A1 as a bare proposition: choose `k = 0` and a nonempty image.
example :
    0 < (2 : Nat) ∧
      ¬localResidueCount (⟨2, Nat.prime_two⟩ : Nat.Primes) ({0} : Finset Int) <= 0 := by
  decide

end FidelityProbes

end D5.S3.Arith.Constellations.FiniteBlockingCriterion
