/- GID: D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite offset set can cover residues only at primes no larger than its size. -/

import Mathlib

/- Library-search audit trail (2026-09-03):
   * Exact pinned-Mathlib hit `Finset.card_image_le` supplies the residue-image
     cardinality bound and is applied directly below.
   * Searches in D5 for finite residue blocking, forbidden-residue counts, and
     negative `Finset.image` constructions into `ZMod` found no existing owner.
   * Pinned-Mathlib semantic searches found no whole-statement theorem.
   * Searches of vendored Lean packages and public Lean code found related
     fixed-cardinality prime-tuple developments, but no theorem with this general
     finite-offset carrier and both public clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

/-- The residue classes forbidden by translating the offsets modulo `p`. -/
def localResidueSet (H : Finset Int) (p : Nat) : Finset (ZMod p) :=
  H.image fun h : Int => -(h : ZMod p)

/-- The number of residue classes forbidden by the offset set modulo `p`. -/
def localResidueCount (H : Finset Int) (p : Nat) : Nat :=
  (localResidueSet H p).card

/-- If a finite offset set has cardinality `k`, then moduli larger than `k`
cannot be completely covered. Consequently, prime admissibility is equivalent to
checking only primes at most `k`. -/
theorem finite_local_residue_blocking_criterion
    (H : Finset Int) (k : Nat) (hcard : H.card = k) :
    (forall p : Nat.Primes, k < p.val ->
      localResidueCount H p.val <= k ∧
        localResidueCount H p.val < p.val) ∧
    ((forall p : Nat.Primes, localResidueCount H p.val < p.val) ↔
      forall p : Nat.Primes, p.val <= k -> localResidueCount H p.val < p.val) := by
  have residue_count_le (p : Nat) : localResidueCount H p <= k := by
    calc
      localResidueCount H p = (H.image fun h : Int => -(h : ZMod p)).card := rfl
      _ <= H.card := Finset.card_image_le
      _ = k := hcard
  constructor
  · intro p hkp
    exact ⟨residue_count_le p.val, (residue_count_le p.val).trans_lt hkp⟩
  · constructor
    · intro hadmissible p _
      exact hadmissible p
    · intro hsmall p
      by_cases hp : p.val <= k
      · exact hsmall p hp
      · exact (residue_count_le p.val).trans_lt (Nat.lt_of_not_ge hp)

#print axioms localResidueSet
#print axioms localResidueCount
#print axioms finite_local_residue_blocking_criterion

end D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
