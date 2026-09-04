/- GID: D5/S3/PrimeGaps/PrimeGap186FiniteFrontEnd
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Record the explicit diameter-186 forty-tuple and close its finite bounded-window consequences. -/

import D5.S3.PrimeGaps.ShortGapOccupancyBridge

namespace D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd

open D5.S3.PrimeGaps.ShortGapOccupancyBridge
open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

/-- The forty shifts of diameter 186 used in the 2026 `DHL[40,2]` bounded-gap argument. -/
def admissibleTuple186 : Finset Nat :=
  {0, 2, 6, 12, 20, 26, 30, 32, 36, 42, 48, 50, 56, 60, 68, 72, 78, 86, 90, 92,
   98, 102, 110, 116, 120, 126, 132, 138, 140, 146, 152, 156, 158, 162, 168, 170,
   176, 180, 182, 186}

/-- The same tuple on the integer carrier used by the admissibility predicate. -/
def admissibleTuple186Int : Finset Int :=
  admissibleTuple186.image Int.ofNat

/-- The explicit tuple really has forty distinct offsets. -/
theorem admissibleTuple186_card : admissibleTuple186.card = 40 := by
  decide

/-- Every offset of the explicit tuple lies in the diameter-186 window. -/
theorem admissibleTuple186_le_186 : ∀ h ∈ admissibleTuple186, h ≤ 186 := by
  decide

/-- The integer presentation also has cardinality forty. -/
theorem admissibleTuple186Int_card : admissibleTuple186Int.card = 40 := by
  unfold admissibleTuple186Int
  rw [Finset.card_image_iff.mpr]
  · exact admissibleTuple186_card
  · intro a ha b hb hab
    exact_mod_cast hab

/-- Any translate of the explicit tuple containing at least two primes already contains two
distinct primes in an interval of length 186. The analytic `DHL[40,2]` input is required only
to prove that such translates occur infinitely often. -/
theorem two_prime_translate_yields_pair186
    (n : Nat) (hocc : 2 ≤ primeTranslateOccupancy admissibleTuple186 n) :
    BoundedPrimePairAt 186 n :=
  two_prime_occupancy_yields_bounded_pair admissibleTuple186 186 n
    admissibleTuple186_le_186 hocc

/-- For every modulus larger than forty, the explicit integer tuple automatically leaves a
strictly positive residue survivor budget. Thus only the small moduli can obstruct
admissibility. -/
theorem admissibleTuple186_large_modulus_survives
    (p : Nat) (hp : 40 < p) :
    0 < localSurvivorCount admissibleTuple186Int p :=
  localSurvivorCount_pos_of_card_lt admissibleTuple186Int 40 p
    admissibleTuple186Int_card hp

#print axioms admissibleTuple186
#print axioms admissibleTuple186Int
#print axioms admissibleTuple186_card
#print axioms admissibleTuple186_le_186
#print axioms admissibleTuple186Int_card
#print axioms two_prime_translate_yields_pair186
#print axioms admissibleTuple186_large_modulus_survives

end D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd
