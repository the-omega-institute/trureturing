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

/-- The exact natural-number supporting conclusion exported by the 2026 short-gap proof for
the explicit tuple. In the upstream formalization this proposition is proved conditionally from
its three declared analytic/numerical inputs. -/
def InfiniteTwoPrimeTranslates186 : Prop :=
  Set.Infinite {n : Nat | 2 ≤ primeTranslateOccupancy admissibleTuple186 n}

/-- The explicit tuple really has forty distinct offsets. -/
theorem admissibleTuple186_card : admissibleTuple186.card = 40 := by
  decide

/-- Every offset of the explicit tuple lies in the diameter-186 window. -/
theorem admissibleTuple186_le_186 : ∀ h ∈ admissibleTuple186, h ≤ 186 := by
  decide

/-- The integer presentation also has cardinality forty. -/
theorem admissibleTuple186Int_card : admissibleTuple186Int.card = 40 := by
  rw [admissibleTuple186Int, Finset.card_image_of_injective _ Int.ofNat_injective]
  exact admissibleTuple186_card

/-- Any translate of the explicit tuple containing at least two primes contains two distinct
primes in an interval of length 186. -/
theorem two_prime_translate_yields_pair186
    (n : Nat) (hocc : 2 ≤ primeTranslateOccupancy admissibleTuple186 n) :
    BoundedPrimePairAt 186 n :=
  two_prime_occupancy_yields_bounded_pair admissibleTuple186 186 n
    admissibleTuple186_le_186 hocc

/-- The same two-hit translate already contains an actual consecutive-prime gap of width at
most 186. This closes the finite combinatorial passage used after `DHL[40,2]`. -/
theorem two_prime_translate_yields_consecutive_gap186
    (n : Nat) (hocc : 2 ≤ primeTranslateOccupancy admissibleTuple186 n) :
    BoundedConsecutivePrimeGapAt 186 n :=
  two_prime_occupancy_yields_consecutive_gap admissibleTuple186 186 n
    admissibleTuple186_le_186 hocc

/-- If the source-level infinite-translate conclusion is available, then bounded prime pairs of
width 186 occur after every prescribed translation threshold. -/
theorem arbitrarily_late_bounded_pair186
    (hsource : InfiniteTwoPrimeTranslates186) (N : Nat) :
    ∃ n : Nat, N < n ∧ BoundedPrimePairAt 186 n := by
  obtain ⟨n, hn, hNn⟩ := Set.Infinite.exists_gt hsource N
  exact ⟨n, hNn, two_prime_translate_yields_pair186 n hn⟩

/-- Under the source-level infinite-translate conclusion, consecutive prime gaps of width at
most 186 occur after every translation threshold. This is the exact finite statement needed
before passing to an `EReal` liminf formulation. -/
theorem arbitrarily_late_consecutive_gap186
    (hsource : InfiniteTwoPrimeTranslates186) (N : Nat) :
    ∃ n : Nat, N < n ∧ BoundedConsecutivePrimeGapAt 186 n := by
  obtain ⟨n, hn, hNn⟩ := Set.Infinite.exists_gt hsource N
  exact ⟨n, hNn, two_prime_translate_yields_consecutive_gap186 n hn⟩

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
#print axioms InfiniteTwoPrimeTranslates186
#print axioms admissibleTuple186_card
#print axioms admissibleTuple186_le_186
#print axioms admissibleTuple186Int_card
#print axioms two_prime_translate_yields_pair186
#print axioms two_prime_translate_yields_consecutive_gap186
#print axioms arbitrarily_late_bounded_pair186
#print axioms arbitrarily_late_consecutive_gap186
#print axioms admissibleTuple186_large_modulus_survives

end D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd
