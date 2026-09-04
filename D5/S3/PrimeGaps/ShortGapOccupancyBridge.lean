/- GID: D5/S3/PrimeGaps/ShortGapOccupancyBridge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantify local residue survivors and turn two prime hits in a bounded translate into a bounded prime pair. -/

import D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

namespace D5.S3.PrimeGaps.ShortGapOccupancyBridge

open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

/-- The number of residue classes modulo `p` left available after the offsets in `H`
forbid their translated zero classes. -/
def localSurvivorCount (H : Finset Int) (p : Nat) : Nat :=
  p - localResidueCount H p

/-- The local survivor count is positive exactly when the offset set does not block every
residue class. This is the finite local notion used by admissible prime tuples. -/
theorem localSurvivorCount_pos_iff
    (H : Finset Int) (p : Nat) (hcount : localResidueCount H p ≤ p) :
    0 < localSurvivorCount H p ↔ localResidueCount H p < p := by
  unfold localSurvivorCount
  omega

/-- A `k`-point offset set leaves at least `p-k` residue classes available modulo every
modulus `p`. For `p > k` this gives a strictly positive local survivor budget without any
prime-specific computation. -/
theorem localSurvivorCount_lower_bound
    (H : Finset Int) (k p : Nat) (hcard : H.card = k) :
    p - k ≤ localSurvivorCount H p := by
  have hres : localResidueCount H p ≤ k := by
    calc
      localResidueCount H p = (H.image fun h : Int => -(h : ZMod p)).card := rfl
      _ ≤ H.card := Finset.card_image_le
      _ = k := hcard
  unfold localSurvivorCount
  omega

/-- In particular, all moduli larger than the tuple size have a nonempty survivor set. -/
theorem localSurvivorCount_pos_of_card_lt
    (H : Finset Int) (k p : Nat) (hcard : H.card = k) (hkp : k < p) :
    0 < localSurvivorCount H p := by
  have hlower := localSurvivorCount_lower_bound H k p hcard
  omega

/-- The number of prime hits obtained by translating the finite offset window `H` by `n`. -/
def primeTranslateOccupancy (H : Finset Nat) (n : Nat) : Nat :=
  (H.filter fun h => (n + h).Prime).card

/-- A pair of distinct primes contained in the translated interval `[n,n+B]`. -/
def BoundedPrimePairAt (B n : Nat) : Prop :=
  ∃ p q : Nat, p.Prime ∧ q.Prime ∧ p < q ∧ n ≤ p ∧ q ≤ n + B

/-- Two prime hits in any offset window of diameter at most `B` produce a pair of distinct
primes in the ambient interval `[n,n+B]`. This is the finite occupancy-to-gap interface used
by bounded-prime-gap arguments before the consecutive-prime extraction step. -/
theorem two_prime_occupancy_yields_bounded_pair
    (H : Finset Nat) (B n : Nat)
    (hwindow : ∀ h ∈ H, h ≤ B)
    (hocc : 2 ≤ primeTranslateOccupancy H n) :
    BoundedPrimePairAt B n := by
  classical
  let S := H.filter fun h => (n + h).Prime
  have htwo : 1 < S.card := by
    have : 1 < primeTranslateOccupancy H n := lt_of_lt_of_le (by omega) hocc
    simpa [S, primeTranslateOccupancy] using this
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have haH : a ∈ H := ha'.1
  have hbH : b ∈ H := hb'.1
  have hap : (n + a).Prime := ha'.2
  have hbp : (n + b).Prime := hb'.2
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · refine ⟨n + a, n + b, hap, hbp, by omega, by omega, ?_⟩
    exact Nat.add_le_add_left (hwindow b hbH) n
  · refine ⟨n + b, n + a, hbp, hap, by omega, by omega, ?_⟩
    exact Nat.add_le_add_left (hwindow a haH) n

#print axioms localSurvivorCount
#print axioms localSurvivorCount_pos_iff
#print axioms localSurvivorCount_lower_bound
#print axioms localSurvivorCount_pos_of_card_lt
#print axioms primeTranslateOccupancy
#print axioms BoundedPrimePairAt
#print axioms two_prime_occupancy_yields_bounded_pair

end D5.S3.PrimeGaps.ShortGapOccupancyBridge
