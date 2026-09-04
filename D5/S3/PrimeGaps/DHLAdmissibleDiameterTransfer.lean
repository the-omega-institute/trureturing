/- GID: D5/S3/PrimeGaps/DHLAdmissibleDiameterTransfer
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate bounded-gap progress into a DHL occupancy axis and an admissible-tuple diameter axis. -/

import D5.S3.PrimeGaps.ShortGapOccupancyBridge

namespace D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer

open D5.S3.PrimeGaps.ShortGapOccupancyBridge

/-- Direct admissibility for a finite natural offset set. -/
def NaturalTupleAdmissible (H : Finset Nat) : Prop :=
  ∀ p : Nat, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- The natural-number `DHL[k,2]` occupancy contract, with no fixed tuple. -/
def DHLTwoNat (k : Nat) : Prop :=
  ∀ H : Finset Nat, H.card = k → NaturalTupleAdmissible H →
    Set.Infinite {n : Nat | 2 ≤ primeTranslateOccupancy H n}

/-- A combinatorial witness that `k` admissible offsets fit inside a normalized window of
width `B`. This is the tuple-diameter axis of a bounded-gap proof. -/
def AdmissibleWindowWitness (k B : Nat) : Prop :=
  ∃ H : Finset Nat,
    H.card = k ∧ NaturalTupleAdmissible H ∧ ∀ h ∈ H, h ≤ B

/-- Consecutive prime gaps of width at most `B` occur beyond every translation threshold. -/
def ArbitrarilyLateConsecutiveGap (B : Nat) : Prop :=
  ∀ N : Nat, ∃ n : Nat, N < n ∧ BoundedConsecutivePrimeGapAt B n

/-- The bounded-gap transfer theorem. An analytic proof of `DHL[k,2]` and an independent
combinatorial admissible `k`-tuple of width `B` combine to force arbitrarily late consecutive
prime gaps of width at most `B`.

This statement exposes the two independent optimization axes. Improving the analytic sieve can
lower the accessible `k`; improving narrow admissible tuples can lower `B` at fixed `k`. -/
theorem dhl_two_and_admissible_window_yield_bounded_gap
    (k B : Nat) (hdhl : DHLTwoNat k) (hwitness : AdmissibleWindowWitness k B) :
    ArbitrarilyLateConsecutiveGap B := by
  rcases hwitness with ⟨H, hcard, hadm, hwindow⟩
  have hinfinite := hdhl H hcard hadm
  intro N
  obtain ⟨n, hocc, hNn⟩ := Set.Infinite.exists_gt hinfinite N
  exact ⟨n, hNn,
    two_prime_occupancy_yields_consecutive_gap H B n hwindow hocc⟩

/-- Monotonicity on the combinatorial axis: a witness fitting in width `B` also fits in every
larger width. -/
theorem admissibleWindowWitness_mono
    {k B C : Nat} (hBC : B ≤ C) :
    AdmissibleWindowWitness k B → AdmissibleWindowWitness k C := by
  rintro ⟨H, hcard, hadm, hwindow⟩
  exact ⟨H, hcard, hadm, fun h hh => (hwindow h hh).trans hBC⟩

/-- Monotonicity of the output gap statement in the permitted width. -/
theorem arbitrarilyLateConsecutiveGap_mono
    {B C : Nat} (hBC : B ≤ C) :
    ArbitrarilyLateConsecutiveGap B → ArbitrarilyLateConsecutiveGap C := by
  intro hgap N
  obtain ⟨n, hNn, p, q, hpq, hnp, hq, hwidth⟩ := hgap N
  refine ⟨n, hNn, p, q, hpq, hnp, ?_, ?_⟩
  · exact hq.trans (Nat.add_le_add_left hBC n)
  · exact hwidth.trans hBC

#print axioms NaturalTupleAdmissible
#print axioms DHLTwoNat
#print axioms AdmissibleWindowWitness
#print axioms ArbitrarilyLateConsecutiveGap
#print axioms dhl_two_and_admissible_window_yield_bounded_gap
#print axioms admissibleWindowWitness_mono
#print axioms arbitrarilyLateConsecutiveGap_mono

end D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
