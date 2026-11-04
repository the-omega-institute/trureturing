/- GID: D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/CarrylessSeventeenNineContainment
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.EvenOddRec]
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.result; instance=D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.related; result=D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.result
   digest: The seventeen-times carryless equation implies the nine-times equation. -/
import D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

/-! # Containment of binary carryless multiplier conditions -/

namespace D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment

open CarrylessMultiplierEquivalence

set_option maxRecDepth 4096

private def related : Finset (State × State) := {
  (some (0, 0), some (0, 0)),
  (some (8, 24), some (4, 12)),
  (some (4, 12), some (2, 6)),
  (some (12, 20), some (6, 10)),
  (some (2, 6), some (1, 3)),
  (some (10, 30), some (5, 15)),
  (some (6, 10), some (3, 5)),
  (some (14, 18), some (7, 9)),
  (some (1, 3), some (0, 1)),
  (some (9, 27), some (5, 13)),
  (some (5, 15), some (2, 7)),
  (some (13, 23), some (7, 11)),
  (some (3, 5), some (1, 2)),
  (some (11, 29), some (6, 14)),
  (some (7, 9), some (3, 4)),
  (some (15, 17), some (8, 8)),
  (some (0, 1), none),
  (some (9, 25), none),
  (some (4, 13), some (2, 6)),
  (some (13, 21), some (7, 10)),
  (some (2, 7), none),
  (some (11, 31), none),
  (some (6, 11), some (3, 5)),
  (some (15, 19), some (8, 9)),
  (some (1, 2), none),
  (some (10, 26), none),
  (some (5, 14), some (3, 7)),
  (some (14, 22), some (7, 11)),
  (some (3, 4), none),
  (some (12, 28), none),
  (some (7, 8), some (4, 4)),
  (some (16, 16), some (8, 8)),
  (none, none),
  (some (4, 12), none),
  (some (13, 20), none),
  (none, some (1, 3)),
  (none, some (5, 15)),
  (some (6, 10), none),
  (some (15, 18), none),
  (some (5, 15), none),
  (some (14, 23), none),
  (none, some (1, 2)),
  (none, some (6, 14)),
  (some (7, 9), none),
  (some (16, 17), none),
  (some (5, 13), none),
  (some (13, 21), none),
  (none, some (6, 15)),
  (some (7, 11), some (3, 5)),
  (some (6, 14), none),
  (some (14, 22), none),
  (none, some (2, 2)),
  (some (8, 8), some (4, 4)),
  (some (2, 6), none),
  (some (10, 30), none),
  (none, some (0, 1)),
  (none, some (5, 13)),
  (none, some (2, 7)),
  (none, some (7, 11)),
  (some (3, 5), none),
  (some (11, 29), none),
  (none, some (3, 7)),
  (some (11, 30), none),
  (some (12, 29), some (6, 14)),
  (some (3, 7), none),
  (some (7, 11), none),
  (some (15, 19), none),
  (none, some (1, 1)),
  (some (4, 4), some (2, 2)),
  (some (12, 28), some (6, 14)),
  (some (1, 3), none),
  (some (9, 27), none),
  (some (13, 23), none),
  (none, some (2, 6)),
  (none, some (7, 10)),
  (none, some (3, 5)),
  (none, some (8, 9)),
  (some (5, 14), none),
  (some (10, 27), none),
  (some (12, 29), none),
  (none, some (0, 0)),
  (none, some (5, 12)),
  (some (2, 2), some (1, 1)),
  (some (10, 26), some (5, 13)),
  (some (6, 14), some (3, 7)),
  (some (4, 13), none),
  (some (6, 11), none),
  (none, some (4, 12)),
  (some (1, 1), some (0, 0)),
  (some (9, 25), some (5, 12)),
  (some (5, 13), some (2, 6)),
  (some (3, 7), some (1, 3)),
  (some (11, 31), some (6, 15)),
  (none, some (6, 10)),
  (some (9, 24), some (4, 12)),
  (some (11, 30), some (5, 15)),
  (some (10, 27), some (5, 13)),
  (none, some (7, 9)),
  (none, some (3, 4)),
  (none, some (8, 8)),
  (none, some (4, 4))
}

private theorem related_final : ∀ p ∈ related,
    holds 49 17 p.1 0 → holds 25 9 p.2 0 := by
  decide

private theorem related_step : ∀ p ∈ related, ∀ b : Bool,
    (step 49 17 p.1 b, step 25 9 p.2 b) ∈ related := by
  decide

private theorem related_implication (k : ℕ) : ∀ p ∈ related,
    holds 49 17 p.1 k → holds 25 9 p.2 k := by
  induction k using Nat.evenOddRec with
  | h0 => exact related_final
  | h_even n ih =>
    intro p hp h
    have hfirst := (holds_step 49 17 p.1 false n).mp (by simpa using h)
    have hsecond := ih _ (related_step p hp false) hfirst
    simpa using (holds_step 25 9 p.2 false n).mpr hsecond
  | h_odd n ih =>
    intro p hp h
    have hfirst := (holds_step 49 17 p.1 true n).mp (by simpa using h)
    have hsecond := ih _ (related_step p hp true) hfirst
    simpa using (holds_step 25 9 p.2 true n).mpr hsecond

/-- Every natural-number solution of the seventeen-times equation also solves
 the nine-times equation, with the same input and binary coefficient convolution. -/
theorem result (k : ℕ) :
    17*k = carryless 49 k → 9*k = carryless 25 k := by
  simp only [carryless_eq]
  have h := related_implication k (some (0,0), some (0,0)) (by decide)
  simpa [holds] using h

#print result
#print axioms related_final
#print axioms related_step
#print axioms related_implication
#print axioms result

end D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment
