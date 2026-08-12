/- GID: D5/S0/Diagonal/CaptureIntersectionCardinality
   generality: G
   mirror-B: D5/B/S0/Diagonal/CaptureIntersectionCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For finite address and value types, a nonempty s-row set has exactly k^s * n^(A*(A-s)) listings that capture the twisted diagonal on every selected row, where A and n are the type cardinalities and k is the number of fixed points of the twist. -/

import D5.S0.Diagonal.CaptureCount

universe u v

namespace D5.S0.Diagonal.CaptureIntersectionCardinality

open EscapeCount

/-- For a nonempty finite set of rows, the simultaneous twisted-diagonal capture count is
`k^s * n^(A*(A-s))`, with each named parameter tied to its source cardinality. -/
theorem capture_intersection_cardinality
    {Address : Type u} {Y : Type v} [Fintype Address] [Fintype Y]
    (f : Y → Y) (S : Finset Address) (A n k s : ℕ)
    (hA : Fintype.card Address = A)
    (hn : Fintype.card Y = n)
    (hk : Nat.card {y : Y // f y = y} = k)
    (hs : S.card = s) (_hs_pos : 1 ≤ s) :
    Nat.card {g : Address → Address → Y // ∀ a ∈ S, g a = diagonal f g} =
      k ^ s * n ^ (A * (A - s)) := by
  rw [CaptureCount.capture_inter_card, hk, hs, hn, hA]

end D5.S0.Diagonal.CaptureIntersectionCardinality
