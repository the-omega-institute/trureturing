/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact count for the connected semi-meander second diagonal. -/


import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Stage5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
/-- Exact connected semi-meander second-diagonal count for every n >= 4. -/
theorem result (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} =
      (n ^ 2 + 2 * n + n % 2 - 20) / 2 := by
  classical
  -- Cut at the midpoint, then contract the fixed lower rainbow.
  -- Transfer the prefix count to the source model and solve the division step.
  change sourceCount n hn = _
  have hcount : sourceCount n hn = 2 * Nat.card
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonical pq.1 pq.2} := by
    unfold sourceCount
    rw [Nat.card_congr (connectedSourcePrefixEquiv n hn)]
    exact connected_pair_card_double n hn
  have h : 2 * sourceCount n hn + 20 = n ^ 2 + 2 * n + n % 2 := by
    have hm : n - 4 + 4 = n := by omega
    calc
      2 * sourceCount n hn + 20 =
          4 * ((n - 4) + ((n - 4) * (n - 4)) / 4 +
            ((n - 4) + 1) + (((n - 4) + 1) / 2)) + 20 := by
        rw [hcount, canonical_card n hn]
        ring
      _ = (n - 4 + 4) * (n - 4 + 4) +
          2 * (n - 4 + 4) + (n - 4 + 4) % 2 :=
        canonical_count_arithmetic (n - 4)
      _ = n ^ 2 + 2 * n + n % 2 := by rw [hm]; ring
  omega

end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
