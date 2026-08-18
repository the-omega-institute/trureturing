/- GID: D5/S3/Arith/PellEquations/PellTowerInnerChain
   generality: G
   mirror-B: D5/B/S3/Arith/PellEquations/PellTowerInnerChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The map d -> d(d-2) preserves the tower's Pell-type equation. -/

import Mathlib.Tactic.Ring

namespace D5.S3.Arith.PellEquations.PellTowerInnerChain

/-- A solution of `(d + 1)(d - 3) = D k^2` produces another solution under the inner-chain
transformation `d' = d(d - 2)`, with new Pell coordinate `(d - 1)k`. -/
theorem pell_tower_inner_chain (D d k : ℤ)
    (h : (d + 1) * (d - 3) = D * k ^ 2) :
    let d' := d * (d - 2)
    (d' + 1) * (d' - 3) = D * ((d - 1) * k) ^ 2 := by
  dsimp only
  calc
    (d * (d - 2) + 1) * (d * (d - 2) - 3) =
        (d - 1) ^ 2 * ((d + 1) * (d - 3)) := by ring
    _ = D * ((d - 1) * k) ^ 2 := by rw [h]; ring

#print axioms pell_tower_inner_chain

end D5.S3.Arith.PellEquations.PellTowerInnerChain
