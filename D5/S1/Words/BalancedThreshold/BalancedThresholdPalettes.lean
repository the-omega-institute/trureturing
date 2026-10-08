/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdPalettes
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdPalettes
   mirror-E: none(waiver:infinite-word-construction)
   anchors: []
   utility: none
   digest: Mechanical occurrence ranks realize both disjoint constant-gap palettes. -/

import D5.S1.Words.Mechanical.MechanicalDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical

/-- Zero-phase colouring by the two-cycle and the interleaved cycles of sizes `t`, `t+1`. -/
noncomputable def colouredMechanicalWord (alpha rho : ℝ) (t : ℕ) (ht : 0 < t)
    (n : ℕ) : Fin (2 * t + 3) := by
  let a := lowerMechanicalWindowTrueCount alpha rho 0 n
  let b := n - a
  by_cases h : lowerMechanicalWord alpha rho n = true
  · exact ⟨a % 2, by have := Nat.mod_lt a (by omega : 0 < 2); omega⟩
  · by_cases he : b % 2 = 0
    · exact ⟨2 + (b / 2) % t, by have := Nat.mod_lt (b / 2) ht; omega⟩
    · exact ⟨2 + t + (b / 2) % (t + 1), by
        have := Nat.mod_lt (b / 2) (by omega : 0 < t + 1)
        omega⟩

end D5.S1.Words.BalancedThreshold
