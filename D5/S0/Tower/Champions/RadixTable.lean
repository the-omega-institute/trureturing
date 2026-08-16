/- GID: D5/S0/Tower/Champions/RadixTable
   generality: G
   mirror-B: D5/B/S0/Tower/Champions/RadixTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Odd and even radix champion assertions are packaged in one exact table theorem. -/

import D5.S0.Tower.ChampionExtremality
import D5.S0.Tower.ConstantArms

/- Library-search audit trail (2026-08-16): repository search found the exact frozen
   `constant_arm`, `odd_champion`, `even_champion_arm`, and `even_champion_sup`
   declarations, so this theorem only packages those results and proves no new mathematics. -/

namespace D5.S0.Tower.Champions.RadixTable

open D5.S0.Tower.ChampionExtremality
open D5.S0.Tower.ConstantArms

/-- The constant arm and the odd/even champion rows, packaged as one radix table. -/
theorem radix_champion_table (b Q : ℕ) (hb : 2 ≤ b) (hQ : 1 ≤ Q) :
    (b : ℝ) ^ Q * radixDistance b Q ((1 : ℝ) / (b + 1)) = (1 : ℝ) / (b + 1)
  ∧ (Odd b →
      sSup {r : ℝ | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
        r ≤ (b : ℝ) ^ Q * radixDistance b Q x} = 1 / 2)
  ∧ (Even b →
      (b : ℝ) ^ Q * radixDistance b Q (((b / 2 : ℕ) : ℝ) / (b + 1)) =
        (b : ℝ) / (2 * (b + 1)) ∧
      sSup {r : ℝ | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
        r ≤ (b : ℝ) ^ Q * radixDistance b Q x} =
        (b : ℝ) / (2 * (b + 1))) := by
  constructor
  · exact constant_arm b Q hb hQ
  constructor
  · intro hbOdd
    exact odd_champion b hb hbOdd
  · intro hbEven
    exact ⟨even_champion_arm b Q hb hQ hbEven, even_champion_sup b hb hbEven⟩

end D5.S0.Tower.Champions.RadixTable
