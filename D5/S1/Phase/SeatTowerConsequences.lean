/- GID: D5/S1/Phase/SeatTowerConsequences
   generality: G
   mirror-B: D5/B/S1/Phase/SeatTowerConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formal consequences for seat-tower residues, characters, angles, and counts. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S1.Phase.SeatTowerConsequences

open scoped BigOperators NumberTheorySymbols

/-- A residue modulo ninety-six determines its residues modulo twenty-four and
forty-eight. -/
theorem mod_ninety_six_refines_twenty_four_and_forty_eight
    (a b : Int) (h : a ≡ b [ZMOD 96]) :
    a ≡ b [ZMOD 24] ∧ a ≡ b [ZMOD 48] := by
  constructor
  · exact h.of_dvd (by norm_num)
  · exact h.of_dvd (by norm_num)

/-- Once the selector numerator is identified, its three Jacobi factors follow
from multiplicativity in the numerator. -/
theorem jacobi_factorization_of_selector_numerator
    (beta : Int) (n : Nat) (j : Int)
    (hSelector : j = J(2 * (-1) * beta | n)) :
    j = J(2 | n) * J(-1 | n) * J(beta | n) := by
  rw [hSelector, jacobiSym.mul_left, jacobiSym.mul_left]

/-- The peak equation has the stated cosecant form when the sine is nonzero. -/
theorem cosecant_peak_identity (r theta : Real)
    (hSin : Real.sin theta ≠ 0)
    (hPeak : 2 * r * Real.sin theta = Real.sqrt 3) :
    r = Real.sqrt 3 / (2 * Real.sin theta) := by
  field_simp [hSin]
  linarith

/-- A leading term minus the total absolute remainder bounds the absolute
value of the full finite sum. -/
theorem dominant_term_gap_bound {alpha : Type}
    (a : Int) (s : Finset alpha) (f : alpha -> Int) :
    abs a - (∑ i ∈ s, abs (f i)) ≤ abs (a + ∑ i ∈ s, f i) := by
  let remainder := ∑ i ∈ s, f i
  have hTriangle : |a| ≤ |a + remainder| + |remainder| := by
    calc
      |a| = |(a + remainder) + (-remainder)| := by ring_nf
      _ ≤ |a + remainder| + |-remainder| := abs_add_le _ _
      _ = |a + remainder| + |remainder| := by rw [abs_neg]
  have hRemainder : |remainder| ≤ ∑ i ∈ s, |f i| := by
    dsimp [remainder]
    exact Finset.abs_sum_le_sum_abs f s
  dsimp [remainder] at hTriangle hRemainder ⊢
  omega

/-- Choosing one labeled stationing side from `n` split factors has `n`
possibilities. -/
theorem singleton_stationing_choice_count (n : Nat) :
    ((Finset.univ : Finset (Fin n)).powersetCard 1).card = n := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_one_right]

/-- Three labeled split factors have exactly three singleton choices. -/
theorem three_split_primes_have_three_singleton_choices :
    ((Finset.univ : Finset (Fin 3)).powersetCard 1).card = 3 := by
  exact singleton_stationing_choice_count 3

end D5.S1.Phase.SeatTowerConsequences
