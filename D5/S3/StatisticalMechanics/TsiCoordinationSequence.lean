/- GID: D5/S3/StatisticalMechanics/TsiCoordinationSequence
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TsiCoordinationSequence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's coordination sequence formulas for the alternating prism tiling tsi. -/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TsiCoordinationSequence

/-- The square layers and the alternating triangular prism slabs of the tsi net. -/
def tsiGraph : SimpleGraph (ℤ × ℤ × ℤ) where
  Adj u v :=
    (u.2.2 = v.2.2 ∧ u.2.1 = v.2.1 ∧ (u.1 = v.1 + 1 ∨ v.1 = u.1 + 1)) ∨
    (u.2.2 = v.2.2 ∧ u.1 = v.1 ∧ (u.2.1 = v.2.1 + 1 ∨ v.2.1 = u.2.1 + 1)) ∨
    (v.2.2 = u.2.2 + 1 ∧
      ((v.1 = u.1 ∧ v.2.1 = u.2.1) ∨
       (Even u.2.2 ∧ v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
       (Odd u.2.2 ∧ v.1 = u.1 ∧ v.2.1 = u.2.1 + 1))) ∨
    (u.2.2 = v.2.2 + 1 ∧
      ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
       (Even v.2.2 ∧ u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
       (Odd v.2.2 ∧ u.1 = v.1 ∧ u.2.1 = v.2.1 + 1)))
  symm := by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless := by
    intro u h
    rcases h with h | h | h | h <;> omega

/-- The coordination sequence, counted at the representative origin. -/
def shell (n : ℕ) : ℕ := Set.ncard {v | tsiGraph.dist (0, 0, 0) v = n}

def claim : Prop :=
  (∀ n : ℕ, 0 < n → Even n → 2 * shell n = 13 * n ^ 2 + 4) ∧
  (∀ n : ℕ, Odd n → 2 * shell n = 13 * n ^ 2 + 3)

private def gap (c i : ℤ) : ℕ :=
  (min 0 c - i).toNat + (i - max 0 c).toNat

private def potential (v : ℤ × ℤ × ℤ) : ℕ :=
  v.2.2.natAbs + gap ((v.2.2 + 1) / 2) v.1 + gap (v.2.2 / 2) v.2.1

private lemma potential_zero : potential (0, 0, 0) = 0 := by
  sorry

private lemma potential_step (u v : ℤ × ℤ × ℤ) (h : tsiGraph.Adj u v) :
    potential u ≤ potential v + 1 := by
  sorry

private lemma potential_descent (v : ℤ × ℤ × ℤ) (h : 0 < potential v) :
    ∃ u, tsiGraph.Adj u v ∧ potential u + 1 = potential v := by
  sorry

private lemma geodesic (v : ℤ × ℤ × ℤ) :
    ∃ p : tsiGraph.Walk (0, 0, 0) v, p.length = potential v := by
  sorry

private lemma distance_formula (v : ℤ × ℤ × ℤ) :
    tsiGraph.dist (0, 0, 0) v = potential v := by
  sorry

private def intervalShell (c : ℤ) (d : ℕ) : Finset ℤ :=
  (Finset.Icc (min 0 c - d) (max 0 c + d)).filter (fun i => gap c i = d)

private lemma interval_shell_mem (c i : ℤ) (d : ℕ) :
    i ∈ intervalShell c d ↔ gap c i = d := by
  sorry

private lemma interval_shell_card (c : ℤ) (d : ℕ) :
    (intervalShell c d).card = if d = 0 then c.natAbs + 1 else 2 := by
  sorry

private def rectangleShell (c e : ℤ) (d : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (d + 1)).biUnion
    (fun t => (intervalShell c t).product (intervalShell e (d - t)))

private lemma rectangle_shell_mem (c e i j : ℤ) (d : ℕ) :
    (i, j) ∈ rectangleShell c e d ↔ gap c i + gap e j = d := by
  sorry

private lemma rectangle_shell_card_zero (c e : ℤ) :
    (rectangleShell c e 0).card = (c.natAbs + 1) * (e.natAbs + 1) := by
  sorry

private lemma rectangle_shell_card_pos (c e : ℤ) (d : ℕ) (hd : 0 < d) :
    (rectangleShell c e d).card = 2 * (c.natAbs + e.natAbs) + 4 * d := by
  sorry

private lemma layer_sum (n : ℕ) :
    shell n = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (rectangleShell ((k + 1) / 2) (k / 2) (n - k.natAbs)).card := by
  sorry

private lemma stack_sum (n : ℕ) (hn : 0 < n) :
    shell n + 2 * n = 6 * n ^ 2 +
      2 * ((n / 2 + 1) * ((n + 1) / 2 + 1)) := by
  sorry

private lemma even_formula (n : ℕ) (hn : 0 < n) (he : Even n) :
    2 * shell n = 13 * n ^ 2 + 4 := by
  sorry

private lemma odd_formula (n : ℕ) (ho : Odd n) :
    2 * shell n = 13 * n ^ 2 + 3 := by
  sorry

theorem result : claim := ⟨even_formula, odd_formula⟩

end D5.S3.StatisticalMechanics.TsiCoordinationSequence
