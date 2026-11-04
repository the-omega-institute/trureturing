/- GID: D5/S3/StatisticalMechanics/TeaCoordinationSequence
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TeaCoordinationSequence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's coordination sequence formula for the tea uniform tiling. -/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TeaCoordinationSequence

/-- The triangular layers and tetrahedral or prismatic slabs of the tea tiling. -/
def teaGraph : SimpleGraph (ℤ × ℤ × ℤ) where
  Adj u v :=
    (u.2.2 = v.2.2 ∧
      ((v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
       (u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
       (v.1 = u.1 ∧ v.2.1 = u.2.1 + 1) ∨
       (u.1 = v.1 ∧ u.2.1 = v.2.1 + 1) ∨
       (v.1 = u.1 + 1 ∧ u.2.1 = v.2.1 + 1) ∨
       (u.1 = v.1 + 1 ∧ v.2.1 = u.2.1 + 1))) ∨
    (v.2.2 = u.2.2 + 1 ∧
      ((v.1 = u.1 ∧ v.2.1 = u.2.1) ∨
       (u.2.2 % 4 = 0 ∧
         ((v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
          (v.1 = u.1 ∧ v.2.1 = u.2.1 + 1))) ∨
       (u.2.2 % 4 = 2 ∧
         ((v.1 = u.1 - 1 ∧ v.2.1 = u.2.1) ∨
          (v.1 = u.1 ∧ v.2.1 = u.2.1 - 1))))) ∨
    (u.2.2 = v.2.2 + 1 ∧
      ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
       (v.2.2 % 4 = 0 ∧
         ((u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
          (u.1 = v.1 ∧ u.2.1 = v.2.1 + 1))) ∨
       (v.2.2 % 4 = 2 ∧
         ((u.1 = v.1 - 1 ∧ u.2.1 = v.2.1) ∨
          (u.1 = v.1 ∧ u.2.1 = v.2.1 - 1)))))
  symm := ⟨by
    intro u v h
    rcases h with ⟨hk, h⟩ | h | h
    · left
      refine ⟨hk.symm, ?_⟩
      rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, h⟩ | h | h
    · rcases h with h | h | h | h | h | h <;> omega
    · omega
    · omega⟩

/-- Vertices at graph distance exactly n from the representative origin. -/
def shell (n : ℕ) : ℕ := Set.ncard {v | teaGraph.dist (0, 0, 0) v = n}

def claim : Prop := ∀ n : ℕ, 0 < n →
  (n % 4 = 0 → 8 * shell n = 63 * n ^ 2 + 16) ∧
  (n % 4 = 1 → 8 * shell n = 63 * n ^ 2 + 17) ∧
  (n % 4 = 2 → 8 * shell n = 63 * n ^ 2 + 12) ∧
  (n % 4 = 3 → 8 * shell n = 63 * n ^ 2 + 17)

private def plusSlabs (k : ℤ) : ℤ :=
  if 0 ≤ k then (k + 3) / 4 else (-k + 2) / 4

private def minusSlabs (k : ℤ) : ℤ :=
  if 0 ≤ k then (k + 1) / 4 else (-k) / 4

private def residual (i j p q : ℤ) : ℤ :=
  max 0 (max (i - p) (max (j - p) (max (i + j - p)
    (max (-q - i) (max (-q - j) (-q - i - j))))))

private def potential (v : ℤ × ℤ × ℤ) : ℕ :=
  v.2.2.natAbs + (residual v.1 v.2.1 (plusSlabs v.2.2) (minusSlabs v.2.2)).toNat

private lemma potential_step (u v : ℤ × ℤ × ℤ) (h : teaGraph.Adj u v) :
    potential u ≤ potential v + 1 := by
  sorry

private lemma potential_descent (v : ℤ × ℤ × ℤ) (h : 0 < potential v) :
    ∃ u, teaGraph.Adj u v ∧ potential u + 1 = potential v := by
  sorry

private lemma geodesic (v : ℤ × ℤ × ℤ) :
    ∃ w : teaGraph.Walk (0, 0, 0) v, w.length = potential v := by
  sorry

private lemma distance_formula (v : ℤ × ℤ × ℤ) :
    teaGraph.dist (0, 0, 0) v = potential v := by
  sorry

private def regionShell (p q : ℤ) (d : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-q - d) (p + d)).product (Finset.Icc (-q - d) (p + d))).filter
    (fun z => residual z.1 z.2 p q = d)

private lemma region_shell_mem (p q i j : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) (d : ℕ) :
    (i, j) ∈ regionShell p q d ↔ residual i j p q = d := by
  sorry

private lemma region_shell_zero (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * ((regionShell p q 0).card : ℤ) = p ^ 2 + 4 * p * q + q ^ 2 + 3*p + 3*q + 2 := by
  sorry

private lemma region_shell_pos (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (d : ℕ) (hd : 0 < d) :
    ((regionShell p q d).card : ℤ) = 3 * (p + q) + 6 * d := by
  sorry

private lemma layer_sum (n : ℕ) :
    shell n = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card := by
  sorry

private lemma period_four_sum (n : ℕ) (hn : 0 < n) :
    (n % 4 = 0 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+16) ∧
    (n % 4 = 1 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+17) ∧
    (n % 4 = 2 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+12) ∧
    (n % 4 = 3 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+17) := by
  sorry

theorem result : claim := by
  intro n hn
  rw [layer_sum n]
  exact period_four_sum n hn

end D5.S3.StatisticalMechanics.TeaCoordinationSequence
