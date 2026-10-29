/- GID: D5/S3/Combinatorics/Partitions/FerrersLevelCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/FerrersLevelCounting
   mirror-E: none(waiver:finite-level-counting-recurrence)
   anchors: [D5/S3/Combinatorics/Partitions/FerrersLevelTransfer, D5/S3/Combinatorics/Partitions/FerrersRowCoordinates]
   utility: none
   digest: A finite Gaussian transfer recurrence counts compatible ordered levels. -/

import D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
import D5.S3.Combinatorics.Partitions.FerrersRowCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open scoped BigOperators

/-- Compatible levels, retaining each row and its prescribed level total. -/
def Paths (r U : ℕ) : List ℕ → Fin (U+1) → Type
  | [], _ => PUnit
  | a::as, u => (v : Fin (U+1)) × (Level r U u.val v.val a × Paths r U as v)

instance pathsFintype (r U : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    Fintype (Paths r U as u) := by
  classical
  induction as generalizing u with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons a as ih =>
      change Fintype ((v : Fin (U+1)) × (Level r U u.val v.val a × Paths r U as v))
      letI := fun v => ih v
      exact inferInstance

/-- Fully finite evaluation: start with the constant one vector and apply one
    guarded Gaussian matrix for each prescribed bottom-to-top level. -/
def count (r U : ℕ) : List ℕ → Fin (U+1) → ℤ
  | [], _ => 1
  | a::as, u => ∑ v : Fin (U+1), transition r U a u v * count r U as v

/-- Cardinality of all compatible level choices, without a board search. -/
theorem paths_card (r U : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    (Fintype.card (Paths r U as u) : ℤ) = count r U as u := by
  induction as generalizing u with
  | nil =>
      change (Fintype.card PUnit : ℤ) = 1
      rw [Fintype.card_unique]
      rfl
  | cons a as ih =>
      change (Fintype.card ((v : Fin (U+1)) ×
        (Level r U u.val v.val a × Paths r U as v)) : ℤ) = _
      rw [Fintype.card_sigma]
      simp only [Fintype.card_prod, Nat.cast_sum, Nat.cast_mul, count]
      apply Finset.sum_congr rfl
      intro v _
      rw [level_card, ih]

def rowIndex (m t : ℕ) (p : Fin t) (j : Fin m) : Fin (m*t) :=
  ⟨m*p.val+j.val, by
    have hp := Nat.mul_le_mul_left m (Nat.succ_le_of_lt p.isLt)
    rw [Nat.mul_succ] at hp
    omega⟩

/-- Flat, bounded, weakly decreasing rows with the exact ordered block sums. -/
abbrev FlatFiber (r U : ℕ) (as : List ℕ) (u : Fin (U+1)) :=
  {x : Fin ((r+1)*as.length) → Fin (U+1) //
    Antitone x ∧ (∀ j, x j ≤ u) ∧
    ∀ p : Fin as.length, ∑ j : Fin (r+1), (x (rowIndex (r+1) as.length p j)).val = as[p.val]}

end D5.S3.Combinatorics.Partitions.FerrersLevelCounting
