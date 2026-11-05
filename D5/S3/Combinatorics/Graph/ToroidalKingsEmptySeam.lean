/- GID: D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ToroidalKingsEmptySeam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Empty seams remove additional toroidal king edges. -/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! # Finite king-board counts and empty seams

The coordinate and cardinality definitions retain both periodic coordinates and
all side lengths. The peak counts all cardinality fibers, including the empty set.
-/

namespace D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam

open Finset

noncomputable section

/-- Absolute coordinate difference, represented in natural arithmetic. -/
def gap (a b : ℕ) : ℕ := (a - b) + (b - a)

def freeAdjacent (u v : ℕ × ℕ) : Prop :=
  u ≠ v ∧ gap u.1 v.1 ≤ 1 ∧ gap u.2 v.2 ≤ 1

def torusAdjacent (n : ℕ) (u v : ℕ × ℕ) : Prop :=
  u ≠ v ∧ min (gap u.1 v.1) (n - gap u.1 v.1) ≤ 1 ∧
    min (gap u.2 v.2) (n - gap u.2 v.2) ≤ 1

private theorem seam_distance {n a b : ℕ} (ha : a < n - 1) (hb : b < n - 1) :
    min (gap a b) (n - gap a b) ≤ 1 ↔ gap a b ≤ 1 := by
  unfold gap
  omega

/-- Identity on the board with the final row and column empty reflects and
preserves all king edges, including for odd side lengths. -/
theorem empty_seam_adjacency {n : ℕ} (u v : ℕ × ℕ)
    (hu : u.1 < n - 1 ∧ u.2 < n - 1)
    (hv : v.1 < n - 1 ∧ v.2 < n - 1) :
    torusAdjacent n u v ↔ freeAdjacent u v := by
  simp only [torusAdjacent, freeAdjacent,
    seam_distance hu.1 hv.1, seam_distance hu.2 hv.2]

/-- The free square board, using the literal coordinate range of the source. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := (range n) ×ˢ (range n)

/-- Independent vertex subsets of a finite board for the specified adjacency. -/
def independentSets (b : Finset (ℕ × ℕ)) (adj : (ℕ × ℕ) → (ℕ × ℕ) → Prop) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact b.powerset.filter fun s => ∀ u ∈ s, ∀ v ∈ s, ¬ adj u v

private theorem mem_independentSets {b : Finset (ℕ × ℕ)}
    {adj : (ℕ × ℕ) → (ℕ × ℕ) → Prop} {s : Finset (ℕ × ℕ)} :
    s ∈ independentSets b adj ↔ s ⊆ b ∧ ∀ u ∈ s, ∀ v ∈ s, ¬ adj u v := by
  classical
  simp [independentSets]

/-- Total free-board and toroidal independent-set counts. -/
def freeCount (n : ℕ) : ℕ := (independentSets (board n) freeAdjacent).card

def torusCount (n : ℕ) : ℕ := (independentSets (board n) (torusAdjacent n)).card

/-- Every coefficient, including zero coefficients outside the independence number. -/
def coefficient (n k : ℕ) : ℕ := by
  classical
  exact ((independentSets (board n) (torusAdjacent n)).filter fun s => s.card = k).card

/-- The maximum over all cardinalities from zero through the number of vertices. -/
def peak (n : ℕ) : ℕ := (range (n ^ 2 + 1)).sup (coefficient n)

private theorem board_mono {m n : ℕ} (h : m ≤ n) : board m ⊆ board n := by
  intro u hu
  simp only [board, mem_product, mem_range] at hu ⊢
  exact ⟨hu.1.trans_le h, hu.2.trans_le h⟩

/-- Empty final row and column give an injection valid for every side length. -/
theorem free_le_torus (n : ℕ) : freeCount (n - 1) ≤ torusCount n := by
  apply card_le_card
  intro s hs
  obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
  refine mem_independentSets.mpr ⟨hb.trans (board_mono (Nat.sub_le n 1)), ?_⟩
  intro u hu v hv hadj
  have hbu := hb hu
  have hbv := hb hv
  simp only [board, mem_product, mem_range] at hbu hbv
  exact hi u hu v hv ((empty_seam_adjacency u v hbu hbv).mp hadj)

/-- Forgetting the wraparound edges is an injection into the free board. -/
theorem torus_le_free (n : ℕ) : torusCount n ≤ freeCount n := by
  apply card_le_card
  intro s hs
  obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
  refine mem_independentSets.mpr ⟨hb, ?_⟩
  intro u hu v hv hfree
  exact hi u hu v hv ⟨hfree.1, (min_le_left _ _).trans hfree.2.1,
    (min_le_left _ _).trans hfree.2.2⟩

private theorem coefficient_sum (n : ℕ) :
    ∑ k ∈ range (n ^ 2 + 1), coefficient n k = torusCount n := by
  classical
  symm
  apply card_eq_sum_card_fiberwise
  intro s hs
  have h := card_le_card (mem_independentSets.mp hs).1
  simpa [board, card_product, card_range, pow_two] using Nat.lt_succ_of_le h

private theorem coefficient_le_peak (n k : ℕ) (hk : k ∈ range (n ^ 2 + 1)) :
    coefficient n k ≤ peak n := Finset.le_sup hk

/-- The modal coefficient loses at most the number of cardinality fibers. -/
theorem count_le_mul_peak (n : ℕ) : torusCount n ≤ (n ^ 2 + 1) * peak n := by
  rw [← coefficient_sum]
  calc
    ∑ k ∈ range (n ^ 2 + 1), coefficient n k ≤
        ∑ _k ∈ range (n ^ 2 + 1), peak n :=
      sum_le_sum fun k hk => coefficient_le_peak n k hk
    _ = (n ^ 2 + 1) * peak n := by simp

theorem peak_le_count (n : ℕ) : peak n ≤ torusCount n := by
  classical
  apply Finset.sup_le
  intro k hk
  exact card_le_card (filter_subset _ _)

#print axioms empty_seam_adjacency
#print axioms free_le_torus
#print axioms torus_le_free
#print axioms count_le_mul_peak
#print axioms peak_le_count
end
end D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
