/- GID: D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ToroidalKingsEmptySeam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Empty seams remove additional toroidal king edges. -/
import Mathlib.Tactic.Omega

namespace D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam

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

#print axioms empty_seam_adjacency
end D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
