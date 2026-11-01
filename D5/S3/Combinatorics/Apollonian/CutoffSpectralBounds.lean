/- GID: D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/CutoffSpectralBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Matrix]
   utility: none
   digest: Euclidean remainder bounds for the actual inner-face Apollonian graph. -/

module
public import D5.S3.Combinatorics.Apollonian.InnerFaceStages
public import D5.S3.SpectralTopology.SchurOperatorBound
public import Mathlib.Tactic

/-! Spectral cutoff estimates use the constructed graph and its proved birth orientation. -/

@[expose] public section
noncomputable section
namespace D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
open InnerFaceStages Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The actual late-edge orientation, with zero-one entries. -/
def lateDirected (k t : ℕ) : Matrix (LateVertex k t) (LateVertex k t) ℝ :=
  fun u v => if Oriented (k+t) u.val v.val then 1 else 0

private theorem late_directed_row (k t : ℕ) (u : LateVertex k t) :
    ∑ v, ‖lateDirected k t u v‖ ≤ 3 := by
  have h := oriented_outdegree_le_three (k+t) u.val
  have he := Finset.sum_subtype (F := inferInstance) (p := fun w : Vertex (k+t) => k < birth (k+t) w)
    (Finset.univ.filter fun w : Vertex (k+t) => k < birth (k+t) w)
    (by intro w; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun w => if Oriented (k+t) u.val w then (1:ℕ) else 0)
  rw [Finset.sum_filter] at he
  have hs : (∑ v : LateVertex k t, if Oriented (k+t) u.val v.val then (1:ℕ) else 0) ≤
      ∑ v : Vertex (k+t), if Oriented (k+t) u.val v then 1 else 0 := by
    rw [← he]
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> omega
  simp only [lateDirected, apply_ite norm, norm_one, norm_zero]
  exact_mod_cast hs.trans h

private theorem late_directed_col (k t : ℕ) (v : LateVertex k t) :
    ∑ u, ‖lateDirected k t u v‖ ≤ (3 * 2 ^ (k+t-k-1) : ℕ) := by
  have h := late_oriented_indegree_le (k+t) k v.val v.property
  have he := Finset.sum_subtype (F := inferInstance) (p := fun w : Vertex (k+t) => k < birth (k+t) w)
    (Finset.univ.filter fun w : Vertex (k+t) => k < birth (k+t) w)
    (by intro w; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun w => if Oriented (k+t) w v.val then (1:ℕ) else 0)
  rw [Finset.sum_filter] at he
  have hs : (∑ u : LateVertex k t, if Oriented (k+t) u.val v.val then (1:ℕ) else 0) =
      ∑ u : Vertex (k+t), if k < birth (k+t) u ∧ Oriented (k+t) u v.val then 1 else 0 := by
    rw [← he]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp_all
  simp only [lateDirected, apply_ite norm, norm_one, norm_zero]
  exact_mod_cast hs ▸ h

/-- Exact decomposition of the late ordinary adjacency into its two birth directions. -/
theorem late_adjacency_eq_directed_add_transpose (k t : ℕ) :
    lateAdjacency k t = lateDirected k t + (lateDirected k t).transpose := by
  ext u v
  change (if adjacent (k+t) u.val v.val then (1:ℝ) else 0) = _
  by_cases ha : adjacent (k+t) u.val v.val
  · rcases late_edge_oriented (k+t) k u.val v.val u.property v.property ha with h | h
    · have hn : ¬ Oriented (k+t) v.val u.val := fun hn => (Nat.lt_asymm h.2 hn.2)
      simp [lateDirected, ha, h, hn, Matrix.transpose_apply]
    · have hn : ¬ Oriented (k+t) u.val v.val := fun hn => (Nat.lt_asymm h.2 hn.2)
      simp [lateDirected, ha, h, hn, Matrix.transpose_apply]
  · have hu : ¬ Oriented (k+t) u.val v.val := fun h => ha h.1
    have hv : ¬ Oriented (k+t) v.val u.val := fun h => ha ((graph (k+t)).adj_symm h.1)
    simp [lateDirected, ha, hu, hv, Matrix.transpose_apply]

/-- Euclidean operator bound for the actual late induced ordinary adjacency. -/
theorem late_adjacency_norm_le (k t : ℕ) :
    ‖lateAdjacency k t‖ ≤ 2 * Real.sqrt (3 * (3 * 2 ^ (k+t-k-1) : ℕ)) := by
  have hd := SpectralTopology.SchurOperatorBound.l2_opNorm_le_schur (lateDirected k t)
    (by norm_num : (0:ℝ) ≤ 3) (Nat.cast_nonneg (3 * 2 ^ (k+t-k-1)))
    (late_directed_row k t) (late_directed_col k t)
  rw [late_adjacency_eq_directed_add_transpose]
  have ht : ‖(lateDirected k t).transpose‖ = ‖lateDirected k t‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose (lateDirected k t)
  calc
    _ ≤ ‖lateDirected k t‖ + ‖(lateDirected k t).transpose‖ := norm_add_le _ _
    _ ≤ _ := by rw [ht]; linarith

end D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
