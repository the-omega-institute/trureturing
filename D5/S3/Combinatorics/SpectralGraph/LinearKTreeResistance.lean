/- GID: D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/LinearKTreeResistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Straight linear k-tree resistance increments converge for every fixed positive k. -/

/-
admission_basis: escape-witness
question_answered: #22865
escape_witness: correction_converges_of_stable_moments
proof_shape: content: correction_converges_of_stable_moments, result.
The remaining theorem declarations are consumed bind-only helpers.
Direct frozen dependencies: D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_control_of_lower_bound (statement_id: sha256:b8e09b551dfe3a331e1cf4d68b29f88742ee7175838b7e7dfb768180e81ae0ce).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25440
intervalVector: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_band, LinearKTreeResistance.gram_entry_nonneg, LinearKTreeResistance.intervalGram, LinearKTreeResistance.intervalGram_entry_extended, LinearKTreeResistance.intervalGram_entry_prefix, LinearKTreeResistance.intervalGram_entry_stable, LinearKTreeResistance.intervalGram_one, LinearKTreeResistance.intervalGram_posSemidef, LinearKTreeResistance.intervalGram_rev, LinearKTreeResistance.intervalGram_row, LinearKTreeResistance.intervalGram_row_exact, LinearKTreeResistance.intervalGram_sum, LinearKTreeResistance.intervalVector_apply, LinearKTreeResistance.intervalVector_one, LinearKTreeResistance.intervalVector_rev, LinearKTreeResistance.intervalVector_sum; Direct frozen dependencies: none.
intervalVector_apply: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_band, LinearKTreeResistance.gram_entry_nonneg, LinearKTreeResistance.intervalGram_entry_extended, LinearKTreeResistance.intervalGram_entry_prefix, LinearKTreeResistance.intervalGram_entry_stable, LinearKTreeResistance.intervalGram_row_exact, LinearKTreeResistance.intervalVector_one, LinearKTreeResistance.intervalVector_rev, LinearKTreeResistance.intervalVector_sum; Direct frozen dependencies: none.
intervalGram: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram, LinearKTreeResistance.gram_band, LinearKTreeResistance.gram_defect, LinearKTreeResistance.gram_entry_formula, LinearKTreeResistance.gram_entry_nonneg, LinearKTreeResistance.gram_entry_stable, LinearKTreeResistance.gram_eq_cutGram, LinearKTreeResistance.gram_lower, LinearKTreeResistance.gram_rev, LinearKTreeResistance.gram_row_le, LinearKTreeResistance.intervalGram_entry_extended, LinearKTreeResistance.intervalGram_entry_prefix, LinearKTreeResistance.intervalGram_entry_stable, LinearKTreeResistance.intervalGram_one, LinearKTreeResistance.intervalGram_posSemidef, LinearKTreeResistance.intervalGram_rev, LinearKTreeResistance.intervalGram_row, LinearKTreeResistance.intervalGram_row_exact, LinearKTreeResistance.intervalGram_row_le, LinearKTreeResistance.intervalGram_sum, LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalGram_sum: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_band, LinearKTreeResistance.gram_entry_nonneg, LinearKTreeResistance.intervalGram_entry_extended, LinearKTreeResistance.intervalGram_entry_prefix, LinearKTreeResistance.intervalGram_one, LinearKTreeResistance.intervalGram_rev, LinearKTreeResistance.intervalGram_row; Direct frozen dependencies: none.
gram: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_band, LinearKTreeResistance.gram_defect, LinearKTreeResistance.gram_entry_formula, LinearKTreeResistance.gram_entry_nonneg, LinearKTreeResistance.gram_entry_stable, LinearKTreeResistance.gram_eq_cutGram, LinearKTreeResistance.gram_lower, LinearKTreeResistance.gram_rev, LinearKTreeResistance.gram_row_le, LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalVector_one: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.intervalGram_one; Direct frozen dependencies: none.
intervalGram_one: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_lower; Direct frozen dependencies: none.
intervalGram_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_eq_cutGram, LinearKTreeResistance.gram_lower, LinearKTreeResistance.result; Direct frozen dependencies: none.
gram_lower: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalVector_sum: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.intervalGram_row; Direct frozen dependencies: none.
intervalGram_row: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.intervalGram_row_exact; Direct frozen dependencies: none.
intervalGram_row_exact: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_defect, LinearKTreeResistance.intervalGram_row_le; Direct frozen dependencies: none.
intervalGram_row_le: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_row_le; Direct frozen dependencies: none.
gram_row_le: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
gram_entry_nonneg: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalGram_entry_prefix: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.intervalGram_entry_stable; Direct frozen dependencies: none.
intervalGram_entry_stable: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_entry_stable; Direct frozen dependencies: none.
gram_entry_stable: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
gram_band: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalVector_rev: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.intervalGram_rev; Direct frozen dependencies: none.
intervalGram_rev: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_rev; Direct frozen dependencies: none.
gram_rev: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
boundaryVector: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_defect; Direct frozen dependencies: none.
gram_defect: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
graph: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.IsResistanceSequence, LinearKTreeResistance.cutGram_entry_formula, LinearKTreeResistance.electrical_coordinates, LinearKTreeResistance.electrical_inverse_identification, LinearKTreeResistance.exists_resistance_sequence, LinearKTreeResistance.gram_eq_cutGram, LinearKTreeResistance.graph_adj_iff, LinearKTreeResistance.graph_connected, LinearKTreeResistance.lap_step_left, LinearKTreeResistance.result; Direct frozen dependencies: none.
IsResistanceSequence: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.claim, LinearKTreeResistance.exists_resistance_sequence, LinearKTreeResistance.result; Direct frozen dependencies: none.
claim: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
graph_adj_iff: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.graph_connected, LinearKTreeResistance.lap_step_left; Direct frozen dependencies: none.
graph_connected: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.exists_resistance_sequence; Direct frozen dependencies: none.
sum_laplacian_mulVec: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.sum_of_augmented_equation; Direct frozen dependencies: none.
ones_mulVec: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.exists_unit_current_voltage, LinearKTreeResistance.sum_of_augmented_equation; Direct frozen dependencies: none.
sum_of_augmented_equation: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.exists_unit_current_voltage; Direct frozen dependencies: none.
exists_unit_current_voltage: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.exists_resistance_sequence; Direct frozen dependencies: none.
exists_resistance_sequence: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
fwdDiff_fin: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.stepMatrix_integrates; Direct frozen dependencies: none.
stepMatrix_integrates: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.electrical_coordinates, LinearKTreeResistance.electrical_inverse_identification; Direct frozen dependencies: none.
stepMatrix_current: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.electrical_coordinates; Direct frozen dependencies: none.
electrical_coordinates: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.electrical_inverse_identification; Direct frozen dependencies: none.
electrical_inverse_identification: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
intervalGram_entry_extended: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_entry_formula; Direct frozen dependencies: none.
gram_entry_formula: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_eq_cutGram; Direct frozen dependencies: none.
lap_step_left: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.cutGram_entry_formula; Direct frozen dependencies: none.
cutGram_entry_formula: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.gram_eq_cutGram; Direct frozen dependencies: none.
gram_eq_cutGram: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
exists_limit_of_stabilizing_approximants: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.correction_converges_of_stable_moments; Direct frozen dependencies: none.
inverse_polynomial_identity: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.inverse_polynomial_error; Direct frozen dependencies: none.
inverse_polynomial_error: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.correction_converges_of_stable_moments; Direct frozen dependencies: none.
quadratic_operator_bound: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.correction_converges_of_stable_moments; Direct frozen dependencies: none.
correction_converges_of_stable_moments: proof_shape: content; escape_witness: correction_converges_of_stable_moments; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
result: proof_shape: content; escape_witness: correction_converges_of_stable_moments; consumers: terminal conclusion; Direct frozen dependencies: D5/S3/Observer/BlockStructure/UniformResolventRemainder.inverse_control_of_lower_bound (sha256:b8e09b551dfe3a331e1cf4d68b29f88742ee7175838b7e7dfb768180e81ae0ce).
-/
import D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.NumberTheory.Bernoulli
import D5.S3.Observer.BlockStructure.UniformResolventRemainder

open D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
open scoped Classical

open Matrix Finset
open scoped BigOperators MatrixOrder

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
noncomputable section

private def intervalVector (N s d : ℕ) (i : Fin N) : ℝ :=
  Set.indicator {j : Fin N | s ≤ j.val ∧ j.val < s + d} (fun _ => (1 : ℝ)) i

private theorem intervalVector_apply (N s d : ℕ) (i : Fin N) :
    intervalVector N s d i = if s ≤ i.val ∧ i.val < s + d then 1 else 0 := by
  classical
  exact Set.indicator_apply _ _ _

private def intervalGram (N d : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N =>
    (WithLp.toLp 2 (fun s : Fin (N + 1 - d) => intervalVector N s.val d i) :
      EuclideanSpace ℝ (Fin (N + 1 - d))))

private theorem intervalGram_sum (N d : ℕ) : intervalGram N d =
    ∑ s ∈ Finset.range (N + 1 - d),
      Matrix.vecMulVec (intervalVector N s d) (intervalVector N s d) := by
  ext i j
  simp only [intervalGram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.gram, Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct]
  simpa only [mul_comm] using
    Fin.sum_univ_eq_sum_range (fun s => intervalVector N s d i *
      intervalVector N s d j) (N + 1 - d)

private def gram (N k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ d ∈ Finset.range k, intervalGram N (d + 1)

private theorem intervalVector_one (N s : ℕ) (i : Fin N) :
    intervalVector N s 1 i = if i.val = s then 1 else 0 := by
  have heq : (s ≤ i.val ∧ i.val < s + 1) ↔ i.val = s := by omega
  simp only [intervalVector_apply, heq]

private theorem intervalGram_one (N : ℕ) : intervalGram N 1 = 1 := by
  ext i j
  simp only [intervalGram_sum, Nat.add_sub_cancel, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i.val]
  · simp only [intervalVector_one]
    by_cases hij : i = j
    · subst j; simp
    · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      simp [hval, hij]
  · intro s hs hsi
    simp only [intervalVector_one, ite_eq_right (Ne.symm hsi), zero_mul]
  · intro hi
    exact (hi (Finset.mem_range.mpr i.is_lt)).elim

private theorem intervalGram_posSemidef (N d : ℕ) : (intervalGram N d).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ _

private theorem gram_lower (N k : ℕ) (hk : 1 ≤ k) :
    (1 : Matrix (Fin N) (Fin N) ℝ) ≤ gram N k := by
  have hk' : k = (k - 1) + 1 := by exact (Nat.sub_eq_iff_eq_add hk).mp rfl
  rw [Matrix.le_iff, gram, hk', Finset.sum_range_succ', intervalGram_one]
  rw [add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro d hd
  exact intervalGram_posSemidef N (d + 1 + 1)

private theorem intervalVector_sum (N s d : ℕ) (hs : s + d ≤ N) :
    ∑ i : Fin N, intervalVector N s d i = (d : ℝ) := by
  have hset : (Finset.range N).filter (fun i => s ≤ i ∧ i < s + d) =
      Finset.Ico s (s + d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp only [intervalVector_apply]
  change (∑ i : Fin N, (fun j : ℕ => if s ≤ j ∧ j < s + d then (1 : ℝ) else 0) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if s ≤ j ∧ j < s + d then (1 : ℝ) else 0) N]
  simp only [Finset.sum_boole]
  rw [hset]
  simp

private theorem intervalGram_row (N d : ℕ) (_hd : 1 ≤ d) (i : Fin N) :
    (intervalGram N d *ᵥ (1 : Fin N → ℝ)) i =
      (d : ℝ) * ∑ s ∈ Finset.range (N + 1 - d), intervalVector N s d i := by
  simp only [intervalGram_sum, Matrix.sum_mulVec, Finset.sum_apply]
  simp only [Matrix.vecMulVec_mulVec, dotProduct, Pi.one_apply, mul_one]
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsd : s + d ≤ N := by
    have := Finset.mem_range.mp hs
    omega
  rw [intervalVector_sum N s d hsd]
  simp only [op_smul_eq_mul]
  ring

private theorem intervalGram_row_exact (N d : ℕ) (hd : 1 ≤ d) (i : Fin N) :
    (intervalGram N d *ᵥ (1 : Fin N → ℝ)) i =
      (d : ℝ) * ((min (N + 1 - d) (i.val + 1) - (i.val + 1 - d) : ℕ) : ℝ) := by
  rw [intervalGram_row N d hd i]
  have hset : (Finset.range (N + 1 - d)).filter
      (fun s => s ≤ i.val ∧ i.val < s + d) =
      Finset.Ico (i.val + 1 - d) (min (N + 1 - d) (i.val + 1)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]
    omega
  simp only [intervalVector_apply, Finset.sum_boole]
  rw [hset]
  simp

private theorem intervalGram_row_le (N d : ℕ) (hd : 1 ≤ d) (i : Fin N) :
    (intervalGram N d *ᵥ (1 : Fin N → ℝ)) i ≤ (d : ℝ) ^ 2 := by
  rw [intervalGram_row_exact N d hd i, pow_two]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  exact_mod_cast (show min (N + 1 - d) (i.val + 1) - (i.val + 1 - d) ≤ d by omega)

private theorem gram_row_le (N k : ℕ) (i : Fin N) :
    (gram N k *ᵥ (1 : Fin N → ℝ)) i ≤
      ∑ d ∈ Finset.range k, ((d : ℝ) + 1) ^ 2 := by
  simp only [gram, Matrix.sum_mulVec, Finset.sum_apply]
  apply Finset.sum_le_sum
  intro d hd
  simpa only [Nat.cast_add, Nat.cast_one] using intervalGram_row_le N (d + 1) (by omega) i

private theorem gram_entry_nonneg (N k : ℕ) (i j : Fin N) : 0 ≤ gram N k i j := by
  simp only [gram, intervalGram_sum, Matrix.sum_apply, Matrix.vecMulVec_apply]
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro s hs
  simp only [intervalVector_apply]
  split_ifs <;> norm_num

private theorem intervalGram_entry_prefix (N d : ℕ) (i j : Fin N)
    (hN : i.val + d ≤ N) :
    intervalGram N d i j = ∑ s ∈ Finset.range (i.val + 1),
      intervalVector N s d i * intervalVector N s d j := by
  simp only [intervalGram_sum, Matrix.sum_apply, Matrix.vecMulVec_apply]
  symm
  apply Finset.sum_subset
  · intro s hs
    simp only [Finset.mem_range] at hs ⊢
    omega
  · intro s hs hsi
    have hi : ¬ s ≤ i.val := by
      simp only [Finset.mem_range] at hsi
      omega
    simp [intervalVector_apply, hi]

private theorem intervalGram_entry_stable (N M d : ℕ) (i j : Fin N) (u v : Fin M)
    (hi : i.val = u.val) (hj : j.val = v.val)
    (hN : i.val + d ≤ N) (hM : u.val + d ≤ M) :
    intervalGram N d i j = intervalGram M d u v := by
  rw [intervalGram_entry_prefix N d i j hN, intervalGram_entry_prefix M d u v hM]
  simp only [intervalVector_apply, hi, hj]

private theorem gram_entry_stable (N M k : ℕ) (i j : Fin N) (u v : Fin M)
    (hi : i.val = u.val) (hj : j.val = v.val)
    (hN : i.val + k ≤ N) (hM : u.val + k ≤ M) :
    gram N k i j = gram M k u v := by
  simp only [gram, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Finset.mem_range.mp hd
  exact intervalGram_entry_stable N M (d + 1) i j u v hi hj (by omega) (by omega)

private theorem gram_band (N k : ℕ) (i j : Fin N) (h : k - 1 < Nat.dist i.val j.val) :
    gram N k i j = 0 := by
  simp only [gram, intervalGram_sum, Matrix.sum_apply, Matrix.vecMulVec_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro s hs
  have hdk := Finset.mem_range.mp hd
  simp only [intervalVector_apply]
  split_ifs with hi hj
  · simp only [Nat.dist] at h
    omega
  · simp
  · simp
  · simp

private theorem intervalVector_rev (N s d : ℕ) (_hd : 1 ≤ d) (hs : s + d ≤ N)
    (i : Fin N) : intervalVector N s d i.rev = intervalVector N (N - d - s) d i := by
  have hi := i.is_lt
  have heq : (s ≤ N - (i.val + 1) ∧ N - (i.val + 1) < s + d) ↔
      (N - d - s ≤ i.val ∧ i.val < N - d - s + d) := by omega
  simp only [intervalVector_apply, Fin.val_rev, heq]

private theorem intervalGram_rev (N d : ℕ) (hd : 1 ≤ d) (i j : Fin N) :
    intervalGram N d i.rev j.rev = intervalGram N d i j := by
  by_cases hdN : d ≤ N
  · simp only [intervalGram_sum, Matrix.sum_apply, Matrix.vecMulVec_apply]
    calc
      _ = ∑ s ∈ Finset.range (N + 1 - d),
          intervalVector N (N - d - s) d i * intervalVector N (N - d - s) d j := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsd : s + d ≤ N := by have := Finset.mem_range.mp hs; omega
        rw [intervalVector_rev N s d hd hsd i, intervalVector_rev N s d hd hsd j]
      _ = _ := by
        have hdim : N + 1 - d - 1 = N - d := by exact Nat.succ_sub_succ_eq_sub N d
        simpa only [hdim] using Finset.sum_range_reflect
          (fun s => intervalVector N s d i * intervalVector N s d j) (N + 1 - d)
  · have hz : N + 1 - d = 0 := by omega
    simp [intervalGram_sum, hz]

private theorem gram_rev (N k : ℕ) (i j : Fin N) :
    gram N k i.rev j.rev = gram N k i j := by
  simp only [gram, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  exact intervalGram_rev N (d + 1) (by omega) i j

private def boundaryVector (N k : ℕ) (i : Fin N) : ℝ :=
  ∑ d ∈ Finset.range k, ((d : ℝ) + 1) * (d - i.val : ℕ)

private theorem gram_defect (N k : ℕ) (hN : k ≤ N) (i : Fin N) :
    (∑ d ∈ Finset.range k, ((d : ℝ) + 1) ^ 2) -
      (gram N k *ᵥ (1 : Fin N → ℝ)) i =
      boundaryVector N k i + boundaryVector N k i.rev := by
  simp only [gram, Matrix.sum_mulVec, Finset.sum_apply, boundaryVector,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk := Finset.mem_range.mp hd
  rw [intervalGram_row_exact N (d + 1) (by omega) i]
  simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one, Fin.val_rev]
  have hc : min (N - d) (i.val + 1) - (i.val - d) +
      (d - i.val) + (d - (N - (i.val + 1))) = d + 1 := by
    have hi := i.is_lt
    omega
  have hc' : ((min (N - d) (i.val + 1) - (i.val - d) : ℕ) : ℝ) +
      (d - i.val : ℕ) + (d - (N - (i.val + 1)) : ℕ) = (d : ℝ) + 1 := by
    exact_mod_cast hc
  nlinarith

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

set_option backward.isDefEq.respectTransparency.types false

open Matrix

/-- Vertex i represents the source's vertex i + 1.  The Mathlib constructor
symmetrizes the relation and excludes loops, giving exactly 0 < |i-j| ≤ k. -/
def graph (n k : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j : Fin n => Nat.dist i.val j.val ≤ k)

/-- R t is the source's r_(G_(t+2,k))(1,t+2).  Unit conductances use the
Mathlib graph Laplacian.  Its product with V is the current-source vector:
+1 at the first vertex and -1 at the last, and zero at every other vertex. -/
noncomputable def IsResistanceSequence (k : ℕ) (R : ℕ → ℝ) : Prop := by
  classical
  exact ∀ t : ℕ, ∃ V : Fin (t + 2) → ℝ,
    (graph (t + 2) k).lapMatrix ℝ *ᵥ V =
      Pi.single 0 (1 : ℝ) - Pi.single (Fin.last (t + 1)) (1 : ℝ) ∧
    R t = V 0 - V (Fin.last (t + 1))

/-- Barrett–Evans–Francis, arXiv:1712.05883v1, Conjecture 44 in the
arXiv PDF; Evans–Francis, arXiv:2108.07942v2, Conjecture 4.5.
The finite shift t = n - 2 leaves the limit unchanged.  Existence is part
of the assertion because resistance is characterized by Kirchhoff's equation. -/
def claim : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∃ R : ℕ → ℝ, IsResistanceSequence k R) ∧
    ∀ R : ℕ → ℝ, IsResistanceSequence k R →
      Filter.Tendsto (fun t : ℕ => R (t + 1) - R t) Filter.atTop
        (nhds ((6 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))))

end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

open Matrix
open scoped BigOperators

noncomputable section

private theorem graph_adj_iff {n k : ℕ} (i j : Fin n) :
    (graph n k).Adj i j ↔ i ≠ j ∧ Nat.dist i.val j.val ≤ k := by
  simp only [graph, SimpleGraph.fromRel_adj, Nat.dist_comm j.val i.val, or_self]

private theorem graph_connected (n k : ℕ) (hk : 1 ≤ k) :
    (graph (n + 1) k).Connected := by
  apply (SimpleGraph.connected_pathGraph_add_one n).mono
  intro i j hij
  rw [graph_adj_iff]
  have h := SimpleGraph.pathGraph_adj.mp hij
  constructor
  · intro heq
    subst j
    omega
  · rcases h with h | h
    · have : Nat.dist i.val j.val = 1 := by
        simp only [Nat.dist]
        omega
      omega
    · have : Nat.dist i.val j.val = 1 := by
        simp only [Nat.dist]
        omega
      omega

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
private theorem sum_laplacian_mulVec (G : SimpleGraph α) [DecidableRel G.Adj]
    (x : α → ℝ) : ∑ i, (G.lapMatrix ℝ *ᵥ x) i = 0 := by
  have hs := G.isSymm_lapMatrix ℝ
  have hz := G.lapMatrix_mulVec_one_eq_zero ℝ
  have h : (1 : α → ℝ) ᵥ* G.lapMatrix ℝ = 0 := by
    rw [← Matrix.mulVec_transpose, hs.eq]
    exact hz
  have hdot := Matrix.dotProduct_mulVec (1 : α → ℝ) (G.lapMatrix ℝ) x
  simpa [h, dotProduct] using hdot

omit [DecidableEq α] [Nonempty α] in
private theorem ones_mulVec (x : α → ℝ) :
    (Matrix.of (fun (_ _ : α) => (1 : ℝ))) *ᵥ x = fun _ => ∑ i, x i := by
  ext a
  simpa [Matrix.replicateRow, Function.const, dotProduct] using
    congrFun (Matrix.replicateRow_mulVec_eq_const (ι := α) (fun _ : α => (1 : ℝ)) x) a

private theorem sum_of_augmented_equation (G : SimpleGraph α) [DecidableRel G.Adj]
    (x b : α → ℝ)
    (h : (G.lapMatrix ℝ + Matrix.of (fun (_ _ : α) => (1 : ℝ))) *ᵥ x = b)
    (hb : ∑ i, b i = 0) : ∑ i, x i = 0 := by
  rw [Matrix.add_mulVec, ones_mulVec] at h
  have hs := congrArg (fun v : α → ℝ => ∑ i, v i) h
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_laplacian_mulVec,
    zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hb] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

private theorem exists_unit_current_voltage (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (i j : α) :
    ∃ V : α → ℝ, G.lapMatrix ℝ *ᵥ V =
      Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ) := by
  let A : Matrix α α ℝ := G.lapMatrix ℝ + Matrix.of (fun (_ _ : α) => (1 : ℝ))
  have hu : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    apply (injective_iff_map_eq_zero (Matrix.mulVecLin A)).mpr
    intro x hx
    have hx' : A *ᵥ x = 0 := hx
    have hsum := sum_of_augmented_equation G x 0 hx' (by simp)
    have hL : G.lapMatrix ℝ *ᵥ x = 0 := by
      simpa only [A, Matrix.add_mulVec, ones_mulVec, hsum,
        show (fun _ : α => (0 : ℝ)) = 0 from rfl, add_zero] using hx'
    have hc := (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable).mp hL
    let i₀ : α := Classical.choice inferInstance
    have hx0 : x i₀ = 0 := by
      have heq : x = fun _ => x i₀ := funext fun a => hc a i₀ (hG a i₀)
      rw [heq] at hsum
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, false_or] using hsum
    funext a
    exact (hc a i₀ (hG a i₀)).trans hx0
  let b : α → ℝ := Pi.single i 1 - Pi.single j 1
  let V := A⁻¹ *ᵥ b
  have hAV : A *ᵥ V = b := by
    dsimp [V]
    rw [Matrix.mulVec_mulVec, A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hu),
      Matrix.one_mulVec]
  have hb : ∑ a, b a = 0 := by simp [b, Finset.sum_sub_distrib]
  have hsum := sum_of_augmented_equation G V b hAV hb
  refine ⟨V, ?_⟩
  simpa only [A, Matrix.add_mulVec, ones_mulVec, hsum,
        show (fun _ : α => (0 : ℝ)) = 0 from rfl, add_zero] using hAV

private theorem exists_resistance_sequence (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ → ℝ, IsResistanceSequence k R := by
  classical
  have hv : ∀ t : ℕ, ∃ V : Fin (t + 2) → ℝ,
      (graph (t + 2) k).lapMatrix ℝ *ᵥ V =
        Pi.single 0 (1 : ℝ) - Pi.single (Fin.last (t + 1)) (1 : ℝ) := by
    intro t
    exact exists_unit_current_voltage (graph (t + 2) k)
      (graph_connected (t + 1) k hk) 0 (Fin.last (t + 1))
  choose V hV using hv
  refine ⟨fun t => V t 0 - V t (Fin.last (t + 1)), ?_⟩
  intro t
  exact ⟨V t, hV t, rfl⟩

private theorem fwdDiff_fin (N : ℕ) (V : Fin (N + 1) → ℝ) (i : Fin N) :
    -fwdDiff (1 : Fin (N + 1)) V i.castSucc = V i.castSucc - V i.succ := by
  have hi : i.castSucc + (1 : Fin (N + 1)) = i.succ := Fin.coeSucc_eq_succ
  simp only [fwdDiff, hi, neg_sub]

private theorem stepMatrix_integrates {N : ℕ} (V : Fin (N + 1) → ℝ) :
    (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) *ᵥ (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) = V - V (Fin.last N) • 1 := by
  let v : ℕ → ℝ := fun i => if hi : i < N + 1 then V ⟨i, hi⟩ else 0
  have hv (i : Fin (N + 1)) : v i.val = V i := by
    dsimp only [v]
    rw [dite_eq_left i.is_lt]
  have hd (i : Fin N) : (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) i = v i.val - v (i.val + 1) := by
    change -fwdDiff (1 : Fin (N + 1)) V i.castSucc = _
    rw [fwdDiff_fin]
    change V i.castSucc - V i.succ = v i.castSucc.val - v i.succ.val
    rw [hv i.castSucc, hv i.succ]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, IncidenceAlgebra.zeta_apply, Fin.le_iff_val_le_val, Fin.val_castSucc]
  change (∑ j : Fin N, (if i.val ≤ j.val then (1 : ℝ) else 0) *
    (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) j) = V i - V (Fin.last N)
  simp_rw [hd, ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if i.val ≤ j then v j - v (j + 1) else 0) N]
  rw [← Finset.sum_filter]
  have hset : (Finset.range N).filter (fun j => i.val ≤ j) = Finset.Ico i.val N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sub _ (by have := i.is_lt; omega)]
  rw [Finset.sum_range_sub', Finset.sum_range_sub']
  have hlast : v N = V (Fin.last N) := hv (Fin.last N)
  rw [hv i, hlast]
  ring

private theorem stepMatrix_current {N : ℕ} :
    ((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ *ᵥ
      (Pi.single (0 : Fin (N + 1)) (1 : ℝ) - Pi.single (Fin.last N) 1) = 1 := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  ext i
  change (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) 0 i - (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) (Fin.last N) i = 1
  simp [Matrix.of_apply, IncidenceAlgebra.zeta_apply, Fin.le_iff_val_le_val, Fin.val_castSucc, Nat.not_le.mpr i.is_lt]

private theorem electrical_coordinates {N k : ℕ}
    (V : Fin (N + 1) → ℝ)
    (hV : (graph (N + 1) k).lapMatrix ℝ *ᵥ V =
      Pi.single 0 (1 : ℝ) - Pi.single (Fin.last N) 1) :
    (((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ * (graph (N + 1) k).lapMatrix ℝ * (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc)) *ᵥ
      (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) = 1 := by
  classical
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, stepMatrix_integrates,
    Matrix.mulVec_sub, Matrix.mulVec_smul,
    (graph (N + 1) k).lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, sub_zero, hV,
    stepMatrix_current]

private theorem electrical_inverse_identification {N k : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : IsUnit Q)
    (hQeq : Q = ((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ * (graph (N + 1) k).lapMatrix ℝ * (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))
    (V : Fin (N + 1) → ℝ)
    (hV : (graph (N + 1) k).lapMatrix ℝ *ᵥ V =
      Pi.single 0 (1 : ℝ) - Pi.single (Fin.last N) 1) :
    V 0 - V (Fin.last N) = (1 : Fin N → ℝ) ⬝ᵥ (Q⁻¹ *ᵥ 1) := by
  classical
  have hx : Q *ᵥ (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) = 1 := by
    rw [hQeq]
    exact electrical_coordinates V hV
  have hdiff : (fun i : Fin N => -fwdDiff (1 : Fin (N + 1)) V i.castSucc) = Q⁻¹ *ᵥ 1 := by
    rw [← hx, Matrix.mulVec_mulVec,
      Q.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det Q).mp hQ), Matrix.one_mulVec]
  have hfirst := congrFun (stepMatrix_integrates V) 0
  simp only [Matrix.of_apply, IncidenceAlgebra.zeta_apply, Fin.le_iff_val_le_val, Fin.val_castSucc, Matrix.mulVec, dotProduct, Fin.val_zero, Nat.zero_le,
    ite_eq_left, one_mul, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
    mul_one] at hfirst
  rw [← hdiff]
  simpa only [dotProduct, Pi.one_apply, one_mul] using hfirst.symm

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
open Matrix Finset
open scoped BigOperators
noncomputable section

private theorem intervalGram_entry_extended (N d : ℕ) (i j : Fin N) (hij : i.val ≤ j.val) :
    intervalGram N (d + 1) i j = ∑ s ∈ Finset.range N,
      if s + d + 1 ≤ N ∧ s ≤ i.val ∧ j.val < s + d + 1 then (1 : ℝ) else 0 := by
  have hset : (Finset.range N).filter (fun s => s + d + 1 ≤ N) =
      Finset.range (N - d) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [intervalGram_sum, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Nat.add_sub_add_right]
  rw [← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [intervalVector_apply]
  split_ifs <;> simp_all <;> omega

private theorem gram_entry_formula (N k : ℕ) (i j : Fin N) (hij : i.val ≤ j.val) :
    gram N k i j = ∑ s ∈ Finset.range (i.val + 1),
      ((min N (s + k) - j.val : ℕ) : ℝ) := by
  simp only [gram, Matrix.sum_apply]
  simp_rw [intervalGram_entry_extended N _ i j hij]
  rw [Finset.sum_comm]
  have hp : i.val + 1 ≤ N := i.is_lt
  rw [← Finset.sum_subset (Finset.range_mono hp) (by
    intro s hs hsi
    apply Finset.sum_eq_zero
    intro d hd
    have hs' : i.val < s := by simp only [Finset.mem_range] at hsi; omega
    rw [ite_eq_right (by omega)])]
  apply Finset.sum_congr rfl
  intro s hs
  have hsi := Finset.mem_range.mp hs
  have hset : (Finset.range k).filter
      (fun d => s + d + 1 ≤ N ∧ s ≤ i.val ∧ j.val < s + d + 1) =
      Finset.Ico (j.val - s) (min k (N - s)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]
    have hj := j.is_lt
    omega
  rw [Finset.sum_boole, hset, Nat.card_Ico]
  congr 1
  have hj := j.is_lt
  omega

private theorem lap_step_left (N k : ℕ) (j : Fin N) (v : Fin (N + 1)) (hv : v.val ≤ j.val) :
    ((graph (N + 1) k).lapMatrix ℝ *ᵥ (fun u => (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) u j)) v =
      ((min N (v.val + k) - j.val : ℕ) : ℝ) := by
  classical
  rw [SimpleGraph.lapMatrix_mulVec_apply']
  have hnei : (graph (N + 1) k).neighborFinset v =
      Finset.univ.filter (fun u => (graph (N + 1) k).Adj v u) := by exact SimpleGraph.neighborFinset_eq_filter (graph (N + 1) k)
  rw [hnei, Finset.sum_filter]
  have hterm (u : Fin (N + 1)) :
      (if (graph (N + 1) k).Adj v u then (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) v j - (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) u j else 0) =
        if j.val < u.val ∧ u.val ≤ v.val + k then (1 : ℝ) else 0 := by
    simp only [graph_adj_iff, Matrix.of_apply, IncidenceAlgebra.zeta_apply, Fin.le_iff_val_le_val, Fin.val_castSucc, ite_eq_left hv]
    by_cases hu : u.val ≤ j.val
    · simp [hu, show ¬ j.val < u.val by omega]
    · have hvu : v ≠ u := by intro he; subst u; omega
      have hd : Nat.dist v.val u.val ≤ k ↔ u.val ≤ v.val + k := by
        simp only [Nat.dist]
        omega
      simp [hu, hvu, hd, show j.val < u.val by omega]
  simp_rw [hterm]
  change (∑ u : Fin (N + 1),
    (fun m : ℕ => if j.val < m ∧ m ≤ v.val + k then (1 : ℝ) else 0) u.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
    if j.val < m ∧ m ≤ v.val + k then (1 : ℝ) else 0) (N + 1), Finset.sum_boole]
  have hset : (Finset.range (N + 1)).filter (fun m => j.val < m ∧ m ≤ v.val + k) =
      Finset.Ioc j.val (min N (v.val + k)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, le_min_iff]
    omega
  rw [hset, Nat.card_Ioc]

private theorem cutGram_entry_formula (N k : ℕ) (i j : Fin N) (hij : i.val ≤ j.val) :
    (((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ * (graph (N + 1) k).lapMatrix ℝ * (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc)) i j =
      ∑ s ∈ Finset.range (i.val + 1), ((min N (s + k) - j.val : ℕ) : ℝ) := by
  classical
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  change (∑ v : Fin (N + 1), (if v.val ≤ i.val then (1 : ℝ) else 0) *
    ((graph (N + 1) k).lapMatrix ℝ *ᵥ (fun u => (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) u j)) v) = _
  have ht (v : Fin (N + 1)) :
      (if v.val ≤ i.val then (1 : ℝ) else 0) *
        ((graph (N + 1) k).lapMatrix ℝ *ᵥ (fun u => (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) u j)) v =
      if v.val ≤ i.val then ((min N (v.val + k) - j.val : ℕ) : ℝ) else 0 := by
    by_cases hv : v.val ≤ i.val
    · rw [ite_eq_left hv, one_mul, ite_eq_left hv, lap_step_left N k j v (by omega)]
    · simp [hv]
  simp_rw [ht]
  change (∑ v : Fin (N + 1), (fun s : ℕ =>
    if s ≤ i.val then ((min N (s + k) - j.val : ℕ) : ℝ) else 0) v.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ =>
    if s ≤ i.val then ((min N (s + k) - j.val : ℕ) : ℝ) else 0) (N + 1),
    ← Finset.sum_filter]
  have hset : (Finset.range (N + 1)).filter (fun s => s ≤ i.val) =
      Finset.range (i.val + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    have hi := i.is_lt
    omega
  rw [hset]

private theorem gram_eq_cutGram (N k : ℕ) : gram N k =
    ((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ * (graph (N + 1) k).lapMatrix ℝ * (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc) := by
  classical
  have hg : (gram N k).IsSymm := (by
    unfold gram
    exact (Matrix.posSemidef_sum (Finset.range k) (fun d hd =>
      intervalGram_posSemidef N (d + 1))).1 : (gram N k).IsHermitian).isSymm
  have hl : (((Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc))ᵀ * (graph (N + 1) k).lapMatrix ℝ * (Matrix.of fun (v : Fin (N + 1)) (i : Fin N) => IncidenceAlgebra.zeta ℝ v i.castSucc)).IsSymm := by
    rw [Matrix.IsSymm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      ((graph (N + 1) k).isSymm_lapMatrix ℝ).eq, Matrix.mul_assoc]
  ext i j
  by_cases hij : i.val ≤ j.val
  · rw [gram_entry_formula N k i j hij, cutGram_entry_formula N k i j hij]
  · rw [← hg.apply i j, ← hl.apply i j]
    rw [gram_entry_formula N k j i (by omega), cutGram_entry_formula N k j i (by omega)]

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
open Matrix Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem exists_limit_of_stabilizing_approximants
    (s : ℕ → ℝ) (p : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (herr : ∀ L, ∀ᶠ n in atTop, |s n - p L n| ≤ e L)
    (hstab : ∀ L, ∃ a : ℝ, ∀ᶠ n in atTop, p L n = a) :
    ∃ a : ℝ, Tendsto s atTop (𝓝 a) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨L, hL⟩ := (he.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨a, ha⟩ := hstab L
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((herr L).and ha)
  refine ⟨N, ?_⟩
  intro n hn m hm
  obtain ⟨hen, hpn⟩ := hN n hn
  obtain ⟨hem, hpm⟩ := hN m hm
  rw [hpn] at hen
  rw [hpm] at hem
  rw [Real.dist_eq]
  calc
    |s n - s m| = |(s n - a) + (a - s m)| := by congr 1; ring
    _ ≤ |s n - a| + |a - s m| := abs_add_le _ _
    _ = |s n - a| + |s m - a| := by rw [abs_sub_comm a (s m)]
    _ ≤ e L + e L := add_le_add hen hem
    _ < ε := by linarith

private theorem inverse_polynomial_identity (Q : Matrix ι ι ℝ) (hQ : IsUnit Q)
    (D : ℝ) (L : ℕ) :
    Q⁻¹ = D⁻¹ • (∑ l ∈ Finset.range L, (1 - D⁻¹ • Q) ^ l) +
      (1 - D⁻¹ • Q) ^ L * Q⁻¹ := by
  have hmul : Q * Q⁻¹ = 1 :=
    Q.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  have hgeom := geom_sum_mul_neg (1 - D⁻¹ • Q) L
  have h := congrArg (fun M : Matrix ι ι ℝ => M * Q⁻¹) hgeom
  simp only [sub_sub_cancel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    hmul, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul] at h
  exact sub_eq_iff_eq_add.mp h.symm

private theorem inverse_polynomial_error [Nonempty ι] (Q : Matrix ι ι ℝ) (hQ : IsUnit Q)
    (D ρ : ℝ) (hρ : 0 ≤ ρ) (hA : ‖(1 : Matrix ι ι ℝ) - D⁻¹ • Q‖ ≤ ρ)
    (hinv : ‖Q⁻¹‖ ≤ 1) (L : ℕ) :
    ‖Q⁻¹ - D⁻¹ • (∑ l ∈ Finset.range L, (1 - D⁻¹ • Q) ^ l)‖ ≤ ρ ^ L := by
  rw [inverse_polynomial_identity Q hQ D L, add_sub_cancel_left]
  calc
    _ ≤ ‖(1 - D⁻¹ • Q) ^ L‖ * ‖Q⁻¹‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ρ ^ L * 1 := by
      gcongr
      exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hA L)
    _ = _ := mul_one _

private theorem quadratic_operator_bound (E : Matrix ι ι ℝ) (c : ι → ℝ) :
    |c ⬝ᵥ (E *ᵥ c)| ≤ ‖WithLp.toLp 2 c‖ ^ 2 * ‖E‖ := by
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 c
  have hinner : c ⬝ᵥ (E *ᵥ c) =
      inner ℝ x ((EuclideanSpace.equiv ι ℝ).symm (E *ᵥ c)) := by
    simp [x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hinner]
  calc
    _ ≤ ‖x‖ * ‖(EuclideanSpace.equiv ι ℝ).symm (E *ᵥ c)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖E‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (E.l2_opNorm_mulVec x) (norm_nonneg _)
    _ = _ := by dsimp [x]; ring

private theorem correction_converges_of_stable_moments
    (Q : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ)
    (c : (N : ℕ) → Fin N → ℝ) (D ρ C : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hC0 : 0 ≤ C) (hC : ∀ᶠ N in atTop, ‖WithLp.toLp 2 (c N)‖ ^ 2 ≤ C)
    (hu : ∀ N, IsUnit (Q N))
    (hA : ∀ N, ‖(1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • Q N‖ ≤ ρ)
    (hinv : ∀ N, ‖(Q N)⁻¹‖ ≤ 1)
    (hmom : ∀ L : ℕ, ∃ a : ℝ, ∀ᶠ N in atTop,
      c N ⬝ᵥ (((1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • Q N) ^ L *ᵥ c N) = a) :
    ∃ a : ℝ, Tendsto (fun N => c N ⬝ᵥ ((Q N)⁻¹ *ᵥ c N)) atTop (𝓝 a) := by
  let A := fun N => (1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • Q N
  let P := fun L N => D⁻¹ • (∑ l ∈ Finset.range L, A N ^ l)
  let s := fun N => c N ⬝ᵥ ((Q N)⁻¹ *ᵥ c N)
  let p := fun L N => c N ⬝ᵥ (P L N *ᵥ c N)
  apply exists_limit_of_stabilizing_approximants s p (fun L => C * ρ ^ L)
  · simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
  · intro L
    filter_upwards [hC, eventually_ge_atTop 1] with N hCN hN
    let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    have he := inverse_polynomial_error (Q N) (hu N) D ρ hρ0 (hA N) (hinv N) L
    have hdiff : s N - p L N = c N ⬝ᵥ (((Q N)⁻¹ - P L N) *ᵥ c N) := by
      simp only [s, p, Matrix.sub_mulVec, dotProduct_sub]
    rw [hdiff]
    calc
      _ ≤ ‖WithLp.toLp 2 (c N)‖ ^ 2 * ‖(Q N)⁻¹ - P L N‖ :=
        quadratic_operator_bound _ _
      _ ≤ C * ρ ^ L := by
        have he' : ‖(Q N)⁻¹ - P L N‖ ≤ ρ ^ L := he
        exact mul_le_mul hCN he' (norm_nonneg _) hC0
  · intro L
    induction L with
    | zero =>
      refine ⟨0, Filter.Eventually.of_forall fun N => ?_⟩
      simp [p, P]
    | succ L ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hmom L
      refine ⟨a + D⁻¹ * b, ?_⟩
      filter_upwards [ha, hb] with N haN hbN
      change c N ⬝ᵥ ((D⁻¹ • (∑ l ∈ Finset.range (L + 1), A N ^ l)) *ᵥ c N) = _
      rw [Finset.sum_range_succ, smul_add, Matrix.add_mulVec, dotProduct_add]
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp only [p, P, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at haN
      change c N ⬝ᵥ (A N ^ L *ᵥ c N) = b at hbN
      rw [haN, hbN]

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance

set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
open Matrix Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.L2Operator
noncomputable section

theorem result : D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance.claim := by
  classical
  intro k hk
  refine ⟨exists_resistance_sequence k hk, ?_⟩
  intro R hR
  let D : ℝ := ∑ d ∈ Finset.range k, ((d : ℝ) + 1) ^ 2
  have hD : 1 ≤ D := by
    have ht := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ) + 1) ^ 2)
      (fun d hd => sq_nonneg ((d : ℝ) + 1))
      (show 0 ∈ Finset.range k from Finset.mem_range.mpr (by omega))
    simpa only [Nat.cast_zero, zero_add, one_pow] using ht
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hHerm (N : ℕ) : (gram N k).IsHermitian := by
    apply (Matrix.posSemidef_sum (Finset.range k) (fun d hd =>
      intervalGram_posSemidef N (d + 1))).1
  have hcontrol (N : ℕ) : IsUnit (gram N k) ∧ ‖(gram N k)⁻¹‖ ≤ 1 := by
    simpa only [one_smul, inv_one] using
      D5.S3.Observer.BlockStructure.UniformResolventRemainder.inverse_control_of_lower_bound
        (gram N k) (hHerm N) zero_lt_one (by simpa using gram_lower N k hk)
  have hhi (N : ℕ) : gram N k ≤ D • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    apply nonnegative_row_bound (gram N k) (hHerm N) (gram_entry_nonneg N k) D
    intro i
    simpa only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] using gram_row_le N k i
  let A := fun N => (1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • gram N k
  let r := k - 1
  let f : ℕ → ℝ := fun i => ∑ d ∈ Finset.range k, ((d : ℝ) + 1) * (d - i : ℕ)
  let c := fun N (i : Fin N) => f i.val + f i.rev.val
  have hf : ∀ i, r ≤ i → f i = 0 := by
    intro i hi
    apply Finset.sum_eq_zero
    intro d hd
    have hdk := Finset.mem_range.mp hd
    have hd0 : d - i = 0 := by dsimp [r] at hi; omega
    simp only [hd0, Nat.cast_zero, mul_zero]
  have hband (N : ℕ) : IsBanded r (A N) := by
    intro i j hij
    have hne : i ≠ j := by
      intro he; subst j
      simp at hij
    simp only [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hne, gram_band N k i j hij, mul_zero, sub_self]
  have hrev (N : ℕ) : IsReversalInvariant (A N) := by
    intro i j
    simp only [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Fin.rev_inj, gram_rev]
  have hcoeff : ∀ (N M : ℕ) (i j : Fin N) (u v : Fin M),
      i.val = u.val → j.val = v.val → i.val + k ≤ N → u.val + k ≤ M →
        A N i j = A M u v := by
    intro N M i j u v hi hj hN hM
    have heq : (i = j) ↔ (u = v) := by simp only [Fin.ext_iff, hi, hj]
    simp only [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      heq, gram_entry_stable N M k i j u v hi hj hN hM]
  let C : ℝ := 4 * ∑ i : Fin r, f i.val ^ 2
  let ρ : ℝ := 1 - D⁻¹
  have hρ0 : 0 ≤ ρ := by
    have := (inv_le_one₀ hDp).mpr hD
    dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [inv_pos.mpr hDp]
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : ∀ᶠ N in atTop, ‖WithLp.toLp 2 (c N)‖ ^ 2 ≤ C := by
    filter_upwards [eventually_ge_atTop r] with N hN
    exact boundary_norm_bound r N hN f hf
  have hAnorm (N : ℕ) : ‖(1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • gram N k‖ ≤ ρ :=
    richardson_norm_bound (gram N k) D hD (gram_lower N k hk) (hhi N)
  have hmom (L : ℕ) : ∃ a : ℝ, ∀ᶠ N in atTop,
      c N ⬝ᵥ (((1 : Matrix (Fin N) (Fin N) ℝ) - D⁻¹ • gram N k) ^ L *ᵥ c N) = a :=
    boundary_moments_stabilize A r r k f hf hband hrev hcoeff L
  obtain ⟨S, hS⟩ := correction_converges_of_stable_moments
    (fun N => gram N k) c D ρ C hρ0 hρ1 hC0 hC
    (fun N => (hcontrol N).1) hAnorm (fun N => (hcontrol N).2) hmom
  let s := fun N => c N ⬝ᵥ ((gram N k)⁻¹ *ᵥ c N)
  change Tendsto s atTop (𝓝 S) at hS
  let B : ℝ := 2 * ∑ i : Fin r, f i.val
  let corr : ℕ → ℝ := fun t => D⁻¹ + (B + s (t + 1)) / D ^ 2
  have hcorr : Tendsto corr atTop (𝓝 (D⁻¹ + (B + S) / D ^ 2)) := by
    exact tendsto_const_nhds.add
      ((tendsto_const_nhds.add (hS.comp (tendsto_add_atTop_nat 1))).div_const (D ^ 2))
  have hdef (N : ℕ) (hN : k ≤ N) :
      D • (1 : Fin N → ℝ) - gram N k *ᵥ 1 = c N := by
    ext i
    simpa only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      D, c, f, boundaryVector] using gram_defect N k hN i
  have hAffine : ∀ᶠ t in atTop, R t = (t : ℝ) * D⁻¹ + corr t := by
    apply eventually_atTop.mpr
    refine ⟨k + r, fun t ht => ?_⟩
    obtain ⟨V, hV, hRt⟩ := hR t
    have hRval : R t = (1 : Fin (t + 1) → ℝ) ⬝ᵥ ((gram (t + 1) k)⁻¹ *ᵥ 1) :=
      hRt.trans (electrical_inverse_identification (gram (t + 1) k)
        (hcontrol (t + 1)).1 (gram_eq_cutGram (t + 1) k) V hV)
    have hexp := inverse_defect_expansion (gram (t + 1) k) (hHerm (t + 1)).isSymm
      (hcontrol (t + 1)).1 (1 : Fin (t + 1) → ℝ) D hDp.ne'
    simp only [hdef (t + 1) (by omega)] at hexp
    have hone : (1 : Fin (t + 1) → ℝ) ⬝ᵥ 1 = ((t + 1 : ℕ) : ℝ) := by simp [dotProduct]
    have hcSum : (1 : Fin (t + 1) → ℝ) ⬝ᵥ c (t + 1) = B := by
      simpa only [dotProduct, Pi.one_apply, one_mul] using
        boundary_sum_constant r (t + 1) (by omega) f hf
    rw [hone, hcSum] at hexp
    rw [hRval, hexp]
    change ((t + 1 : ℕ) : ℝ) / D + (B + s (t + 1)) / D ^ 2 =
      (t : ℝ) * D⁻¹ + (D⁻¹ + (B + s (t + 1)) / D ^ 2)
    push_cast
    ring
  have hInc := increment_limit_of_affine_correction R corr D⁻¹
    (D⁻¹ + (B + S) / D ^ 2) hcorr hAffine
  have hsq : 6 * D = (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) := by
    have hsum := sum_Ico_pow k 2
    norm_num [Finset.sum_range_succ] at hsum
    have hreal := congrArg (fun x : ℚ => (x : ℝ)) hsum
    push_cast at hreal
    have hDsum : D = ∑ j ∈ Finset.Ico 1 (k + 1), (j : ℝ) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, D, add_comm (1 : ℝ)]
    rw [← hDsum] at hreal
    nlinarith
  have hconst : D⁻¹ = (6 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1)) := by
    rw [← hsq]
    field_simp [hDp.ne']
  simpa only [hconst] using hInc

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeResistance
