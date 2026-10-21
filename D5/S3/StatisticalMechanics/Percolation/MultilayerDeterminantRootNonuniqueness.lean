/- GID: D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.claim; result=D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result; claim=D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.claim
   digest: Three zeros refute the multilayer percolation determinant uniqueness conjecture. -/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The matrix and excess-degree ratio are those of Guha, Towsley, Nain, Çapar, Swami and Basu,
"Spanning connectivity in a multilayer network and its relationship to site-bond percolation",
arXiv:1402.7057v4, equation (3). Their conjecture following equation (5) asserts uniqueness
of the determinant's zero in `[0, 1]` when the excess-degree ratio exceeds one.

For three layers and degree identically 65, the determinant takes the values
`1, -36, 281, -63` at `0, 1/4, 1/2, 1`. Continuity gives three distinct interior zeros.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Percolation.MultilayerDeterminantRootNonuniqueness

/-- The source indices `1, …, M` are represented by `Fin M` with one added to each value.
`Nat.choose` is zero when its lower argument exceeds its upper argument. -/
noncomputable def multilayerMatrix (M : ℕ) (C q : ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j =>
    if i = j then
      1 - C * ((M.choose (j.val + 1) : ℝ) -
        ((M - (j.val + 1)).choose (j.val + 1) : ℝ)) *
        q ^ (j.val + 1) * (1 - q) ^ (M - (j.val + 1))
    else
      -C * ((M.choose (j.val + 1) : ℝ) -
        ((M - (i.val + 1)).choose (j.val + 1) : ℝ)) *
        q ^ (j.val + 1) * (1 - q) ^ (M - (j.val + 1))

/-- A finitely supported probability distribution on the nonnegative integer degrees. -/
def IsDegreeDistribution (p : ℕ →₀ ℝ) : Prop :=
  (∀ k, 0 ≤ p k) ∧ p.sum (fun _ pk => pk) = 1

/-- The mean degree `z = ∑ k, k pₖ`. -/
noncomputable def meanDegree (p : ℕ →₀ ℝ) : ℝ :=
  p.sum (fun k pk => (k : ℝ) * pk)

/-- The excess-degree ratio `C = (∑ k, (k - 1) k pₖ) / z`. -/
noncomputable def excessRatio (p : ℕ →₀ ℝ) : ℝ :=
  p.sum (fun k pk => ((k : ℝ) - 1) * (k : ℝ) * pk) / meanDegree p

/-- The uniqueness conjecture for finitely supported degree distributions. -/
def claim : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ p : ℕ →₀ ℝ, IsDegreeDistribution p →
    0 < meanDegree p → 1 < excessRatio p →
      ∃! q : ℝ, q ∈ Set.Icc 0 1 ∧ (multilayerMatrix M (excessRatio p) q).det = 0

private theorem determinant_samples :
    (multilayerMatrix 3 64 0).det = 1 ∧
    (multilayerMatrix 3 64 (1 / 4)).det = -36 ∧
    (multilayerMatrix 3 64 (1 / 2)).det = 281 ∧
    (multilayerMatrix 3 64 1).det = -63 := by
  norm_num [Matrix.det_fin_three, multilayerMatrix, Nat.choose]

private theorem determinant_continuous (M : ℕ) (C : ℝ) :
    Continuous (fun q : ℝ => (multilayerMatrix M C q).det) := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  unfold multilayerMatrix
  exact Continuous.if_const (i = j)
    (continuous_const.sub ((continuous_const.mul (continuous_id.pow _)).mul
      ((continuous_const.sub continuous_id).pow _)))
    ((continuous_const.mul (continuous_id.pow _)).mul
      ((continuous_const.sub continuous_id).pow _))

private theorem determinant_three_roots :
    ∃ x y z : ℝ,
      x ∈ Set.Ioo 0 (1 / 4) ∧ y ∈ Set.Ioo (1 / 4) (1 / 2) ∧
      z ∈ Set.Ioo (1 / 2) 1 ∧
      (multilayerMatrix 3 64 x).det = 0 ∧
      (multilayerMatrix 3 64 y).det = 0 ∧
      (multilayerMatrix 3 64 z).det = 0 := by
  obtain ⟨h0, hquarter, hhalf, h1⟩ := determinant_samples
  have hc := determinant_continuous 3 64
  obtain ⟨x, hx, hxzero⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Icc (multilayerMatrix 3 64 (1 / 4)).det
      (multilayerMatrix 3 64 0).det from ⟨by rw [hquarter]; norm_num, by rw [h0]; norm_num⟩)
  obtain ⟨y, hy, hyzero⟩ := intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Icc (multilayerMatrix 3 64 (1 / 4)).det
      (multilayerMatrix 3 64 (1 / 2)).det from
        ⟨by rw [hquarter]; norm_num, by rw [hhalf]; norm_num⟩)
  obtain ⟨z, hz, hzzero⟩ := intermediate_value_Icc' (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Icc (multilayerMatrix 3 64 1).det
      (multilayerMatrix 3 64 (1 / 2)).det from
        ⟨by rw [h1]; norm_num, by rw [hhalf]; norm_num⟩)
  change (multilayerMatrix 3 64 x).det = 0 at hxzero
  change (multilayerMatrix 3 64 y).det = 0 at hyzero
  change (multilayerMatrix 3 64 z).det = 0 at hzzero
  have hx0 : x ≠ 0 := by intro h; rw [h, h0] at hxzero; norm_num at hxzero
  have hxquarter : x ≠ 1 / 4 := by
    intro h; rw [h, hquarter] at hxzero; norm_num at hxzero
  have hyquarter : y ≠ 1 / 4 := by
    intro h; rw [h, hquarter] at hyzero; norm_num at hyzero
  have hyhalf : y ≠ 1 / 2 := by intro h; rw [h, hhalf] at hyzero; norm_num at hyzero
  have hzhalf : z ≠ 1 / 2 := by intro h; rw [h, hhalf] at hzzero; norm_num at hzzero
  have hz1 : z ≠ 1 := by intro h; rw [h, h1] at hzzero; norm_num at hzzero
  exact ⟨x, y, z, ⟨lt_of_le_of_ne hx.1 hx0.symm, lt_of_le_of_ne hx.2 hxquarter⟩,
    ⟨lt_of_le_of_ne hy.1 hyquarter.symm, lt_of_le_of_ne hy.2 hyhalf⟩,
    ⟨lt_of_le_of_ne hz.1 hzhalf.symm, lt_of_le_of_ne hz.2 hz1⟩,
    hxzero, hyzero, hzzero⟩

theorem result : ¬ claim := by
  intro h
  let p : ℕ →₀ ℝ := Finsupp.single 65 1
  have hp : IsDegreeDistribution p := by
    constructor
    · intro k
      dsimp [p]
      rw [Finsupp.single_apply]
      split_ifs <;> norm_num
    · norm_num [p, Finsupp.sum_single_index]
  have hz : meanDegree p = 65 := by
    norm_num [meanDegree, p, Finsupp.sum_single_index]
  have hC : excessRatio p = 64 := by
    norm_num [excessRatio, meanDegree, p, Finsupp.sum_single_index]
  obtain ⟨r, hr, hu⟩ := h 3 (by norm_num) p hp
    (by rw [hz]; norm_num) (by rw [hC]; norm_num)
  obtain ⟨x, y, z, hx, hy, hzroot, hxzero, hyzero, hzzero⟩ := determinant_three_roots
  have hxr : x = r := hu x ⟨⟨hx.1.le, by linarith [hx.2]⟩, by rw [hC]; exact hxzero⟩
  have hzr : z = r := hu z ⟨⟨by linarith [hzroot.1], hzroot.2.le⟩,
    by rw [hC]; exact hzzero⟩
  have hxy : x < y := lt_trans hx.2 hy.1
  have hyz : y < z := lt_trans hy.2 hzroot.1
  linarith

end D5.S3.StatisticalMechanics.Percolation.MultilayerDeterminantRootNonuniqueness
