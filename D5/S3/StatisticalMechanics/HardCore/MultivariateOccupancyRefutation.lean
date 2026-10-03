/- GID: D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.claim; result=D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result; claim=D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.claim
   digest: The three-vertex star at fugacities (15,2,2) refutes the occupancy bound. -/

/-
proof_shape: result: bind-only (finite independent-set and degree computation,
  followed by exact rational normalization)
escape_witness: none
admission_basis: open-problem-resolution (#12413; Refuted)
Direct frozen dependencies:
  D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations
  D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition
  statement_id: sha256:8014b9cde4f69ed8e5049e30e505073622cbf5d96e9707ac8cda86d3aa47ff93
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.StatisticalMechanics.HardCore.MultivariateOccupancyRefutation

/-- Expected cardinality for the hard-core measure: the weighted cardinality
sum over actual independent subsets divided by the multivariate partition. -/
noncomputable def expectedSize {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lam : Fin n → ℝ) : ℝ :=
  (∑ S ∈ configurations G Finset.univ, (S.card : ℝ) * ∏ v ∈ S, lam v) /
    partition G Finset.univ lam

/-- The proposed degree-sequence occupancy bound for every finite simple graph
and every strictly positive vertex fugacity vector. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : Fin n → ℝ),
    (∀ v, 0 < lam v) →
      (∑ v, lam v / (1 + (G.degree v + 1) * lam v)) ≤ expectedSize G lam

/-- On the star centered at zero with fugacities (15,2,2), the expectation is
9/8 while the proposed lower bound is 259/230, exceeding it by 1/920. -/
theorem result : ¬ claim := by
  intro h
  let G := SimpleGraph.starGraph (0 : Fin 3)
  let lam : Fin 3 → ℝ := fun v => if v = 0 then 15 else 2
  have hpos : ∀ v, 0 < lam v := by
    intro v
    simp only [lam]
    split_ifs <;> norm_num
  have hc := h 3 G lam hpos
  have hconfig : configurations G Finset.univ =
      ({∅, {0}, {1}, {2}, {1, 2}} : Finset (Finset (Fin 3))) := by
    decide
  have hd0 : G.degree 0 = 2 := by decide
  have hd1 : G.degree 1 = 1 := by decide
  have hd2 : G.degree 2 = 1 := by decide
  have hn10 : (1 : Fin 3) ≠ 0 := by decide
  have hn20 : (2 : Fin 3) ≠ 0 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  have hZ : partition G Finset.univ lam = (24 : ℝ) := by
    rw [partition, hconfig]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [lam, Finset.prod_insert, Finset.card_insert_of_notMem, hn10, hn20, hn12]
  have hN : (∑ S ∈ configurations G Finset.univ,
      (S.card : ℝ) * ∏ v ∈ S, lam v) = (27 : ℝ) := by
    rw [hconfig]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [lam, Finset.prod_insert, Finset.card_insert_of_notMem, hn10, hn20, hn12]
  have hE : expectedSize G lam = (9 / 8 : ℝ) := by
    rw [expectedSize, hN, hZ]
    norm_num
  have hB : (∑ v : Fin 3,
      lam v / (1 + (G.degree v + 1) * lam v)) = (259 / 230 : ℝ) := by
    rw [Fin.sum_univ_three, hd0, hd1, hd2]
    norm_num [lam, hn10, hn20]
  rw [hB, hE] at hc
  norm_num at hc

#print axioms result

end D5.S3.StatisticalMechanics.HardCore.MultivariateOccupancyRefutation
