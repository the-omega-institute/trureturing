/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every finite-group subset with generator classes of size at most four admits distinct powers. -/

/- admission_basis: open-problem-resolution (GitHub #29890)
   result proof_shape: content
   The allocation and subgroup-fibre assembly use the order-four classification
   through the four-generator modular block. The classification is discharged
   by MaLatin.orderFour. Direct frozen dependencies: none. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Assembly
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFour

namespace D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

/-- The size-four extension of Ma's Theorem 1.1 for every positive subset size. -/
theorem result :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G] (A : Finset G),
      0 < n → A.card = n →
      (∀ (x : G) (k : ℕ), 2 ≤ k → k ≤ n + 1 → orderOf x ≠ k) →
      (∀ x : G, x ∈ A →
        Nat.card {y : G // y ∈ A ∧ Subgroup.zpowers y = Subgroup.zpowers x} ≤ 4) →
      ∃ a : Fin n ≃ {x : G // x ∈ A},
        ∀ i j : Fin n, (a i : G) ^ (i.val + 1) = (a j : G) ^ (j.val + 1) → i = j :=
  claim_of_orderFour MaLatin.orderFour

end D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
