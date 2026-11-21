/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ma's order exclusions, generator classes and distinct-power enumeration. -/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

/-- The elements of A generating the same cyclic subgroup as x. -/
def generatorClass {G : Type*} [Group G] (A : Finset G) (x : G) : Set G :=
  {y : G | y ∈ A ∧ Subgroup.zpowers y = Subgroup.zpowers x}

/-- No element of G has any order in {2, ..., n + 1}. -/
def noSmallOrders (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (x : G) (k : ℕ), 2 ≤ k → k ≤ n + 1 → orderOf x ≠ k

/-- Every generator class inside A has at most four elements. -/
def classesAtMostFour {G : Type*} [Group G] (A : Finset G) : Prop :=
  ∀ x : G, x ∈ A → Nat.card (generatorClass A x) ≤ 4

/-- A is enumerated once, with exponents 1 through n and pairwise distinct powers. -/
def hasDistinctPowersEnumeration {G : Type*} [Group G] (n : ℕ) (A : Finset G) : Prop :=
  ∃ a : Fin n ≃ {x : G // x ∈ A},
    Function.Injective (fun i : Fin n => (a i : G) ^ (i.val + 1))

/-- The size-four analogue of Ma's Theorem 1.1, asked in Remark 2.2 and Section 9. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [Finite G] (A : Finset G),
    0 < n → A.card = n → noSmallOrders n G → classesAtMostFour A →
      hasDistinctPowersEnumeration n A

end D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
