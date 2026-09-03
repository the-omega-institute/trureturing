/- GID: D5/S3/Analytic/SeriesInequalities/PartitionMobiusInversion
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/PartitionMobiusInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Incidence-algebra inversion gives the moment-cumulant formulas
     on a finite partition lattice. -/

import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Partition.Finpartition

/- Library-search and duplication audit (2026-09-04):
   * Repository searches covered partition lattices, cumulants, moments, Bell
     expansions, Mobius inversion, and the general theorem shape. No D5 theorem
     states either partition moment-cumulant formula or their equivalence.
   * The source atom has no formalization receipt or digestion binding, and the
     in-flight branch scan found no competing partition-inversion deposit.
   * Pinned Mathlib provides `Finpartition` with its refinement order and
     `IncidenceAlgebra.moebius_inversion_bot`, which is applied directly.
   * Mathlib does not provide the closed formula for the Mobius function of the
     partition lattice. That exact missing identity is exposed as `hmu`, rather
     than re-proving it or assuming either target formula.
   * The nonempty hypothesis on `A` ensures every partition has at least one
     block, so `parts.card - 1` is not the truncated subtraction at zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.PartitionMobiusInversion

open Finset

noncomputable section

local instance finpartitionLocallyFiniteOrder {α : Type*} [DecidableEq α]
    {A : Finset α} : LocallyFiniteOrder (Finpartition A) := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- Product of block weights over a finite set partition. -/
def partitionProduct {α R : Type*} [DecidableEq α] [CommMonoid R]
    {A : Finset α} (weight : Finset α → R) (partition : Finpartition A) : R :=
  ∏ block ∈ partition.parts, weight block

/-- The classical closed coefficient for a partition with `k` blocks. -/
def partitionMoebiusCoefficient {α R : Type*} [DecidableEq α] [CommRing R]
    {A : Finset α} (partition : Finpartition A) : R :=
  (-1 : R) ^ (partition.parts.card - 1) *
    (Nat.factorial (partition.parts.card - 1) : R)

/-- On a nonempty finite partition lattice, the multiplicative moment relation
and the classical closed formula for its Mobius function imply both directions
of the moment-cumulant correspondence. -/
theorem partition_mobius_moment_cumulant_inversion
    {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (hA : A.Nonempty) (moment cumulant : Finset α → R)
    (hrelation : ∀ partition : Finpartition A,
      partitionProduct moment partition =
        ∑ refinement ∈ Finset.Iic partition,
          partitionProduct cumulant refinement)
    (hmu : ∀ partition : Finpartition A,
      IncidenceAlgebra.mu R partition (⊤ : Finpartition A) =
        partitionMoebiusCoefficient partition) :
    cumulant A =
        ∑ partition : Finpartition A,
          partitionMoebiusCoefficient partition *
            partitionProduct moment partition ∧
      moment A =
        ∑ partition : Finpartition A, partitionProduct cumulant partition := by
  classical
  have htopParts : (⊤ : Finpartition A).parts = {A} := by
    apply Finset.Subset.antisymm (Finpartition.parts_top_subset A)
    intro block hblock
    rw [Finset.mem_singleton] at hblock
    subst block
    obtain ⟨block, hblock⟩ :=
      (⊤ : Finpartition A).parts_nonempty hA.ne_empty
    have hblockA : block = A :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset A hblock)
    simpa [hblockA] using hblock
  have hblockPositive : ∀ partition : Finpartition A, 0 < partition.parts.card := by
    intro partition
    exact Finset.card_pos.mpr (partition.parts_nonempty hA.ne_empty)
  have hinverse := IncidenceAlgebra.moebius_inversion_bot
    (partitionProduct cumulant) (partitionProduct moment) hrelation
    (⊤ : Finpartition A)
  have hcumulant : cumulant A =
      ∑ partition : Finpartition A,
        partitionMoebiusCoefficient partition *
          partitionProduct moment partition := by
    rw [Finset.Iic_top] at hinverse
    simp_rw [hmu] at hinverse
    simpa [partitionProduct, htopParts] using hinverse
  have hmomentTop := hrelation (⊤ : Finpartition A)
  rw [Finset.Iic_top] at hmomentTop
  have hmoment : moment A =
      ∑ partition : Finpartition A, partitionProduct cumulant partition := by
    simpa [partitionProduct, htopParts] using hmomentTop
  exact ⟨hcumulant, hmoment⟩

#print axioms partition_mobius_moment_cumulant_inversion

end

end D5.S3.Analytic.SeriesInequalities.PartitionMobiusInversion
