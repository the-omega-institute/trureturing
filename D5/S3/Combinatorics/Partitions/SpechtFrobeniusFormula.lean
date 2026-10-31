/- GID: D5/S3/Combinatorics/Partitions/SpechtFrobeniusFormula
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtFrobeniusFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-degree finite-alphabet Frobenius formula from actual same-partition ordinary Specht traces. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected and adapted from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
License, exact selections and consumers: Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtYoungRule

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti
open Equiv MvPolynomial

variable {n : ℕ} {σ : Type*} [Fintype σ] (R : Type*) [CommRing R]

theorem psumPart_eq_sum_spechtCharValue_smul_schurPoly (ρ : n.Partition) :
    psumPart σ R ρ = ∑ l : n.Partition, spechtCharValue l ρ • schurPoly σ R l := by
  obtain ⟨π, hπ⟩ := (partitionEquivConjClasses n ρ).exists_rep
  have hχ (l : n.Partition) : spechtCharValue l ρ = spechtChar l π :=
    spechtCharValue_eq_spechtChar l ρ hπ
  classical
  simp_rw [psumPart_eq_sum_card_fixedPoints_smul_msymm R hπ, hχ,
    schurPoly_eq_sum_kostkaNumber_smul_msymm, Finset.smul_sum, ← smul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := congrArg (Int.cast : ℤ → R) (card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar ν π)
  push_cast at h
  simp_rw [h, zsmul_eq_mul, mul_comm]

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
