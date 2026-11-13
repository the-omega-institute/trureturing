/- GID: D5/S3/Combinatorics/Partitions/PositiveEnergyPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/PositiveEnergyPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure positive-energy coordinates and their ordinary partition equivalence. -/

/-
proof_shape: energyFiberEquivPartition: content
escape_witness: Positive successor weights identify finite-support exponent
vectors with multisets of positive parts; predecessor decoding is inverse on
positive partition parts.
admission_basis: escape-witness
The concrete Fock eigenspace and Euler-product consumers remain in their
original I modules. This module contains only the reusable pure coordinate
construction.
-/

import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum

/-- Weighted degree, with the variable `X i` contributing `i + 1`. -/
def energy (d : ℕ →₀ ℕ) : ℕ := d.sum fun i e => (i + 1) * e

/-- Exponent vectors of a fixed nonnegative energy. -/
abbrev EnergyFiber (N : ℕ) := {d : ℕ →₀ ℕ // energy d = N}


end D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum

namespace D5.S3.VertexAlgebra.PolynomialFockCharacter

open D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum

/-- An exponent of `X i` records the multiplicity of the partition part `i + 1`. -/
noncomputable def energyFiberEquivPartition (N : ℕ) : EnergyFiber N ≃ Nat.Partition N := by
  classical
  have hsum (x : ℕ →₀ ℕ) : (x.toMultiset.map Nat.succ).sum = energy x := by
    rw [Finsupp.toMultiset_apply, Finsupp.multiset_map_sum,
      Finsupp.multiset_sum_sum]
    simp only [Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton]
    simp [energy, Finsupp.sum, Nat.succ_eq_add_one, mul_comm]
  let toPartition (d : EnergyFiber N) : Nat.Partition N := {
    parts := d.1.toMultiset.map Nat.succ
    parts_pos := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hj
      omega
    parts_sum := (hsum d.1).trans d.2
  }
  have hinj : Function.Injective toPartition := by
    intro d e h
    apply Subtype.ext
    have hm := Multiset.map_injective Nat.succ_injective
      (congrArg Nat.Partition.parts h)
    simpa using congrArg Multiset.toFinsupp hm
  have hsurj : Function.Surjective toPartition := by
    intro p
    let d : ℕ →₀ ℕ := (p.parts.map Nat.pred).toFinsupp
    have hparts : d.toMultiset.map Nat.succ = p.parts := by
      rw [Multiset.toFinsupp_toMultiset, Multiset.map_map]
      exact (Multiset.map_congr rfl (by
        intro j hj
        exact Nat.succ_pred_eq_of_pos (p.parts_pos hj))).trans p.parts.map_id'
    have henergy : energy d = N := by
      rw [← hsum d, hparts, p.parts_sum]
    exact ⟨⟨d, henergy⟩, Nat.Partition.ext hparts⟩
  exact Equiv.ofBijective toPartition ⟨hinj, hsurj⟩


end D5.S3.VertexAlgebra.PolynomialFockCharacter
