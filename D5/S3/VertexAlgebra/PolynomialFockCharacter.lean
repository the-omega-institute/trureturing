/- GID: D5/S3/VertexAlgebra/PolynomialFockCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete polynomial Fock zero-mode character is the partition Euler product. -/

/-
proof_shape: energyFiberEquivPartition: content; lZero_character_euler_product: content
escape_witness: The finite exponent vector at energy N is converted bijectively to
  a multiset of positive parts by replacing each variable index i with i+1 and
  repeating it d_i times. This new bridge identifies the concrete zero-mode
  multiplicities with the partition coefficients in Mathlib's generating product.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.lZero_spectrum.
-/

import D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockCharacter

open D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum
open PowerSeries
open scoped PowerSeries.WithPiTopology

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

/-- The formal character of the actual polynomial Fock `L 0` eigenspaces is Euler's
partition product. The factor indexed by `i` represents the positive part `i + 1`. -/
theorem lZero_character_euler_product :
    PowerSeries.mk (fun N => (Module.finrank ℂ (lZeroEigenspace N) : ℂ)) =
      ∏' i : ℕ, (1 - (X : ℂ⟦X⟧) ^ (i + 1))⁻¹ := by
  classical
  have hcoeff :
      PowerSeries.mk (fun N => (Module.finrank ℂ (lZeroEigenspace N) : ℂ)) =
        Nat.Partition.genFun (fun _ _ => (1 : ℂ)) := by
    apply PowerSeries.ext
    intro N
    rw [PowerSeries.coeff_mk, Nat.Partition.coeff_genFun]
    simp only [Finsupp.prod, Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [(lZero_spectrum N).2]
    simpa only [Nat.card_eq_fintype_card, Fintype.card] using
      congrArg (fun n : ℕ => (n : ℂ))
        (Nat.card_congr (energyFiberEquivPartition N))
  rw [hcoeff, Nat.Partition.genFun_eq_tprod]
  congr 1
  funext i
  have hzero : ((X : ℂ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by simp
  have hsum :=
    (PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hzero).tsum_eq_zero_add
  have hgeom :
      (1 : ℂ⟦X⟧) + ∑' j : ℕ, (X : ℂ⟦X⟧) ^ ((i + 1) * (j + 1)) =
        ∑' j : ℕ, ((X : ℂ⟦X⟧) ^ (i + 1)) ^ j := by
    simpa [pow_mul, mul_comm] using hsum.symm
  rw [show (fun j : ℕ => (1 : ℂ) • (X : ℂ⟦X⟧) ^ ((i + 1) * (j + 1))) =
      (fun j : ℕ => (X : ℂ⟦X⟧) ^ ((i + 1) * (j + 1))) by simp, hgeom]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hzero])).2
  exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hzero

end D5.S3.VertexAlgebra.PolynomialFockCharacter
