/- GID: D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtFrobeniusPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complex Specht traces pair with full-cycle power sums through Young permutation multiplicities. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations and surrounding namespaces; exact pinned Mathlib
and existing D5 suppliers are reused. Library/FiniteGroups/tauceti2026spechtpolytabloids.md
records immutable locators, license, consumers and retirement against OUR Mathlib pin.
SOURCE ONLY: no Lean/Lake invocation, native elaboration, axiom closure, proof-term
liveness, admission, validated Reg, emission, firstfreeze, deposit, PR or CI claim.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
These are necessary suppliers/comparisons for the full HSW target. No independent
firstfreeze or new-content qualification is claimed. Both original ordinary weighted
identities remain unfinished. No character is defined by a polynomial coefficient.
utility: none: arbitrary degrees and finite alphabets, no bounded enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtFixedTabloidPowerSum
import D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid

noncomputable section
open scoped BigOperators
namespace TauCeti
open _root_.Equiv Finset MvPolynomial CategoryTheory
open scoped Classical

universe u v w

section PermutationCharacter
variable (k : Type u) [Field k] {G : Type v} [Monoid G]

@[simp]
theorem char_ofMulAction (X : Type w) [MulAction G X] [Finite X] (g : G) :
    (Representation.ofMulAction k G X).character g = Nat.card {x : X // g • x = x} := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis X k), Matrix.trace]
  simp [LinearMap.toMatrix_apply, MonoidAlgebra.basis, Finsupp.single_apply,
    Fintype.card_subtype]

end PermutationCharacter

variable {n : ℕ}

/-- The actual complex permutation representation on cosets of the literal Young subgroup.
This scalar choice adapts PermutationModule/Basic; its character is still a trace, not a count
installed as its definition. -/
noncomputable abbrev permutationModuleℂ (ν : n.Partition) :
    _root_.FDRep ℂ (Perm (Fin n)) :=
  _root_.FDRep.of (Representation.ofMulAction ℂ (Perm (Fin n))
    (Perm (Fin n) ⧸ youngSubgroup ν))

private theorem char_permutationModuleℂ (ν : n.Partition) (π : Perm (Fin n)) :
    (permutationModuleℂ ν).character π =
      (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) := by
  change (Representation.ofMulAction ℂ (Perm (Fin n))
    (Perm (Fin n) ⧸ youngSubgroup ν)).character π = _
  exact char_ofMulAction ℂ _ π

/-- This uses the existing every-representative trace certification with the full partition;
it does not replace the module by a coefficient-defined character. -/
theorem spechtTrace_inv (μ : n.Partition) (π : Perm (Fin n)) :
    LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π⁻¹) =
      LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) := by
  let ν := (partitionEquivConjClasses n).symm (ConjClasses.mk π)
  have hp : π.partition.parts = ν.parts :=
    (parts_partitionEquivConjClasses_symm_mk n π).symm
  obtain ⟨_, _, htrace⟩ := (spechtCharValue_ordinaryTrace μ ν).2
  rw [htrace π hp, htrace π⁻¹ (by
    simpa only [Equiv.Perm.parts_partition, Equiv.Perm.cycleType_inv,
      Equiv.Perm.support_inv] using hp)]

/-- The Young-rule pairing before the missing identification of multiplicities with Kostka
numbers. Both characters are traces of the actual independently constructed representations.
This is a necessary precursor, not Young's rule or the Schur expansion. -/
theorem sum_spechtTrace_mul_card_fixedPoints (μ ν : n.Partition) :
    ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
        (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) =
      (n.factorial : ℂ) * (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) := by
  have hc : (Nat.card (Perm (Fin n)) : ℂ) ≠ 0 := by
    rw [Nat.card_perm, Nat.card_fin]
    exact Nat.cast_ne_zero.mpr n.factorial_ne_zero
  letI : Invertible (Nat.card (Perm (Fin n)) : ℂ) := invertibleOfNonzero hc
  have h := D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank
    (permutationModuleℂ ν) (spechtModuleℂ μ)
  rw [D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_apply] at h
  simp only [D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.ofCharacter_apply] at h
  change (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ π : Perm (Fin n),
    (permutationModuleℂ ν).character π * (spechtModuleℂ μ).character π⁻¹ =
      (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) at h
  have hs : ∑ π : Perm (Fin n),
      (permutationModuleℂ ν).character π * (spechtModuleℂ μ).character π⁻¹ =
      ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
        (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) := by
    apply Finset.sum_congr rfl
    intro π _
    rw [char_permutationModuleℂ]
    change _ * LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π⁻¹) = _
    rw [spechtTrace_inv, mul_comm]
  rw [hs, Nat.card_perm, Nat.card_fin] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  calc
    _ = (n.factorial : ℂ) * ((n.factorial : ℂ)⁻¹ *
        ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
          (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ)) :=
      (mul_inv_cancel_left₀ hf _).symm
    _ = _ := by rw [h]

/-- An arbitrary-degree finite-alphabet comparison that consumes actual ordinary traces and
the fixed-tabloid power-sum expansion. The remaining coefficients are genuine dimensions of
Hom spaces into Young permutation modules. They have NOT been identified with Kostka numbers;
therefore the right side is NOT asserted to be the Schur polynomial of μ. -/
theorem sum_spechtTrace_smul_psumPart_eq_multiplicities {σ : Type*} [Fintype σ]
    (μ : n.Partition) :
    (∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) •
      psumPart σ ℂ π.partition) =
    (n.factorial : ℂ) • ∑ ν : n.Partition,
      (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) • msymm σ ℂ ν := by
  classical
  have hp (π : Perm (Fin n)) :
      psumPart σ ℂ π.partition = ∑ ν : n.Partition,
        (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) • msymm σ ℂ ν := by
    let ρ := (partitionEquivConjClasses n).symm (ConjClasses.mk π)
    have hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ :=
      ((partitionEquivConjClasses n).apply_symm_apply _).symm
    rw [← psumPart_eq_psumPart_partition ℂ hπ]
    exact psumPart_eq_sum_card_fixedPoints_smul_msymm ℂ hπ
  simp_rw [hp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_spechtTrace_mul_card_fixedPoints]

/-- Exact list-to-partition power-sum transport. The equality of full multisets retains all
parts equal to one and every repeated occurrence; no degree/alphabet condition is used. -/
theorem hsw_powerSumProd_eq_psumPart {τ : List ℕ} (ρ : n.Partition)
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.powerSumProd τ =
      psumPart (Fin 3) ℤ ρ := by
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.powerSumProd, psumPart, ← hτ,
    Multiset.map_coe, Multiset.prod_coe]

set_option maxHeartbeats 1000000 in
/-- The exact existing HSW coefficient expressed through fixed tabloids. This supplies its
monomial-coordinate input to Young's rule. It is NOT an ordinary-character identification. -/
theorem hsw_frobChar_eq_fixedTabloid_coefficients (μ : Fin 3 → ℕ)
    (ρ : n.Partition) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar μ τ =
      ∑ ν : n.Partition,
        (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℤ) *
          (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3 *
            msymm (Fin 3) ℤ ν).coeff
              (Finsupp.equivFunOnFinite.symm fun i => μ i + (2 - (i : ℕ))) := by
  classical
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar,
    hsw_powerSumProd_eq_psumPart ρ hτ,
    psumPart_eq_sum_card_fixedPoints_smul_msymm ℤ hπ, Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [mul_smul_comm, coeff_smul, smul_eq_mul]
  rfl

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
