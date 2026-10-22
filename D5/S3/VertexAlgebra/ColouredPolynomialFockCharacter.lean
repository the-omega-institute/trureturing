/- GID: D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/ColouredPolynomialFockCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-colour oscillator energy fibers are partition profiles and have the powered Euler character. -/

/-
proof_shape: energyFiberEquivPartitionProfile: content; character_euler_product: content
escape_witness: The concrete energy constraint is preserved by the computed colour
  restrictions and their uncurried inverse. Cardinalities of the resulting partition
  profiles are exactly the finite antidiagonal convolution of the actual counting
  coefficients, rather than a definition of the character by an Euler product.
admission_basis: escape-witness
consumed_helpers: energy_eq_colour_sum is bind-only and is used by
  energyFiberEquivPartitionProfile on the live energy-compatibility path.
  energyFiber_finite is bind-only and supplies the finite enumeration used in
  character_euler_product's actual fiber-cardinality comparison.
computational_content: none; these are structural equivalences and formal-series
  identities for arbitrary finite colour types and all energies, not bounded searches,
  numerical reductions, certified finite instances or reflection infrastructure.
literature_novelty: 0; the partition mathematics is standard.
-/

import D5.S3.VertexAlgebra.PolynomialFockCharacter
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter

open scoped BigOperators PowerSeries.WithPiTopology
open PowerSeries

universe colourLevel

variable (C : Type colourLevel) [Fintype C]

def energy (powers : C × ℕ →₀ ℕ) : ℕ :=
  powers.sum fun index exponent => (index.2 + 1) * exponent

abbrev EnergyFiber (level : ℕ) := {powers : C × ℕ →₀ ℕ // energy C powers = level}

abbrev Allocation [DecidableEq C] (level : ℕ) :=
  {allocation : C →₀ ℕ // allocation ∈ Finset.finsuppAntidiag Finset.univ level}

abbrev PartitionProfile [DecidableEq C] (level : ℕ) :=
  Σ allocation : Allocation C level, (colour : C) → Nat.Partition (allocation.1 colour)

private theorem energy_eq_colour_sum (powers : C × ℕ →₀ ℕ) :
    energy C powers = ∑ colour : C,
      PolynomialFockLZeroSpectrum.energy (powers.curry colour) := by
  classical
  calc
    energy C powers = powers.curry.sum
        (fun _ exponent => PolynomialFockLZeroSpectrum.energy exponent) :=
      (Finsupp.sum_curry_index powers (fun _ frequency exponent =>
        (frequency + 1) * exponent)).symm
    _ = ∑ colour : C, PolynomialFockLZeroSpectrum.energy (powers.curry colour) := by
      exact Finsupp.sum_fintype _ _ (by
        intro colour
        simp [PolynomialFockLZeroSpectrum.energy])

noncomputable def energyFiberEquivPartitionProfile [DecidableEq C] (level : ℕ) :
    EnergyFiber C level ≃ PartitionProfile C level := by
  classical
  let oneColour : (ℕ →₀ ℕ) ≃ Σ total : ℕ, Nat.Partition total :=
    (Equiv.sigmaFiberEquiv PolynomialFockLZeroSpectrum.energy).symm.trans
      (Equiv.sigmaCongrRight PolynomialFockCharacter.energyFiberEquivPartition)
  let package : ((colour : C) → Σ total : ℕ, Nat.Partition total) ≃
      Σ allocation : C → ℕ, (colour : C) → Nat.Partition (allocation colour) := {
    toFun := fun profile => ⟨fun colour => (profile colour).1,
      fun colour => (profile colour).2⟩
    invFun := fun profile colour => ⟨profile.1 colour, profile.2 colour⟩
    left_inv := by intro profile; rfl
    right_inv := by intro profile; rfl
  }
  let total : (C × ℕ →₀ ℕ) ≃
      Σ allocation : C →₀ ℕ, (colour : C) → Nat.Partition (allocation colour) :=
    ((Finsupp.curryEquiv.trans Finsupp.equivFunOnFinite).trans
      (Equiv.piCongrRight (fun _ : C => oneColour))).trans
      (package.trans (Equiv.sigmaCongr Finsupp.equivFunOnFinite.symm
        (fun _ => Equiv.refl _)))
  have graded (powers : C × ℕ →₀ ℕ) :
      energy C powers = ∑ colour : C, (total powers).1 colour := by
    exact energy_eq_colour_sum C powers
  let restricted : EnergyFiber C level ≃
      {profile : Σ allocation : C →₀ ℕ,
          (colour : C) → Nat.Partition (allocation colour) //
        profile.1 ∈ Finset.finsuppAntidiag Finset.univ level} :=
    total.subtypeEquiv (by
      intro powers
      simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
      rw [← graded])
  exact restricted.trans (Equiv.subtypeSigmaEquiv
    (fun allocation : C →₀ ℕ => (colour : C) → Nat.Partition (allocation colour))
    (fun allocation => allocation ∈ Finset.finsuppAntidiag Finset.univ level))

noncomputable instance energyFiber_finite (level : ℕ) : Finite (EnergyFiber C level) := by
  classical
  exact Finite.of_equiv (PartitionProfile C level)
    (energyFiberEquivPartitionProfile C level).symm

noncomputable def character : ℂ⟦X⟧ :=
  PowerSeries.mk fun level => (Nat.card (EnergyFiber C level) : ℂ)

theorem character_euler_product :
    character C =
      (∏' frequency : ℕ, (1 - (X : ℂ⟦X⟧) ^ (frequency + 1))⁻¹) ^ Fintype.card C := by
  classical
  let oneColour : ℂ⟦X⟧ := PowerSeries.mk fun level =>
    (Module.finrank ℂ (PolynomialFockLZeroSpectrum.lZeroEigenspace level) : ℂ)
  have oneColour_coeff (level : ℕ) :
      PowerSeries.coeff level oneColour = (Nat.card (Nat.Partition level) : ℂ) := by
    rw [PowerSeries.coeff_mk, (PolynomialFockLZeroSpectrum.lZero_spectrum level).2]
    exact congrArg (fun count : ℕ => (count : ℂ))
      (Nat.card_congr (PolynomialFockCharacter.energyFiberEquivPartition level))
  have profile_count (level : ℕ) : (Nat.card (EnergyFiber C level) : ℂ) =
      ∑ allocation ∈ Finset.finsuppAntidiag (Finset.univ : Finset C) level,
        ∏ colour : C, (Nat.card (Nat.Partition (allocation colour)) : ℂ) := by
    letI : Fintype (EnergyFiber C level) := Fintype.ofFinite _
    have cardinality : Nat.card (EnergyFiber C level) = Nat.card (PartitionProfile C level) := by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_congr (energyFiberEquivPartitionProfile C level)
    rw [cardinality, Nat.card_sigma]
    simp only [Nat.card_pi, Nat.cast_sum, Nat.cast_prod]
    exact Finset.sum_coe_sort
      (Finset.finsuppAntidiag (Finset.univ : Finset C) level)
      (fun allocation : C →₀ ℕ => ∏ colour : C,
        (Nat.card (Nat.Partition (allocation colour)) : ℂ))
  have finite_product : character C = ∏ _ : C, oneColour := by
    apply PowerSeries.ext
    intro level
    rw [character, PowerSeries.coeff_mk, profile_count, PowerSeries.coeff_prod]
    apply Finset.sum_congr rfl
    intro allocation present
    apply Finset.prod_congr rfl
    intro colour member
    exact (oneColour_coeff (allocation colour)).symm
  calc
    character C = ∏ _ : C, oneColour := finite_product
    _ = oneColour ^ Fintype.card C := by simp
    _ = (∏' frequency : ℕ, (1 - (X : ℂ⟦X⟧) ^ (frequency + 1))⁻¹) ^
        Fintype.card C := congrArg (fun series : ℂ⟦X⟧ => series ^ Fintype.card C)
          PolynomialFockCharacter.lZero_character_euler_product

end D5.S3.VertexAlgebra.ColouredPolynomialFockCharacter
