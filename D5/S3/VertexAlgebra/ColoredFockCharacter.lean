/- GID: D5/S3/VertexAlgebra/ColoredFockCharacter
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/ColoredFockCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-color oscillator fibers realize the independent partition convolution. -/

import D5.S3.VertexAlgebra.PolynomialFockCharacter
import Mathlib.Algebra.Order.Antidiag.Finsupp

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.ColoredFockCharacter

open scoped BigOperators
open scoped PowerSeries.WithPiTopology
open PolynomialFockCharacter

noncomputable section

variable (Colors : Type*) [Fintype Colors] [DecidableEq Colors]

abbrev Occupation := Colors × ℕ →₀ ℕ

def energy (powers : Occupation Colors) : ℕ :=
  powers.sum fun index count => (index.2 + 1) * count

abbrev EnergyFiber (level : ℕ) := {powers : Occupation Colors // energy Colors powers = level}

def colorSplit : Occupation Colors ≃ (Colors → ℕ →₀ ℕ) :=
  Finsupp.curryEquiv.trans Finsupp.equivFunOnFinite

private theorem energy_colorSplit (powers : Occupation Colors) :
    energy Colors powers = ∑ color, PolynomialFockLZeroSpectrum.energy
      (colorSplit Colors powers color) := by
  change powers.sum (fun index count => (index.2 + 1) * count) =
    ∑ color, (powers.curry color).sum (fun frequency count => (frequency + 1) * count)
  rw [← Finsupp.sum_curry_index powers (fun _ frequency count => (frequency + 1) * count)]
  exact Finsupp.sum_fintype _ _ (by simp)

abbrev EnergyComposition (level : ℕ) :=
  ↥((Finset.univ : Finset Colors).finsuppAntidiag level)

abbrev PartitionTuple (level : ℕ) :=
  Σ composition : EnergyComposition Colors level, ∀ color, Nat.Partition (composition.val color)

def fiberPartitionTuple (level : ℕ) : EnergyFiber Colors level ≃ PartitionTuple Colors level where
  toFun powers :=
    let composition : Colors →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun color => PolynomialFockLZeroSpectrum.energy (colorSplit Colors powers.val color))
    ⟨⟨composition, Finset.mem_finsuppAntidiag.mpr
      ⟨(energy_colorSplit Colors powers.val).symm.trans powers.property,
        Finset.subset_univ _⟩⟩,
      fun color => energyFiberEquivPartition (composition color)
        ⟨colorSplit Colors powers.val color, rfl⟩⟩
  invFun tuple :=
    let pieces := fun color => (energyFiberEquivPartition (tuple.1.val color)).symm (tuple.2 color)
    ⟨(colorSplit Colors).symm (fun color => (pieces color).val), by
      rw [energy_colorSplit, Equiv.apply_symm_apply]
      simpa only [funext_iff] using
        (Finset.sum_congr rfl (fun color _ => (pieces color).property)).trans
          (Finset.mem_finsuppAntidiag.mp tuple.1.property).1⟩
  left_inv powers := by
    apply Subtype.ext
    apply (colorSplit Colors).injective
    funext color
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv tuple := by
    have repack {first second : ℕ}
        (piece : PolynomialFockLZeroSpectrum.EnergyFiber first)
        (other : PolynomialFockLZeroSpectrum.EnergyFiber second)
        (same : piece.val = other.val) :
        HEq (energyFiberEquivPartition first piece)
          (energyFiberEquivPartition second other) := by
      have levels : first = second := piece.property.symm.trans
        ((congrArg PolynomialFockLZeroSpectrum.energy same).trans other.property)
      subst second
      exact heq_of_eq (congrArg (energyFiberEquivPartition first) (Subtype.ext same))
    rcases tuple with ⟨composition, partitions⟩
    dsimp only
    simp only [Equiv.apply_symm_apply]
    have same : Finsupp.equivFunOnFinite.symm
        (fun color => PolynomialFockLZeroSpectrum.energy
          ((energyFiberEquivPartition (composition.val color)).symm (partitions color)).val) =
        composition.val := by
      ext color
      exact ((energyFiberEquivPartition (composition.val color)).symm (partitions color)).property
    have same' : Finsupp.equivFunOnFinite.symm
        (fun color => PolynomialFockLZeroSpectrum.energy
          (colorSplit Colors ((colorSplit Colors).symm (fun color =>
            ((energyFiberEquivPartition (composition.val color)).symm
              (partitions color)).val)) color)) = composition.val := by
      rw [Equiv.apply_symm_apply]
      exact same
    refine Sigma.ext (Subtype.ext ?_) ?_
    · change (Finsupp.equivFunOnFinite.symm
        (fun color => PolynomialFockLZeroSpectrum.energy
          (colorSplit Colors ((colorSplit Colors).symm (fun color =>
            ((energyFiberEquivPartition (composition.val color)).symm
              (partitions color)).val)) color))) = composition.val
      exact same'
    apply Function.hfunext rfl
    intro color other equality
    have colorEquality : color = other := eq_of_heq equality
    subst other
    refine HEq.trans ?_
      (heq_of_eq ((energyFiberEquivPartition (composition.val color)).apply_symm_apply
        (partitions color)))
    apply repack
    rfl

instance energyFiber_finite (level : ℕ) : Finite (EnergyFiber Colors level) :=
  Finite.of_equiv (PartitionTuple Colors level) (fiberPartitionTuple Colors level).symm

def partitionCoefficient (level : ℕ) : ℕ :=
  PowerSeries.coeff level
    ((Nat.Partition.genFun (fun _ _ => (1 : ℕ))) ^ Fintype.card Colors)

theorem energyFiber_card (level : ℕ) :
    Nat.card (EnergyFiber Colors level) = partitionCoefficient Colors level := by
  classical
  rw [Nat.card_congr (fiberPartitionTuple Colors level), Nat.card_sigma]
  simp_rw [Nat.card_pi]
  unfold partitionCoefficient
  rw [show (Nat.Partition.genFun (fun _ _ => (1 : ℕ))) ^ Fintype.card Colors =
    ∏ _color : Colors, Nat.Partition.genFun (fun _ _ => (1 : ℕ)) by simp,
    PowerSeries.coeff_prod]
  simp only [Nat.Partition.coeff_genFun, Finsupp.prod, Finset.prod_const_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card, Finset.card_univ]
  exact Finset.sum_coe_sort
    ((Finset.univ : Finset Colors).finsuppAntidiag level)
    (fun composition : Colors →₀ ℕ => ∏ color, Fintype.card (Nat.Partition (composition color)))

theorem character (colors : ℕ) :
    PowerSeries.mk (fun level => Nat.card (EnergyFiber (Fin colors) level)) =
      (Nat.Partition.genFun (fun _ _ => (1 : ℕ))) ^ colors := by
  ext level
  simpa [partitionCoefficient] using energyFiber_card (Fin colors) level

theorem character_euler (colors : ℕ) :
    PowerSeries.mk (fun level => (Nat.card (EnergyFiber (Fin colors) level) : ℂ)) =
      (∏' frequency : ℕ,
        (1 - (PowerSeries.X : PowerSeries ℂ) ^ (frequency + 1))⁻¹) ^ colors := by
  classical
  have mapPartition :
      PowerSeries.map (Nat.castRingHom ℂ) (Nat.Partition.genFun (fun _ _ => (1 : ℕ))) =
        Nat.Partition.genFun (fun _ _ => (1 : ℂ)) := by
    ext level
    simp [PowerSeries.coeff_map, Nat.Partition.coeff_genFun, Finsupp.prod]
  have mapped := congrArg (PowerSeries.map (Nat.castRingHom ℂ)) (character colors)
  rw [map_pow, mapPartition] at mapped
  have mapCharacter :
      PowerSeries.map (Nat.castRingHom ℂ)
        (PowerSeries.mk (fun level => Nat.card (EnergyFiber (Fin colors) level))) =
      PowerSeries.mk (fun level => (Nat.card (EnergyFiber (Fin colors) level) : ℂ)) := by
    ext level
    simp [PowerSeries.coeff_map]
  rw [mapCharacter] at mapped
  have mono : Nat.Partition.genFun (fun _ _ => (1 : ℂ)) =
      PowerSeries.mk (fun level =>
        (Module.finrank ℂ (PolynomialFockLZeroSpectrum.lZeroEigenspace level) : ℂ)) := by
    ext level
    rw [Nat.Partition.coeff_genFun, PowerSeries.coeff_mk,
      (PolynomialFockLZeroSpectrum.lZero_spectrum level).2,
      Nat.card_congr (energyFiberEquivPartition level)]
    simp [Finsupp.prod, Nat.card_eq_fintype_card]
  rw [mono, lZero_character_euler_product] at mapped
  exact mapped

end

end D5.S3.VertexAlgebra.ColoredFockCharacter
