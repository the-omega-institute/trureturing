/- GID: D5/S3/VertexAlgebra/Characters/IntegerFockCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/IntegerFockCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer polynomial energy grades have ordinary-partition multiplicities. -/

import D5.S3.VertexAlgebra.PolynomialFockCharacter
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! The colour curry and finite energy allocations come from ColouredOddOccupation;
only their weight-independent bookkeeping is used. The single-colour partition
equivalence comes from PolynomialFockCharacter. No signed or odd character is used.
The carrier is the full polynomial algebra, with no frequency cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators PowerSeries.WithPiTopology
open Module

namespace D5.S3.VertexAlgebra.IntegerFockCharacter

open D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation (integerEnergy)
open D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum (energy)
open D5.S3.VertexAlgebra.PolynomialFockCharacter (energyFiberEquivPartition)

abbrev Fock (r : ℕ) := MvPolynomial (Fin r × ℕ) ℂ

abbrev EnergyFiber (r N : ℕ) :=
  {d : (Fin r × ℕ) →₀ ℕ // integerEnergy (Fin r) d = N}

/-- Ordinary partitions, with a separate energy for each colour and total energy N. -/
abbrev PartitionTuple (r N : ℕ) :=
  Σ e : EnergyAllocation (Fin r) N, (i : Fin r) → Nat.Partition (e.1 i)

/-- The genuine weighted homogeneous submodule in the infinite-variable algebra. -/
def grade (r N : ℕ) : Submodule ℂ (Fock r) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (fun x : Fin r × ℕ => x.2 + 1) N

private theorem energy_eq_sum (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) :
    integerEnergy (Fin r) d = ∑ i, energy (colourEquiv (Fin r) d i) := by
  classical
  calc
    integerEnergy (Fin r) d = d.sum (fun x c => c • (x.2 + 1)) := rfl
    _ = d.curry.sum (fun (_ : Fin r) f => f.sum (fun n c => c • (n + 1))) :=
      (Finsupp.sum_curry_index d (fun (_ : Fin r) n c => c • (n + 1))).symm
    _ = ∑ i, (d.curry i).sum (fun n c => c • (n + 1)) :=
      Finsupp.sum_fintype _ _ (by intro i; simp)
    _ = ∑ i, energy (colourEquiv (Fin r) d i) := by
      apply Finset.sum_congr rfl
      intro i _
      change (d.curry i).sum (fun n c => c • (n + 1)) = energy (d.curry i)
      simp [energy, Finsupp.sum, nsmul_eq_mul, mul_comm]

/-- Exact integer-energy fibre decomposition, including empty colour families. -/
def energyFiberEquivPartitionTuple (r N : ℕ) : EnergyFiber r N ≃ PartitionTuple r N := by
  let split : EnergyFiber r N ≃
      {f : Fin r → ℕ →₀ ℕ // ∑ i, energy (f i) = N} :=
    (colourEquiv (Fin r)).subtypeEquiv (fun d => by rw [energy_eq_sum])
  let group :
      (Σ e : EnergyAllocation (Fin r) N,
        {f : Fin r → ℕ →₀ ℕ // (fun i => energy (f i)) = e.1}) ≃
      {f : Fin r → ℕ →₀ ℕ // ∑ i, energy (f i) = N} :=
    Equiv.sigmaSubtypeFiberEquivSubtype (fun f : Fin r → ℕ →₀ ℕ => fun i => energy (f i))
      (fun _ => Iff.rfl)
  refine split.trans (group.symm.trans (Equiv.sigmaCongrRight (fun e => ?_)))
  exact ((Equiv.subtypeEquivRight (fun _ => funext_iff)).trans
    (Equiv.subtypePiEquivPi (p := fun i d => energy d = e.1 i))).trans
      (Equiv.piCongrRight (fun i => energyFiberEquivPartition (e.1 i)))

private def energyFiberEquivAntidiag (r N : ℕ) :
    EnergyFiber r N ≃
      Σ e : ↥((Finset.univ : Finset (Fin r)).finsuppAntidiag N),
        (i : Fin r) → Nat.Partition (e.1 i) :=
  (energyFiberEquivPartitionTuple r N).trans
    (Equiv.sigmaCongr (energyAllocationEquivAntidiag (Fin r) N) (fun _ => Equiv.refl _))

instance energyFiberFinite (r N : ℕ) : Finite (EnergyFiber r N) :=
  Finite.of_equiv _ (energyFiberEquivAntidiag r N).symm

/-- A finite convolution counts all occupations, without an imposed mode bound. -/
theorem card_energyFiber (r N : ℕ) :
    Nat.card (EnergyFiber r N) =
      ∑ e ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
        ∏ i : Fin r, Nat.card (Nat.Partition (e i)) := by
  classical
  rw [Nat.card_congr (energyFiberEquivAntidiag r N),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_pi, Nat.card_eq_fintype_card]
  exact Finset.sum_coe_sort ((Finset.univ : Finset (Fin r)).finsuppAntidiag N)
    (fun e : Fin r →₀ ℕ => ∏ i : Fin r, Fintype.card (Nat.Partition (e i)))

/-- Restrict Mathlib's monomial basis to the actual integer-energy fibre. -/
def gradeBasis (r N : ℕ) : Basis (EnergyFiber r N) ℂ (grade r N) := by
  let h := MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported ℂ
    (fun x : Fin r × ℕ => x.2 + 1) N
  exact (MvPolynomial.basisRestrictSupport ℂ
    {d : (Fin r × ℕ) →₀ ℕ | integerEnergy (Fin r) d = N}).map
      (LinearEquiv.ofEq _ _ h.symm)

instance gradeFinite (r N : ℕ) : Module.Finite ℂ (grade r N) :=
  Module.Finite.of_basis (gradeBasis r N)

/-- Actual finite energy multiplicity, obtained from the polynomial basis. -/
theorem finrank_grade (r N : ℕ) :
    Module.finrank ℂ (grade r N) = Nat.card (PartitionTuple r N) := by
  classical
  letI : Fintype (EnergyFiber r N) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (gradeBasis r N), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (energyFiberEquivPartitionTuple r N)

/-- Ordinary one-colour partition coefficients in the complex coefficient ring. -/
def ordinaryPartitionSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun N => (Nat.card (Nat.Partition N) : ℂ))

/-- Formal character of the genuine weighted polynomial grades. -/
def character (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun N => (Module.finrank ℂ (grade r N) : ℂ))

private theorem ordinaryPartitionSeries_eq_oneColour :
    ordinaryPartitionSeries = PowerSeries.mk
      (fun N => (Module.finrank ℂ
        (PolynomialFockLZeroSpectrum.lZeroEigenspace N) : ℂ)) := by
  apply PowerSeries.ext
  intro N
  simp only [ordinaryPartitionSeries, PowerSeries.coeff_mk,
    (PolynomialFockLZeroSpectrum.lZero_spectrum N).2]
  exact congrArg (fun n : ℕ => (n : ℂ))
    (Nat.card_congr (energyFiberEquivPartition N)).symm

/-- The exact finite-colour convolution is the finrank character, in every energy. -/
theorem character_eq_partition_power (r : ℕ) :
    character r = ordinaryPartitionSeries ^ r := by
  classical
  rw [show ordinaryPartitionSeries ^ r = ∏ _ : Fin r, ordinaryPartitionSeries by simp]
  apply PowerSeries.ext
  intro N
  rw [character, PowerSeries.coeff_mk,
    finrank_grade, ← Nat.card_congr (energyFiberEquivPartitionTuple r N), card_energyFiber,
    PowerSeries.coeff_prod]
  simp only [Nat.cast_sum, Nat.cast_prod, ordinaryPartitionSeries, PowerSeries.coeff_mk]

/-- The unshifted ordinary integer bosonic character; this is a formal identity. -/
theorem character_euler_product (r : ℕ) :
    character r = (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))⁻¹) ^ r := by
  rw [character_eq_partition_power, ordinaryPartitionSeries_eq_oneColour,
    PolynomialFockCharacter.lZero_character_euler_product]

end D5.S3.VertexAlgebra.IntegerFockCharacter
