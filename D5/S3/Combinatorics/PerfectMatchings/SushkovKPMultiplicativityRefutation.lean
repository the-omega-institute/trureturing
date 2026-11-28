/- GID: D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.claim; result=D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.result; claim=D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.claim
   digest: The normalized KP series 1 + t₁ refutes multiplicativity necessity at H = N = 1. -/
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
Sushkov, arXiv:2611.02795v1, §6 item 1 (issue #35289).
At H = N = 1 all YJM factors of (6.1) are units, so its unscaled class-sum
coordinates are exactly the input family, including in degree zero.
Equation (2.15) sends the class sum indexed by ρ to p_ρ / z_ρ.
-/

noncomputable section

namespace D5.S3.Combinatorics.PerfectMatchings.SushkovKPMultiplicativityRefutation

open DeformedJucysMurphyC2
open scoped BigOperators

abbrev Coefficients := (n : ℕ) → Nat.Partition n → ℂ

/-- The degreewise class-sum Frobenius map for (6.1) at H = N = 1. -/
def frobenius (a : Coefficients) (n : ℕ) : PowerSum ℂ :=
  ∑ ρ : Nat.Partition n, (a n ρ / (zPartition ρ : ℂ)) • powerSumMonomial ρ

/-- Both sequences of KP times are independent indeterminates.
Index `i` in either copy denotes time `i + 1`. -/
abbrev Times := MvPolynomial (Sum ℕ ℕ) ℂ

private def timeDifference : PowerSeries Times :=
  PowerSeries.mk fun
    | 0 => 0
    | i + 1 => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)

/-- The full formal exponential in the KP bilinear identity. -/
def timeExponential : PowerSeries Times :=
  (PowerSeries.exp Times).subst timeDifference

/-- After pⱼ = j tⱼ, the Miwa shift with sign ε sends pⱼ to j tⱼ + ε z⁻ʲ.
Here each image is multiplied by zʲ. On weight n this clears a common z⁻ⁿ. -/
def scaledMiwa (side : ℕ → Sum ℕ ℕ) (ε : ℂ) : PowerSum ℂ →+* PowerSeries Times :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp MvPolynomial.C) fun i =>
    PowerSeries.C (MvPolynomial.C (variableWeight i : ℂ) * MvPolynomial.X (side i)) *
      PowerSeries.X ^ variableWeight i + PowerSeries.C (MvPolynomial.C ε)

/-- The weight-d part of the full residue for a series given by its weighted pieces.
For pieces of weights m and n, coefficient d of the scaled product with the
exponential has time weight d. Undoing the scaling changes its z-exponent to
d - (m + n), so exactly the pairs m + n = d + 1 contribute to the residue.
This gives a finite sum in each weight for arbitrary completed series. -/
def residue (τ : ℕ → PowerSum ℂ) (d : ℕ) : Times :=
  ∑ mn ∈ Finset.antidiagonal (d + 1),
    PowerSeries.coeff d
      (scaledMiwa Sum.inl (-1) (τ mn.1) * scaledMiwa Sum.inr 1 (τ mn.2) *
        timeExponential)

/-- One value per positive part size, indexed by size minus one.
The multiset product retains all repeated parts. -/
def Multiplicative (a : Coefficients) : Prop :=
  ∃ b : ℕ → ℂ, ∀ (n : ℕ) (ρ : Nat.Partition n),
    a n ρ = (ρ.parts.map fun j => b (j - 1)).prod

/-- The necessity implication for normalized KP series at H = N = 1. -/
def claim : Prop :=
  ∀ a : Coefficients, MvPolynomial.constantCoeff (frobenius a 0) = 1 →
    (∀ d, residue (frobenius a) d = 0) → Multiplicative a

private def witness : Coefficients := fun n _ => if n ≤ 1 then 1 else 0

private theorem frobenius_zero : frobenius witness 0 = 1 := by
  classical
  simp [frobenius, witness, powerSumMonomial, zPartition, partitionExponent, zExponent,
    MvPolynomial.monomial_zero_eq_C]

private theorem frobenius_one : frobenius witness 1 = MvPolynomial.X 0 := by
  classical
  simp [frobenius, witness, powerSumMonomial, zPartition, partitionExponent, zExponent,
    Finsupp.prod_single_index, MvPolynomial.X]

private theorem frobenius_high {n : ℕ} (hn : 1 < n) : frobenius witness n = 0 := by
  classical
  simp [frobenius, witness, Nat.not_le.mpr hn]

private theorem frobenius_image (n : ℕ) :
    frobenius witness n =
      MvPolynomial.weightedHomogeneousComponent variableWeight n
        (1 + MvPolynomial.X 0 : PowerSum ℂ) := by
  have h₀ : MvPolynomial.IsWeightedHomogeneous variableWeight (1 : PowerSum ℂ) 0 :=
    MvPolynomial.isWeightedHomogeneous_one
  have h₁ : MvPolynomial.IsWeightedHomogeneous variableWeight
      (MvPolynomial.X 0 : PowerSum ℂ) 1 :=
    MvPolynomial.isWeightedHomogeneous_X variableWeight 0
  rw [map_add]
  rcases n with _ | _ | n
  · simp [frobenius_zero, h₀.weightedHomogeneousComponent_same,
      h₁.weightedHomogeneousComponent_ne 0 (by decide : 0 ≠ 1)]
  · simp [frobenius_one, h₁.weightedHomogeneousComponent_same,
      h₀.weightedHomogeneousComponent_ne 1 (by decide : 1 ≠ 0)]
  · rw [frobenius_high (by omega), h₀.weightedHomogeneousComponent_ne _ (by omega),
      h₁.weightedHomogeneousComponent_ne _ (by omega), add_zero]

private theorem not_multiplicative : ¬ Multiplicative witness := by
  rintro ⟨b, hb⟩
  have onePart : b 0 = 1 := by
    simpa [witness, eq_comm] using hb 1 (Nat.Partition.indiscrete 1)
  let twoOnes := Nat.Partition.ofSums 2 ({1, 1} : Multiset ℕ) (by decide)
  have h := hb 2 twoOnes
  simp [witness, twoOnes, onePart] at h

private theorem timeDifference_constant : PowerSeries.constantCoeff timeDifference = 0 := rfl

private theorem exponential_constant : PowerSeries.constantCoeff timeExponential = 1 := by
  rw [timeExponential, PowerSeries.constantCoeff_subst_of_constantCoeff_zero timeDifference_constant]
  simp

private theorem exponential_linear :
    PowerSeries.coeff 1 timeExponential =
      MvPolynomial.X (Sum.inl 0) - MvPolynomial.X (Sum.inr 0) := by
  rw [timeExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' timeDifference_constant), finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp, timeDifference]
  · intro k hk
    rcases k with _ | _ | k
    · simp
    · exact (hk rfl).elim
    · rw [PowerSeries.coeff_one_pow, timeDifference_constant]
      simp

private def affineShift (side : ℕ → Sum ℕ ℕ) (ε : ℂ) : PowerSeries Times :=
  PowerSeries.C (1 + MvPolynomial.X (side 0)) * PowerSeries.X +
    PowerSeries.C (MvPolynomial.C ε)

/-- Clearing a factor of z from the affine tau gives (1 + t₁)z + ε. -/
private theorem scaledMiwa_X (side : ℕ → Sum ℕ ℕ) (ε : ℂ) :
    PowerSeries.X + scaledMiwa side ε (MvPolynomial.X 0) = affineShift side ε := by
  simp [scaledMiwa, affineShift, variableWeight, MvPolynomial.eval₂Hom_X',
    add_mul, add_assoc]

private theorem affine_residue :
    PowerSeries.coeff 1
      (affineShift Sum.inl (-1) * affineShift Sum.inr 1 * timeExponential) = 0 := by
  rw [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_mul, exponential_constant,
    exponential_linear]
  simp [affineShift, PowerSeries.coeff_one_mul]
  ring

private theorem witness_kp : ∀ d, residue (frobenius witness) d = 0 := by
  intro d
  rcases d with _ | _ | d
  · have hp : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
    simp [residue, hp, frobenius_zero, frobenius_one, scaledMiwa, variableWeight,
      MvPolynomial.eval₂Hom_X', PowerSeries.coeff_zero_eq_constantCoeff, exponential_constant]
  · have hp : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
    have hz : frobenius witness 2 = 0 := frobenius_high (by decide)
    have ht (side : ℕ → Sum ℕ ℕ) (ε : ℂ) :
        scaledMiwa side ε (frobenius witness 1) = affineShift side ε - PowerSeries.X := by
      rw [frobenius_one, eq_sub_iff_add_eq, add_comm, scaledMiwa_X]
    have hsingle : residue (frobenius witness) 1 =
        PowerSeries.coeff 1 (scaledMiwa Sum.inl (-1) (frobenius witness 1) *
          scaledMiwa Sum.inr 1 (frobenius witness 1) * timeExponential) := by
      simp [residue, hp, hz]
    rw [hsingle, ht, ht, ← affine_residue]
    simp [affineShift, PowerSeries.coeff_one_mul, exponential_constant]
    ring
  · apply Finset.sum_eq_zero
    intro mn hm
    have hs := Finset.mem_antidiagonal.mp hm
    by_cases h : 1 < mn.1
    · simp [frobenius_high h]
    · have h' : 1 < mn.2 := by omega
      simp [frobenius_high h']

/-- The degree-zero and degree-one coefficient family refutes the necessity clause. -/
theorem result : ¬ claim := by
  intro h
  apply not_multiplicative
  apply h witness
  · have h₀ : MvPolynomial.IsWeightedHomogeneous variableWeight (1 : PowerSum ℂ) 0 :=
      MvPolynomial.isWeightedHomogeneous_one
    have h₁ : MvPolynomial.IsWeightedHomogeneous variableWeight
        (MvPolynomial.X 0 : PowerSum ℂ) 1 :=
      MvPolynomial.isWeightedHomogeneous_X variableWeight 0
    simp [frobenius_image, h₀.weightedHomogeneousComponent_same,
      h₁.weightedHomogeneousComponent_ne 0 (by decide : 0 ≠ 1)]
  · exact witness_kp

end D5.S3.Combinatorics.PerfectMatchings.SushkovKPMultiplicativityRefutation
