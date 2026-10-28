/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite scalar common numerators for actual canonical lattice channels. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
The factorial pairing tests the common vector series against an arbitrary
finite oscillator polynomial. Actual mode grading bounds the resulting total
degree, without positivity or a vacuum assumption.

proof_shape: content
admission_basis: escape-witness
escape_witness: finite multilinear expansion and actual mode grading force a
charge-energy lower bound on every nonzero double canonical coefficient.
This bound makes the scalar common series an exact polynomial truncation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorScalarNumerator
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticePositiveEnergy LatticeSugawaraCurrents SupportedChannelSeries MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

open private map_extend from D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
open private inner_coefficient_expansion from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation

private theorem inclusion_monomial_grade (D : LatticeData) (α : Charge D)
    (U : Exponent D) (c : ℂ) :
    inclusion D α (monomial U c) ∈ grade D (chargeEnergy D α + oscillatorEnergy U) := by
  classical
  rw [mem_grade_iff]
  rintro ⟨β, T⟩ h
  by_cases hα : α = β
  · subst β
    by_cases hT : U = T
    · subst T
      exact (h rfl).elim
    · simp [inclusion, coeff_monomial, hT]
  · simp [inclusion, Finsupp.single_apply, hα]

private theorem double_coefficient_zero_below_charge (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (m n : ℤ) (T : Exponent D)
    (low : chargeEnergy D (α + (β + γ)) + oscillatorEnergy T <
      chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2) :
    (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T = 0 := by
  classical
  induction u using MvPolynomial.induction_on' with
  | add u₁ u₂ ih₁ ih₂ =>
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply, MvPolynomial.coeff_add, ih₁, ih₂, add_zero]
  | monomial U a =>
    induction v using MvPolynomial.induction_on' with
    | add v₁ v₂ ih₁ ih₂ =>
      simpa only [map_add, Pi.add_apply, LinearMap.add_apply, MvPolynomial.coeff_add, ih₁, ih₂, add_zero]
    | monomial V b =>
      induction w using MvPolynomial.induction_on' with
      | add w₁ w₂ ih₁ ih₂ =>
        simpa only [map_add, Pi.add_apply, LinearMap.add_apply, MvPolynomial.coeff_add, ih₁, ih₂, add_zero]
      | monomial W c =>
        have hi := actual_mode_grade D J hJG hGJ _ _ n _ _
          (inclusion_monomial_grade D β V b) (inclusion_monomial_grade D γ W c)
        rw [← inclusion_canonical] at hi
        have ho := actual_mode_grade D J hJG hGJ _ _ m _ _
          (inclusion_monomial_grade D α U a) hi
        rw [← inclusion_canonical] at ho
        have hz := (mem_grade_iff D _ _).mp ho (α + (β + γ), T) (by
          simp only [energy]
          omega)
        simpa only [inclusion, Finsupp.lsingle_apply, Finsupp.single_eq_same] using hz

/-- Every nonzero double actual coefficient has at least the sum of the three
charge energies minus the two signed mode shifts. Inputs may mix energies. -/
theorem actual_product_coefficient_energy_le (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (m n : ℤ) (T : Exponent D)
    (hne : (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T ≠ 0) :
    chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2 ≤
      chargeEnergy D (α + (β + γ)) + oscillatorEnergy T := by
  by_contra h
  exact hne (double_coefficient_zero_below_charge D J hJG hGJ α β γ u v w m n T
    (lt_of_not_ge h))

/-- The actual factorial test functional, complex-linear in the tested state. -/
def readout (D : LatticeData) (p : Oscillator D) : Oscillator D →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ (FactorialFockMetric.embedding (Index D) p)).comp
    (FactorialFockMetric.embedding (Index D))

/-- Maximum oscillator energy in the finite test state; the empty maximum is zero. -/
def testEnergy (D : LatticeData) (p : Oscillator D) : ℕ := by
  classical
  exact p.support.sup oscillatorEnergy

/-- The exact integer cutoff, including all three clearing shifts. -/
def degreeBound (D : LatticeData) (α β γ : Charge D)
    (A B N : ℕ) (p : Oscillator D) : ℤ :=
  (A + B + N + testEnergy D p : ℕ) + chargeEnergy D (α + (β + γ)) -
    chargeEnergy D α - chargeEnergy D β - chargeEnergy D γ

private theorem readout_zero_of_above (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w p : Oscillator D) (m n : ℤ)
    (low : chargeEnergy D (α + (β + γ)) + testEnergy D p <
      chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2) :
    readout D p (canonical D α (β + γ) u m (canonical D β γ v n w)) = 0 := by
  classical
  change CanonicalOccupationSewing.H D p _ = 0
  rw [inner_coefficient_expansion]
  apply Finset.sum_eq_zero
  intro T hT
  have hE : oscillatorEnergy T ≤ testEnergy D p := Finset.le_sup hT
  rw [double_coefficient_zero_below_charge D J hJG hGJ α β γ u v w m n T (by omega)]
  exact mul_zero _

/-- A common actual vector numerator has no tested coefficient above the
explicit energy cutoff. The clearing summation index cancels from the bound. -/
theorem scalar_numerator_support (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (N A B : ℕ)
    (P : MvPowerSeries (Fin 2) (Oscillator D))
    (common : ∀ a b : ℤ,
      clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b)
    (p : Oscillator D) (d : Fin 2 →₀ ℕ)
    (hne : MvPowerSeries.coeff d (mapSeries (readout D p) P) ≠ 0) :
    (d.degree : ℤ) ≤ degreeBound D α β γ A B N p := by
  classical
  by_contra h
  have hd : d = powerIndex (d 0) (d 1) := by
    ext i
    fin_cases i <;> simp [powerIndex]
  have hdeg : d.degree = d 0 + d 1 := by
    rw [Finsupp.degree_eq_sum]
    exact Fin.sum_univ_two _
  have hc := common (d 0) (d 1)
  rw [extend, if_pos (by constructor <;> positivity)] at hc
  simp only [Int.toNat_natCast, ← hd] at hc
  apply hne
  change readout D p (MvPowerSeries.coeff d P) = 0
  rw [← hc]
  simp only [clear, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k hk
  rw [product, readout_zero_of_above D J hJG hGJ α β γ u v w p _ _ (by
    unfold degreeBound at h
    rw [hdeg] at h
    push_cast at h
    omega), smul_zero]

end
end D5.S3.VertexAlgebra.LatticeSectorScalarNumerator
