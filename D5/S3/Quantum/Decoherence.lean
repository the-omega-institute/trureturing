/- GID: D5/S3/Quantum/Decoherence
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize composition and fixed points of qubit phase damping. -/

import D5.S3.Quantum.QubitWitnesses

namespace D5.S3.Quantum.Decoherence

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- The product of two real coherence-retention coefficients. -/
def dampingProduct (c d : DampingCoefficient) : DampingCoefficient :=
  ⟨(c : Real) * (d : Real),
    mul_nonneg c.property.1 d.property.1,
    calc
      (c : Real) * (d : Real) ≤ 1 * (d : Real) :=
        mul_le_mul_of_nonneg_right c.property.2 d.property.1
      _ ≤ 1 := by simpa using d.property.2⟩

/-- Composing phase-damping maps multiplies their retention coefficients. -/
theorem phase_damping_composition (c d : DampingCoefficient) (rho : QubitMatrix) :
    phaseDamping c (phaseDamping d rho) = phaseDamping (dampingProduct c d) rho := by
  funext i j
  by_cases h : i = j
  · simp [phaseDamping, h]
  · simp [phaseDamping, dampingProduct, h, mul_assoc]

/-- Nontrivial phase damping fixes exactly the diagonal matrices. -/
theorem phase_damping_fixed_iff_diagonal (c : DampingCoefficient)
    (hCoefficient : (c : Real) ≠ 1) (rho : QubitMatrix) :
    phaseDamping c rho = rho ↔ ∀ i j, i ≠ j -> rho i j = 0 := by
  constructor
  · intro hFixed i j hOffDiagonal
    have hEntry := congrFun (congrFun hFixed i) j
    rw [phaseDamping, if_neg hOffDiagonal] at hEntry
    have hCoefficientComplex : ((c : Real) : Complex) ≠ 1 := by
      exact_mod_cast hCoefficient
    have hProduct : ((((c : Real) : Complex) - 1) * rho i j) = 0 := by
      calc
        (((c : Real) : Complex) - 1) * rho i j =
            ((c : Real) : Complex) * rho i j - rho i j := by ring
        _ = 0 := sub_eq_zero.mpr hEntry
    exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr hCoefficientComplex)
  · intro hDiagonal
    funext i j
    by_cases hOffDiagonal : i = j
    · simp [phaseDamping, hOffDiagonal]
    · simp [phaseDamping, hOffDiagonal, hDiagonal i j hOffDiagonal]

/-- Phase damping transported through a coordinate equivalence records in that basis. -/
def phaseDampingInBasis (coordinates : QubitMatrix ≃ QubitMatrix)
    (c : DampingCoefficient) (rho : QubitMatrix) : QubitMatrix :=
  coordinates.symm (phaseDamping c (coordinates rho))

/-- A nontrivial transported damping channel fixes exactly the matrices diagonal in
the coordinates selected by its record rule. -/
theorem phase_damping_in_basis_fixed_iff (coordinates : QubitMatrix ≃ QubitMatrix)
    (c : DampingCoefficient) (hCoefficient : (c : Real) ≠ 1) (rho : QubitMatrix) :
    phaseDampingInBasis coordinates c rho = rho ↔
      ∀ i j, i ≠ j -> coordinates rho i j = 0 := by
  unfold phaseDampingInBasis
  rw [coordinates.symm_apply_eq]
  exact phase_damping_fixed_iff_diagonal c hCoefficient (coordinates rho)

end D5.S3.Quantum.Decoherence
