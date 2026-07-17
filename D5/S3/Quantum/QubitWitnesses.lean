/- GID: D5/S3/Quantum/QubitWitnesses
   generality: G
   mirror-B: D5/B/S3/Quantum/QubitWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize explicit qubit incompatibility, entanglement, and dephasing witnesses. -/

import D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.QubitWitnesses

open D5.S3.Quantum.FiniteDimensional

/-- A state vector for a two-dimensional complex Hilbert space. -/
abbrev QubitState := Fin 2 → ℂ

/-- The Pauli `X` and `Z` observables have no nonzero common eigenvector. -/
theorem pauli_observables_have_no_common_eigenvector
    (psi : QubitState) (x z : ℂ)
    (hX : Matrix.mulVec qubitX psi = x • psi)
    (hZ : Matrix.mulVec qubitZ psi = z • psi) :
    psi = 0 := by
  have hX0 : psi 1 = x * psi 0 := by
    simpa [Matrix.mulVec, dotProduct, qubitX, Fin.sum_univ_two] using congrFun hX 0
  have hX1 : psi 0 = x * psi 1 := by
    simpa [Matrix.mulVec, dotProduct, qubitX, Fin.sum_univ_two] using congrFun hX 1
  have hZ0 : psi 0 = z * psi 0 := by
    simpa [Matrix.mulVec, dotProduct, qubitZ, Fin.sum_univ_two] using congrFun hZ 0
  have hZ1 : -psi 1 = z * psi 1 := by
    simpa [Matrix.mulVec, dotProduct, qubitZ, Fin.sum_univ_two] using congrFun hZ 1
  have hPsi0 : psi 0 = 0 := by
    by_contra hPsi0
    have hPsi1 : psi 1 ≠ 0 := by
      intro hPsi1
      rw [hPsi1, mul_zero] at hX1
      exact hPsi0 hX1
    have hZOne : z = 1 := by
      have hProduct : (z - 1) * psi 0 = 0 := by
        calc
          (z - 1) * psi 0 = z * psi 0 - psi 0 := by ring
          _ = 0 := by rw [← hZ0]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hPsi0)
    have hNeg : -psi 1 = psi 1 := by simpa [hZOne] using hZ1
    have hPsi1Zero : psi 1 = 0 := by
      linear_combination (-1 / 2 : ℂ) * hNeg
    exact hPsi1 hPsi1Zero
  have hPsi1 : psi 1 = 0 := by simpa [hPsi0] using hX0
  funext i
  fin_cases i
  · exact hPsi0
  · exact hPsi1

/-- Coefficients of a simple tensor in the standard two-qubit basis. -/
def productCoefficients (left right : QubitState) : QubitMatrix :=
  fun i j => left i * right j

/-- The unnormalized Bell coefficient matrix for `|00> + |11>`. -/
def bellCoefficients : QubitMatrix := !![1, 0; 0, 1]

/-- The Bell coefficient matrix cannot be factored as a simple tensor. -/
theorem bell_coefficients_are_not_product :
    ¬ ∃ left right, productCoefficients left right = bellCoefficients := by
  rintro ⟨left, right, hProduct⟩
  have h00 : left 0 * right 0 = 1 := by
    simpa [productCoefficients, bellCoefficients] using
      congrFun (congrFun hProduct 0) 0
  have h01 : left 0 * right 1 = 0 := by
    simpa [productCoefficients, bellCoefficients] using
      congrFun (congrFun hProduct 0) 1
  have h11 : left 1 * right 1 = 1 := by
    simpa [productCoefficients, bellCoefficients] using
      congrFun (congrFun hProduct 1) 1
  have hLeft0 : left 0 ≠ 0 := by
    intro hLeft0
    rw [hLeft0, zero_mul] at h00
    exact zero_ne_one h00
  have hRight1 : right 1 = 0 :=
    (mul_eq_zero.mp h01).resolve_left hLeft0
  rw [hRight1, mul_zero] at h11
  exact zero_ne_one h11

/-- A real coherence-retention coefficient between zero and one. -/
abbrev DampingCoefficient := Set.Icc (0 : ℝ) 1

/-- Real phase damping preserves diagonal entries and scales off-diagonal entries. -/
def phaseDamping (c : DampingCoefficient) (rho : QubitMatrix) : QubitMatrix :=
  fun i j => if i = j then rho i j else (((c : ℝ) : ℂ) * rho i j)

/-- Repeated application of the same phase-damping map. -/
def phaseDampingIterate (c : DampingCoefficient) : ℕ → QubitMatrix → QubitMatrix
  | 0, rho => rho
  | Nat.succ N, rho => phaseDamping c (phaseDampingIterate c N rho)

/-- Entries of an iterated phase-damping map. -/
theorem phaseDampingIterate_apply (c : DampingCoefficient) (N : ℕ)
    (rho : QubitMatrix) (i j : Fin 2) :
    phaseDampingIterate c N rho i j =
      if i = j then rho i j else (((c : ℝ) : ℂ) ^ N * rho i j) := by
  induction N generalizing i j with
  | zero => simp [phaseDampingIterate]
  | succ N ih =>
      by_cases h : i = j
      · subst j
        simp [phaseDampingIterate, phaseDamping, ih]
      · rw [phaseDampingIterate, phaseDamping, if_neg h, ih, if_neg h]
        simp only [pow_succ]
        simp [h]
        ring

/-- The density matrix of the equal superposition in the standard basis. -/
noncomputable def equalSuperpositionDensity : QubitMatrix :=
  !![(1 : ℂ) / 2, (1 : ℂ) / 2; (1 : ℂ) / 2, (1 : ℂ) / 2]

/-- Repeated real phase damping leaves both populations at one half and scales
the two coherence entries by exactly `c ^ N`. -/
theorem equal_superposition_phase_damping_certificate
    (c : DampingCoefficient) (N : ℕ) :
    let rhoN := phaseDampingIterate c N equalSuperpositionDensity
    rhoN 0 0 = (1 : ℂ) / 2 ∧
      rhoN 1 1 = (1 : ℂ) / 2 ∧
      rhoN 0 1 = (1 : ℂ) / 2 * (((c : ℝ) : ℂ) ^ N) ∧
      rhoN 1 0 = (1 : ℂ) / 2 * (((c : ℝ) : ℂ) ^ N) := by
  simp [phaseDampingIterate_apply, equalSuperpositionDensity, mul_comm]

end D5.S3.Quantum.QubitWitnesses
