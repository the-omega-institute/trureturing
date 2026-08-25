/- GID: D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/StaticLossVersusReturnFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two qubit witnesses prove independence, including zero dynamics and nonzero loss. -/

/- Library-search audit trail (2026-08-25):
   * Repository searches of `Quantum/Decoherence` and `QuantumChannels` found no reusable
     diagonal-projection or return-flow-strength interface.
   * Pinned Mathlib search found `Matrix.frobeniusNormedAddCommGroup` and
     `Matrix.frobenius_norm_def`; the latter is the square root of the entrywise square sum.
   * The Lean skill's local smart search returned no exact declaration for the combined claim.
   We use the square sum, the squared Hilbert-Schmidt norm, to keep both witnesses computable. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Decoherence.StaticLossVersusReturnFlow

/-- Real two-by-two matrices suffice for both counterexamples. -/
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- A future dynamics is linear, so the only constant dynamics is the zero map. -/
abbrev Dynamics := QubitMatrix →ₗ[ℝ] QubitMatrix

/-- Retain exactly the visible diagonal record. -/
def diagonalProjection : Dynamics where
  toFun X i j := if i = j then X i j else 0
  map_add' X Y := by
    ext i j
    change (if i = j then (X + Y) i j else 0) =
      (if i = j then X i j else 0) + (if i = j then Y i j else 0)
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  map_smul' c X := by
    ext i j
    change (if i = j then (c • X) i j else 0) =
      c * (if i = j then X i j else 0)
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]

/-- The discarded part `(I - D)X`. -/
def discardedPart (D : Dynamics) (X : QubitMatrix) : QubitMatrix :=
  X - D X

/-- The entrywise square sum, equal to the square of the real Frobenius/HS norm. -/
def hilbertSchmidtSquared (X : QubitMatrix) : ℝ :=
  ∑ i, ∑ j, (X i j) ^ 2

/-- Static loss measured by the squared HS norm of `(I - D)X`. -/
def staticLossSquared (D : Dynamics) (X : QubitMatrix) : ℝ :=
  hilbertSchmidtSquared (discardedPart D X)

/-- Squared strength returned from the discarded part into the visible diagonal record. -/
def returnFlowSquared (D dynamics : Dynamics) (X : QubitMatrix) : ℝ :=
  hilbertSchmidtSquared (D (dynamics (discardedPart D X)))

/-- Send the `(0,1)` discarded entry into the visible `(0,0)` record entry. -/
def offDiagonalReturnDynamics : Dynamics where
  toFun X i j := if i = 0 ∧ j = 0 then X 0 1 else 0
  map_add' X Y := by
    ext i j
    change (if i = 0 ∧ j = 0 then (X + Y) 0 1 else 0) =
      (if i = 0 ∧ j = 0 then X 0 1 else 0) +
        (if i = 0 ∧ j = 0 then Y 0 1 else 0)
    by_cases hij : i = 0 ∧ j = 0
    · simp [hij]
    · simp [hij]
  map_smul' c X := by
    ext i j
    change (if i = 0 ∧ j = 0 then (c • X) 0 1 else 0) =
      c * (if i = 0 ∧ j = 0 then X 0 1 else 0)
    by_cases hij : i = 0 ∧ j = 0
    · simp [hij]
    · simp [hij]

/- Degenerate-input audit: the carrier has exactly two indices, so empty, singleton, and
dimension-zero cases are not inputs to these closed witness theorems. -/
example : Fintype.card (Fin 2) = 2 := by decide

/- A constant linear dynamics must be the zero constant. -/
example (dynamics : Dynamics) (C : QubitMatrix)
    (hconstant : ∀ X, dynamics X = C) : C = 0 := by
  simpa using (hconstant 0).symm

/- Zero dynamics and identity dynamics both return no discarded entry to the diagonal. -/
example (X : QubitMatrix) : returnFlowSquared diagonalProjection 0 X = 0 := by
  simp [returnFlowSquared, hilbertSchmidtSquared, LinearMap.coe_mk]

example (X : QubitMatrix) :
    returnFlowSquared diagonalProjection LinearMap.id X = 0 := by
  have hdiag (Y : QubitMatrix) (i j : Fin 2) :
      diagonalProjection Y i j = if i = j then Y i j else 0 := by
    rfl
  simp [returnFlowSquared, hilbertSchmidtSquared, discardedPart, hdiag,
    Matrix.sub_apply, Fin.sum_univ_two]

example (D dynamics : Dynamics) :
    staticLossSquared D 0 = 0 ∧ returnFlowSquared D dynamics 0 = 0 := by
  simp [staticLossSquared, returnFlowSquared, hilbertSchmidtSquared, discardedPart,
    LinearMap.coe_mk]

example (dynamics : Dynamics) (X : QubitMatrix) :
    staticLossSquared LinearMap.id X = 0 ∧
      returnFlowSquared LinearMap.id dynamics X = 0 := by
  simp [staticLossSquared, returnFlowSquared, hilbertSchmidtSquared, discardedPart,
    LinearMap.coe_mk]

/-- A single off-diagonal entry of size two has squared static loss four, while zero dynamics
has exactly zero return flow. Thus large static loss does not force later return. -/
theorem large_static_loss_with_zero_return :
    ∃ (X : QubitMatrix) (D dynamics : Dynamics),
      D = diagonalProjection ∧
        (1 : ℝ) ≤ staticLossSquared D X ∧
        returnFlowSquared D dynamics X = 0 := by
  let X : QubitMatrix := !![0, 2; 0, 0]
  refine ⟨X, diagonalProjection, 0, rfl, ?_, ?_⟩
  · norm_num [staticLossSquared, hilbertSchmidtSquared, discardedPart,
      X, Matrix.sub_apply, Fin.sum_univ_two,
      show ∀ (Y : QubitMatrix) (i j : Fin 2),
        diagonalProjection Y i j = if i = j then Y i j else 0 from
        fun Y i j => rfl]
  · simp [returnFlowSquared, hilbertSchmidtSquared]

#print axioms large_static_loss_with_zero_return

/-- A single off-diagonal entry of size one half has nonzero squared static loss at most one
quarter, while a linear future dynamics returns it to the visible record with nonzero strength. -/
theorem small_static_loss_with_nonzero_return :
    ∃ (X : QubitMatrix) (D dynamics : Dynamics),
      D = diagonalProjection ∧
        0 < staticLossSquared D X ∧
        staticLossSquared D X ≤ (1 : ℝ) / 4 ∧
        returnFlowSquared D dynamics X ≠ 0 := by
  let X : QubitMatrix := !![0, (1 : ℝ) / 2; 0, 0]
  refine ⟨X, diagonalProjection, offDiagonalReturnDynamics, rfl, ?_, ?_, ?_⟩
  · norm_num [staticLossSquared, hilbertSchmidtSquared, discardedPart,
      X, Matrix.sub_apply, Fin.sum_univ_two,
      show ∀ (Y : QubitMatrix) (i j : Fin 2),
        diagonalProjection Y i j = if i = j then Y i j else 0 from
        fun Y i j => rfl]
  · norm_num [staticLossSquared, hilbertSchmidtSquared, discardedPart,
      X, Matrix.sub_apply, Fin.sum_univ_two,
      show ∀ (Y : QubitMatrix) (i j : Fin 2),
        diagonalProjection Y i j = if i = j then Y i j else 0 from
        fun Y i j => rfl]
  · norm_num [returnFlowSquared, hilbertSchmidtSquared, discardedPart,
      X, Matrix.sub_apply, Fin.sum_univ_two,
      show ∀ (Y : QubitMatrix) (i j : Fin 2),
        diagonalProjection Y i j = if i = j then Y i j else 0 from
        fun Y i j => rfl,
      show ∀ (Y : QubitMatrix) (i j : Fin 2),
        offDiagonalReturnDynamics Y i j = if i = 0 ∧ j = 0 then Y 0 1 else 0 from
        fun Y i j => rfl]

#print axioms small_static_loss_with_nonzero_return

/-- The two squared strengths are logically independent at the concrete large threshold one:
neither large static loss forces nonzero return nor nonzero return forces large static loss. -/
theorem static_loss_and_return_flow_are_logically_independent :
    (¬ ∀ (X : QubitMatrix) (D dynamics : Dynamics),
        D = diagonalProjection →
          (1 : ℝ) ≤ staticLossSquared D X →
          returnFlowSquared D dynamics X ≠ 0) ∧
      (¬ ∀ (X : QubitMatrix) (D dynamics : Dynamics),
        D = diagonalProjection →
          returnFlowSquared D dynamics X ≠ 0 →
          (1 : ℝ) ≤ staticLossSquared D X) := by
  constructor
  · intro h
    obtain ⟨X, D, dynamics, hD, hlarge, hzero⟩ := large_static_loss_with_zero_return
    exact (h X D dynamics hD hlarge) hzero
  · intro h
    obtain ⟨X, D, dynamics, hD, _, hsmall, hreturn⟩ :=
      small_static_loss_with_nonzero_return
    have hlarge := h X D dynamics hD hreturn
    linarith

#print axioms static_loss_and_return_flow_are_logically_independent

end D5.S3.Quantum.Decoherence.StaticLossVersusReturnFlow
