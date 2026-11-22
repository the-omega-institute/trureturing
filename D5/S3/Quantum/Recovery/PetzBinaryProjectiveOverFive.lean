/- GID: D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient five fails for ordinary Petz recovery after binary projective measurement. -/

import D5.S3.Quantum.Measurement.Auric.CoordinatePinching
import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

/-! Ordinary Petz recovery for faithful inputs to a binary projective measurement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive

noncomputable section

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Recovery.ReferencePetzChannel
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.QubitNormalFormState
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
  (cfc_diagonal cfc_log_diagonal)

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℂ
local notation "Qubit" => DensityState (Fin 2)

/-- The two computational-basis projectors. -/
def projector (i : Fin 2) : M₂ := (coordinatePVM (id : Fin 2 → Fin 2)).proj i

/-- The nonselective computational-basis measurement with diagonal output. -/
def measurement : QuantumChannel (Fin 2) (Fin 2) :=
  pinchingChannel (coordinatePVM (id : Fin 2 → Fin 2))

private abbrev raw (ρ : Qubit) : M₂ := CStarMatrix.ofMatrix.symm ρ.1

private abbrev action (Φ : QuantumChannel (Fin 2) (Fin 2)) (X : M₂) : M₂ :=
  CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

private theorem projectors_normalized : (∑ i, (projector i)ᴴ * projector i) = 1 := by
  let P := coordinatePVM (id : Fin 2 → Fin 2)
  change (∑ i, (P.proj i)ᴴ * P.proj i) = 1
  simp_rw [(P.hermitian _).eq, P.idempotent]
  exact P.complete

private theorem projectors_hermitian (i : Fin 2) : (projector i)ᴴ = projector i :=
  ((coordinatePVM (id : Fin 2 → Fin 2)).hermitian i).eq

private theorem projectors_action (X : M₂) :
    (∑ i, projector i * X * (projector i)ᴴ) = diagonal X.diag := by
  simp only [projectors_hermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, coordinatePVM, Matrix.sum_apply,
      diagonal_mul, mul_diagonal]

private theorem measurement_action (X : M₂) :
    action measurement X = diagonal X.diag := by
  change CStarMatrix.ofMatrix.symm ((pinchingChannel (coordinatePVM id)).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix X)) = _
  rw [pinchingChannel_apply]
  have h := projectors_action X
  simp only [projectors_hermitian] at h
  exact h

private theorem measurement_adjoint (X Y : M₂) :
    (X * action measurement Y).trace = (action measurement X * Y).trace := by
  rw [measurement_action, measurement_action]
  simp [Matrix.trace, Matrix.diag, mul_diagonal, diagonal_mul]

private abbrev realDiagonal (a : Fin 2 → ℝ) : M₂ := diagonal fun i => (a i : ℂ)

private def rotation (t : ℝ) : M₂ :=
  !![((1 / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ), ((-t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ);
     ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ), ((1 / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)]

private theorem rotation_unitary (t : ℝ) : rotation t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hs : (Real.sqrt (1 + t ^ 2) : ℂ) ^ 2 = 1 + (t : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
  have hn : (Real.sqrt (1 + t ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity : 0 < 1 + t ^ 2)).ne'
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_div] <;>
    field_simp [hn] <;> ring_nf <;> rw [hs] <;> ring

private def rotated (t u v : ℝ) : M₂ :=
  !![(((u + v * t^2) / (1 + t^2) : ℝ) : ℂ), ((((u-v)*t) / (1+t^2) : ℝ) : ℂ);
     ((((u-v)*t) / (1+t^2) : ℝ) : ℂ), (((v + u * t^2) / (1 + t^2) : ℝ) : ℂ)]

private theorem rotated_diagonal (t u v : ℝ) :
    rotated t u v = rotation t * realDiagonal ![u,v] * (rotation t)ᴴ := by
  have hs : (Real.sqrt (1 + t ^ 2) : ℂ) ^ 2 = 1 + (t : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
  have hn : (Real.sqrt (1 + t ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity : 0 < 1 + t ^ 2)).ne'
  have hd : 1 + (t : ℂ) ^ 2 ≠ 0 := by rw [← hs]; exact pow_ne_zero _ hn
  have hm (i j : Fin 2) :
      (rotation t * realDiagonal ![u,v]) i j = rotation t i j * ((![u,v] : Fin 2 → ℝ) j : ℂ) :=
    Matrix.mul_diagonal _ _ _ _
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, hm, hm]
  fin_cases i <;> fin_cases j <;>
    simp [rotated, rotation, Matrix.conjTranspose_apply, Complex.ofReal_div] <;>
    rw [← hs] <;> field_simp [hn] <;> ring

private theorem cfc_rotated (f : ℝ → ℝ) (t u v : ℝ) :
    cfc f (rotated t u v) = rotated t (f u) (f v) := by
  let U : Matrix.unitaryGroup (Fin 2) ℂ := ⟨rotation t, rotation_unitary t⟩
  rw [rotated_diagonal, rotated_diagonal]
  change cfc f (U.val * realDiagonal ![u,v] * (↑(U⁻¹) : M₂)) =
    U.val * realDiagonal ![f u,f v] * (↑(U⁻¹) : M₂)
  rw [Matrix.cfc_conj_unitary f U, cfc_diagonal]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem rotated_posDef (t u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (rotated t u v).PosDef := by
  have hd : (realDiagonal ![u,v]).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_lt_real.mpr hu
    · exact Complex.zero_lt_real.mpr hv
  have hU : IsUnit (rotation t) := Unitary.isUnit_coe
    (U := (⟨rotation t, rotation_unitary t⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
  rw [rotated_diagonal, ← Matrix.star_eq_conjTranspose]
  exact (hU.posDef_star_right_conjugate_iff).mpr hd

private theorem rotated_trace (t u v : ℝ) : (rotated t u v).trace = ((u+v : ℝ) : ℂ) := by
  rw [rotated_diagonal, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have h := Matrix.mem_unitaryGroup_iff'.mp (rotation_unitary t)
  rw [show (rotation t)ᴴ * rotation t = 1 from h, Matrix.one_mul]
  simp [Matrix.trace_diagonal, Fin.sum_univ_two]

private theorem square_le {x : ℝ} (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    x ^ 2 ≤ 1 / 10000 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ x + 1/100 by positivity)]

private theorem rho_disk {x : ℝ} (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    (-2*x/3)^2 + (-4/5 : ℝ)^2 ≤ 1 := by nlinarith [square_le hx hsmall]

/-- The input of the simultaneous family. -/
def input (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) : Qubit :=
  qubitState (-2*x/3) (-4/5) (rho_disk hx hsmall)

/-- The reference has eigenvalues (1-x^4,x^4), with rotation parameter (x^3). -/
def reference (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) : Qubit := by
  have hx4 : x^4 < 1 := by
    have h := mul_nonneg (sub_nonneg.mpr (square_le hx hsmall))
      (show 0 ≤ x^2 + 1/10000 by positivity)
    nlinarith
  exact ⟨CStarMatrix.ofMatrix (rotated (x^3) (1-x^4) (x^4)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (rotated_posDef _ _ _ (by linarith) (by positivity)).posSemidef.nonneg,
    by change (rotated (x^3) (1-x^4) (x^4)).trace = 1; rw [rotated_trace]; simp⟩

private theorem input_raw (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    raw (input x hx hsmall) = !![1/10, ((-(x/3) : ℝ) : ℂ); ((-(x/3) : ℝ) : ℂ), 9/10] := by
  change qubitMatrix (-2*x/3) (-4/5) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitMatrix, Complex.ofReal_div] <;> ring

private theorem input_faithful (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    (raw (input x hx hsmall)).PosDef := by
  have hp : (raw (input x hx hsmall)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (input x hx hsmall).2.1)
  apply hp.posDef_iff_det_ne_zero.mpr
  intro h
  have hh := congrArg Complex.re h
  rw [input_raw] at hh
  simp [Matrix.det_fin_two, Complex.ofReal_div, Complex.mul_re] at hh
  nlinarith [square_le hx hsmall]

private theorem reference_faithful (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    (raw (reference x hx hsmall)).PosDef := by
  change (rotated (x^3) (1-x^4) (x^4)).PosDef
  apply rotated_posDef
  · nlinarith [mul_nonneg (sub_nonneg.mpr (square_le hx hsmall))
      (show 0 ≤ x^2 + 1/10000 by positivity)]
  · positivity

private theorem measured_faithful (ρ : Qubit) (hρ : (raw ρ).PosDef) :
    (raw (measurement.mapState ρ)).PosDef := by
  change (action measurement (raw ρ)).PosDef
  rw [measurement_action]
  exact Matrix.posDef_diagonal_iff.mpr fun _ => hρ.diag_pos

end

end D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
