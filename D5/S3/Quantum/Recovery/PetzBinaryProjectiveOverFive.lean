/- GID: D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.claim; result=D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.result; claim=D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.claim
   digest: Coefficient five fails for ordinary Petz recovery after binary projective measurement. -/

import D5.S3.Quantum.Measurement.Auric.CoordinatePinching
import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Ordinary Petz recovery for faithful inputs to a binary projective measurement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive

noncomputable section

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Recovery.ReferencePetzChannel
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.QubitNormalFormState
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
  (cfc_diagonal)

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
private theorem projectors_hermitian (i : Fin 2) : (projector i)ᴴ = projector i :=
  ((coordinatePVM (id : Fin 2 → Fin 2)).hermitian i).eq
private theorem projectors_action (X : M₂) :
    (∑ i, projector i * X * (projector i)ᴴ) = diagonal X.diag := by
  simp only [projectors_hermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, coordinatePVM, Matrix.sum_apply,
      diagonal_mul, mul_diagonal]
/-- The computational-basis measurement keeps exactly the diagonal. -/
theorem measurement_action (X : M₂) :
    action measurement X = diagonal X.diag := by
  change CStarMatrix.ofMatrix.symm ((pinchingChannel (coordinatePVM id)).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix X)) = _
  rw [pinchingChannel_apply]
  have h := projectors_action X
  simp only [projectors_hermitian] at h
  exact h

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
    field_simp [hn] <;> ring_nf <;> rw [hs]

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

/-- The measurement probabilities of the reference. -/
def probability (σ : Qubit) (i : Fin 2) : ℝ := (raw σ i i).re
private theorem probability_pos (σ : Qubit) (hσ : (raw σ).PosDef) (i : Fin 2) :
    0 < probability σ i :=
  (Complex.pos_iff.mp (hσ.diag_pos (i := i))).1
private theorem measured_reference (σ : Qubit) (hσ : (raw σ).PosDef) :
    raw (measurement.mapState σ) = realDiagonal (probability σ) := by
  change action measurement (raw σ) = _
  rw [measurement_action]
  congr 1
  funext i
  apply Complex.ext
  · exact rfl
  · exact (Complex.pos_iff.mp (hσ.diag_pos (i := i))).2.symm

/-- The ordinary Petz action in the physical computational basis. -/
def ordinaryAction (σ : Qubit) (X : M₂) : M₂ :=
  let S := CFC.sqrt (raw σ)
  S * diagonal (fun i => X i i / (probability σ i : ℂ)) * S
private theorem inverse_root_sandwich (q : Fin 2 → ℝ) (hq : ∀ i, 0 < q i) (X : M₂) :
    diagonal (diag ((realDiagonal fun i => (Real.sqrt (q i))⁻¹) * X *
      (realDiagonal fun i => (Real.sqrt (q i))⁻¹))) =
    diagonal (fun i => X i i / (q i : ℂ)) := by
  congr 1
  funext i
  have hs : (Real.sqrt (q i) : ℂ)^2 = (q i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hq i).le
  simp only [diag_apply, mul_diagonal, diagonal_mul, Complex.ofReal_inv]
  rw [div_eq_mul_inv, ← hs, ← inv_pow]
  ring

-- Factoring the canonical Kraus sum gives the ordinary full-support map.
private theorem ordinary_exists (σ : Qubit) (hσ : (raw σ).PosDef) :
    ∃ R : QuantumChannel (Fin 2) (Fin 2),
      (∀ X : M₂, action R X = ordinaryAction σ X) ∧
      R.mapState (measurement.mapState σ) = σ := by
  let q := probability σ
  let Q := realDiagonal q
  let W := realDiagonal (fun i => (Real.sqrt (q i))⁻¹)
  let S := cfc Real.sqrt (raw σ)
  have hτ : (∑ i, projector i * raw σ * (projector i)ᴴ) = Q := by
    rw [projectors_action, ← measurement_action]
    exact measured_reference σ hσ
  have hP : spectralSupport Q = 1 := by
    change cfc (fun z : ℝ => if z = 0 then 0 else 1) (realDiagonal q) = 1
    rw [cfc_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [q, (probability_pos σ hσ i).ne']
  have hW : spectralInverseSqrt Q = W := by
    change cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (realDiagonal q) = W
    rw [cfc_diagonal]
  obtain ⟨R, hR, hrec⟩ := completed_reference_petz_channel projector
    (pvm_kraus_normalized (coordinatePVM (id : Fin 2 → Fin 2))) σ
  rw [hτ, hP, hW] at hR
  rw [hτ] at hrec
  have hS : S = CFC.sqrt (raw σ) := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ hσ.posSemidef.nonneg]
    change cfc Real.sqrt _ = _
    congr 1
    funext z
    rw [Real.sqrt]
  refine ⟨R, ?_, ?_⟩
  · intro X
    change CStarMatrix.ofMatrix.symm (R.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      CFC.sqrt (raw σ) * _ * CFC.sqrt (raw σ)
    rw [← hS, hR X]
    simp only [sub_self, zero_mul, Matrix.trace_zero, zero_smul, add_zero,
      projectors_hermitian]
    calc
      _ = S * (∑ i, projector i * (W * X * W) * (projector i)ᴴ) * S := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, projectors_hermitian, Matrix.mul_assoc, S]
      _ = _ := by
        rw [projectors_action, inverse_root_sandwich q (probability_pos σ hσ)]
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change action R (raw (measurement.mapState σ)) = raw σ
    rw [measured_reference σ hσ]
    exact hrec

/-- The actual finite trace-log loss across the projective channel. -/
def loss (ρ σ : Qubit) : ℝ :=
  finiteTraceLogRelativeEntropy ρ σ -
    finiteTraceLogRelativeEntropy (measurement.mapState ρ) (measurement.mapState σ)

/-- The squared full trace norm of the ordinary Petz recovery error. -/
def errorSq (ρ σ : Qubit) : ℝ :=
  traceNorm (raw ρ - ordinaryAction σ (raw (measurement.mapState ρ))) ^ 2

/-- The universal coefficient-five estimate for the fixed binary projective measurement. -/
def claim : Prop :=
  ∀ ρ σ : Qubit, (raw ρ).PosDef → (raw σ).PosDef →
    0 < loss ρ σ → errorSq ρ σ ≤ 5 * loss ρ σ
private theorem finite_branches (ρ σ : Qubit) (hσ : (raw σ).PosDef) :
    extendedQuantumRelativeEntropy ρ σ = finiteTraceLogRelativeEntropy ρ σ ∧
    extendedQuantumRelativeEntropy (measurement.mapState ρ) (measurement.mapState σ) =
      finiteTraceLogRelativeEntropy (measurement.mapState ρ) (measurement.mapState σ) :=
  ⟨extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef _ _ hσ),
    extendedQuantumRelativeEntropy_eq_coe_of_support
      (support_of_posDef _ _ (measured_faithful σ hσ))⟩
private def largerEigenvalue (x : ℝ) : ℝ :=
  (1 + Real.sqrt ((4 / 5 : ℝ)^2 + 4*x^2/9)) / 2
private def qOne (x : ℝ) : ℝ := x^4 * (1 + (1 - x^4)*x^2) / (1 + x^6)
private def vWeight (x : ℝ) : ℝ :=
  9/10 + ((2/3)*x^4 - (4/5)*x^6) / (1 + x^6)
private theorem reference_prob_one (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    probability (reference x hx hs) 1 = qOne x := by
  change (rotated (x^3) (1-x^4) (x^4) 1 1).re = _
  change (x^4 + (1-x^4)*(x^3)^2) / (1+(x^3)^2) = _
  unfold qOne
  ring
private theorem reference_prob_zero (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    probability (reference x hx hs) 0 = 1 - qOne x := by
  change (rotated (x^3) (1-x^4) (x^4) 0 0).re = _
  change (1-x^4 + x^4*(x^3)^2) / (1+(x^3)^2) = _
  unfold qOne
  have hd : 1 + x^6 ≠ 0 := by positivity
  rw [show (x^3)^2 = x^6 by ring]
  field_simp
  ring

private theorem measured_input_raw (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    raw (measurement.mapState (input x hx hs)) = realDiagonal ![1/10,9/10] := by
  change action measurement (raw (input x hx hs)) = _
  rw [measurement_action, input_raw]
  congr 1
  funext i
  fin_cases i <;> norm_num [Matrix.diag, Complex.ofReal_div]
private theorem input_entropy (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    vonNeumannEntropy (input x hx hs) = Real.binEntropy (largerEigenvalue x) := by
  rw [input, qubit_state_entropy, largerEigenvalue]
  rw [show (-2*x/3)^2 + (-4/5 : ℝ)^2 = (4/5)^2 + 4*x^2/9 by ring]
private theorem measured_input_entropy (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    vonNeumannEntropy (measurement.mapState (input x hx hs)) = Real.binEntropy (9/10) := by
  have hdisk : (0 : ℝ)^2 + (-4/5 : ℝ)^2 ≤ 1 := by norm_num
  have h : measurement.mapState (input x hx hs) = qubitState 0 (-4/5) hdisk := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change raw (measurement.mapState (input x hx hs)) = qubitMatrix 0 (-4/5)
    rw [measured_input_raw]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [qubitMatrix, Complex.ofReal_div]
  rw [h, qubit_state_entropy]
  norm_num

open scoped Matrix.Norms.L2Operator in
private theorem log_raw (σ : Qubit) :
    CStarMatrix.ofMatrix.symm (CFC.log σ.1) = cfc Real.log (raw σ) := by
  have hp : (raw σ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
  have hlog : CStarMatrix.ofMatrix (cfc Real.log (raw σ)) = CFC.log σ.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log (raw σ)
      ((raw σ).finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      hp.isHermitian (by exact hp.isHermitian)
  simpa only [CStarMatrix.ofMatrix.symm_apply_apply] using
    (congrArg CStarMatrix.ofMatrix.symm hlog).symm

private theorem pair_reference_log (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    (raw (input x hx hs) * cfc Real.log (raw (reference x hx hs))).trace.re =
    (1 - vWeight x) * Real.log (1 - x^4) + vWeight x * Real.log (x^4) := by
  change (_ * cfc Real.log (rotated (x^3) (1-x^4) (x^4))).trace.re = _
  rw [cfc_rotated, input_raw]
  rw [show (1/10 : ℂ) = ((1/10 : ℝ) : ℂ) by norm_num,
    show (9/10 : ℂ) = ((9/10 : ℝ) : ℂ) by norm_num]
  have pair (a b c d e f : ℝ) :
      ((!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] : M₂) *
        !![(d : ℂ), (e : ℂ); (e : ℂ), (f : ℂ)]).trace.re =
        a*d + b*e + (b*e + c*f) := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re]
  unfold rotated
  rw [pair]
  unfold vWeight
  rw [show (x^3)^2 = x^6 by ring]
  have hd : 1 + x^6 ≠ 0 := by positivity
  field_simp
  ring

private theorem pair_measured_log (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    (raw (measurement.mapState (input x hx hs)) *
      cfc Real.log (raw (measurement.mapState (reference x hx hs)))).trace.re =
    (1/10) * Real.log (1-qOne x) + (9/10) * Real.log (qOne x) := by
  rw [measured_input_raw, measured_reference _ (reference_faithful x hx hs), cfc_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [Complex.mul_re, reference_prob_zero, reference_prob_one]
/-- The finite trace-log entropy splits into negative input entropy and the reference-log pairing. -/
theorem trace_log_split (ρ σ : Qubit) :
    finiteTraceLogRelativeEntropy ρ σ =
      -vonNeumannEntropy ρ - (raw ρ * cfc Real.log (raw σ)).trace.re := by
  have h := quantum_relative_entropy_eq_neg_entropy_sub_cross ρ σ
  change finiteTraceLogRelativeEntropy ρ σ = -vonNeumannEntropy ρ -
    (raw ρ * CStarMatrix.ofMatrix.symm (CFC.log σ.1)).trace.re at h
  rwa [log_raw] at h

private theorem loss_identity (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    loss (input x hx hs) (reference x hx hs) =
      -Real.binEntropy (largerEigenvalue x) + Real.binEntropy (9/10) -
      (1 - vWeight x) * Real.log (1-x^4) + (1/10) * Real.log (1-qOne x) -
      (vWeight x - 9/10) * Real.log (x^4) + (9/10) * Real.log (qOne x / x^4) := by
  rw [loss, trace_log_split, trace_log_split, input_entropy, measured_input_entropy,
    pair_reference_log, pair_measured_log, Real.log_div]
  · ring
  · rw [← reference_prob_one x hx hs]
    exact (probability_pos _ (reference_faithful x hx hs) 1).ne'
  · positivity

private theorem binary_self_entropy_bounds (u : ℝ) (hu : 0 < u) (hu' : u ≤ 1 / 10000) :
    let lam := (1 + Real.sqrt ((4 / 5 : ℝ)^2 + 4*u/9))/2
    0 ≤ Real.binEntropy (9 / 10) - Real.binEntropy lam ∧
      Real.binEntropy (9 / 10) - Real.binEntropy lam ≤ (5 / 16)*u := by
  let lam := (1 + Real.sqrt ((4 / 5 : ℝ)^2 + 4*u/9))/2
  change 0 ≤ Real.binEntropy (9 / 10) - Real.binEntropy lam ∧ _
  have hlt : (9 / 10 : ℝ) < lam := by
    have h := Real.sqrt_lt_sqrt (sq_nonneg (4 / 5 : ℝ))
      (show (4 / 5 : ℝ)^2 < (4 / 5 : ℝ)^2 + 4*u/9 by linarith only [hu])
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 5)] at h
    dsimp [lam]
    linarith only [h]
  have hle : lam - 9 / 10 ≤ (5 / 36)*u := by
    have h : Real.sqrt ((4 / 5 : ℝ)^2 + 4*u/9) ≤ 4 / 5 + (5 / 18)*u := by
      apply (Real.sqrt_le_left (by positivity)).2
      nlinarith only [sq_nonneg u]
    dsimp [lam]
    linarith only [h]
  have hlam1 : lam < 1 := by linarith only [hle, hu']
  have hentropy : Real.binEntropy lam < Real.binEntropy (9 / 10) :=
    Real.binEntropy_strictAntiOn (by constructor <;> norm_num)
      (by constructor <;> norm_num <;> linarith only [hlt, hlam1]) hlt
  refine ⟨sub_nonneg.mpr hentropy.le, ?_⟩
  obtain ⟨c, hc, hmean⟩ := exists_hasDerivAt_eq_slope Real.binEntropy
    (fun y : ℝ => Real.log (1-y) - Real.log y) hlt Real.binEntropy_continuous.continuousOn
    (by
      intro y hy
      exact Real.hasDerivAt_binEntropy (by linarith only [hy.1]) (by linarith only [hy.2, hlam1]))
  have hc0 : 0 < c := by linarith only [hc.1]
  have hc1 : 0 < 1-c := by linarith only [hc.2, hlam1]
  have hrat : c/(1-c) < 91/10 := by
    apply (div_lt_iff₀ hc1).2
    linarith only [hc.2, hle, hu']
  have hexp : (91 / 10 : ℝ) < Real.exp (9 / 4) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  have hlog : Real.log c - Real.log (1-c) ≤ 9/4 := by
    rw [← Real.log_div hc0.ne' hc1.ne']
    exact ((Real.log_lt_iff_lt_exp (div_pos hc0 hc1)).2 (hrat.trans hexp)).le
  have hmean' := (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp hmean
  have hmul := mul_le_mul_of_nonneg_right hlog (sub_nonneg.mpr hlt.le)
  have hlammul := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ 9/4 by norm_num)
  change Real.binEntropy (9 / 10) - Real.binEntropy lam ≤ (5 / 16)*u
  nlinarith only [hmean', hmul, hlammul]

private theorem log_one_sub_lower {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
    -2*y ≤ Real.log (1-y) := by
  have hpos : 0 < 1-y := by linarith only [hy']
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hpos)
  rw [show 1 - (1-y)⁻¹ = -y/(1-y) by field_simp [hpos.ne']; ring]
  apply (le_div_iff₀ hpos).2
  nlinarith only [mul_nonneg hy (show 0 ≤ 1-2*y by linarith only [hy'])]

private theorem square_neg_log_bound (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1/100)
    (hu : x^2 ≤ 1/10000) : x^2 * (-Real.log x) ≤ 5/10000 := by
  have h100 : Real.log (100 : ℝ) ≤ 5 := by
    rw [show (100 : ℝ) = 10^2 by norm_num, Real.log_pow, Real.log_ten_eq]
    norm_num
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 100*x by positivity)
  rw [Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) hx.ne'] at h
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
  have h100m := mul_le_mul_of_nonneg_right h100 (sq_nonneg x)
  have hsimp : x^2 * (100*x)⁻¹ = x/100 := by
    field_simp [hx.ne']
    <;> ring
  calc
    x^2 * (-Real.log x) ≤ 4*x^2 + x^2 * (100*x)⁻¹ := by
      nlinarith only [hm, h100m]
    _ ≤ 5/10000 := by rw [hsimp]; linarith only [hu, hx']

private theorem scalar_loss_bounds (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1/100) :
    let u := x^2
    let s := 1 + u*((1-2*u^2)/(1+u^3))
    let q0 := 1-u^2*s
    let gdiff := ((2/3)*u^2-(4/5)*u^3)/(1+u^3)
    let lam := (1 + Real.sqrt ((4 / 5 : ℝ)^2 + 4*u/9))/2
    let δ := Real.binEntropy (9 / 10) - Real.binEntropy lam -
      (1/10-gdiff)*Real.log (1-u^2) + (1/10)*Real.log q0 -
      gdiff*Real.log (u^2) + (9/10)*Real.log s
    u/5 < δ ∧ δ < (12141/10000)*u := by
  dsimp only
  let u := x^2
  let w := (1-2*u^2)/(1+u^3)
  let s := 1+u*w
  let q0 := 1-u^2*s
  let gdiff := ((2/3)*u^2-(4/5)*u^3)/(1+u^3)
  let lam := (1 + Real.sqrt ((4 / 5 : ℝ)^2 + 4*u/9))/2
  let e := Real.binEntropy (9 / 10) - Real.binEntropy lam
  let δ := e - (1/10-gdiff)*Real.log (1-u^2) + (1/10)*Real.log q0 -
    gdiff*Real.log (u^2) + (9/10)*Real.log s
  change u/5 < δ ∧ δ < (12141/10000)*u
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu : u ≤ 1/10000 := by
    dsimp [u]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsmall)
      (show 0 ≤ 1/100 + x by positivity)]
  have hu2 : u^2 ≤ u/10000 := by
    nlinarith only [mul_nonneg hu0.le (sub_nonneg.mpr hu)]
  have hu3 : u^3 ≤ u^2/10000 := by
    nlinarith only [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]
  have hd : 0 < 1 + u^3 := by positivity
  have hwl : (1/2 : ℝ) ≤ w := by
    change (1/2 : ℝ) ≤ (1-2*u^2)/(1+u^3)
    apply (le_div_iff₀ hd).2
    linarith only [hu, hu2, hu3]
  have hwu : w ≤ 1 := by
    change (1-2*u^2)/(1+u^3) ≤ 1
    apply (div_le_iff₀ hd).2
    linarith only [sq_nonneg u, pow_nonneg hu0.le 3]
  have hsl : 1+u/2 ≤ s := by
    change 1+u/2 ≤ 1+u*w
    linarith only [mul_le_mul_of_nonneg_left hwl hu0.le]
  have hsu : s ≤ 1+u := by
    change 1+u*w ≤ 1+u
    linarith only [mul_le_mul_of_nonneg_left hwu hu0.le]
  have hs0 : 0 < s := by linarith only [hsl, hu0]
  have hs2 : s ≤ 2 := by linarith only [hsu, hu]
  have hlogsL : u/4 ≤ Real.log s := by
    apply le_trans _ (Real.one_sub_inv_le_log_of_pos hs0)
    rw [show 1-s⁻¹ = (s-1)/s by field_simp [hs0.ne']]
    apply (le_div_iff₀ hs0).2
    linarith only [hsl, mul_le_mul_of_nonneg_left hs2 (show 0 ≤ u/4 by positivity)]
  have hlogsU : Real.log s ≤ u := by
    linarith only [Real.log_le_sub_one_of_pos hs0, hsu]
  have hq1 : 0 ≤ u^2*s := by positivity
  have hq2 : u^2*s ≤ 2*u^2 := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs2 (sq_nonneg u)
  have hqsmall : u^2*s ≤ 1/2 := by linarith only [hq2, hu2, hu]
  have hlogqL : -4*u^2 ≤ Real.log q0 := by
    change -4*u^2 ≤ Real.log (1-u^2*s)
    linarith only [log_one_sub_lower hq1 hqsmall, hq2]
  have hlogqU : Real.log q0 ≤ 0 := by
    exact Real.log_nonpos (by change 0 ≤ 1-u^2*s; linarith only [hqsmall])
      (by change 1-u^2*s ≤ 1; linarith only [hq1])
  have hgL : 0 ≤ gdiff := by
    change 0 ≤ ((2/3)*u^2-(4/5)*u^3)/(1+u^3)
    apply div_nonneg _ hd.le
    linarith only [hu3, sq_nonneg u]
  have hgU : gdiff ≤ (2/3)*u^2 := by
    change ((2/3)*u^2-(4/5)*u^3)/(1+u^3) ≤ (2/3)*u^2
    apply (div_le_iff₀ hd).2
    nlinarith only [pow_nonneg hu0.le 3, pow_nonneg hu0.le 5]
  have hg' : gdiff ≤ 1/10 := by linarith only [hgU, hu2, hu]
  have hlogu2 : Real.log (1-u^2) ≤ 0 :=
    Real.log_nonpos (by linarith only [hu2, hu]) (by linarith only [sq_nonneg u])
  have hlogu2L : -2*u^2 ≤ Real.log (1-u^2) :=
    log_one_sub_lower (sq_nonneg u) (by linarith only [hu2, hu])
  have htermL : 0 ≤ (1/10-gdiff) * (-Real.log (1-u^2)) :=
    mul_nonneg (sub_nonneg.mpr hg') (neg_nonneg.mpr hlogu2)
  have htermU : (1/10-gdiff) * (-Real.log (1-u^2)) ≤ 2*u^2 :=
    calc
      _ ≤ 1 * (2*u^2) := mul_le_mul (by linarith only [hgL]) (by linarith only [hlogu2L])
        (neg_nonneg.mpr hlogu2) (by norm_num)
      _ = _ := one_mul _
  have hlogid : Real.log (u^2) = 4*Real.log x := by
    rw [show u^2 = x^4 by dsimp [u]; ring, Real.log_pow]
    norm_num
  have hneglog : 0 ≤ -Real.log x :=
    neg_nonneg.mpr (Real.log_nonpos hx.le (by linarith only [hsmall]))
  have hcorL : 0 ≤ gdiff * (-Real.log (u^2)) := by
    rw [hlogid]
    exact mul_nonneg hgL (by linarith only [hneglog])
  have hcorU : gdiff * (-Real.log (u^2)) ≤ ((8/3)*(5/10000))*u := by
    rw [hlogid]
    calc
      _ ≤ ((2/3)*u^2) * (-(4*Real.log x)) :=
        mul_le_mul_of_nonneg_right hgU (by linarith only [hneglog])
      _ = ((8/3)*u) * (u * (-Real.log x)) := by ring
      _ ≤ ((8/3)*u) * (5/10000) :=
        mul_le_mul_of_nonneg_left (square_neg_log_bound x hx hsmall hu) (by positivity)
      _ = _ := by ring
  have ⟨heL, heU⟩ : 0 ≤ e ∧ e ≤ (5/16)*u := binary_self_entropy_bounds u hu0 hu
  change 0 ≤ e at heL
  change e ≤ (5/16)*u at heU
  dsimp only [δ]
  have htermL' : (1/10-gdiff) * Real.log (1-u^2) ≤ 0 := by simpa using htermL
  have htermU' : -(2*u^2) ≤ (1/10-gdiff) * Real.log (1-u^2) := by
    simpa [neg_le] using htermU
  have hcorL' : gdiff * Real.log (u^2) ≤ 0 := by simpa using hcorL
  have hcorU' : -(((8/3)*(5/10000))*u) ≤ gdiff * Real.log (u^2) := by
    simpa [neg_le] using hcorU
  constructor
  · linarith only [heL, htermL', hlogqL, hcorL', hlogsL, hu2, hu0]
  · linarith only [heU, htermU', hlogqU, hcorU', hlogsU, hu2, hu0]

private theorem physical_loss_bounds (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    x^2/5 < loss (input x hx hs) (reference x hx hs) ∧
      loss (input x hx hs) (reference x hx hs) < (12141/10000)*x^2 := by
  let s := 1+x^2*((1-2*x^4)/(1+x^6))
  let g := ((2/3)*x^4-(4/5)*x^6)/(1+x^6)
  have hd : 1+x^6 ≠ 0 := by positivity
  have hq : qOne x = x^4*s := by
    dsimp [qOne, s]
    field_simp [hd]
    ring
  have hratio : qOne x / x^4 = s := by
    rw [hq]
    field_simp [hx.ne']
    <;> ring
  have hv : vWeight x = 9/10 + g := rfl
  have hδ : loss (input x hx hs) (reference x hx hs) =
      Real.binEntropy (9/10) - Real.binEntropy (largerEigenvalue x) -
        (1/10-g)*Real.log (1-x^4) + (1/10)*Real.log (1-x^4*s) -
        g*Real.log (x^4) + (9/10)*Real.log s := by
    rw [loss_identity, hratio, hq, hv]
    ring
  rw [hδ]
  have hb := scalar_loss_bounds x hx hs
  dsimp only at hb
  simpa only [largerEigenvalue, s, g, show (x^2)^2 = x^4 by ring,
    show (x^2)^3 = x^6 by ring] using hb

/-- A real symmetric qubit matrix in the computational basis. -/
def symmetric (d e f : ℝ) : M₂ :=
  !![(d : ℂ), (e : ℂ); (e : ℂ), (f : ℂ)]
private def root00 (x : ℝ) : ℝ :=
  (Real.sqrt (1-x^4) + x^2*(x^3)^2) / (1+(x^3)^2)
private def root01 (x : ℝ) : ℝ :=
  ((Real.sqrt (1-x^4) - x^2)*x^3) / (1+(x^3)^2)
private def root11 (x : ℝ) : ℝ :=
  (x^2 + Real.sqrt (1-x^4)*(x^3)^2) / (1+(x^3)^2)
private theorem reference_root (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    CFC.sqrt (raw (reference x hx hs)) = symmetric (root00 x) (root01 x) (root11 x) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ (reference_faithful x hx hs).posSemidef.nonneg]
  rw [← show Real.sqrt = (fun z => (NNReal.sqrt z.toNNReal : ℝ)) by
    funext z
    rw [Real.sqrt]]
  change cfc Real.sqrt (rotated (x^3) (1-x^4) (x^4)) = _
  have h : Real.sqrt (x^4) = x^2 := by
    rw [show x^4 = (x^2)^2 by ring, Real.sqrt_sq (sq_nonneg x)]
  rw [cfc_rotated, h]
  rfl

/-- Sandwiching a real diagonal matrix by a real symmetric qubit matrix. -/
theorem symmetric_sandwich (a b c u v : ℝ) :
    symmetric a b c * realDiagonal ![u,v] * symmetric a b c =
      symmetric (u*a*a+v*b*b) (u*a*b+v*b*c) (u*b*b+v*c*c) := by
  have hm (i j : Fin 2) : (symmetric a b c * realDiagonal ![u,v]) i j =
      symmetric a b c i j * ((![u,v] : Fin 2 → ℝ) j : ℂ) :=
    Matrix.mul_diagonal _ _ _ _
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, hm, hm]
  fin_cases i <;> fin_cases j <;> simp [symmetric] <;> ring

private def recovered01 (x : ℝ) : ℝ :=
  (1/10)*root00 x*root01 x/(1-qOne x) + (9/10)*root01 x*root11 x/qOne x
private theorem recover_symmetric (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    ∃ d f : ℝ, ordinaryAction (reference x hx hs) (raw (measurement.mapState (input x hx hs))) =
      symmetric d (recovered01 x) f := by
  rw [ordinaryAction, reference_root, measured_input_raw]
  have hd : diagonal (fun i => realDiagonal ![(1/10 : ℝ),9/10] i i /
      (probability (reference x hx hs) i : ℂ)) =
      realDiagonal ![(1/10)/(1-qOne x),(9/10)/qOne x] := by
    congr 1
    funext i
    fin_cases i <;>
      simp [reference_prob_zero, reference_prob_one, Complex.ofReal_div]
  rw [hd, symmetric_sandwich]
  refine ⟨(1/10)/(1-qOne x)*root00 x*root00 x + (9/10)/qOne x*root01 x*root01 x,
    (1/10)/(1-qOne x)*root01 x*root01 x + (9/10)/qOne x*root11 x*root11 x, ?_⟩
  congr 1
  unfold recovered01
  ring

/-- Subtracting real symmetric qubit matrices entrywise. -/
theorem symmetric_sub (a b c d e f : ℝ) :
    symmetric a b c - symmetric d e f = symmetric (a-d) (b-e) (c-f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetric]
/-- The squared full trace norm of a real symmetric traceless qubit matrix. -/
theorem traceless_symmetric_normSq (d e : ℝ) :
    traceNorm (symmetric d e (-d)) ^ 2 = 4*(d^2+e^2) := by
  let c := Real.sqrt (d^2+e^2)
  have hc : c^2 = d^2+e^2 := Real.sq_sqrt (by positivity)
  have hc' : (c : ℂ)^2 = (d : ℂ)^2+(e : ℂ)^2 := by exact_mod_cast hc
  have hg : (symmetric d e (-d))ᴴ * symmetric d e (-d) =
      (c : ℂ) • ((c : ℂ) • (1 : M₂)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetric, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> rw [hc'] <;> ring
  rw [D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_of_scalar_gram _ c
    (Real.sqrt_nonneg _) hg]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  nlinarith [hc]

private theorem error_identity (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    ∃ d : ℝ, errorSq (input x hx hs) (reference x hx hs) =
      4*(d^2+(x/3+recovered01 x)^2) := by
  let ρ := input x hx hs
  let σ := reference x hx hs
  obtain ⟨R, hR, _⟩ := ordinary_exists σ (reference_faithful x hx hs)
  obtain ⟨d, f, hdf⟩ := recover_symmetric x hx hs
  have ht : (symmetric d (recovered01 x) f).trace = 1 := by
    rw [← hdf, ← hR]
    exact (R.mapState (measurement.mapState ρ)).2.2
  have hsum : d+f = 1 := by
    simpa [symmetric, Matrix.trace, Fin.sum_univ_two, ← Complex.ofReal_add] using ht
  have hi : raw ρ = symmetric (1/10) (-(x/3)) (9/10) := by
    rw [input_raw]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [symmetric, Complex.ofReal_div]
  refine ⟨1/10-d, ?_⟩
  change traceNorm (raw ρ - ordinaryAction σ (raw (measurement.mapState ρ))) ^ 2 = _
  rw [hi, hdf, symmetric_sub, show 9/10-f = -(1/10-d) by linarith,
    traceless_symmetric_normSq]
  ring

private theorem recovered_off_diagonal_lower {x q0 : ℝ} (hx : 0 < x)
    (hsmall : x ≤ 1 / 100) (hq0 : 0 < q0) :
    let b := Real.sqrt (1 - x ^ 4)
    let D := 1 + x ^ 6
    let q1 := x ^ 4 * (1 + (1 - x ^ 4) * x ^ 2) / D
    let S00 := (b + x ^ 2 * x ^ 6) / D
    let S01 := (b - x ^ 2) * x ^ 3 / D
    let S11 := (x ^ 2 + b * x ^ 6) / D
    (8997 / 10000) * x < (1 / 10) * S00 * S01 / q0 + (9 / 10) * (S01 * S11) / q1 := by
  let b := Real.sqrt (1 - x ^ 4)
  let D : ℝ := 1 + x ^ 6
  let F : ℝ := 1 + (1 - x ^ 4) * x ^ 2
  let q1 := x ^ 4 * F / D
  let S00 := (b + x ^ 2 * x ^ 6) / D
  let S01 := (b - x ^ 2) * x ^ 3 / D
  let S11 := (x ^ 2 + b * x ^ 6) / D
  change (8997 / 10000) * x < (1 / 10) * S00 * S01 / q0 + (9 / 10) * (S01 * S11) / q1
  have hx2 : x ^ 2 ≤ 1 / 10000 := by
    calc
      x ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hx.le hsmall 2
      _ = _ := by norm_num
  have hx4 : x ^ 4 ≤ 1 / 100000000 := by
    calc
      x ^ 4 ≤ (1 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ hx.le hsmall 4
      _ = _ := by norm_num
  have hx6 : x ^ 6 ≤ 1 / 1000000000000 := by
    calc
      x ^ 6 ≤ (1 / 100 : ℝ) ^ 6 := pow_le_pow_left₀ hx.le hsmall 6
      _ = _ := by norm_num
  have hr : 0 ≤ 1 - x ^ 4 := by linarith only [hx4]
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb_lower : 1 - x ^ 4 ≤ b :=
    Real.le_sqrt_self_iff.mpr (sub_le_self _ (by positivity))
  have hb_gap : (9998 / 10000 : ℝ) < b - x ^ 2 := by
    linarith only [hx2, hx4, hb_lower]
  have hgap : 0 ≤ b - x ^ 2 := le_trans (by norm_num) hb_gap.le
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hD_upper : D ≤ 1000001 / 1000000 := by
    dsimp [D]
    linarith only [hx6]
  have hF_upper : F ≤ 10001 / 10000 := by
    dsimp [F]
    have hprod : (1 - x ^ 4) * x ^ 2 ≤ x ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (sub_le_self (1 : ℝ) (show 0 ≤ x ^ 4 by positivity))
        (show 0 ≤ x ^ 2 by positivity)
      simpa only [one_mul] using h
    linarith only [hprod, hx2]
  have hden : D * F ≤ (1000001 / 1000000) * (10001 / 10000) :=
    mul_le_mul hD_upper hF_upper hF.le (by norm_num)
  have hnum : b - x ^ 2 ≤ (b - x ^ 2) * (1 + b * x ^ 4) :=
    le_mul_of_one_le_right hgap (by linarith only [mul_nonneg hb (pow_nonneg hx.le 4)])
  have hcoeff : (8997 / 10000) < (9 / 10 : ℝ) * ((b - x ^ 2) * (1 + b * x ^ 4)) / (D * F) := by
    apply (lt_div_iff₀ (mul_pos hD hF)).2
    linarith only [hden, hnum, hb_gap]
  have hcancel :
      (9 / 10) * (S01 * S11) / q1 =
        ((9 / 10) * ((b - x ^ 2) * (1 + b * x ^ 4)) / (D * F)) * x := by
    dsimp only [S01, S11, q1]
    field_simp [hD.ne', hF.ne', hx.ne'] <;> ring
  have hfirst : 0 ≤ (1 / 10) * S00 * S01 / q0 := by
    dsimp only [S00, S01]
    positivity
  rw [hcancel]
  exact (mul_lt_mul_of_pos_right hcoeff hx).trans_le (le_add_of_nonneg_left hfirst)

private theorem squared_error_from_off_diagonal {x r : ℝ} (hx : 0 < x)
    (hr : (8997 / 10000) * x < r) : (152 / 25) * x ^ 2 < 4 * (x / 3 + r) ^ 2 := by
  have hlow : (0 : ℝ) ≤ (36991 / 30000) * x := by positivity
  have hgap : (36991 / 30000) * x < x / 3 + r := by linarith only [hr]
  have hsq := (sq_lt_sq₀ hlow (hlow.trans hgap.le)).2 hgap
  have hconstant : (152 / 25 : ℝ) < 4 * (36991 / 30000) ^ 2 := by norm_num
  have hscaled := mul_lt_mul_of_pos_right hconstant (show 0 < x ^ 2 by positivity)
  nlinarith only [hsq, hscaled]

open scoped Matrix.Norms.L2Operator in
private theorem skew_block_norm (c : ℝ) (hc : 0 ≤ c) :
    ‖(!![0, (c : ℂ); -(c : ℂ), 0] : M₂)‖ = c := by
  let K : M₂ := !![0, (c : ℂ); -(c : ℂ), 0]
  change ‖K‖ = c
  have hgram : Kᴴ * K = ((c ^ 2 : ℝ) : ℂ) • (1 : M₂) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.one_apply, pow_two]
  apply (sq_eq_sq₀ (norm_nonneg K) hc).mp
  rw [pow_two ‖K‖, ← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose, hgram,
    norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]

open scoped Matrix.Norms.L2Operator in
private theorem commutator_bound (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) (i : Fin 2) :
    ‖projector i * raw (reference x hx hs) - raw (reference x hx hs) * projector i‖ ≤ x ^ 3 := by
  let c := (1 - x ^ 4 - x ^ 4) * x ^ 3 / (1 + (x ^ 3) ^ 2)
  have h4 : x ^ 4 ≤ (1 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ hx.le hs 4
  have hfactor : 0 ≤ 1 - x ^ 4 - x ^ 4 := by linarith
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (mul_nonneg hfactor (by positivity)) (by positivity)
  have hc' : c ≤ x ^ 3 := by
    calc
      c ≤ (1 - x ^ 4 - x ^ 4) * x ^ 3 :=
        div_le_self (mul_nonneg hfactor (by positivity)) (le_add_of_nonneg_right (sq_nonneg _))
      _ ≤ 1 * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith [pow_nonneg hx.le 4]) (by positivity)
      _ = x ^ 3 := one_mul _
  let A : M₂ := rotated (x ^ 3) (1 - x ^ 4) (x ^ 4)
  let K : M₂ := !![0, (c : ℂ); -(c : ℂ), 0]
  change ‖projector i * A - A * projector i‖ ≤ x ^ 3
  have entry (l j k : Fin 2) : (projector l * A - A * projector l) j k =
      (if j = l then 1 else 0) * A j k - A j k * (if k = l then 1 else 0) := by
    change ((diagonal (fun i => if i = l then 1 else 0) * A) -
      A * diagonal (fun i => if i = l then 1 else 0) : M₂) j k = _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hzero : projector 0 * A - A * projector 0 = K := by
    ext j k
    rw [entry]
    fin_cases j <;> fin_cases k <;> simp [A, K, c, rotated]
  have hone : projector 1 * A - A * projector 1 = -K := by
    ext j k
    rw [entry]
    fin_cases j <;> fin_cases k <;> simp [A, K, c, rotated]
  fin_cases i
  · change ‖projector 0 * A - A * projector 0‖ ≤ _
    rw [hzero, skew_block_norm c hc]
    exact hc'
  · change ‖projector 1 * A - A * projector 1‖ ≤ _
    rw [hone, norm_neg, skew_block_norm c hc]
    exact hc'

private theorem physical_error_bound (x : ℝ) (hx : 0 < x) (hs : x ≤ 1 / 100) :
    (152 / 25) * x ^ 2 < errorSq (input x hx hs) (reference x hx hs) := by
  have hq0 : 0 < 1 - qOne x := by
    rw [← reference_prob_zero x hx hs]
    exact probability_pos _ (reference_faithful x hx hs) 0
  have hr : (8997 / 10000) * x < recovered01 x := by
    have h := recovered_off_diagonal_lower hx hs hq0
    dsimp only at h
    unfold recovered01 root00 root01 root11 qOne
    rw [show (x ^ 3) ^ 2 = x ^ 6 by ring]
    simpa only [mul_assoc, qOne] using h
  obtain ⟨d, hd⟩ := error_identity x hx hs
  rw [hd]
  nlinarith only [sq_nonneg d, squared_error_from_off_diagonal hx hr]

/-- Physical conditions for faithful ordinary Petz recovery through the fixed measurement. -/
def Physical (ρ σ : Qubit) : Prop :=
  (∀ X : M₂, action measurement X = diagonal X.diag) ∧
  (∀ X Y : M₂, (X * action measurement Y).trace = (action measurement X * Y).trace) ∧
  (raw ρ).PosDef ∧ (raw σ).PosDef ∧
  (raw (measurement.mapState ρ)).PosDef ∧ (raw (measurement.mapState σ)).PosDef ∧
  extendedQuantumRelativeEntropy ρ σ = finiteTraceLogRelativeEntropy ρ σ ∧
  extendedQuantumRelativeEntropy (measurement.mapState ρ) (measurement.mapState σ) =
    finiteTraceLogRelativeEntropy (measurement.mapState ρ) (measurement.mapState σ) ∧
  ∃ R : QuantumChannel (Fin 2) (Fin 2), (∀ X : M₂, action R X = ordinaryAction σ X) ∧
    R.mapState (measurement.mapState σ) = σ ∧
    errorSq ρ σ = traceNorm (raw ρ - raw (R.mapState (measurement.mapState ρ))) ^ 2

open scoped Matrix.Norms.L2Operator in
/-- The largest operator norm of the commutator with either projector. -/
def commutatorNorm (σ : Qubit) : ℝ :=
  max ‖projector 0 * raw σ - raw σ * projector 0‖
    ‖projector 1 * raw σ - raw σ * projector 1‖

/-- Uniform loss, full trace error and commutator estimates in the physical family. -/
theorem family_bounds (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100) :
    x ^ 2 / 5 < loss (input x hx hsmall) (reference x hx hsmall) ∧
    loss (input x hx hsmall) (reference x hx hsmall) < (12141 / 10000) * x ^ 2 ∧
    (152 / 25) * x ^ 2 < errorSq (input x hx hsmall) (reference x hx hsmall) ∧
    commutatorNorm (reference x hx hsmall) ≤ x ^ 3 ∧
    Physical (input x hx hsmall) (reference x hx hsmall) := by
  obtain ⟨hlo, hhi⟩ := physical_loss_bounds x hx hsmall
  refine ⟨hlo, hhi, physical_error_bound x hx hsmall, ?_, ?_⟩
  · exact max_le (commutator_bound _ hx hsmall 0) (commutator_bound _ hx hsmall 1)
  · let ρ := input x hx hsmall
    let σ := reference x hx hsmall
    have hρ := input_faithful x hx hsmall
    have hσ := reference_faithful x hx hsmall
    obtain ⟨hin, hout⟩ := finite_branches ρ σ hσ
    obtain ⟨R, hR, hrec⟩ := ordinary_exists σ hσ
    refine ⟨measurement_action, ?_, hρ, hσ, measured_faithful _ hρ,
      measured_faithful _ hσ, hin, hout, R, hR, hrec, ?_⟩
    · intro X Y
      unfold action measurement
      rw [pinchingChannel_apply, pinchingChannel_apply]
      exact (trace_pinching (coordinatePVM id) X Y).symm
    · unfold errorSq
      congr 3
      exact (hR _).symm

/-- The rational entries of the input at a rational parameter. -/
def inputQ (x : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 / 10, -(x / 3); -(x / 3), 9 / 10]

/-- The rational entries of the reference at a rational parameter. -/
def referenceQ (x : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  let t := x ^ 3
  let u := 1 - x ^ 4
  let v := x ^ 4
  !![(u + v * t ^ 2) / (1 + t ^ 2), (u - v) * t / (1 + t ^ 2);
     (u - v) * t / (1 + t ^ 2), (v + u * t ^ 2) / (1 + t ^ 2)]

private theorem inputQ_cast (x : ℚ) (hx : 0 < (x : ℝ)) (hs : (x : ℝ) ≤ 1 / 100) :
    raw (input (x : ℝ) hx hs) = (inputQ x).map (fun q => (q : ℂ)) := by
  rw [input_raw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inputQ, Matrix.map_apply, Complex.ofReal_div, Rat.cast_div]
private theorem referenceQ_cast (x : ℚ) (hx : 0 < (x : ℝ)) (hs : (x : ℝ) ≤ 1 / 100) :
    raw (reference (x : ℝ) hx hs) = (referenceQ x).map (fun q => (q : ℂ)) := by
  change rotated ((x : ℝ) ^ 3) (1 - (x : ℝ) ^ 4) ((x : ℝ) ^ 4) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceQ, rotated, Matrix.map_apply, Complex.ofReal_div, Rat.cast_div]

/-- The rational parameter sequence, beginning at the explicit parameter 1/100. -/
def sequenceParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 100)
private theorem sequenceParameter_pos (n : ℕ) : 0 < sequenceParameter n := by
  unfold sequenceParameter
  positivity
private theorem sequenceParameter_le (n : ℕ) : sequenceParameter n ≤ 1 / 100 := by
  unfold sequenceParameter
  apply one_div_le_one_div_of_le (by norm_num)
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

/-- Rational state pairs with coefficient-five separation and vanishing loss and commutator. -/
structure CounterexampleSequence where
  ρ : ℕ → Qubit
  σ : ℕ → Qubit
  input_entries : ∀ n, raw (ρ n) = (inputQ (1 / ((n : ℚ) + 100))).map (fun q => (q : ℂ))
  reference_entries : ∀ n, raw (σ n) = (referenceQ (1 / ((n : ℚ) + 100))).map (fun q => (q : ℂ))
  physical : ∀ n, Physical (ρ n) (σ n)
  positive_loss : ∀ n, 0 < loss (ρ n) (σ n)
  exceeds_five : ∀ n, 5 * loss (ρ n) (σ n) < errorSq (ρ n) (σ n)
  loss_tendsto : Filter.Tendsto (fun n => loss (ρ n) (σ n)) Filter.atTop (𝓝 0)
  commutator_tendsto : Filter.Tendsto (fun n => commutatorNorm (σ n)) Filter.atTop (𝓝 0)

private theorem sequenceParameter_cast (n : ℕ) :
    ((1 / ((n : ℚ) + 100) : ℚ) : ℝ) = sequenceParameter n := by
  simp [sequenceParameter]

open scoped Matrix.Norms.L2Operator in
/-- The sequence begins at the rational witness x = 1/100 with h = 1/10000. -/
def counterexamples : CounterexampleSequence := by
  let ρ := fun n => input (sequenceParameter n) (sequenceParameter_pos n) (sequenceParameter_le n)
  let σ := fun n => reference (sequenceParameter n) (sequenceParameter_pos n)
    (sequenceParameter_le n)
  let bounds := fun n => family_bounds (sequenceParameter n) (sequenceParameter_pos n)
    (sequenceParameter_le n)
  have hseq : Filter.Tendsto sequenceParameter Filter.atTop (𝓝 0) := by
    have ht := (Filter.tendsto_add_atTop_iff_nat 100).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    unfold sequenceParameter
    simpa only [Nat.cast_add, Nat.cast_ofNat] using ht
  refine ⟨ρ, σ, ?_, ?_, fun n => (bounds n).2.2.2.2, ?_, ?_, ?_, ?_⟩
  · intro n
    have hp : 0 < ((1 / ((n : ℚ) + 100) : ℚ) : ℝ) :=
      (sequenceParameter_cast n).symm ▸ sequenceParameter_pos n
    have hl : ((1 / ((n : ℚ) + 100) : ℚ) : ℝ) ≤ 1 / 100 :=
      (sequenceParameter_cast n).symm ▸ sequenceParameter_le n
    simpa only [ρ, sequenceParameter_cast] using inputQ_cast _ hp hl
  · intro n
    have hp : 0 < ((1 / ((n : ℚ) + 100) : ℚ) : ℝ) :=
      (sequenceParameter_cast n).symm ▸ sequenceParameter_pos n
    have hl : ((1 / ((n : ℚ) + 100) : ℚ) : ℝ) ≤ 1 / 100 :=
      (sequenceParameter_cast n).symm ▸ sequenceParameter_le n
    simpa only [σ, sequenceParameter_cast] using referenceQ_cast _ hp hl
  · intro n
    exact lt_trans (div_pos (pow_pos (sequenceParameter_pos n) 2) (by norm_num)) (bounds n).1
  · intro n
    have hsq : 0 < sequenceParameter n ^ 2 := pow_pos (sequenceParameter_pos n) 2
    linarith only [(bounds n).2.1, (bounds n).2.2.1, hsq]
  · have ht : Filter.Tendsto (fun n : ℕ => (12141 / 10000 : ℝ) * sequenceParameter n ^ 2)
        Filter.atTop (𝓝 0) := by
      simpa using (hseq.pow 2).const_mul (12141 / 10000 : ℝ)
    refine Filter.Tendsto.squeeze (g := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds ht ?_ ?_
    · intro n
      exact (show 0 ≤ sequenceParameter n ^ 2 / 5 by positivity).trans (bounds n).1.le
    · intro n
      exact (bounds n).2.1.le
  · have ht : Filter.Tendsto (fun n : ℕ => sequenceParameter n ^ 3)
        Filter.atTop (𝓝 0) := by
      simpa using hseq.pow 3
    refine Filter.Tendsto.squeeze (g := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds ht ?_ ?_
    · intro n
      unfold commutatorNorm
      exact le_trans (norm_nonneg (projector 0 * raw (σ n) - raw (σ n) * projector 0))
        (le_max_left _ _)
    · intro n
      exact (bounds n).2.2.2.1

/-- The faithful rational states at (x=1/100) refute the coefficient-five estimate. -/
theorem result : ¬ claim := by
  intro h
  let w := counterexamples
  have hp := w.physical 0
  exact (not_le_of_gt (w.exceeds_five 0))
    (h (w.ρ 0) (w.σ 0) hp.2.2.1 hp.2.2.2.1 (w.positive_loss 0))

#print axioms family_bounds
#print axioms counterexamples
#print axioms result

end

end D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
