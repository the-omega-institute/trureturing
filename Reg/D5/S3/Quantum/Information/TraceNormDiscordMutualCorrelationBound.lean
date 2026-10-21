import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the trace-norm discord-correlation bound. -/

namespace Reg.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound

open _root_.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
open _root_.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
  (maximalMutualCorrelation localCovariance connectedCorrelation rotateState
    rotated_spin_witness measuredState)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen)
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (unitaryEvolution)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ
local notation "TwoQubit" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Observe maximal mutual correlation as the two-qubit matrix varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := TwoQubit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain both density hypotheses and the full trace-norm discord bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    traceNormDiscord ρ ≤ r.readout () () ρ

private def correlatedState : TwoQubit :=
  diagonal (fun p => if p.1 = p.2 then (1 / 2 : ℂ) else 0)

private theorem correlatedState_positive : correlatedState.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ if i.1 = i.2 then 1 / 2 else 0
  split_ifs <;> norm_num [Complex.nonneg_iff]

private theorem correlatedState_trace : trace correlatedState = 1 := by
  norm_num [correlatedState, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem discord_nonneg (ρ : TwoQubit) : 0 ≤ traceNormDiscord ρ := by
  apply le_csInf
  · exact ⟨_, 1, (1 : Matrix.unitaryGroup (Fin 2) ℂ).property, rfl⟩
  · rintro _ ⟨U, _, rfl⟩
    exact traceNorm_nonneg _

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h correlatedState correlatedState_positive correlatedState_trace
  change traceNormDiscord correlatedState ≤ -1 at hbad
  linarith [discord_nonneg correlatedState]

private theorem correlation_zero : maximalMutualCorrelation (0 : TwoQubit) = 0 := by
  unfold maximalMutualCorrelation
  have hs : {r : ℝ | ∃ a b : Qubit, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      r = ‖localCovariance 0 a b‖} = {0} := by
    ext r
    constructor
    · rintro ⟨a, b, _, _, hr⟩
      simpa [localCovariance] using hr
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      exact ⟨1, 1, norm_one, norm_one, by simp [localCovariance]⟩
  rw [hs, csSup_singleton]

private theorem correlatedState_correlation : 1 ≤ maximalMutualCorrelation correlatedState := by
  have h := rotated_spin_witness correlatedState correlatedState_positive
    correlatedState_trace 1 ![0, 0, 1] ![0, 0, 1]
    (by norm_num [vlen, Fin.sum_univ_three])
    (by norm_num [vlen, Fin.sum_univ_three])
  have hrot : rotateState ((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Qubit)
      correlatedState = correlatedState := by
    simp [rotateState, unitaryEvolution]
  rw [hrot] at h
  norm_num [connectedCorrelation, corr, blochA, blochB, pauli, pauliMatrix, qubitX,
    qubitZ, correlatedState, dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three] at h
  exact h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, correlatedState, ?_⟩
  change maximalMutualCorrelation 0 ≠ maximalMutualCorrelation correlatedState
  rw [correlation_zero]
  linarith [correlatedState_correlation]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ ρ => maximalMutualCorrelation ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
    definition := some {
      owner := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
      name := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
