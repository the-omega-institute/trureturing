import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
import D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound

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
open _root_.D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot
  (local_marginal_correlation_blind_spot)
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

private abbrev correlatedState : TwoQubit :=
  _root_.D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot.classicalCorrelatedDensity

private theorem correlatedState_positive : correlatedState.PosSemidef :=
  (local_marginal_correlation_blind_spot
    2 2 (by omega) (by omega) (by omega)).2.2.2.2.2.2.2.2.1

private theorem correlatedState_trace : trace correlatedState = 1 :=
  (local_marginal_correlation_blind_spot
    2 2 (by omega) (by omega) (by omega)).2.2.2.2.2.2.2.2.2.1

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

theorem dependence : ObservationalDependence signature actual :=
  _root_.Reg.D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.dependence

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
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

namespace SpinSquare
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Qubit) (fun _ => Qubit → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Fin 3 → ℝ,
    R.readout () () (spin c * spin c) ((vlen c ^ 2 : ℝ) • (1 : Qubit))
private theorem rejected_law : ¬ arena.Law rejected := fun h => h 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)
def source_registration : Registration arena (type_of% @spin_square) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spin_square, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spin_square) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.spin_square
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end SpinSquare

namespace SpinHermitian
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Star ℂ) (fun _ => Qubit → Prop)

/-- Read the Hermitian relation at the source scalar conjugation. -/
def actual : Realization signature :=
  realize signature (fun _ _ conjugation => @Matrix.IsHermitian ℂ (Fin 2) conjugation)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ conjugation X => ¬ @Matrix.IsHermitian ℂ (Fin 2) conjugation X)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Fin 3 → ℝ, R.readout () () (inferInstance : Star ℂ) (spin c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (spin_hermitian 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let X : Qubit := fun _ _ => Complex.I
  have hnot : ¬ X.IsHermitian := by
    intro h
    have he := congrArg (fun M : Qubit => M 0 0) h.eq
    change star Complex.I = Complex.I at he
    have him := congrArg Complex.im he
    norm_num [Complex.star_def] at him
  have hyes : @Matrix.IsHermitian ℂ (Fin 2) ⟨id⟩ X := rfl
  refine ⟨(), (inferInstance : Star ℂ), ⟨id⟩, ?_⟩
  intro h
  have he := congrFun h X
  change X.IsHermitian = @Matrix.IsHermitian ℂ (Fin 2) ⟨id⟩ X at he
  exact hnot (Eq.mpr he hyes)

def source_registration : Registration arena (type_of% @spin_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spin_hermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spin_hermitian) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.spin_hermitian
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ conjugation => @Matrix.IsHermitian ℂ (Fin 2) conjugation)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SpinHermitian

namespace SpinAnticommutator
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Qubit) (fun _ => Qubit → Prop)
/-- Read the equality relation on the anticommutator identity. -/
def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ X Y => X ≠ Y) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c d : Fin 3 → ℝ,
    R.readout () () (spin c * spin d + spin d * spin c)
      ((2 * (c ⬝ᵥ d) : ℝ) • (1 : Qubit))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (spin_anticommutator 0 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)
def source_registration : Registration arena (type_of% @spin_anticommutator) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spin_anticommutator, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spin_anticommutator) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound.spin_anticommutator
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms registration

end SpinAnticommutator

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
