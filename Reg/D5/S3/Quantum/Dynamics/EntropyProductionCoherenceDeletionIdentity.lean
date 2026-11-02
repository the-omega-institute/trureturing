import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the diagonal logarithm in the pinched-state entropy identity. -/

namespace Reg.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

open _root_.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open _root_.D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (densityMatrix)
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Read the logarithm at the real diagonal entry appearing in the Shannon sum. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

/-- Preserve the original type, dictionaries, state and entire entropy equality. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (rho : DensityState n),
    vonNeumannEntropy (basisPinchingState rho) =
      -(∑ i, (densityMatrix rho i i).re * R.readout () () (densityMatrix rho i i).re)

private def oneState : DensityState (ULift.{u} Unit) :=
  ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag]⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h oneState
  have htrue := von_neumann_entropy_basisPinchingState oneState
  simp [oneState, densityMatrix, rejected, realize] at hbad htrue
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  simp [actual, realize]

def source_registration :
    Registration arena.{u} (type_of% @von_neumann_entropy_basisPinchingState.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@von_neumann_entropy_basisPinchingState, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@von_neumann_entropy_basisPinchingState.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print von_neumann_entropy_basisPinchingState

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
