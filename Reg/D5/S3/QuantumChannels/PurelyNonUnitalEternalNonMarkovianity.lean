import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the qubit depolarizing channel's CPTP property. -/

namespace Reg.D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity

open _root_.D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
open _root_.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound (depolarized)
open _root_.D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the channel itself as its real mixing parameter varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := MatrixMap (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ eta => depolarized (d := 2) LinearMap.id (1 - eta))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both bounds and the full completely positive, trace-preserving law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (eta : ℝ) (_h0 : 0 ≤ eta) (_h1 : eta ≤ 1),
    IsCPTP (R.readout () () eta)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := (h 1 (by norm_num) (by norm_num)).2 (1 : Matrix (Fin 2) (Fin 2) ℂ)
  change Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.trace 1 at ht
  norm_num at ht

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun N : MatrixMap (Fin 2) (Fin 2) ℂ =>
    N !![0, 1; 0, 0] 0 1) he
  norm_num [actual, realize, depolarized, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,
    Matrix.trace, Fin.sum_univ_two] at hc

def source_registration : Registration arena (type_of% @dep_cptp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dep_cptp, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dep_cptp) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity.source_registration
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
    (fun _ _ eta => depolarized (d := 2) LinearMap.id (1 - eta)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
    definition := none
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
end Reg.D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
