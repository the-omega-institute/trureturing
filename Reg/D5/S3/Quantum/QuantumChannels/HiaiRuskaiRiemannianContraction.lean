import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of Hermiticity of real Bloch coordinates. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction

open _root_.D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.Pauli
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the matrix computed from a real Bloch vector. -/
abbrev signature : Signature where
  Params := Unit
  State _ := EuclideanSpace ℝ (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => blochMatrix 1 w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => !![0, 1; 0, 0]) (fun e => nomatch e)

/-- Preserve all three real coordinates and the complete Hermitian predicate. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (w1 w2 w3 : ℝ),
    (r.readout () () (WithLp.toLp 2 ![w1, w2, w3])).IsHermitian

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 0 0).apply 0 1
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), WithLp.toLp 2 ![0, 0, 0], WithLp.toLp 2 ![0, 0, 1], ?_⟩
  intro h
  have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 0 0).re) h
  norm_num [actual, realize, blochMatrix] at he

def source_registration : Registration arena (type_of% @rho_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rho_hermitian, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rho_hermitian) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.source_registration
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
    (fun _ _ w => blochMatrix 1 w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
