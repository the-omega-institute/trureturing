import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
import Reg.Support.DependentFamily

/-! Source-bound audit of conjugation of a rank-one operator. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility

open _root_.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace KetbraStar

abbrev signature : Signature where
  Params := Σ n : Type u, n → ℂ
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => (ketbra p.2 w)ᴴ) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n] (v w : n → ℂ),
    r.readout () ⟨n, v⟩ w = ketbra w v

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance
    (fun _ => 1) (fun _ => 1)
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) hh
  simp [rejected, realize, ketbra, Matrix.vecMulVec_apply] at he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, fun _ => 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) h
  simp [actual, realize, ketbra, Matrix.vecMulVec_apply] at he

def source_registration : Registration arena.{u} (type_of% (@ketbra_star.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ketbra_star, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ketbra_star.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KetbraStar.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KetbraStar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

run_cmd do
  let env ← Lean.getEnv
  for name in [`D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.ketbra_star,
      `D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.trace_pairing_ext,
      `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KetbraStar.registration] do
    if let some info := env.find? name then
      Lean.logInfo m!"UNIVERSE_PARAMETERS {name}: {info.levelParams}"

end KetbraStar
end
end Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
