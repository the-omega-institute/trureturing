import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
open _root_.D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section
universe u_1

namespace DiagonalNorm

/-- Sum the absolute diagonal entries over the observed finite index set. -/
abbrev signature : Signature where
  Params := Σ n : Type u_1, n → ℝ
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p indices => ∑ i ∈ indices, |p.2 i|) (fun e => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u_1} [Fintype n] [DecidableEq n] (d : n → ℝ),
    traceNorm (diagonal (fun i => (d i : ℂ))) = R.readout () ⟨n, d⟩ Finset.univ

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have he := h (n := ULift.{u_1} Unit) (fun _ => 1)
  rw [diagonal_norm] at he
  simp [rejected, realize] at he

def source_registration : Registration arena.{u_1} (type_of% @diagonal_norm.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_norm, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, fun _ => 1⟩, ∅, {⟨()⟩}, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diagonal_norm.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.DiagonalNorm.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.DiagonalNorm
      "source_registration"
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
    (realize signature (fun _ p indices => ∑ i ∈ indices, |p.2 i|) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end DiagonalNorm
end
end Reg.D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
