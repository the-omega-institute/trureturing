import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
import Reg.Support.DependentFamily

/-! Source-bound audit of the perfect-state-transfer relation of the seven-state walks. -/

namespace Reg.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer

open _root_.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the transfer relation as the walk matrix varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 7) (Fin 7) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 7 → Fin 7 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => PerfectStateTransfer U) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => True) (fun e => nomatch e)

/-- Retain both failures of transfer, varying the first transfer relation. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ r.readout () () Udef 5 0 ∧ ¬ PerfectStateTransfer Udisp 5 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h.1 trivial

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), Udef, Udisp.transpose, ?_⟩
  have htransfer : PerfectStateTransfer Udisp.transpose 5 0 := by
    refine ⟨1, 1, ?_, ?_⟩
    · simpa only [Nat.cast_one] using Complex.norm_natCast 1
    · rw [pow_one, one_smul, Matrix.mulVec_single_one]
      ext j
      fin_cases j <;>
        norm_num [Udisp, Matrix.col_apply, Matrix.transpose_apply, Pi.single_apply]
  intro heq
  exact result.1 (Eq.mpr (congrFun (congrFun heq 5) 0) htransfer)

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
      (@_root_.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.source_registration
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
    (realize signature (fun _ _ U => PerfectStateTransfer U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
    definition := some {
      owner := `D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
      name := `D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "fn", "fn", "fn"]
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
end Reg.D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
