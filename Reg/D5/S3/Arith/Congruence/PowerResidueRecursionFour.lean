import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.PowerResidueRecursionFour
import Reg.Support.SingleDependentReadout

/-! # Source-bound audit of positivity in the A374911 recursion -/

open _root_.D5.S3.Arith.Congruence.PowerResidueRecursionFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Congruence.PowerResidueRecursionFour

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => seq n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 0 < R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected :=
  fun h => (by decide : ¬ 0 < (0 : ℕ)) (h 0)

def registration : Registration arena (type_of% @seq_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨seq_pos, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change seq 0 ≠ seq 1
    rw [(seq_eq_one 0).mpr rfl, (seq_eq_two 1).mpr rfl]
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@seq_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Congruence.PowerResidueRecursionFour.seq_pos.informationUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.PowerResidueRecursionFour.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => seq n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.PowerResidueRecursionFour
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"], stateBinder := 0
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Congruence.PowerResidueRecursionFour
