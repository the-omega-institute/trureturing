import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.Golay.IntegerLeech
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Lattices.Golay.IntegerLeech
open _root_.D5.S3.Arith.Lattices.Golay.GolayEncoder
open _root_.D5.S3.Arith.Lattices.Golay.IntegerLeech
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => IntVector) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ x => scaledSquare x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ x : IntVector, Admissible code x → x ≠ 0 → 4 ≤ R.readout () () x) ∧
    (Admissible code shortestVector ∧ shortestVector ≠ 0 ∧ scaledSquare shortestVector = 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have witness := minimum_norm.2
  have bad := h.1 shortestVector witness.1 witness.2.1
  change (4 : ℚ) ≤ 0 at bad
  norm_num at bad

def evidence : Registration arena
    ((∀ x : IntVector, Admissible code x → x ≠ 0 → 4 ≤ scaledSquare x) ∧
      (Admissible code shortestVector ∧ shortestVector ≠ 0 ∧ scaledSquare shortestVector = 4)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨minimum_norm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : IntVector), shortestVector, ?_⟩
    change scaledSquare 0 ≠ scaledSquare shortestVector
    rw [minimum_norm.2.2.2]
    norm_num [scaledSquare, squareSum]

def minimumRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Lattices.Golay.IntegerLeech.minimum_norm)
    (type_of% (realize signature (fun _ _ x => scaledSquare x) (fun e => nomatch e)))
    Unit Unit where
  unitName := `Reg.D5.S3.Arith.Lattices.Golay.IntegerLeech.minimumUnit
  realizationName := `Reg.D5.S3.Arith.Lattices.Golay.IntegerLeech.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => scaledSquare x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.Golay.IntegerLeech
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Lattices.Golay.IntegerLeech
