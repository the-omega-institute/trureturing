import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity (StronglyPseudoperfect)

namespace Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ j => 60 * 2 ^ j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ j : ℕ, StronglyPseudoperfect (R.readout () () j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (Nat.lt_irrefl 0) (h 0).1

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (60 * 2 ^ (0 : ℕ) : ℕ) ≠ 60 * 2 ^ (1 : ℕ)
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => 60 * 2 ^ j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion38
