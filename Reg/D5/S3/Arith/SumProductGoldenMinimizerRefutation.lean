import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.SumProductGoldenMinimizerRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.SumProductGoldenMinimizerRefutation

open _root_.D5.S3.Arith.SumProductGoldenMinimizerRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => r ^ 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ r : ℝ, 1 < r ∧ r < 2 ∧ R.readout () () r = r + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨r, hlower, _, hEq⟩
  change (0 : ℝ) = r + 1 at hEq
  linarith

def realization : Registration arena (type_of% (@plastic_root)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨plastic_root, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 3 ≠ (1 : ℝ) ^ 3
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.SumProductGoldenMinimizerRefutation.plastic_root)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.SumProductGoldenMinimizerRefutation.plastic_root.__information_unit
  realizationName := `Reg.D5.S3.Arith.SumProductGoldenMinimizerRefutation.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r ^ 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.SumProductGoldenMinimizerRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.SumProductGoldenMinimizerRefutation
