import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation

namespace Reg.D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsGreedyPermutation (R.readout () ())

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hfirst := h.1
  change (0 : ℕ) = 1 at hfirst
  omega

noncomputable def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, bad, bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    intro he
    have h := result.2.2.2.1 1 2 (by omega) (by omega) he
    omega

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result)
    (type_of% (realize signature (fun _ _ n => a n) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
