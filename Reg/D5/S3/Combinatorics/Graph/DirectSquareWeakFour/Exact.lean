import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact

namespace Reg.D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact

open _root_.D5.S3.Combinatorics.Graph.DirectSquareWeakFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => wdim n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 4 ≤ n →
    r.readout () () n = 2*n + ⌈(2*(n : ℚ))/11⌉₊ + (if n = 5 then 1 else 0)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 4 (by decide)
  have h4 : ⌈(8 : ℚ)/11⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num [rejected, realize, h4] at hh

def record : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 4, 5, ?_⟩
    change wdim 4 ≠ wdim 5
    rw [result 4 (by decide), result 5 (by decide)]
    have h4 : ⌈(8 : ℚ)/11⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
    have h5 : ⌈(10 : ℚ)/11⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
    norm_num [h4, h5]

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.DirectSquareWeakFour.result)
    (type_of% (realize signature (fun _ _ n => wdim n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.DirectSquareWeakFour.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => wdim n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact
    definition := some {
      owner := `D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact
      name := `D5.S3.Combinatorics.Graph.DirectSquareWeakFour.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms record
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exact
