import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount

open _root_.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open _root_.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n k => supportCount n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, R.readout () n k = Nat.choose ((n + 1) - k) k

noncomputable def registration : Registration arena
    (∀ n k : ℕ, supportCount n k = Nat.choose ((n + 1) - k) k) := by
  have rejected_law : ¬ arena.Law rejected := by
    intro h
    have h0 := h 0 0
    change 0 = Nat.choose (1 - 0) 0 at h0
    simp at h0
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨support_count_eq_choose, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · intro i
        exact nomatch i
    dependence := by
      intro i
      refine ⟨0, 0, 1, ?_⟩
      change supportCount 0 0 ≠ supportCount 0 1
      rw [support_count_eq_choose, support_count_eq_choose]
      decide }

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount.support_count_eq_choose)
      (type_of% (realize signature (fun _ n k => supportCount n k)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => supportCount n k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
