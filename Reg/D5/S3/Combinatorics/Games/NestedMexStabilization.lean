import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.NestedMexStabilization
import Reg.Support.DependentFamily

set_option maxRecDepth 10000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Combinatorics.Games.NestedMexStabilization

open _root_.D5.S3.Combinatorics.Games.NestedMexStabilization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := List Coefficients
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ L x => run L (run L (run L x))) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : List Coefficients), L ≠ [] → ∀ (x : ℕ), 0 < x →
    R.readout () L x = run L (run L x)

def sample : Coefficients :=
  ⟨{0}, {0}, {0,3}, {0}, by simp, by simp, by simp, by simp⟩

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [sample] (by simp) 1 (by decide)
  have hc : run [sample] (run [sample] 1) = 1 := by decide
  change 0 = run [sample] (run [sample] 1) at hh
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨[sample], 1, 2, ?_⟩
    change run [sample] (run [sample] (run [sample] 1)) ≠
      run [sample] (run [sample] (run [sample] 2))
    decide

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Games.NestedMexStabilization.result)
      (type_of% (realize signature (fun _ L x => run L (run L (run L x)))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.NestedMexStabilization.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.NestedMexStabilization.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L x => run L (run L (run L x)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.NestedMexStabilization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Games.NestedMexStabilization
