import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Latin.Tableaux.Counting
import Reg.Support.DependentFamily

/-! Source-bound information audits for literal Latin tableaux. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Latin.Tableaux.Counting
open _root_.D5.S3.Combinatorics.Latin.Tableaux.Source

namespace Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting

namespace UniversalNatural
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
  realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ), 5 ≤ k → r.readout () () k = 9 * 4^(k-3)

private noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 5 (by decide)
  norm_num [bad,realize] at hx

noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjecture63,bad,bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_not_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),5,6,?_⟩
    change _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 5 ≠ _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 6
    rw [conjecture63 5 (by decide),conjecture63 6 (by decide)]
    norm_num }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63)
    (type_of% (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting.UniversalNatural.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.Tableaux.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end UniversalNatural

namespace UniversalInteger
abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k.toNat) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (k : ℤ), 5 ≤ k → r.readout () () k = 9 * 4^(k.toNat-3)

private noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 5 (by decide)
  norm_num [bad,realize] at hx

noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63_integer)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjecture63_integer,bad,bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_not_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),5,6,?_⟩
    change _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 5 ≠ _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 6
    rw [conjecture63 5 (by decide),conjecture63 6 (by decide)]
    norm_num }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63_integer)
    (type_of% (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k.toNat) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Latin.Tableaux.Counting.conjecture63_integer.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting.UniversalInteger.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k.toNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.Tableaux.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end UniversalInteger

namespace SourceEnumeration
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
  realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ), r.readout () () k = (enumerate (shape k)).card

private noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 5
  change 0 = (enumerate (shape 5)).card at hx
  rw [base_count_and_invariant.1] at hx
  omega

noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.source_enumeration)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_enumeration,bad,bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_not_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),5,6,?_⟩
    change _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 5 ≠ _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT 6
    rw [conjecture63 5 (by decide),conjecture63 6 (by decide)]
    norm_num }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.source_enumeration)
    (type_of% (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Latin.Tableaux.Counting.source_enumeration.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting.SourceEnumeration.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => _root_.D5.S3.Combinatorics.Latin.Tableaux.Source.LT k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.Tableaux.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end SourceEnumeration


namespace ShapeGrowth
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p s => shape (s+1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k : ℕ, 5 ≤ k → r.readout () () k = (k+1)::shape k
private noncomputable def bad : Realization signature :=
  realize signature (fun _ p s => []) (fun e => nomatch e)
private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 5 (by decide)
  change ([] : List ℕ) = 6::shape 5 at hx
  simp at hx
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.shape_succ)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shape_succ,bad,bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_not_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(),5,6,by decide⟩ }
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Latin.Tableaux.Counting.shape_succ)
    (type_of% (realize signature (fun _ p s => shape (s+1)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Latin.Tableaux.Counting.shape_succ.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting.ShapeGrowth.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => shape (s+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.Tableaux.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ShapeGrowth

end Reg.D5.S3.Combinatorics.Latin.Tableaux.Counting
