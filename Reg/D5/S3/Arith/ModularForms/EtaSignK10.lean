import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.ModularForms.EtaSignK10

/-! Faithful full-telescope audit attempts for the two original endpoints.
One actual C10 observation is selected; all other source clauses remain fixed.
The native source-binding producer, not this comment, determines registration status. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.ModularForms.EtaSignK10

open _root_.D5.S3.Arith.ModularForms.EtaSignK10
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => C10 n) (fun e => nomatch e)

noncomputable def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change C10 0 ≠ C10 1
  have hn : C10 1 < 0 := by simpa using (progression_signs 0).1
  rw [C10_zero]
  linarith

namespace AllSigns

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    (0 < r.readout () () n ↔ n % 9 = 0 ∨ n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 8) ∧
    (C10 n < 0 ↔ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 6 ∨ n % 9 = 7) ∧
    C10 n ≠ 0

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hp := (h 0).1.mpr (Or.inl rfl)
  norm_num [erased, realize] at hp

noncomputable def family : Registration arena (type_of% @all_index_signs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨all_index_signs, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_index_signs) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ModularForms.EtaSignK10.all_index_signs.__information_unit
  realizationName := `Reg.D5.S3.Arith.ModularForms.EtaSignK10.AllSigns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => C10 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ModularForms.EtaSignK10
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AllSigns

namespace Constant

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () 0 = 1

private theorem erased_fails : ¬ arena.Law erased := by
  norm_num [arena, erased, realize]

noncomputable def family : Registration arena (type_of% @C10_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨C10_zero, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@C10_zero) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ModularForms.EtaSignK10.C10_zero.__information_unit
  realizationName := `Reg.D5.S3.Arith.ModularForms.EtaSignK10.Constant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => C10 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ModularForms.EtaSignK10
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Constant
end Reg.D5.S3.Arith.ModularForms.EtaSignK10
