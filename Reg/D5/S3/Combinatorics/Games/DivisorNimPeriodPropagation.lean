import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation
open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev singletonSignature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def singletonActual : Realization singletonSignature :=
  realize singletonSignature (fun _ _ n => grundy ({n} : Position)) (fun e => nomatch e)

def singletonRejected : Realization singletonSignature :=
  realize singletonSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev singletonArena : Arena where
  signature := singletonSignature
  Law R := ∀ n, 0 < n → R.readout () () n = n

private theorem singleton_rejected_law : ¬ singletonArena.Law singletonRejected := by
  intro h
  have he := h 1 (by decide)
  change (0 : ℕ) = 1 at he
  omega

noncomputable def singletonRegistration :
    Registration singletonArena (type_of% (@singleton_grundy)) where
  actual := singletonActual
  bridge := Iff.rfl
  variation := ⟨singleton_grundy, singletonRejected, singleton_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨singletonRejected, ?_, rfl, singleton_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change grundy ({1} : Position) ≠ grundy ({2} : Position)
    rw [singleton_grundy 1 (by decide), singleton_grundy 2 (by decide)]
    decide

noncomputable def singleton_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@singleton_grundy)
      (type_of% (realize singletonSignature (fun _ _ n => grundy ({n} : Position))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation.singletonUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation.singletonRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨singletonArena⟩
  objectArena := .source ⟨singletonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source singletonArena ⟨singletonRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize singletonSignature (fun _ _ n => grundy ({n} : Position))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation
    definition := none
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

end Reg.D5.S3.Combinatorics.Games.DivisorNimPeriodPropagation
