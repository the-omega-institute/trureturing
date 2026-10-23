import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.OriginalPairLanguages

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.OriginalPairLanguages
open _root_.Complexity
open _root_.PredictiveThermodynamic.OriginalClasses
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Guards

inductive Role
  | left | right
  deriving DecidableEq, Fintype, Inhabited

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Word
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Word
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun (i : Role) (_ : Unit) (w : Word) => if i = Role.left then leftGuard w else rightGuard w)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ w : Word, Q w ↔ ¬ S (R.readout Role.left () w) ∧ S (R.readout Role.right () w)

abbrev sourceScope := type_of% (@pair_split)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erasedRole (i : Role) : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun (j : Role) (_ : Unit) (w : Word) =>
    if j = i then (if i = Role.left then trueWord else falseWord)
    else if j = Role.left then leftGuard w else rightGuard w) (fun e => nomatch e)

theorem original_values : S trueWord ∧ ¬ S falseWord ∧ U falseWord := by
  have hnS : ¬ S [] := by
    rintro ⟨F,hF,_⟩
    change (none : Option _root_.PredictiveThermodynamic.Conventional.Formula) = some F at hF
    cases hF
  have hnU : ¬ U [] := by
    rintro ⟨⟨F,hF⟩,_⟩
    change (none : Option _root_.PredictiveThermodynamic.Conventional.Formula) = some F at hF
    cases hF
  have ht : S trueWord := by
    by_contra ht
    exact hnU ((repair_laws []).2.2.1.mpr ht)
  have hf : ¬ S falseWord := fun hs => hnS ((repair_laws []).2.1.mp hs)
  exact ⟨ht,hf,⟨(repair_laws []).1,hf⟩⟩

theorem erased_fails (i : Role) : ¬ arena.Law (erasedRole i) := by
  intro h
  have hv := original_values
  have hQ : Q (pairWords falseWord trueWord) := ⟨falseWord,trueWord,rfl,hv.2.2,hv.1⟩
  have hh := (h (pairWords falseWord trueWord)).mp hQ
  cases i
  · exact hh.1 hv.1
  · exact hv.2.1 hh.2

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨pair_split,erasedRole Role.left,erased_fails Role.left⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erasedRole i,?_,rfl,erased_fails i⟩
      intro j hj
      funext p w
      simp [erasedRole,actual,DependentFamily.realize,hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    change Role at i
    cases i <;> refine ⟨(),[],pairWords falseWord trueWord,?_⟩
    · change ([false,false] : Word) ≠ [false,true,true,false,false,false]
      decide
    · change ([false,true,true,false,false,false] : Word) ≠ [false,false]
      decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@pair_split) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.OriginalClasses.pair_split.__information_unit
  realizationName := `Reg.D5.S0.Computability.OriginalPairLanguages.Guards.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun (i : Role) (_ : Unit) (w : Word) => if i = Role.left then leftGuard w else rightGuard w)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.OriginalPairLanguages
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body","arg","fn","arg","arg","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg","arg","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Guards
end Reg.D5.S0.Computability.OriginalPairLanguages
