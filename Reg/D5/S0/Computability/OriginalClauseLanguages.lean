import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.OriginalClauseLanguages

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.OriginalClauseLanguages
open _root_.Complexity
open _root_.PredictiveThermodynamic.OriginalClasses
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Repairs

inductive Role
  | wellFormed | sat | complement | falseIdentity | trueIdentity
  deriving DecidableEq, Fintype, Inhabited

def fallback : Role → Word
  | .complement | .trueIdentity => trueWord
  | _ => falseWord

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
    (fun (role : Role) (_ : Unit) (w : Word) =>
      repair (fallback role) w) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ w : Word,
    W (R.readout Role.wellFormed () w) ∧ (S (R.readout Role.sat () w) ↔ S w) ∧
      (U w ↔ ¬ S (R.readout Role.complement () w)) ∧
      (W w → R.readout Role.falseIdentity () w = w ∧ R.readout Role.trueIdentity () w = w)

abbrev sourceScope := type_of% (@repair_laws)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erasedRole (i : Role) : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun (j : Role) (_ : Unit) (w : Word) =>
    if j = i then [] else repair (fallback j) w)
    (fun e => nomatch e)

theorem values : ¬ S [] ∧ ¬ U [] ∧ S trueWord ∧ W trueWord := by
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
  have hw : W trueWord := by obtain ⟨F,hF,_⟩ := ht; exact ⟨F,hF⟩
  exact ⟨hnS,hnU,ht,hw⟩

theorem erased_fails (i : Role) : ¬ arena.Law (erasedRole i) := by
  intro h
  have hv := values
  cases i
  · obtain ⟨F,hF⟩ := (h []).1
    change (none : Option _root_.PredictiveThermodynamic.Conventional.Formula) = some F at hF
    cases hF
  · exact hv.1 ((h trueWord).2.1.mpr hv.2.2.1)
  · exact hv.2.1 ((h []).2.2.1.mpr hv.1)
  · have hh := (h trueWord).2.2.2 hv.2.2.2 |>.1
    change ([] : Word) = [false,false] at hh
    cases hh
  · have hh := (h trueWord).2.2.2 hv.2.2.2 |>.2
    change ([] : Word) = [false,false] at hh
    cases hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨repair_laws,erasedRole Role.wellFormed,erased_fails Role.wellFormed⟩
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
    cases i <;>
      refine ⟨(),trueWord,falseWord,?_⟩ <;>
      change ([false,false] : Word) ≠ [false,true,true,false,false,false] <;>
      decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@repair_laws) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.OriginalClasses.repair_laws.__information_unit
  realizationName := `Reg.D5.S0.Computability.OriginalClauseLanguages.Repairs.family
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
    (fun (role : Role) (_ : Unit) (w : Word) =>
      repair (fallback role) w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.OriginalClauseLanguages
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body","fn","arg","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg","fn","arg","fn","arg","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg","arg","fn","arg","arg","arg","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg","arg","arg","body","fn","arg","fn","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg","arg","arg","body","arg","fn","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Repairs

namespace PairDecoder

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option (Word × Word)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ w => StackPair.decodePair w) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ w,
    Q w ↔ ∃ u v, R.readout () () w = some (u,v) ∧ U u ∧ S v

abbrev sourceScope := type_of% (@pair_language)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (none : Option (Word × Word))) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hnotU : ¬ U [] := by
    rintro ⟨⟨F,hF⟩,_⟩
    change (none : Option _root_.PredictiveThermodynamic.Conventional.Formula) = some F at hF
    cases hF
  have htrue : S trueWord := by
    have hh := (repair_laws []).2.2.1
    change (U [] ↔ ¬ S trueWord) at hh
    by_contra hn
    exact hnotU (hh.mpr hn)
  have hfalseW : W falseWord := by
    have hh := (repair_laws []).1
    exact hh
  have hfalseS : ¬ S falseWord := by
    have hh := (repair_laws []).2.1
    change (S falseWord ↔ S []) at hh
    intro hf
    obtain ⟨F,hF,_⟩ := hh.mp hf
    change (none : Option _root_.PredictiveThermodynamic.Conventional.Formula) = some F at hF
    cases hF
  have hQ : Q (pairWords falseWord trueWord) :=
    ⟨falseWord,trueWord,rfl,⟨hfalseW,hfalseS⟩,htrue⟩
  obtain ⟨u,v,hD,_⟩ := (h (pairWords falseWord trueWord)).mp hQ
  change (none : Option (Word × Word)) = some (u,v) at hD
  cases hD

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨pair_language,erased,erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased,?_,rfl,erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(),[],[false],?_⟩
    change (none : Option (Word × Word)) ≠ some ([],[])
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@pair_language) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.OriginalClasses.pair_language.__information_unit
  realizationName := `Reg.D5.S0.Computability.OriginalClauseLanguages.PairDecoder.family
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
    (fun _ _ w => StackPair.decodePair w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.OriginalClauseLanguages
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg","arg","body","arg","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PairDecoder
end Reg.D5.S0.Computability.OriginalClauseLanguages
