import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
import Reg.Support.DependentFamily

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval (coordinates)
open D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Four source occurrences, over the original infinite native source family. -/
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Source
  Role := Bool × Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := match i.1 with
    | false => List Bool
    | true => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ s => match i with
    | (false, _) => wd s
    | (true, _) => coordinates s) (fun e => nomatch e)

def leftThree : Source := .mul (.mul (.of false) (.of false)) (.of false)
def rightThree : Source := .mul (.of false) (.mul (.of false) (.of false))

def wordLeftBad : Realization signature :=
  realize signature (fun i _ s => match i with
    | (false,false) => [false]
    | (false,true) => wd s
    | (true,_) => coordinates s) (fun e => nomatch e)

def wordRightBad : Realization signature :=
  realize signature (fun i _ s => match i with
    | (false,false) => wd s
    | (false,true) => [false]
    | (true,_) => coordinates s) (fun e => nomatch e)

def areaLeftBad : Realization signature :=
  realize signature (fun i _ s => match i with
    | (false,_) => wd s
    | (true,false) => coordinates rightThree
    | (true,true) => coordinates s) (fun e => nomatch e)

def areaRightBad : Realization signature :=
  realize signature (fun i _ s => match i with
    | (false,_) => wd s
    | (true,false) => coordinates s
    | (true,true) => coordinates leftThree) (fun e => nomatch e)

/-- The original telescope, including both observation equalities and native equality. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (s t : Source),
    R.readout (false,false) () s = R.readout (false,true) () t →
    R.readout (true,false) () s = R.readout (true,true) () t → s = t

def familyRegistration : Registration arena
    (∀ (s t : Source), wd s = wd t → coordinates s = coordinates t → s = t) := {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨native_ancestor_uniqueness, wordLeftBad, by
      intro h
      have he := h (.of true) (.of false) rfl rfl
      cases he⟩
    sensitivity := ⟨by
      have wl : ¬ arena.Law wordLeftBad := by
        intro h
        have he := h (.of true) (.of false) rfl rfl
        cases he
      have wr : ¬ arena.Law wordRightBad := by
        intro h
        have he := h (.of false) (.of true) rfl rfl
        cases he
      have al : ¬ arena.Law areaLeftBad := by
        intro h
        have he := h leftThree rightThree rfl rfl
        cases he
      have ar : ¬ arena.Law areaRightBad := by
        intro h
        have he := h leftThree rightThree rfl rfl
        cases he
      intro i
      rcases i with ⟨a,b⟩
      cases a <;> cases b
      · refine ⟨wordLeftBad, ?_, rfl, wl⟩
        intro j hj
        rcases j with ⟨a,b⟩
        cases a <;> cases b <;> try rfl
        exact False.elim (hj rfl)
      · refine ⟨wordRightBad, ?_, rfl, wr⟩
        intro j hj
        rcases j with ⟨a,b⟩
        cases a <;> cases b <;> try rfl
        exact False.elim (hj rfl)
      · refine ⟨areaLeftBad, ?_, rfl, al⟩
        intro j hj
        rcases j with ⟨a,b⟩
        cases a <;> cases b <;> try rfl
        exact False.elim (hj rfl)
      · refine ⟨areaRightBad, ?_, rfl, ar⟩
        intro j hj
        rcases j with ⟨a,b⟩
        cases a <;> cases b <;> try rfl
        exact False.elim (hj rfl)
    , fun e => nomatch e⟩
    dependence := by
      intro i
      rcases i with ⟨a,b⟩
      cases a with
      | false =>
        refine ⟨(), .of false, .of true, ?_⟩
        exact (by decide : ([false] : List Bool) ≠ [true])
      | true =>
        refine ⟨(), leftThree, rightThree, ?_⟩
        exact (by decide : ([1,2] : List ℕ) ≠ [2,1])
  }

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_ancestor_uniqueness)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness.native_ancestor_uniqueness
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body","body","body","domain","arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","domain","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","domain","arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","domain","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
