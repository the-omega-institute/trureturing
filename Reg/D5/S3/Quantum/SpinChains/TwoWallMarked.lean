import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TwoWallMarked
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.TwoWallWords
open _root_.D5.S3.Quantum.SpinChains.TwoWallMarked

namespace Reg.D5.S3.Quantum.SpinChains.TwoWallMarked
universe u

namespace descent

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State p := MarkedWord p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MarkedWord p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ x => J x) (fun e => nomatch e)
def shifted : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Type u) [Field K] (a b : ℕ),
    Function.Involutive (@J a b) ∧
    (∀ x : MarkedWord a b, R.readout () ⟨a,b⟩ x ≠ x) ∧
    (∀ (t : Pos a b) (x : MarkedWord a b),
      markedRotate t (J x) = J (markedRotate t x)) ∧
    (Q K a b).comp (S K a b) = (2 : K) • LinearMap.id ∧
    (S K a b).comp (Q K a b) = LinearMap.id + Jstar K a b ∧
    (∀ t : Pos a b, (markedTranslation K t).comp (S K a b) =
      (S K a b).comp (translation K t)) ∧
    (∀ t : Pos a b, (Q K a b).comp (markedTranslation K t) =
      (translation K t).comp (Q K a b)) ∧
    (markedU K a b).comp (S K a b) = (S K a b).comp (U K a b) ∧
    (Q K a b).comp (markedU K a b) = (U K a b).comp (Q K a b)

def point : MarkedWord 0 0 :=
  encode ⟨0, 0, 0, Fin.elim0, Fin.elim0, rfl,
    by simp [D5.S1.Words.ParityCode.OddTopWeight.ones]⟩

theorem rejected_law : ¬ arena.{u}.Law shifted := by
  intro law
  exact (law (ULift.{u} ℚ) 0 0).2.1 point rfl

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0⟩, point, J point, ?_⟩
  change J point ≠ J (J point)
  rw [(marked_descent ℚ 0 0).1]
  exact (marked_descent ℚ 0 0).2.1 point

noncomputable def family : Registration arena.{u} (type_of% @marked_descent.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@marked_descent.{u}, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@marked_descent.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallMarked.descent.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallMarked.descent.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TwoWallMarked
    definition := none
    coordinates := #[2,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end descent

namespace coordinates

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State p := Coordinates p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Coordinates p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ x => coordinateSwap x) (fun e => nomatch e)
def shifted : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ),
    (∀ c : Coordinates a b, decode (encode c) = c) ∧
    (∀ x : MarkedWord a b, encode (decode x) = x) ∧
    (∀ c : Coordinates a b, c.m < a + b + 1 ∧ c.n = a + b - c.m) ∧
    (∀ c : Coordinates a b,
      (encode c).1.1.1 c.p = wall ∧
      (encode c).1.1.1 (c.p + ((c.m + 1 : ℕ) : Pos a b)) = wall ∧
      (∀ i : Fin c.m, (encode c).1.1.1 (c.p + ((i.val + 1 : ℕ) : Pos a b)) =
        if c.u i then two else one) ∧
      (∀ i : Fin c.n, (encode c).1.1.1 (c.p + ((c.m + 2 + i.val : ℕ) : Pos a b)) =
        if c.v i then two else one)) ∧
    (∀ c : Coordinates a b, encode (coordinateSwap c) = J (encode c)) ∧
    Function.Involutive (@coordinateSwap a b) ∧
    (∀ c : Coordinates a b, R.readout () ⟨a,b⟩ c ≠ c) ∧
    (∀ (t : Pos a b) (c : Coordinates a b),
      encode (coordinateRotate t c) = markedRotate t (encode c)) ∧
    (∀ (t : Pos a b) (c : Coordinates a b),
      coordinateRotate t (coordinateSwap c) = coordinateSwap (coordinateRotate t c))

def point : Coordinates 0 0 :=
  ⟨0, 0, 0, Fin.elim0, Fin.elim0, rfl, by simp [D5.S1.Words.ParityCode.OddTopWeight.ones]⟩

theorem rejected_law : ¬ arena.Law shifted := by
  intro law
  exact (law 0 0).2.2.2.2.2.2.1 point rfl

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0⟩, point, coordinateSwap point, ?_⟩
  change coordinateSwap point ≠ coordinateSwap (coordinateSwap point)
  rw [(marked_coordinates 0 0).2.2.2.2.2.1]
  exact (marked_coordinates 0 0).2.2.2.2.2.2.1 point

noncomputable def family : Registration arena (type_of% @marked_coordinates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@marked_coordinates, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@marked_coordinates) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallMarked.coordinates.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallMarked.coordinates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TwoWallMarked
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end coordinates

end Reg.D5.S3.Quantum.SpinChains.TwoWallMarked
