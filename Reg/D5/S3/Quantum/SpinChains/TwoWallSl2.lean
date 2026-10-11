import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TwoWallSl2
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.TwoWallWords
open _root_.D5.S3.Quantum.SpinChains.TwoWallMarked
open _root_.D5.S3.Quantum.SpinChains.TwoWallSl2
open _root_.D5.S3.Quantum.SpinChains.Sl2WeightFiltration
open _root_.D5.S3.Quantum.SpinChains.HypereclecticNonShortening (level)
open _root_.D5.S1.Words.ParityCode.OddTopWeight (ones)
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Reg.D5.S3.Quantum.SpinChains.TwoWallSl2
universe u

abbrev testK := ULift.{u} ℚ
instance testCharZero : CharZero testK.{u} := ⟨fun _m _n eq =>
  (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
    (congrArg ULift.down eq)⟩

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State p := Coordinates p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => integerWeight c) (fun e => nomatch e)
def shifted : Realization signature :=
  realize signature (fun _ _ c => integerWeight c + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Type u) [Field K] [CharZero K] (a b : ℕ),
    Sl2Relations (markedH K a b) (markedE K a b) (markedF K a b) ∧
    (Commute (Jstar K a b) (markedH K a b) ∧
      Commute (Jstar K a b) (markedE K a b) ∧
      Commute (Jstar K a b) (markedF K a b) ∧
      ∀ t : Pos a b,
        Commute (markedTranslation K t) (markedH K a b) ∧
        Commute (markedTranslation K t) (markedE K a b) ∧
        Commute (markedTranslation K t) (markedF K a b)) ∧
    Sl2Relations (h K a b) (e K a b) (f K a b) ∧
    f K a b = F3 K a b ∧
    ((∀ t : Pos a b, Commute (translation K t) (h K a b) ∧
      Commute (translation K t) (e K a b) ∧ Commute (translation K t) (f K a b)) ∧
      Commute (U K a b) (h K a b) ∧ Commute (U K a b) (e K a b) ∧
      Commute (U K a b) (f K a b)) ∧
    ∀ c : Coordinates a b,
    h K a b (delta K (encode c).1.1) = (R.readout () ⟨a,b⟩ c : K) • delta K (encode c).1.1 ∧
    e K a b (delta K (encode c).1.1) =
      (∑ j : Fin (c.m - 1), if c.u (⟨j.val, by omega⟩ : Fin c.m) = false ∧
        c.u (⟨j.val + 1, by omega⟩ : Fin c.m) = true then
        (((j.val + 1 : ℕ) : K) * ((c.m : K) - ((j.val + 1 : ℕ) : K))) •
          delta K (encode (leftMove c j)).1.1 else 0) +
      (∑ j : Fin (c.n - 1), if c.v (⟨j.val, by omega⟩ : Fin c.n) = false ∧
        c.v (⟨j.val + 1, by omega⟩ : Fin c.n) = true then
        (((j.val + 1 : ℕ) : K) * ((c.n : K) - ((j.val + 1 : ℕ) : K))) •
          delta K (encode (rightMove c j)).1.1 else 0) ∧
    f K a b (delta K (encode c).1.1) =
      (∑ j : Fin (c.m - 1), if c.u (⟨j.val, by omega⟩ : Fin c.m) = true ∧
        c.u (⟨j.val + 1, by omega⟩ : Fin c.m) = false then
        delta K (encode (leftMove c j)).1.1 else 0) +
      (∑ j : Fin (c.n - 1), if c.v (⟨j.val, by omega⟩ : Fin c.n) = true ∧
        c.v (⟨j.val + 1, by omega⟩ : Fin c.n) = false then
        delta K (encode (rightMove c j)).1.1 else 0)

def point : Coordinates 0 0 :=
  ⟨0,0,0,Fin.elim0,Fin.elim0,rfl,by simp [ones]⟩

def high : Coordinates 1 1 :=
  ⟨0,2,0,![true,false],Fin.elim0,rfl,by decide⟩
def low : Coordinates 1 1 :=
  ⟨0,2,0,![false,true],Fin.elim0,rfl,by decide⟩

theorem rejected_law : ¬ arena.{u}.Law shifted := by
  intro law
  have z := (law testK.{u} 0 0).2.2.2.2.2 point |>.1
  have eq := (literal_action testK.{u} 0 0).2.2.2.2.2 point |>.1
  rw [eq] at z
  have zz := congrArg (fun v : Space testK 0 0 => v (encode point).1.1) z
  norm_num [shifted, realize, integerWeight, point, level, ones, delta, basis,
    Finsupp.coe_basisSingleOne] at zz

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, high, low, ?_⟩
  change integerWeight high ≠ integerWeight low
  decide

noncomputable def family : Registration arena.{u} (type_of% @literal_action.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_action.{u}, shifted, rejected_law⟩
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
    (@literal_action.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallSl2.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallSl2.family
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
    owner := `D5.S3.Quantum.SpinChains.TwoWallSl2
    definition := none
    coordinates := #[3,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Reg.D5.S3.Quantum.SpinChains.TwoWallSl2
