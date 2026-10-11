import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TwoWallWeights
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.TwoWallWords
open _root_.D5.S3.Quantum.SpinChains.TwoWallSl2
open _root_.D5.S3.Quantum.SpinChains.TwoWallWeights
open _root_.D5.S3.Quantum.SpinChains.Sl2WeightFiltration
open _root_.D5.S1.Words.ParityCode.OddTopWeight (ones)
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Quantum.SpinChains.TwoWallWeights
universe u

abbrev testK := ULift.{u} ℚ
instance testCharZero : CharZero testK.{u} := ⟨fun _m _n eq =>
  (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
    (congrArg ULift.down eq)⟩

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State p := Word p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ w => wordWeight w) (fun e => nomatch e)
noncomputable def shifted : Realization signature :=
  realize signature (fun _ _ w => wordWeight w + 1) (fun e => nomatch e)

def point : Coordinates 0 0 :=
  ⟨0,0,0,Fin.elim0,Fin.elim0,rfl,by simp [ones]⟩
def high : Coordinates 1 1 :=
  ⟨0,2,0,![true,false],Fin.elim0,rfl,by decide⟩
def low : Coordinates 1 1 :=
  ⟨0,2,0,![false,true],Fin.elim0,rfl,by decide⟩

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, (encode high).1.1, (encode low).1.1, ?_⟩
  change wordWeight (encode high).1.1 ≠ wordWeight (encode low).1.1
  rw [(weight_structure ℚ 1 1).1, (weight_structure ℚ 1 1).1]
  decide

namespace Structure
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Type u) [Field K] [CharZero K] (a b : ℕ),
    (∀ c : Coordinates a b, wordWeight (encode c).1.1 = integerWeight c) ∧
    (∀ w : Word a b, h K a b (delta K w) = (R.readout () ⟨a,b⟩ w : K) • delta K w) ∧
    IntegralWeights (h K a b) ∧
    (∀ w : Word a b, -(a * b : ℤ) ≤ wordWeight w ∧ wordWeight w ≤ (a * b : ℤ))

theorem rejected_law : ¬ arena.{u}.Law shifted := by
  intro law
  let w := (encode point).1.1
  have z := (law testK.{u} 0 0).2.1 w
  have eq := (weight_structure testK.{u} 0 0).2.1 w
  rw [eq] at z
  have zz := congrArg (fun v : Space testK 0 0 => v w) z
  simp only [shifted, realize, Finsupp.smul_apply, delta, basis,
    Finsupp.coe_basisSingleOne, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    Int.cast_add, Int.cast_one] at zz
  have : (1 : testK) = 0 := by linear_combination -zz
  exact one_ne_zero this

noncomputable def family : Registration arena.{u} (type_of% @weight_structure.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_structure.{u}, shifted, rejected_law⟩
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
    (@weight_structure.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWeights.Structure.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWeights.Structure.family
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
    owner := `D5.S3.Quantum.SpinChains.TwoWallWeights
    definition := none
    coordinates := #[3,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms family
end Structure

namespace Control
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Type u) [Field K] [CharZero K] (a b : ℕ),
    (∀ (w : Word a b) (p : Pos a b), Allowed 0 w p →
      wordWeight (swapWord p w) = R.readout () ⟨a,b⟩ w - a) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 1 w p →
      wordWeight (swapWord p w) = wordWeight w - b) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 2 w p →
      wordWeight (swapWord p w) = wordWeight w - 2) ∧
    (2 ≤ a → 2 ≤ b →
      (∀ (i : Fin 3) (s : ℤ), (weightLE (h K a b) s).map (F K a b i) ≤
        weightLE (h K a b) (s - 2)) ∧
      (∀ (ξ : Fin 3 → K) (s : ℤ), (weightLE (h K a b) s).map (T K a b ξ) ≤
        weightLE (h K a b) (s - 2)) ∧
      (∀ ξ : Fin 3 → K, T K a b ξ ^ (a * b + 1) = 0)) ∧
    F3 K a b ^ (a * b + 1) = 0

theorem rejected_law : ¬ arena.{u}.Law shifted := by
  intro law
  have layout := (marked_coordinates 1 1).2.2.2.1 high
  have hp : Allowed 0 (encode high).1.1 0 := by
    constructor
    · exact layout.1
    · change (encode high).1.1.1 (0 + 1) = two
      simpa only [high, Fin.val_zero, zero_add, Nat.cast_one, Matrix.cons_val_zero,
        if_true] using layout.2.2.1 (0 : Fin 2)
  have z := (law testK.{u} 1 1).1 (encode high).1.1 0 hp
  have eq := (weight_control testK.{u} 1 1).1 (encode high).1.1 0 hp
  change wordWeight (swapWord 0 (encode high).1.1) =
    wordWeight (encode high).1.1 + 1 - 1 at z
  omega

noncomputable def family : Registration arena.{u} (type_of% @weight_control.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_control.{u}, shifted, rejected_law⟩
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
    (@weight_control.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWeights.Control.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWeights.Control.family
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
    owner := `D5.S3.Quantum.SpinChains.TwoWallWeights
    definition := none
    coordinates := #[3,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms family
end Control

end Reg.D5.S3.Quantum.SpinChains.TwoWallWeights
