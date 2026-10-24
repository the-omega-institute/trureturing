import D5.S1.Words.Sequenceability.CharacteristicSevenDetour
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Faithful source-bound registration for the six-column lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour

open _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev LiftParams := Σ K : Type u, Σ f : Field K, @Units K f.toMonoid × K

abbrev liftSignature : Signature where
  Params := LiftParams.{u}
  State p := Fin 6 × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def liftActual : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p v => by
    letI := p.2.1
    exact edgeLabel p.2.2.1 p.2.2.2 v) (fun e => nomatch e)

def liftBad : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev liftArena : Arena where
  signature := liftSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7] (c : K),
    ∃ r : Kˣ, (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 6 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (R.readout () ⟨K, f, r, c⟩) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 6) (0, h) =
        (0, _root_.D5.S1.Words.Sequenceability.RowOrbitLift.rowReturn r c h))

private theorem lift_bad_law : ¬ liftArena.{u}.Law liftBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨r, _, _, hlabel, _, _⟩ := h K 0
  exact hlabel.1 (show (0, (0 : K)) ∈ Set.univ from trivial) rfl

def liftFamily : Registration liftArena.{u}
    (type_of% (@exists_characteristic_seven_lift.{u})) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_seven_lift, liftBad, lift_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftBad, ?_, rfl, lift_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1, 0⟩, (0, 0), (1, 0), ?_⟩
    intro he
    have h := congrArg Prod.fst he
    have h' : (3 : ZMod 7) - 1 = 2 - 3 := by
      simpa [liftActual, realize,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.edgeLabel,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.lift,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.vertex,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.column] using h
    exact (by decide : (3 : ZMod 7) - 1 ≠ 2 - 3) h'

def liftAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_seven_lift.{u}) (Realization liftSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.exists_characteristic_seven_lift.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.liftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature liftActual.readout liftActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev SeamsParams := Σ K : Type u, Σ f : Field K, K

abbrev seamsSignature : Signature where
  Params := SeamsParams.{u}
  State p := carrier (K := p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def seamsActual : Realization seamsSignature.{u} :=
  realize seamsSignature (fun _ p v => by
    letI := p.2.1
    exact vertexWithEndpoints p.2.2 v) (fun e => nomatch e)

def seamsBad : Realization seamsSignature.{u} :=
  realize seamsSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev seamsArena : Arena where
  signature := seamsSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [CharP K 7]
    (r : Kˣ) (u : K) (_hu : u ≠ 0) (_hr : (r : K) + 1 ≠ 0),
    (splice r u (predecessorOne r u) = headTwo r u) ∧
    (splice r u (predecessorTwo r u) = target) ∧
    (splice r u source = headOne r u) ∧
    (splice r u target = source) ∧
    (R.readout () ⟨K, f, u⟩ (headTwo r u) -
        R.readout () ⟨K, f, u⟩ (predecessorOne r u) = (0, u)) ∧
    (R.readout () ⟨K, f, u⟩ target -
        R.readout () ⟨K, f, u⟩ (predecessorTwo r u) = (2, 2 * alpha r u)) ∧
    (R.readout () ⟨K, f, u⟩ (headOne r u) -
        R.readout () ⟨K, f, u⟩ source = (3, alpha r u)) ∧
    (R.readout () ⟨K, f, u⟩ source -
        R.readout () ⟨K, f, u⟩ target = (0, -u))

private theorem seams_bad_law : ¬ seamsArena.{u}.Law seamsBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨_, _, _, _, he, _, _, _⟩ := h K 1 1 (by simp) (by norm_num)
  have hz : (0 : K) = 1 := by
    simpa [seamsBad, realize] using congrArg Prod.snd he
  exact zero_ne_one hz

def seamsFamily : Registration seamsArena.{u}
    (type_of% (@six_column_splice_seams.{u})) where
  actual := seamsActual
  bridge := Iff.rfl
  variation := ⟨six_column_splice_seams, seamsBad, seams_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seamsBad, ?_, rfl, seams_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1⟩, source, target, ?_⟩
    simp [seamsActual, realize, vertexWithEndpoints, source, target]

def seamsAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@six_column_splice_seams.{u}) (Realization seamsSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.six_column_splice_seams.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.seamsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨seamsArena⟩
  objectArena := .source ⟨seamsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seamsArena ⟨seamsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seamsSignature seamsActual.readout seamsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev PathParams := Σ K : Type u, Field K

abbrev pathSignature : Signature where
  Params := PathParams.{u}
  State p := (ℕ → ZMod 7 × p.1) × (ℕ → ZMod 7 × p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def pathActual : Realization pathSignature.{u} :=
  realize pathSignature (fun _ _ p => p.2) (fun e => nomatch e)

def pathBad : Realization pathSignature.{u} :=
  realize pathSignature (fun _ p _ _ => by
    letI := p.2
    exact (0, 0)) (fun e => nomatch e)

abbrev pathArena : Arena where
  signature := pathSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7]
    (u : K) (_hu : u ≠ 0),
    let N := 6 * Nat.card K + 1;
    ∃ v w : ℕ → ZMod 7 × K,
      v 0 = (0, 0) ∧ v N = (0, u) ∧
      Function.Injective (fun i : Fin (N + 1) => v i.val) ∧
      Set.range (fun i : Fin (N - 1) => v (i.val + 1)) = {z | z.1 ≠ 0} ∧
      (∀ n < N, (R.readout () ⟨K, f⟩ (v, w)) n = v (n + 1) - v n) ∧
      Function.Injective (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val) ∧
      Set.range (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val) = {z | z.1 ≠ 0 ∨ z = (0, u)} ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).length = 6 * Nat.card K + 2 ∧
      (List.ofFn (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val)).length = 6 * Nat.card K + 1 ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).Nodup ∧
      (List.ofFn (fun i : Fin N => (R.readout () ⟨K, f⟩ (v, w)) i.val)).Nodup ∧
      (∀ n ≤ N, (∑ i ∈ Finset.range n, (R.readout () ⟨K, f⟩ (v, w)) i) = v n) ∧
      Function.Injective (fun n : Fin (N + 1) => ∑ i ∈ Finset.range n.val, (R.readout () ⟨K, f⟩ (v, w)) i) ∧
      (∀ a b : ℕ, a < b → b ≤ N → (∑ i ∈ Finset.Ico a b, (R.readout () ⟨K, f⟩ (v, w)) i) ≠ 0) ∧
      (∑ i ∈ Finset.range N, (R.readout () ⟨K, f⟩ (v, w)) i) = (0, u)

private theorem path_bad_law : ¬ pathArena.{u}.Law pathBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨v, w, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htotal⟩ :=
    h K 1 (by simp)
  have hz : (0 : K) = 1 := by
    simpa [pathBad, realize] using congrArg Prod.snd htotal
  exact zero_ne_one hz

def pathFamily : Registration pathArena.{u}
    (type_of% (@exists_characteristic_seven_relative_path.{u})) where
  actual := pathActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_seven_relative_path, pathBad, path_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pathBad, ?_, rfl, path_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance⟩, ((fun _ => (0, (0 : K))), (fun _ => (0, 0))),
      ((fun _ => (0, (0 : K))), (fun _ => (0, 1))), ?_⟩
    intro he
    have hz : (0 : K) = 1 := congrArg (fun f => (f 0).2) he
    exact zero_ne_one hz

def pathAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_seven_relative_path.{u}) (Realization pathSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.exists_characteristic_seven_relative_path.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.pathFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pathArena⟩
  objectArena := .source ⟨pathArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathArena ⟨pathFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pathSignature pathActual.readout pathActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
