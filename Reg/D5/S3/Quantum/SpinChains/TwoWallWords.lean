import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TwoWallWords
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.TwoWallWords

namespace Reg.D5.S3.Quantum.SpinChains.TwoWallWords
universe u

abbrev countSignature : Signature where
  Params := ℕ × ℕ × Letter
  State p := Pos p.1 p.2.1 → Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization countSignature :=
  realize countSignature (fun _ p w => count p.2.2 w) (fun e => nomatch e)
def shifted : Realization countSignature :=
  realize countSignature (fun _ p w => count p.2.2 w + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := countSignature
  Law R := ∀ (K : Type u) [Field K] (a b : ℕ),
    (∀ (c : Letter) (p : Pos a b) (w : Pos a b → Letter),
      count c (fun q => w (Equiv.swap p (p + 1) q)) = R.readout () (a,b,c) w) ∧
    (∀ (t : Pos a b) (w : Word a b),
      translation K t (delta K w) = delta K (rotate t w)) ∧
    (∀ (i : Fin 3) (w : Word a b),
      F K a b i (delta K w) = ∑ p, bond K i p w) ∧
    U K a b ^ (a + b + 2) = 1 ∧
    (∀ i : Fin 3, Commute (U K a b) (F K a b i)) ∧
    (∀ ξ : Fin 3 → K, Commute (U K a b) (T K a b ξ))

theorem rejected_law : ¬ arena.{u}.Law shifted := by
  intro law
  have h := (law (ULift.{u} ℚ) 0 0).1 one 0 (fun _ => two)
  norm_num [shifted, realize, count, one, two] at h

theorem actual_dependence : ObservationalDependence countSignature actual := by
  intro i
  refine ⟨(0,0,one), (fun _ => one), (fun _ => two), ?_⟩
  simp [actual, realize, count, one, two]

def family : Registration arena.{u} (type_of% @cyclic_action.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_action.{u}, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cyclic_action.{u}) (Realization countSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWords.cyclic_action.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TwoWallWords.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize countSignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TwoWallWords
    definition := none
    coordinates := #[2,3,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.SpinChains.TwoWallWords
