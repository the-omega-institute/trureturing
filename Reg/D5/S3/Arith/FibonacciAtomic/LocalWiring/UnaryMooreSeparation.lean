import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation
import Reg.Support.DependentFamily

/-! The actual output of the selected unary source at a fixed bound and index. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p word => generated p.1 word p.2) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (K : Nat) (_hK : 1 ≤ K),
    (∀ (word : List Bool) (i : Nat) (Q : Type) [Fintype Q] (m : Machine Q),
      Fintype.card Q ≤ K → word = observations m (2*K-1) →
      F.readout () ⟨K, i⟩ word = some (m.emit i)) ∧
    (∀ (Q R : Type) [Fintype Q] [Fintype R] (m : Machine Q) (m' : Machine R),
      Fintype.card Q ≤ K → Fintype.card R ≤ K →
      observations m (2*K-1) = observations m' (2*K-1) → ∀ i, m.emit i = m'.emit i) ∧
    (∀ (word : List Bool) (Q : Type) [Fintype Q] (m : Machine Q),
      Fintype.card Q ≤ K → word = observations m (2*K-1) →
      ∃ x, synthesize K word = some x ∧
        0 < x.1 ∧ x.1 ≤ K ∧ (∀ i, (Table.machine x.2).emit i = m.emit i) ∧
        ∃ earlier later, allTables K = earlier ++ x :: later ∧ ∀ y ∈ earlier,
          observations (Table.machine y.2) (2*K-1) ≠ word) ∧
    (∀ (Q : Type) (m : Machine Q) (i : Nat), m.emit i = m.label (m.transition^[i] m.start)) ∧
    (allTables K).length =
      ((List.range K).map (fun n => (n+1)^(n+2)*2^(n+1))).sum

private def constantMachine (b : Bool) : Machine (Fin 1) :=
  ⟨id, fun _ => b, 0⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : Fintype.card (Fin 1) ≤ 1 := by simp
  have bad := (h 1 (by decide)).1 [false] 0 (Fin 1) (constantMachine false) hn rfl
  change (none : Option Bool) = some false at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let m₀ := constantMachine false
  let m₁ := constantMachine true
  refine ⟨⟨1, 0⟩, [false], [true], ?_⟩
  change generated 1 [false] 0 ≠ generated 1 [true] 0
  have hn : Fintype.card (Fin 1) ≤ 1 := by simp
  have good := (unary_moore_separation_and_synthesis 1 (by decide)).1
  rw [good [false] 0 _ m₀ hn rfl, good [true] 0 _ m₁ hn rfl]
  decide

def family : Registration arena (type_of% unary_moore_separation_and_synthesis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unary_moore_separation_and_synthesis, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unary_moore_separation_and_synthesis) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation
