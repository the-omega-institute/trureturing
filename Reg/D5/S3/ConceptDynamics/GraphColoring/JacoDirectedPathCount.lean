import D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance] directed

abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ+) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => n.val) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ+,
    Finite (Shortest n) ∧ Nonempty (Shortest n) ∧ 0 < psi n.val ∧
      (∀ r : ℕ, n.val ≤ r →
        ∃ e : TruncatedPath r 1 n ≃ TruncatedPath (R.readout () () n) 1 n,
          ∀ p, (e p).val.length = p.val.length)

private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 1, 2, by change (1 : ℕ) ≠ 2; omega⟩

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := (h 1).2.2.2 1 le_rfl
  let p : TruncatedPath 1 (1 : ℕ+) 1 := ⟨.nil, by simp⟩
  have hx := (e p).property 1 (e p).val.start_mem_vertices
  change (1 : ℕ) ≤ 0 at hx
  omega

def evidence : Registration arena (type_of% @path_count_foundations) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨path_count_foundations, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@path_count_foundations) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.path_count_foundations.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "body", "body", "fn", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
namespace Distance

abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ l => Nat.fib (l + 2)) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law R := ∀ (l : ℕ) (n : ℕ+),
    ((∃ p : TruncatedPath n.val 1 n, p.val.length ≤ l) ↔ n.val ≤ R.readout () () l) ∧
    (∀ p : Shortest n, p.val.val.length ≤ l ↔ n.val ≤ R.readout () () l)
private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 0, 1, by change Nat.fib 2 ≠ Nat.fib 3; decide⟩
private theorem bad : ¬ arena.Law rejected := by
  intro h
  let p : TruncatedPath 1 (1 : ℕ+) 1 := ⟨.nil, by simp⟩
  have hx := (h 0 1).1.mp ⟨p, le_rfl⟩
  change (1 : ℕ) ≤ 0 at hx
  omega

def evidence : Registration arena (type_of% @fibonacci_distance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_distance, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@fibonacci_distance) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.fibonacci_distance.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.Distance.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ l => Nat.fib (l + 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
end Distance

namespace Original

abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => psi n) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law R := ∀ k : ℕ, 7 ≤ k → ∀ i : ℕ, Nat.fib i < k → k ≤ Nat.fib (i + 1) →
    ((outdegree (k - 1) ≠ outdegree k ∧ outdegree k ≠ outdegree (k + 1)) ↔
      (R.readout () () (k - 1) ≠ R.readout () () k ∧
        R.readout () () k ≠ R.readout () () (k + 1)))

private theorem at_eight : outdegree 7 ≠ outdegree 8 ∧ outdegree 8 ≠ outdegree 9 := by
  decide +kernel

private theorem depends : ObservationalDependence sig actual := by
  intro i
  refine ⟨(), 7, 8, ?_⟩
  have h := (result 8 (by decide) 5 (by decide) (by decide)).mp at_eight
  exact h.1

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hx := (h 8 (by decide) 5 (by decide) (by decide)).mp at_eight
  change (0 : ℕ) ≠ 0 ∧ (0 : ℕ) ≠ 0 at hx
  exact hx.1 rfl

def evidence : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.result.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount.Original.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => psi n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
end Original
end
end Reg.D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount
