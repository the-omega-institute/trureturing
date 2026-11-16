import Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Graph
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Result (rev3 rev3_adj rev3_connected rev3_deleted run3 run_nonempty)

namespace Adj
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : Equiv.Perm (Fin n), Fin n
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => (valueGraph p.2.1).Adj p.2.2 v) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n), R.readout () ⟨n,π,u⟩ v ↔
    (u < v ∧ π.symm v < π.symm u) ∨ (v < u ∧ π.symm u < π.symm v)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (@h 3 rev3 0 1).mpr ((value_adj rev3 0 1).mp (rev3_adj 0 1 (by decide)))
def family : Registration arena (type_of% (@value_adj)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@value_adj, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨3,rev3,0⟩, 1, 0, ?_⟩
    intro h
    have hadj := Eq.mp h (rev3_adj 0 1 (by decide))
    change (valueGraph rev3).Adj 0 0 at hadj
    exact hadj.ne rfl
noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@value_adj) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.value_adj.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Graph.Adj.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => (valueGraph p.2.1).Adj p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Graph
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Adj

namespace Start
abbrev signature : Signature where
  Params := Σ n : ℕ, Equiv.Perm (Fin n)
  State p := Finset (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p S => EarRun p.2 S)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 3 ≤ n),
    (valueGraph π).Connected → (∀ v, ((valueGraph π).induce {v}ᶜ).Connected) →
    ∃ S : Finset (Fin n), R.readout () ⟨n,π⟩ S ∧
      (⟨0, by omega⟩ : Fin n) ∈ S ∧ π.symm ⟨0, by omega⟩ ∈ S
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨S,hS,_,_⟩ := @h 3 rev3 (by omega) rev3_connected rev3_deleted
  exact hS
def family : Registration arena (type_of% (@anchored_start)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@anchored_start, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨3,rev3⟩, Finset.univ, ∅, ?_⟩
    intro h
    have hrun : EarRun rev3 ∅ := Eq.mp h run3
    exact Finset.not_nonempty_empty (run_nonempty hrun)
noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@anchored_start) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.anchored_start.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Graph.Start.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => EarRun p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Graph
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Start
end Reg.D5.S3.Combinatorics.Permutation.Verkama62Graph
