import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedVertexProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph
open scoped BigOperators Classical
set_option autoImplicit false
noncomputable section
universe u

abbrev lengthSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lengthActual : Realization lengthSignature :=
  realize lengthSignature (fun _ _ n => (circuit n).length) (fun e => Empty.elim e)

def lengthRejected : Realization lengthSignature :=
  realize lengthSignature (fun _ _ _ => 0) (fun e => Empty.elim e)

abbrev lengthArena : Arena where
  signature := lengthSignature
  Law r := ∀ n : ℕ, r.readout () () n = 2 * (n + 2)

private theorem lengthBad : ¬ lengthArena.Law lengthRejected := by
  intro h
  have hh := h 0
  norm_num [lengthRejected, realize] at hh

private theorem lengthDependence : ObservationalDependence lengthSignature lengthActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (circuit 0).length ≠ (circuit 1).length
  rw [circuit_length, circuit_length]
  norm_num

def lengthSource : Registration lengthArena (type_of% @circuit_length) where
  actual := lengthActual
  bridge := Iff.rfl
  variation := ⟨circuit_length, lengthRejected, lengthBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lengthRejected, ?_, rfl, lengthBad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := lengthDependence

abbrev cycleSignature : Signature where
  Params := ℕ
  State n := (evenCycleGraph n).Walk (Sum.inl 0) (Sum.inl 0)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def cycleActual : Realization cycleSignature :=
  realize cycleSignature (fun _ _ p => decide p.IsCycle) (fun e => Empty.elim e)

def cycleRejected : Realization cycleSignature :=
  realize cycleSignature (fun _ _ _ => false) (fun e => Empty.elim e)

abbrev cycleArena : Arena where
  signature := cycleSignature
  Law r := ∀ n : ℕ, r.readout () n (circuit n) = true

private theorem cyclePositive : cycleArena.Law cycleActual := by
  intro n
  exact decide_eq_true (circuit_isCycle n)

private theorem cycleBad : ¬ cycleArena.Law cycleRejected := by
  intro h
  exact Bool.false_ne_true (h 0)

private theorem cycleDependence : ObservationalDependence cycleSignature cycleActual := by
  intro i
  refine ⟨0, .nil, circuit 0, ?_⟩
  change decide (Walk.nil : (evenCycleGraph 0).Walk (Sum.inl 0) (Sum.inl 0)).IsCycle ≠
    decide (circuit 0).IsCycle
  rw [decide_eq_true (circuit_isCycle 0)]
  simp

def cycleSource : Registration cycleArena (type_of% @circuit_isCycle) where
  actual := cycleActual
  bridge := by simp [cycleArena, cycleActual, realize]
  variation := ⟨cyclePositive, cycleRejected, cycleBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cycleRejected, ?_, rfl, cycleBad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := cycleDependence

abbrev alphaSignature : Signature where
  Params := Σ _A : Type u, ℕ
  State p := Sym2 (Fin (p.2 + 2) ⊕ Fin (p.2 + 2)) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Sym2 (Fin (p.2 + 2) ⊕ Fin (p.2 + 2)) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def alphaActual : Realization alphaSignature.{u} :=
  realize alphaSignature (fun _ _ w => w) (fun e => Empty.elim e)

def alphaRejected : Realization alphaSignature.{u} :=
  realize alphaSignature (fun _ _ w => fun _ => w s(Sum.inl 0, Sum.inr 0)) (fun e => Empty.elim e)

abbrev alphaArena : Arena where
  signature := alphaSignature.{u}
  Law r := ∀ {A : Type u} [CommGroup A] (n : ℕ)
    (w : Sym2 (Fin (n + 2) ⊕ Fin (n + 2)) → A),
    alpha (r.readout () ⟨A, n⟩ w) (circuit n) =
      (∏ i, w s(Sum.inl i, Sum.inr (finRotate (n + 2) i))) /
        ∏ i : Fin (n + 2), w s(Sum.inl i, Sum.inr i)

private theorem alphaBad : ¬ alphaArena.{u}.Law alphaRejected := by
  intro h
  let g : ULift.{u} (Multiplicative ℤ) := ⟨Multiplicative.ofAdd 1⟩
  let w : Sym2 (Fin 2 ⊕ Fin 2) → ULift.{u} (Multiplicative ℤ) :=
    fun s => if s = s(Sum.inl 0, Sum.inr 1) then g else 1
  have hh := @h (ULift.{u} (Multiplicative ℤ)) inferInstance 0 w
  change alpha (fun _ => w s(Sum.inl 0, Sum.inr 0)) (circuit 0) = _ at hh
  rw [circuit_alpha] at hh
  norm_num [w, Fin.prod_univ_two, Sym2.eq_iff, finRotate_apply] at hh
  have hx : ∀ x : Fin 2, ¬ (x = 0 ∧ x = 1) := by
    intro x hx
    rcases hx with ⟨rfl, hx⟩
    exact (by decide : (0 : Fin 2) ≠ 1) hx
  simp only [hx, ite_false, Finset.prod_const_one, div_one] at hh
  have hc := congrArg (fun a : ULift.{u} (Multiplicative ℤ) => Multiplicative.toAdd a.down) hh
  norm_num [g] at hc

private theorem alphaDependence : ObservationalDependence alphaSignature.{u} alphaActual := by
  intro i
  refine ⟨⟨ULift.{u} (Multiplicative ℤ), 0⟩, (fun _ => 1),
    (fun _ => ⟨Multiplicative.ofAdd 1⟩), ?_⟩
  intro h
  have hh := congrArg (fun w : Sym2 (Fin 2 ⊕ Fin 2) → ULift.{u} (Multiplicative ℤ) =>
    Multiplicative.toAdd (w s(Sum.inl 0, Sum.inr 0)).down) h
  change (0 : ℤ) = 1 at hh
  omega

def alphaSource : Registration alphaArena.{u} (type_of% @circuit_alpha.{u}) where
  actual := alphaActual
  bridge := Iff.rfl
  variation := ⟨circuit_alpha, alphaRejected, alphaBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨alphaRejected, ?_, rfl, alphaBad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := alphaDependence

def lengthRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@circuit_length) (Realization lengthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.length
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.lengthSource
  realizationSource := none
  generated := false
  arena := .source ⟨lengthArena⟩
  objectArena := .source ⟨lengthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthArena ⟨lengthSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lengthSignature (fun _ _ n => (circuit n).length) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms lengthSource
#print axioms lengthRegistration

def cycleRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@circuit_isCycle) (Realization cycleSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.cycle
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.cycleSource
  realizationSource := none
  generated := false
  arena := .source ⟨cycleArena⟩
  objectArena := .source ⟨cycleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cycleArena ⟨cycleSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cycleSignature (fun _ _ p => decide p.IsCycle) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms cycleSource
#print axioms cycleRegistration

def alphaRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@circuit_alpha.{u}) (Realization alphaSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.alpha
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk.alphaSource
  realizationSource := none
  generated := false
  arena := .source ⟨alphaArena.{u}⟩
  objectArena := .source ⟨alphaArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source alphaArena.{u} ⟨alphaSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize alphaSignature.{u} (fun _ _ w => w) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms alphaSource
#print axioms alphaRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
