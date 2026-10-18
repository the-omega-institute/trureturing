import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := LiteralRow
  State C := List (TableRow C)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := Nat × (LiteralRow → RootTree C LiteralRow) × Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ C W => (minimaxValue C W, (fun fallback => minimaxTree C fallback W), (chartList C).length))
  (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ C W => (1, (fun fallback => minimaxTree C fallback W), (chartList C).length))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (C : LiteralRow) (W : List (TableRow C)),
    let out := R.readout () C W
    (if constantTarget W = true then out.1 = 0
     else out.1 = scoreMinimum C W (minimaxValue C)) ∧
    (∀ fallback, (∀ row ∈ W, (rootRun row.type (out.2.1 fallback)).1 = row.target) ∧
      rootDepth (out.2.1 fallback) = out.1) ∧
    (∀ T, (∀ row ∈ W, (rootRun row.type T).1 = row.target) → out.1 ≤ rootDepth T) ∧
    out.2.2 ≤ 3 ^ Fintype.card (Classes C) ∧
    (∀ θ : Chart C, θ ∈ chartList C) ∧
    (∀ θ, computedTarget C θ = target C θ)

private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have hh := (h (.of (.inl false)) []).1
  change (if constantTarget ([] : List (TableRow (.of (.inl false)))) = true
    then 1 = 0 else _) at hh
  simp [constantTarget,rowTargets] at hh

private def zero : LiteralRow := .of (.inl false)
private def row : TableRow zero :=
  { type := fun _ => none,
    admissible := by
      refine ⟨rfl,Finset.card_le_one.mpr ?_,Finset.card_le_one.mpr ?_⟩ <;>
        intro a ha b hb
      all_goals
        have hn := a.property
        simp [zero,labels] at hn,
    target := computedTarget zero (fun _ => none), target_eq := rfl }

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨zero, [], [row], ?_⟩
  intro heq
  have ht := congrArg (fun out : Nat × (LiteralRow → RootTree zero LiteralRow) × Nat =>
    rootRun (fun _ => none) (out.2.1 (.of (.inl false)))) heq
  have hc := (finite_root_minimax zero [row]).2.1 (.of (.inl false)) |>.1 row (by simp)
  have he : minimaxTree zero (.of (.inl false)) [] = .stop (.of (.inl false)) := rfl
  change rootRun (fun _ => none) (minimaxTree zero (.of (.inl false)) []) =
    rootRun (fun _ => none) (minimaxTree zero (.of (.inl false)) [row]) at ht
  have ho := congrArg Prod.fst ht
  rw [he] at ho
  change FreeMagma.of (Sum.inl false) = _ at ho
  change (rootRun (fun _ => none) (minimaxTree zero (.of (.inl false)) [row])).1 = row.target at hc
  rw [hc] at ho
  unfold row computedTarget at ho
  change FreeMagma.of (Sum.inl false) = FreeMagma.of (Sum.inl true) at ho
  cases ho

def family : Registration arena (type_of% (@finite_root_minimax)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_root_minimax,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_root_minimax)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax.finite_root_minimax.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace Admissibility
abbrev signature : Signature where
  Params := LiteralRow
  State C := Classes C → Option Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ C θ => admissibleCode C θ) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ C θ, R.readout () C θ = true ↔ Admissible C θ
private theorem badLaw : ¬ arena.Law bad := by
  intro law
  have h := law (.of (.inl false)) (fun _ => none)
  have good : Admissible (.of (.inl false)) (fun _ => none) :=
    ⟨rfl,by decide,by decide⟩
  have impossible := h.mpr good
  cases impossible
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨.of (.inr 0),(fun _ => some false),(fun _ => some true),?_⟩
  decide +kernel

def family : Registration arena (type_of% (@admissibleCode_spec)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨admissibleCode_spec,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,badLaw⟩,
    fun e => nomatch e⟩
  dependence := dependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@admissibleCode_spec)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax.admissibleCode_spec.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax.Admissibility.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Admissibility
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
