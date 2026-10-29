import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMixedImageConstruction
import Reg.Support.DependentFamily

/-! Observe original positive expression equality over the entire source family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeMixedImageConstruction
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.GenealogicalFiberTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMixedImageConstruction

noncomputable section

abbrev signature : Signature where
  Params := Σ X : Type, List (MixedExpr X × MixedExpr X)
  State q := q.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => @decide (∀ e ∈ q.2, eval v e.1 = eval v e.2)
    (Classical.propDecidable _)) (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : Type) (E : List (MixedExpr X × MixedExpr X)) (v : X → Source),
    R.readout () ⟨X,E⟩ v = true ↔ ∀ q ∈ flatten E, q.Holds (extend v)

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, decide_eq_true_eq] using (@flatten_exact)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h Empty [] Empty.elim).mpr (by intro q hq; cases hq)
  exact Bool.noConfusion bad

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  let E : List (MixedExpr Unit × MixedExpr Unit) :=
    [(.residual 0 (), .ground (.of true))]
  let v : Unit → Source := fun _ => .of true
  let w : Unit → Source := fun _ => .of false
  have good : ∀ e ∈ E, eval v e.1 = eval v e.2 := by simp [E, v, eval]
  have bad : ¬ ∀ e ∈ E, eval w e.1 = eval w e.2 := by simp [E, w, eval]
  refine ⟨⟨Unit,E⟩,v,w,?_⟩
  simp only [actual, realize, good, bad, decide_true, decide_false]
  decide

def evidence : Registration arena (type_of% (@flatten_exact)) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatten_exact) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeMixedImageConstruction.flatten_exact.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMixedImageConstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q v => @decide (∀ e ∈ q.2, eval v e.1 = eval v e.2)
      (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun X : Type => X → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMixedImageConstruction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMixedImageConstruction
