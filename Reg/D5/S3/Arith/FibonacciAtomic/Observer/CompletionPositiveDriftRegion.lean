import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, Σ _E : System k m,
    Σ _mode : Fin k → Bool, Σ _param : Fin k → Nat, (Fin m → CompletionTree) → Prop
  State p := Fin p.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p v => decide
    (Solution p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 v)) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (E : System k m) (mode : Fin k → Bool)
    (param : Fin k → Nat) (root : Fin m) (c : PositiveCycle E root)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree),
    (R.readout () ⟨k, m, E, mode, param, extra⟩ v = true ↔
      FiniteAlternative c mode param extra v ∨ InfiniteAlternative c mode param extra v) ∧
    ¬ (FiniteAlternative c mode param extra v ∧ InfiniteAlternative c mode param extra v)

private def cycleSystem : System 0 1 :=
  [(.var 2 0, .pair (.var 0 0) (.ground (.of true)))]

private def cycleEdge : Edge cycleSystem 0 0 where
  headPower := 2
  occPower := 0
  address := [false]
  occurrence := ⟨.pair (.var 0 0) (.ground (.of true)),
    .original (List.mem_singleton_self _), .left (.var 0 0)⟩

private def cycle : PositiveCycle cycleSystem 0 where
  walk := .snoc (.nil 0) cycleEdge
  strict := by simp [Walk.Strict, cycleEdge]
  positive := by norm_num [Walk.weight, cycleEdge]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let mode : Fin 0 → Bool := fun i => nomatch i
  let param : Fin 0 → Nat := fun i => nomatch i
  let v : Fin 1 → CompletionTree := fun _ => Omega
  have alternatives := (law cycleSystem mode param 0 cycle (fun _ => False) v).1.mp rfl
  have sol := (positive_drift_region_split cycleSystem mode param 0 cycle
    (fun _ => False) v).1.mpr alternatives
  exact sol.2

private theorem leaf_ne (a b : Bool) (hab : a ≠ b) : leaf a ≠ leaf b := by
  intro h
  have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
  have hsum : (Sum.inl a : Bool ⊕ Unit) = Sum.inl b := by
    simpa only [leaf, PFunctor.M.dest_mk] using hh
  exact hab (Sum.inl.inj hsum)

def evidence : Registration arena (type_of% (@positive_drift_region_split)) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro k m E mode param root c extra v
    simpa only [actual, realize, decide_eq_true_eq] using
      positive_drift_region_split E mode param root c extra v,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let extra : (Fin 1 → CompletionTree) → Prop := fun v => v 0 = leaf true
    refine ⟨⟨0, 1, [], (fun j => nomatch j), (fun j => nomatch j), extra⟩,
      (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    have hne : leaf false ≠ leaf true := leaf_ne false true (by decide)
    simp [actual, realize, Solution, Satisfies, extra, hne]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.positive_drift_region_split)
    (type_of% (realize signature (fun _ p v => decide
      (Solution p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 v))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.positive_drift_region_split.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p v => decide
    (Solution p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 v)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion,
    definition := none, coordinates := #[0, 1, 2, 3, 4, 7],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
