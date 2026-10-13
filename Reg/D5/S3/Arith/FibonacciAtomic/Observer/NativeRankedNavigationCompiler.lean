import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
  (RankedExpr rankedEval)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler

abbrev signature : Signature where
  Params := Nat
  State k := Fin k → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Record k → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => RecordHolds n) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : Nat) (records : List (Record k)) (n : Fin k → Nat),
    (refinementFormula records).Realize n ↔
      ∀ r ∈ records, R.readout () k n r

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  let a : Endpoint 0 := ⟨.ground (.of true),0,[]⟩
  let records : List (Record 0) := [.literal a .alpha]
  let n : Fin 0 → Nat := Fin.elim0
  have hf : (refinementFormula records).Realize n :=
    (rank_only_refinement_compilation 0 records n).mpr (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rfl)
  have h := (law 0 records n).mp hf (.literal a .alpha) (List.mem_singleton_self _)
  exact h

def proof : Registration arena (type_of% (@rank_only_refinement_compilation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_only_refinement_compilation, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1,(fun _ => 0),(fun _ => 1),?_⟩
    intro he
    let a : Endpoint 1 := ⟨.residual 0 (.inl 0),0,[]⟩
    have h := congrFun he (.literal a .alpha)
    have hp : RecordHolds (fun _ : Fin 1 => 0) (.literal a .alpha) := rfl
    have hn : ¬ RecordHolds (fun _ : Fin 1 => 1) (.literal a .alpha) := by
      intro h
      change _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.Reply.beta =
        .alpha at h
      cases h
    change RecordHolds (fun _ : Fin 1 => 0) (.literal a .alpha) =
      RecordHolds (fun _ : Fin 1 => 1) (.literal a .alpha) at h
    exact hn (h ▸ hp)

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler.rank_only_refinement_compilation)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler.rank_only_refinement_compilation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => RecordHolds n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg","body","body","fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
