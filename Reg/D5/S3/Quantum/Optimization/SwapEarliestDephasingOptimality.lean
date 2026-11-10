import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
import Reg.Support.DependentFamily

/-! Source-bound audit of optimal dephasing for every complete greedy history. -/

namespace Reg.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality

open _root_.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the optimal dephasing as the ready-time list varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => dstar x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every ready-time list, history, and greedy-run hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (x : List ℕ) (hs : List ℕ),
    IsGreedyRun x hs → runCost x hs = r.readout () () x

private theorem two_element_run : IsGreedyRun [0, 1] [0] := by
  change IsGreedyStep [0, 1] 0 ∧ (merge [0, 1] 0).length ≤ 1
  refine ⟨⟨by decide, ?_⟩, by decide⟩
  intro j hj
  have hj0 : j = 0 := by
    change j + 1 < 2 at hj
    omega
  subst j
  exact le_rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h [0, 1] [0] two_element_run
  change runCost [0, 1] [0] = 0 at hbad
  norm_num [runCost, swapCost] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), [], [0, 1], ?_⟩
  change dstar [] ≠ dstar [0, 1]
  have hcost := result [0, 1] [0] two_element_run
  norm_num [runCost, swapCost] at hcost
  change 0 ≠ dstar [0, 1]
  omega

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => dstar x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
    definition := some {
      owner := `D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
      name := `D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.result
#print _root_.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
