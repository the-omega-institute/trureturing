/- Transient cost comparison. Every branch, original cache update, lower
bound and actual symmetry cut is retained. A complete value list replaces
the recursive Decidable-forall machinery, with a proved transfer to check.
This probe does not establish complete global acceptance. -/
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalListCostPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check checked_split)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

section Generic
variable {Coord Value Sym State : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

def listCheck (values : List Value)
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : State → Coord → Value → State) (lower : State → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ) :
    ℕ → Fin N → State → Partial Coord Value → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, p =>
    match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominates s p
    | .split i children => values.all fun a =>
        listCheck values nodes step lower dominates gap fuel (children a)
          (step cache i a) (Function.update p i (some a))

theorem list_checked (values : List Value) (complete : ∀ a, a ∈ values)
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : State → Coord → Value → State) (lower : State → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (fuel : ℕ) (index : Fin N) (cache : State) (p : Partial Coord Value)
    (accepted : listCheck values nodes step lower dominates gap fuel index cache p = true) :
    check nodes step lower dominates gap fuel index cache p = true := by
  induction fuel generalizing index cache p with
  | zero => simpa only [listCheck, check] using accepted
  | succ fuel ih =>
    cases node : nodes (fuel + 1) index with
    | bound => simpa only [listCheck, check, node] using accepted
    | symmetry s => simpa only [listCheck, check, node] using accepted
    | split i children =>
      simp only [listCheck, node] at accepted
      apply checked_split nodes step lower dominates gap fuel index cache p i children node
      intro a
      exact ih (children a) (step cache i a) (Function.update p i (some a))
        ((List.all_eq_true.mp accepted) a (complete a))
end Generic

private def actualInitial : Cache :=
  ⟨fun _ => ⟨(41293, (0, 0)), EJMTriangleCacheData.mirror 41293⟩,
   fun _ => ⟨(8688, (0, 0)), EJMSingletonCacheData.mirror 8688⟩⟩

private def prefixOutcomes : Fin 15 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def cache : Cache :=
  (List.finRange 15).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (prefixOutcomes i))
    actualInitial
private def partialEvent : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 15 then some (prefixOutcomes ⟨g.val, h⟩) else none

set_option maxHeartbeats 100000000 in
set_option trace.profiler true in
private theorem suffix_list_accepted :
    listCheck (List.finRange 4) EJMOriginalGlobalDAGData.nodes step lower
      EJMGlobalScoreSymmetry.dominates scale 6 ⟨55, by decide⟩ cache partialEvent = true := by
  decide +kernel

private theorem exact_original_context :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨55, by decide⟩ cache partialEvent = true :=
  list_checked (List.finRange 4) List.mem_finRange EJMOriginalGlobalDAGData.nodes
    step lower EJMGlobalScoreSymmetry.dominates scale 6 ⟨55, by decide⟩ cache partialEvent
    suffix_list_accepted

#print axioms list_checked
#print axioms exact_original_context
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalListCostPilot
