/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/AdjacentIncomparableSwapInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/AdjacentIncomparableSwapInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjacent parent-independent structural updates commute, so swapping incomparable neighboring nodes preserves evaluation and every readout. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * `QueryImpliedCausalOrder` extracts strict precedence obligations from a
     counterfactual query, but it does not prove invariance across compatible
     total extensions.
   * `StructuralEvaluationSemantics` and
     `ParentOrderedStructuralEvaluationSemantics` evaluate one certified order,
     but contain no adjacent-swap theorem.
   * Repository searches found no theorem connecting two causal evaluation
     orders by commuting neighboring parent-independent updates.
   * This module proves the local generator needed by the extension-invariance
     programme. A separate connectivity theorem is still required to pass from
     one adjacent swap to arbitrary finite linear extensions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.AdjacentIncomparableSwapInvariance

/-- A scalar state functional ignores one coordinate when replacing that
coordinate never changes its value. -/
def IgnoresCoordinate
    {Node X : Type*} [DecidableEq Node]
    (functional : (Node -> X) -> X)
    (coordinate : Node) : Prop :=
  forall state value,
    functional (Function.update state coordinate value) = functional state

/-- One deterministic structural update. The selected coordinate is replaced
by its local equation evaluated in the current state. -/
def evaluateNode
    {Node X : Type*} [DecidableEq Node]
    (equation : Node -> (Node -> X) -> X)
    (node : Node)
    (state : Node -> X) : Node -> X :=
  Function.update state node (equation node state)

/-- Two distinct structural updates commute when each local equation ignores
the coordinate written by the other update. -/
theorem evaluateNode_comm_of_mutual_irrelevance
    {Node X : Type*} [DecidableEq Node]
    (equation : Node -> (Node -> X) -> X)
    (left right : Node)
    (left_ne_right : left ≠ right)
    (left_ignores_right : IgnoresCoordinate (equation left) right)
    (right_ignores_left : IgnoresCoordinate (equation right) left)
    (state : Node -> X) :
    evaluateNode equation right (evaluateNode equation left state) =
      evaluateNode equation left (evaluateNode equation right state) := by
  unfold evaluateNode
  rw [right_ignores_left state (equation left state)]
  rw [left_ignores_right state (equation right state)]
  funext node
  by_cases node_eq_left : node = left
  · subst node
    simp [left_ne_right]
  · by_cases node_eq_right : node = right
    · subst node
      simp [left_ne_right, node_eq_left]
    · simp [node_eq_left, node_eq_right]

/-- A finite structural system whose local equation sees only the displayed
parent coordinates. -/
structure ParentLocalSystem
    (Node X : Type*) [DecidableEq Node] where
  parents : Node -> Finset Node
  equation : (node : Node) -> (parents node -> X) -> X

/-- Evaluate one local equation by restricting the ambient state to the
certified parent coordinates. -/
def localValue
    {Node X : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (node : Node)
    (state : Node -> X) : X :=
  system.equation node (fun parent => state parent.1)

/-- Updating a coordinate outside a node's parent set leaves that node's local
value unchanged. -/
theorem localValue_ignores_nonparent
    {Node X : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (node coordinate : Node)
    (coordinate_not_parent : coordinate ∉ system.parents node) :
    IgnoresCoordinate (localValue system node) coordinate := by
  intro state value
  unfold localValue
  apply congrArg (system.equation node)
  funext parent
  have parent_ne_coordinate : parent.1 ≠ coordinate := by
    intro parent_eq
    apply coordinate_not_parent
    simpa [parent_eq] using parent.2
  simp [parent_ne_coordinate]

/-- One update of a parent-local structural system. -/
def localEvaluateNode
    {Node X : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (node : Node)
    (state : Node -> X) : Node -> X :=
  evaluateNode (localValue system) node state

/-- Distinct nodes with no direct parent edge in either direction have
commuting parent-local updates. -/
theorem localEvaluateNode_comm_of_no_direct_edges
    {Node X : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (left right : Node)
    (left_ne_right : left ≠ right)
    (right_not_parent_of_left : right ∉ system.parents left)
    (left_not_parent_of_right : left ∉ system.parents right)
    (state : Node -> X) :
    localEvaluateNode system right (localEvaluateNode system left state) =
      localEvaluateNode system left (localEvaluateNode system right state) := by
  exact evaluateNode_comm_of_mutual_irrelevance
    (localValue system) left right left_ne_right
    (localValue_ignores_nonparent
      system left right right_not_parent_of_left)
    (localValue_ignores_nonparent
      system right left left_not_parent_of_right)
    state

/-- Execute a list of state transformations from left to right. -/
def evaluateOrder
    {Node State : Type*}
    (step : Node -> State -> State) :
    List Node -> State -> State
  | [], state => state
  | node :: remaining, state =>
      evaluateOrder step remaining (step node state)

/-- A commuting pair of neighboring steps may be swapped inside any prefix and
suffix without changing the final state. -/
theorem evaluateOrder_adjacent_swap
    {Node State : Type*}
    (step : Node -> State -> State)
    (left right : Node)
    (commutes : forall state,
      step right (step left state) = step left (step right state))
    (prefix suffix : List Node)
    (state : State) :
    evaluateOrder step (prefix ++ left :: right :: suffix) state =
      evaluateOrder step (prefix ++ right :: left :: suffix) state := by
  induction prefix generalizing state with
  | nil =>
      simp only [List.nil_append, evaluateOrder]
      rw [commutes state]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, evaluateOrder]
      exact inductionHypothesis (step head state)

/-- Swapping adjacent parent-independent nodes preserves the complete state
produced by a finite parent-local structural evaluation. -/
theorem parent_local_evaluation_invariant_under_adjacent_swap
    {Node X : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (left right : Node)
    (left_ne_right : left ≠ right)
    (right_not_parent_of_left : right ∉ system.parents left)
    (left_not_parent_of_right : left ∉ system.parents right)
    (prefix suffix : List Node)
    (state : Node -> X) :
    evaluateOrder (localEvaluateNode system)
        (prefix ++ left :: right :: suffix) state =
      evaluateOrder (localEvaluateNode system)
        (prefix ++ right :: left :: suffix) state := by
  exact evaluateOrder_adjacent_swap
    (localEvaluateNode system) left right
    (localEvaluateNode_comm_of_no_direct_edges
      system left right left_ne_right
      right_not_parent_of_left left_not_parent_of_right)
    prefix suffix state

/-- Every readout of the final structural state is invariant under the same
adjacent swap. This is the local query-invariance certificate needed before
comparing LPs compiled from different total extensions. -/
theorem readout_invariant_under_adjacent_swap
    {Node X QueryValue : Type*} [DecidableEq Node]
    (system : ParentLocalSystem Node X)
    (readout : (Node -> X) -> QueryValue)
    (left right : Node)
    (left_ne_right : left ≠ right)
    (right_not_parent_of_left : right ∉ system.parents left)
    (left_not_parent_of_right : left ∉ system.parents right)
    (prefix suffix : List Node)
    (state : Node -> X) :
    readout
        (evaluateOrder (localEvaluateNode system)
          (prefix ++ left :: right :: suffix) state) =
      readout
        (evaluateOrder (localEvaluateNode system)
          (prefix ++ right :: left :: suffix) state) := by
  exact congrArg readout
    (parent_local_evaluation_invariant_under_adjacent_swap
      system left right left_ne_right
      right_not_parent_of_left left_not_parent_of_right
      prefix suffix state)

#print axioms evaluateNode_comm_of_mutual_irrelevance
#print axioms localEvaluateNode_comm_of_no_direct_edges
#print axioms parent_local_evaluation_invariant_under_adjacent_swap
#print axioms readout_invariant_under_adjacent_swap

end D5.S3.ConceptDynamics.Causal.PartialIdentification.AdjacentIncomparableSwapInvariance
