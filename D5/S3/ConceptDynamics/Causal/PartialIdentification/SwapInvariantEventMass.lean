/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/SwapInvariantEventMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/SwapInvariantEventMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Swap-connected causal orders induce identical finite event masses, event profiles, and linear query values under every exogenous law. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.SwapClosureExtensionInvariance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Library-search audit trail (2026-09-03):
   * `SwapClosureExtensionInvariance` proves pointwise equality of structural
     response readouts across a certified swap chain.
   * `CausalOrderLinearProgram` compiles finite signature events to linear
     objectives, but the repository had no bridge from order-level semantic
     equality to equality of event statistics under an exogenous law.
   * This module proves that bridge without assuming positivity or
     normalization. Probability-law hypotheses remain separate from the pure
     extension-invariance identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.SwapInvariantEventMass

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.PartialIdentification.AdjacentIncomparableSwapInvariance
open D5.S3.ConceptDynamics.Causal.PartialIdentification.SwapClosureExtensionInvariance

/-- The mass of a Boolean event evaluated after structural execution in one
chosen total order. -/
def eventMass
    {Node X U : Type*} [DecidableEq Node] [Fintype U]
    (system : ParentLocalSystem Node X)
    (initial : U -> Node -> X)
    (order : List Node)
    (exogenousMass : U -> ℚ)
    (event : (Node -> X) -> Bool) : ℚ :=
  ∑ u, exogenousMass u *
    if event (responseProfile system initial order u) then 1 else 0

/-- Swap-connected orders give the same mass to every final-state event under
any fixed finite exogenous law. -/
theorem eventMass_invariant_of_swap_chain
    {Node X U : Type*} [DecidableEq Node] [Fintype U]
    (system : ParentLocalSystem Node X)
    (initial : U -> Node -> X)
    (exogenousMass : U -> ℚ)
    (event : (Node -> X) -> Bool)
    {before after : List Node}
    (chain : SwapChain system before after) :
    eventMass system initial before exogenousMass event =
      eventMass system initial after exogenousMass event := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro u _
  rw [query_readout_invariant_of_swap_chain
    system initial event chain u]

/-- The vector of masses for a finite family of compiled event readouts. -/
def eventMassProfile
    {Node X U Event : Type*}
    [DecidableEq Node] [Fintype U]
    (system : ParentLocalSystem Node X)
    (initial : U -> Node -> X)
    (order : List Node)
    (exogenousMass : U -> ℚ)
    (event : Event -> (Node -> X) -> Bool) : Event -> ℚ :=
  fun eventIndex =>
    eventMass system initial order exogenousMass (event eventIndex)

/-- Every finite event profile is extension invariant along a swap chain. -/
theorem eventMassProfile_invariant_of_swap_chain
    {Node X U Event : Type*}
    [DecidableEq Node] [Fintype U]
    (system : ParentLocalSystem Node X)
    (initial : U -> Node -> X)
    (exogenousMass : U -> ℚ)
    (event : Event -> (Node -> X) -> Bool)
    {before after : List Node}
    (chain : SwapChain system before after) :
    eventMassProfile system initial before exogenousMass event =
      eventMassProfile system initial after exogenousMass event := by
  funext eventIndex
  exact eventMass_invariant_of_swap_chain
    system initial exogenousMass (event eventIndex) chain

/-- A finite linear scalar query on an event-mass profile. -/
def linearEventQuery
    {Event : Type*} [Fintype Event]
    (coefficient profile : Event -> ℚ) : ℚ :=
  ∑ eventIndex, coefficient eventIndex * profile eventIndex

/-- Any finite linear objective assembled from extension-invariant event masses
has the same value under swap-connected causal orders. -/
theorem linearEventQuery_invariant_of_swap_chain
    {Node X U Event : Type*}
    [DecidableEq Node] [Fintype U] [Fintype Event]
    (system : ParentLocalSystem Node X)
    (initial : U -> Node -> X)
    (exogenousMass : U -> ℚ)
    (event : Event -> (Node -> X) -> Bool)
    (coefficient : Event -> ℚ)
    {before after : List Node}
    (chain : SwapChain system before after) :
    linearEventQuery coefficient
        (eventMassProfile system initial before exogenousMass event) =
      linearEventQuery coefficient
        (eventMassProfile system initial after exogenousMass event) := by
  rw [eventMassProfile_invariant_of_swap_chain
    system initial exogenousMass event chain]

#print axioms eventMass_invariant_of_swap_chain
#print axioms eventMassProfile_invariant_of_swap_chain
#print axioms linearEventQuery_invariant_of_swap_chain

end D5.S3.ConceptDynamics.Causal.PartialIdentification.SwapInvariantEventMass
