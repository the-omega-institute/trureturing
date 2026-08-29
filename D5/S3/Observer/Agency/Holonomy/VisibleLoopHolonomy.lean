/- GID: D5/S3/Observer/Agency/Holonomy/VisibleLoopHolonomy
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Holonomy/VisibleLoopHolonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointed holonomy is a visible return with nontrivial hidden transport; strategy factorization hides policy drift, while a faithful joint readout rules out hidden loops. -/

import D5.S3.Observer.Agency.Self.AgencyEnrichment
import D5.S3.ObserverMemory.RefinementClosure.BehaviorUpdateWordAction

/- Library-search audit trail (2026-08-29):
   * The canonical controlled word action is `runWord`; it is reused directly.
   * The canonical current-strategy pair is `agencyEnrichment`.
   * Repository search found no exact pointed visible-loop criterion, so this
     module adds predicates only after making the base-return condition explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Agency.Holonomy.VisibleLoopHolonomy

open D5.S3.Observer.Agency.Self.AgencyEnrichment
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

universe u v w z

/-- A finite action word forms a loop relative to the chosen visible readout at
a specified base state. -/
def VisibleLoopAt
    {U : Type u} {H : Type v} {B : Type w}
    (update : U -> H -> H) (readout : H -> B)
    (word : List U) (state : H) : Prop :=
  readout (runWord update word state) = readout state

/-- The pointed transport changes the hidden state, without yet asserting a
visible return. -/
def NontrivialTransportAt
    {U : Type u} {H : Type v}
    (update : U -> H -> H) (word : List U) (state : H) : Prop :=
  runWord update word state ≠ state

/-- Pointed holonomy is exactly a visible return together with nontrivial
hidden-state transport. -/
def PointedHolonomyAt
    {U : Type u} {H : Type v} {B : Type w}
    (update : U -> H -> H) (readout : H -> B)
    (word : List U) (state : H) : Prop :=
  VisibleLoopAt update readout word state ∧
    NontrivialTransportAt update word state

/-- Strategy detects the pointed transport. -/
def StrategyVisibleHolonomyAt
    {U : Type u} {H : Type v} {P : Type z}
    (update : U -> H -> H) (strategy : H -> P)
    (word : List U) (state : H) : Prop :=
  strategy (runWord update word state) ≠ strategy state

/-- Strategy change on a visible loop certifies pointed holonomy, including
both the visible-return and hidden-transport clauses. -/
theorem visible_loop_policy_change_witnesses_pointed_holonomy
    {U : Type u} {H : Type v} {B : Type w} {P : Type z}
    (update : U -> H -> H) (readout : H -> B) (strategy : H -> P)
    (word : List U) (state : H)
    (visibleLoop : VisibleLoopAt update readout word state)
    (strategyChanges : StrategyVisibleHolonomyAt update strategy word state) :
    PointedHolonomyAt update readout word state := by
  refine ⟨visibleLoop, ?_⟩
  intro stateReturns
  exact strategyChanges (congrArg strategy stateReturns)

/-- The hidden-transport component of the pointed-holonomy witness. -/
theorem visible_loop_policy_change_implies_nontrivial_transport
    {U : Type u} {H : Type v} {B : Type w} {P : Type z}
    (update : U -> H -> H) (readout : H -> B) (strategy : H -> P)
    (word : List U) (state : H)
    (visibleLoop : VisibleLoopAt update readout word state)
    (strategyChanges : StrategyVisibleHolonomyAt update strategy word state) :
    NontrivialTransportAt update word state :=
  (visible_loop_policy_change_witnesses_pointed_holonomy
    update readout strategy word state visibleLoop strategyChanges).2

/-- If strategy factors through the visible readout, every visible loop is
strategy-invisible. -/
theorem strategy_factorization_makes_visible_loops_invisible
    {U : Type u} {H : Type v} {B : Type w} {P : Type z}
    (update : U -> H -> H) (readout : H -> B) (strategy : H -> P)
    (factor : B -> P)
    (strategyFactors : forall state, strategy state = factor (readout state))
    (word : List U) (state : H)
    (visibleLoop : VisibleLoopAt update readout word state) :
    strategy (runWord update word state) = strategy state := by
  calc
    strategy (runWord update word state) =
        factor (readout (runWord update word state)) :=
      strategyFactors (runWord update word state)
    _ = factor (readout state) := congrArg factor visibleLoop
    _ = strategy state := (strategyFactors state).symm

/-- A joint current-strategy readout that is injective rules out any nontrivial
transport hidden from both coordinates. -/
theorem faithful_joint_readout_kills_hidden_holonomy
    {U : Type u} {H : Type v} {B : Type w} {P : Type z}
    (update : U -> H -> H) (readout : H -> B) (strategy : H -> P)
    (jointFaithful : Function.Injective (agencyEnrichment readout strategy))
    (word : List U) (state : H)
    (visibleLoop : VisibleLoopAt update readout word state)
    (strategyReturns :
      strategy (runWord update word state) = strategy state) :
    runWord update word state = state := by
  apply jointFaithful
  exact Prod.ext visibleLoop strategyReturns

/-- With identity readout, every visible loop is an actual return. -/
example (update : Unit -> Bool -> Bool) (word : List Unit) (state : Bool)
    (visibleLoop : VisibleLoopAt update id word state) :
    runWord update word state = state := by
  exact visibleLoop

#print axioms visible_loop_policy_change_witnesses_pointed_holonomy
#print axioms strategy_factorization_makes_visible_loops_invisible
#print axioms faithful_joint_readout_kills_hidden_holonomy

end D5.S3.Observer.Agency.Holonomy.VisibleLoopHolonomy
