# Visible Loop Holonomy

## Abstract

Pointed holonomy is a visible return with nontrivial hidden transport; strategy factorization hides policy drift, while a faithful joint readout rules out hidden loops.

**Theorem 1.1 (Visible Loop Policy Change Witnesses Pointed Holonomy).**

$$\forall U: Type, H: Type, B: Type, P: Type, update: U \to \left(H \to H\right), readout: H \to B, strategy: H \to P, word: List U, state: H,\\{}(VisibleLoopAt update readout word state) \land (StrategyVisibleHolonomyAt update strategy word state) \Rightarrow\\{}(PointedHolonomyAt update readout word state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.visible_loop_policy_change_witnesses_pointed_holonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strategy change on a visible loop certifies pointed holonomy, including both the visible-return and hidden-transport clauses.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Visible Loop Policy Change Implies Nontrivial Transport).**

$$\forall U: Type, H: Type, B: Type, P: Type, update: U \to \left(H \to H\right), readout: H \to B, strategy: H \to P, word: List U, state: H,\\{}(VisibleLoopAt update readout word state) \land (StrategyVisibleHolonomyAt update strategy word state) \Rightarrow\\{}(NontrivialTransportAt update word state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.visible_loop_policy_change_implies_nontrivial_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden-transport component of the pointed-holonomy witness.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Strategy Factorization Makes Visible Loops Invisible).**

$$\forall U: Type, H: Type, B: Type, P: Type, update: U \to \left(H \to H\right), readout: H \to B, strategy: H \to P, factor: B \to P, word: List U, state: H,\\{}(\forall state, strategy state = factor (readout state)) \land (VisibleLoopAt update readout word state) \Rightarrow\\{}(strategy (runWord update word state) = strategy state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.strategy_factorization_makes_visible_loops_invisible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If strategy factors through the visible readout, every visible loop is strategy-invisible.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Faithful Joint Readout Kills Hidden Holonomy).**

$$\forall U: Type, H: Type, B: Type, P: Type, update: U \to \left(H \to H\right), readout: H \to B, strategy: H \to P, word: List U, state: H,\\{}(Function.Injective (agencyEnrichment readout strategy)) \land (VisibleLoopAt update readout word state) \land (strategy (runWord update word state) = strategy state) \Rightarrow\\{}(runWord update word state = state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.faithful_joint_readout_kills_hidden_holonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A joint current-strategy readout that is injective rules out any nontrivial transport hidden from both coordinates.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.faithful_joint_readout_kills_hidden_holonomy`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.strategy_factorization_makes_visible_loops_invisible`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.visible_loop_policy_change_implies_nontrivial_transport`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.visible_loop_policy_change_witnesses_pointed_holonomy`
- Dependency: [D5/S3/Observer/AgencySelf/AgencyEnrichment](../AgencySelf/AgencyEnrichment.md)
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction](../../ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.md)
