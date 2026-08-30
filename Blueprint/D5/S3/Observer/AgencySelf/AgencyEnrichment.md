# Agency Enrichment

## Abstract

Agency enrichment pairs current state and strategy, isolates the strategy residual inside current fibers, and becomes agency completion only after controlled behavior closure.

**Theorem 1.1 (Current Kernel Strategy Residual Partition).**

$$\forall H: Type, B: Type, P: Type, current: H \to B, strategy: H \to P, x: H, y: H,\\{}(current x = current y \Leftrightarrow agencyEnrichment current strategy x = agencyEnrichment current strategy y \lor StrategyResidual current strategy x y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyEnrichment.current_kernel_strategy_residual_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside a current-state fiber, a pair either agrees under the enriched readout or is a strategy residual.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Agency Kernel Disjoint Strategy Residual).**

$$\forall H: Type, B: Type, P: Type, current: H \to B, strategy: H \to P, x: H, y: H,\\{}(\neg (agencyEnrichment current strategy x = agencyEnrichment current strategy y \land StrategyResidual current strategy x y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyEnrichment.agency_kernel_disjoint_strategy_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The enriched kernel and the strategy residual are disjoint.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (No Strategy Residual iff Kernel Inclusion).**

$$\forall H: Type, B: Type, P: Type, current: H \to B, strategy: H \to P,\\{}((\forall x y, \neg StrategyResidual current strategy x y) \Leftrightarrow \forall x y, current x = current y \Rightarrow strategy x = strategy y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyEnrichment.no_strategy_residual_iff_kernel_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is no strategy residual exactly when strategy is constant on every current-state fiber.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Strategy Factorization iff No Residual).**

$$\forall H: Type, B: Type, P: Type, current: H \to B, strategy: H \to P,\\{}((\exists! factor : Set.range current \to Set.range strategy, \forall x, factor (Set.rangeFactorization current x) = Set.rangeFactorization strategy x) \Leftrightarrow \forall x y, \neg StrategyResidual current strategy x y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyEnrichment.strategy_factorization_iff_no_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing strategy residual is equivalent to a unique factor from the realized current-state image to the realized strategy image.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Agency Enrichment Kernel eq Current iff No Residual).**

$$\forall H: Type, B: Type, P: Type, current: H \to B, strategy: H \to P,\\{}(Setoid.ker (agencyEnrichment current strategy) = Setoid.ker current \Leftrightarrow \forall x y, \neg StrategyResidual current strategy x y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyEnrichment.agency_enrichment_kernel_eq_current_iff_no_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing strategy adds no new distinction exactly when the strategy residual vanishes.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyEnrichment.agency_enrichment_kernel_eq_current_iff_no_residual`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyEnrichment.agency_kernel_disjoint_strategy_residual`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyEnrichment.current_kernel_strategy_residual_partition`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyEnrichment.no_strategy_residual_iff_kernel_inclusion`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyEnrichment.strategy_factorization_iff_no_residual`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion](../../ObserverMemory/Refinement/EffectiveImageKernelCriterion.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/JointReadoutSupremum](../../ObserverMemory/Refinement/JointReadoutSupremum.md)
