# Complete mediation, weighted cuts and exact pricing

## Abstract

Complete mediation uses one response table in both treatment worlds. For a fixed mediator coupling, fair response marginals yield an exact weighted-cut interval and attaining independent-noise models.

Mediator is an arbitrary finite type with decidable equality. coupling is an existing normalized nonnegative rational law on Mediator times Mediator; law is such a law on Mediator to Bool. table and best are complete Boolean response assignments, multiplier maps mediator states to rationals, and target is rational. All sums use the full finite carriers. The set Values displayed by setOf is the actual image of all fair laws under completeMediatorBenefit. The final two entries specialize Mediator to Fin 3.

**Definition 1.1 (Embed the no-direct-effect mechanism).**

$$\forall Mediator, law, (\operatorname{completeOutcomeLaw}(law)) = (\operatorname{pushforwardResponseLaw}(law, (\lambda table \mapsto (\lambda index \mapsto \operatorname{table}(\operatorname{snd}(index))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both treatment coordinates read the same original response-table entry. This enforces equality of coordinates, rather than only equality of their means.

**Theorem 1.2 (Recover the actual success kernel).**

$$\forall Mediator, law, a, m, (\operatorname{outcomeSuccess}(\operatorname{completeOutcomeLaw}(law), a, m)) = (\operatorname{linearObjective}((\lambda table \mapsto \operatorname{ite}(\operatorname{apply}(table, m), 1, 0)), \operatorname{mass}(law)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing pushforward expectation theorem identifies each intervention success probability.

**Definition 1.3 (Fair response coordinates).**

$$\forall Mediator, law, (\operatorname{FairCompleteOutcome}(law)) \Leftrightarrow (\forall m, (\operatorname{linearObjective}((\lambda table \mapsto \operatorname{ite}(\operatorname{apply}(table, m), 1, 0)), \operatorname{mass}(law))) = (\frac{1}{2}))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.FairCompleteOutcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each mediator-indexed outcome response has probability one half. Dependence between different coordinates remains unrestricted.

**Theorem 1.4 (Bind fairness to the mediator kernel API).**

$$\forall Mediator, law, (\operatorname{FairCompleteOutcome}(law)) \Rightarrow (\operatorname{HasOutcomeKernel}(\operatorname{completeOutcomeLaw}(law), (\lambda index \mapsto \frac{1}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw_fair_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input condition is transported to the existing full treatment/mediator success-kernel predicate.

**Definition 1.5 (Use the original independent source query).**

$$\forall Mediator, coupling, law, (\operatorname{completeMediatorBenefit}(coupling, law)) = (\operatorname{partialMediatorBenefit}(coupling, \operatorname{completeOutcomeLaw}(law)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mediator coupling stays fixed and the lifted outcome disturbance is combined with it by the existing product semantics.

**Theorem 1.6 (Identify the actual benefit response cell).**

$$\forall Mediator, coupling, law, (\operatorname{completeMediatorBenefit}(coupling, law)) = (\operatorname{benefitResponseMass}(\operatorname{mass}(\operatorname{partialMediatorResponseLaw}(coupling, \operatorname{completeOutcomeLaw}(law)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit_actual_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The query is tied to the original two-world response pushforward and its existing benefit cell.

**Definition 1.7 (Directed weight crossing a Boolean cut).**

$$\forall Mediator, coupling, table, (\operatorname{mediatorCutMass}(coupling, table)) = (\operatorname{linearObjective}((\lambda pair \mapsto \operatorname{ite}((\operatorname{table}(\operatorname{fst}(pair))) \neq (\operatorname{table}(\operatorname{snd}(pair))), 1, 0)), \operatorname{mass}(coupling)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each directed pair contributes its own weight. Symmetry is not assumed; loops never cross a cut.

**Theorem 1.8 (Retain the complete mean-drift identity).**

$$\forall Mediator, coupling, law, ((2) \cdot (\operatorname{completeMediatorBenefit}(coupling, law))) = ((\operatorname{linearObjective}((\lambda table \mapsto \operatorname{mediatorCutMass}(coupling, table)), \operatorname{mass}(law))) + (\sum_{pair} ((\operatorname{mass}(coupling, pair)) \cdot ((\operatorname{linearObjective}((\lambda table \mapsto \operatorname{ite}(\operatorname{apply}(table, \operatorname{snd}(pair)), 1, 0)), \operatorname{mass}(law))) - (\operatorname{linearObjective}((\lambda table \mapsto \operatorname{ite}(\operatorname{apply}(table, \operatorname{fst}(pair)), 1, 0)), \operatorname{mass}(law)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit_cut_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise Boolean identity is averaged under the actual source law. Fairness is not needed for this identity.

**Definition 1.9 (Actual outcome-column reduced cost).**

$$\forall Mediator, coupling, multiplier, table, (\operatorname{completeMediatorPricingScore}(coupling, multiplier, table)) = ((\operatorname{linearObjective}((\lambda pair \mapsto \operatorname{ite}(((\operatorname{table}(\operatorname{fst}(pair))) = (false)) \land ((\operatorname{table}(\operatorname{snd}(pair))) = (true)), 1, 0)), \operatorname{mass}(coupling))) - (\sum_{m} ((\operatorname{multiplier}(m)) \cdot (\operatorname{ite}(\operatorname{apply}(table, m), 1, 0)))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorPricingScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This subtracts the outcome-marginal dual terms from the actual deterministic benefit column. The separate constant normalization multiplier is omitted because it cannot affect the maximizing assignment.

**Theorem 1.10 (Expose cut plus vertex-field pricing).**

$$\forall Mediator, coupling, multiplier, table, ((2) \cdot (\operatorname{completeMediatorPricingScore}(coupling, multiplier, table))) = ((\operatorname{mediatorCutMass}(coupling, table)) + (\sum_{m} ((((\operatorname{rightResponseMarginal}(\operatorname{mass}(coupling), m)) - (\operatorname{leftResponseMarginal}(\operatorname{mass}(coupling), m))) - ((2) \cdot (\operatorname{multiplier}(m)))) \cdot (\operatorname{ite}(\operatorname{apply}(table, m), 1, 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorPricingScore_graph_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity retains incoming and outgoing mediator masses and every rational dual multiplier. It is exact for arbitrary directed couplings and does not assert an efficient generic graph solver.

**Theorem 1.11 (Cancel drift using the fair kernel).**

$$\forall Mediator, coupling, law, (\operatorname{FairCompleteOutcome}(law)) \Rightarrow ((\operatorname{completeMediatorBenefit}(coupling, law)) = (\frac{\operatorname{linearObjective}((\lambda table \mapsto \operatorname{mediatorCutMass}(coupling, table)), \operatorname{mass}(law))}{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.fair_completeMediatorBenefit_eq_half_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal coordinate success probabilities cancel every signed mean difference, leaving half the expected weighted cut.

**Definition 1.12 (One fair disturbance selects an assignment or its complement).**

$$\forall Mediator, table, (\operatorname{complementOutcomeLaw}(table)) = (\operatorname{pushforwardResponseLaw}(\operatorname{uniformThresholdLaw}(2), (\lambda bit \mapsto \operatorname{ite}((bit) = (0), table, (\lambda m \mapsto \operatorname{not}(\operatorname{table}(m)))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-denominator proof is implicit in the displayed two-point uniform law. The same one-bit disturbance controls all response coordinates.

**Theorem 1.13 (Simultaneous fairness of all coordinates).**

$$\forall Mediator, table, \operatorname{FairCompleteOutcome}(\operatorname{complementOutcomeLaw}(table))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw_fair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two complementary complete assignments jointly realize the prescribed success probability at every mediator value.

**Theorem 1.14 (Whole-table complementation preserves the cut).**

$$\forall Mediator, coupling, table, (\operatorname{mediatorCutMass}(coupling, (\lambda m \mapsto \operatorname{not}(\operatorname{table}(m))))) = (\operatorname{mediatorCutMass}(coupling, table))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge has unchanged disagreement status after both endpoints are complemented.

**Theorem 1.15 (Realize every deterministic cut value).**

$$\forall Mediator, coupling, table, (\operatorname{completeMediatorBenefit}(coupling, \operatorname{complementOutcomeLaw}(table))) = (\frac{\operatorname{mediatorCutMass}(coupling, table)}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw_benefit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual no-direct-effect model attains half the chosen cut mass, using one shared outcome disturbance independent of the mediator disturbance.

**Theorem 1.16 (Obtain a maximizing cut and an attaining causal maximum).**

$$\forall Mediator, coupling, \exists best, (\forall table, (\operatorname{mediatorCutMass}(coupling, table)) \le (\operatorname{mediatorCutMass}(coupling, best))) \land (\operatorname{IsGreatest}(\operatorname{setOf}((\lambda value \mapsto \exists law, (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (value)))), \frac{\operatorname{mediatorCutMass}(coupling, best)}{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_maxcut_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite.exists_max chooses from the full Boolean assignment carrier. A complement pair attains the bound; every fair law is bounded by the maximum cut.

**Theorem 1.17 (Exact image for every rational target).**

$$\forall Mediator, coupling, \exists best, (\forall table, (\operatorname{mediatorCutMass}(coupling, table)) \le (\operatorname{mediatorCutMass}(coupling, best))) \land (\forall target, (\exists law, (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (target))) \Leftrightarrow (((0) \le (target)) \land ((target) \le (\frac{\operatorname{mediatorCutMass}(coupling, best)}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_cut_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower witness uses two constant assignments. Mixing it with the maximizing complement law fills the entire interval within one outcome mechanism and leaves the mediator coupling unchanged.

**Theorem 1.18 (Full cut mass is a simultaneous support condition).**

$$\forall Mediator, coupling, table, ((\operatorname{mediatorCutMass}(coupling, table)) = (1)) \Leftrightarrow (\forall pair, ((\operatorname{mass}(coupling, pair)) \neq (0)) \Rightarrow ((\operatorname{table}(\operatorname{fst}(pair))) \neq (\operatorname{table}(\operatorname{snd}(pair)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative missed-edge masses sum to zero exactly when no positive mediator pair remains unseparated.

**Theorem 1.19 (Characterize saturation by a single two-coloring).**

$$\forall Mediator, coupling, (\exists law, (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (\frac{1}{2}))) \Leftrightarrow (\exists table, \forall pair, ((\operatorname{mass}(coupling, pair)) \neq (0)) \Rightarrow ((\operatorname{table}(\operatorname{fst}(pair))) \neq (\operatorname{table}(\operatorname{snd}(pair)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_half_attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a full iff on the positive directed-pair support. It treats loops and odd cycles through the actual Boolean separation condition.

**Definition 1.20 (Normalized directed three-cycle instance).**

$$\forall pair, (\operatorname{mass}(\operatorname{threeCycleCoupling}(), pair)) = (\operatorname{ite}(((pair) = (\operatorname{pair}(0, 1))) \lor (((pair) = (\operatorname{pair}(1, 2))) \lor ((pair) = (\operatorname{pair}(2, 0)))), \frac{1}{3}, 0))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.threeCycleCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete mediator law has three equally weighted directed edges. The source supplies nonnegativity and normalization, with no estimated edge weights.

**Theorem 1.21 (Exact one-third endpoint on the odd cycle).**

$$\operatorname{IsGreatest}(\operatorname{setOf}((\lambda value \mapsto \exists law, (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(\operatorname{threeCycleCoupling}(), law)) = (value)))), \frac{1}{3})$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.three_cycle_complete_mediation_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Boolean labeling cuts at most two of the three cycle edges. The assignment 001 and its complement give an actual fair attaining outcome law. The cellwise half bound is therefore strictly loose.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.FairCompleteOutcome`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw_benefit`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complementOutcomeLaw_fair`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit_actual_response`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorBenefit_cut_identity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorPricingScore`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeMediatorPricingScore_graph_identity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw_fair_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.completeOutcomeLaw_success`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_cut_interval`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_half_attainable_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.complete_mediator_maxcut_sharp`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.fair_completeMediatorBenefit_eq_half_cut`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass_complement`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.mediatorCutMass_eq_one_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.threeCycleCoupling`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.three_cycle_complete_mediation_sharp`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction](PartialMediatorTransportReduction.md)
