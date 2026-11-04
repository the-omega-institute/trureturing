# Exact original-view action prices

## Abstract

Every exact original view has acquired action price two and preset action price four.

**Theorem 1.1 (One prior and both controller classes).**

$$\forall V\in\{B,T,S,M,(B,T,S,M)\}, \operatorname{FeasibleRec}\left(V, 2\right)\land (\forall h,\operatorname{FeasibleRec}\left(V, h\right)\longrightarrow2\leq h)\land \operatorname{FeasiblePre}\left(V, 4\right)\land (\forall h,\operatorname{FeasiblePre}\left(V, h\right)\longrightarrow4\leq h)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/Prices.original_view_action_prices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five targets are separately the exact original rational B, its entire chronological word T, its rooted oriented named-edge path S, its indexed prefix-pair table M and the joint full output. The prior includes both c_0=1/6 and c_1=2/3 and all c_i-1/n for every integer n at least 12. Every action and nondisturbing dyadic floor read is executed on one current source. Common initialization and a source-independent instruction function rule out exact unknown input and unknown source advice.

For each target the conjunction states feasibility at acquired cap 2, that every feasible acquired cap is at least 2, feasibility at preset cap 4, and that every feasible preset cap is at least 4. Feasibility quantifies over arbitrary deterministic state and instruction functions and arbitrary common preset schedules, a class containing ordinary finite controllers. The attaining source-dependent decisions are made by the explicit finite acquisition code, and the only added calculation maps its recovered rational to the requested whole original output. This calculation preserves every physical action, actual read and stopping cut and is finite even when the original word and table are long.

The finite actual-image decoders make each target injective on the prior. Consequently the universal finite-run replay and incompatible short routes apply to each one. Conversely, the actual two-mode rational acquisition and finite original-view construction attain the stated caps. Preset acquisition follows the single word LLRL and may stop after its first LL on the lower band. Adaptive scales and early stopping are included in that opponent class.

Only the uniform new-source action coordinate is minimized. The proof gives no uniform bound or optimum for read counts, scale encodings, local arithmetic, transient or retained memory, service work or complete output length. The services are conditional exact, noiseless, unclipped and finite-completing ports; no physical implementation or noise tolerance is asserted.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/Prices.original_view_action_prices`
- Dependency: [D5/S3/Observer/RationalRouting/Acquisition](Acquisition.md)
- Dependency: [D5/S3/Observer/RationalRouting/Views](Views.md)
