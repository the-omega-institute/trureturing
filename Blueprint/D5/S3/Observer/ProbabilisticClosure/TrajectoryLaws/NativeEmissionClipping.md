# Lawful emission clipping on the original observer

## Abstract

NativeEmissionClipping

**Theorem 1.1 (A finite disjoint-event clipping estimate).**

$$\forall A:MeasurableType, (\forall P:ProbabilityMeasureA, (\forall R:ProbabilityMeasureA, (\forall T:ProbabilityMeasureA, (\forall E:MeasurableSetA, (\forall G:MeasurableSetA, (\forall hd:DisjointEG, (\forall a:Real, (\forall b:Real, (\forall gap:Real, (\forall hab:OrderedEndpoints, (\forall ha:PMassGa, (\forall hb:RMassGb, (\forall he:EndpointEventGap, (\operatorname{FiniteEventClippingBudget}(A, P, R, T, E, G, hd, a, b, gap, hab, ha, hb, he)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.finite_event_clipping_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P, R and T are probability measures on the same measurable carrier A. E and G are measurable and disjoint. The real masses of G under P and R are a and b with a less than or equal to b, and P(E)-R(E)=gap. Then the absolute difference between T(G) and max(a,min(b,T(G))) is at most TV(T,P).toReal plus TV(T,R).toReal minus gap. Testing E and E union G in the two possible orders detects deviations below a and above b. Testing E in both laws covers the intervening interval. TV uses the supremum over measurable events.

**Theorem 1.2 (Original configuration budgets for a lawful emission clamp).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\operatorname{NativeConfigurationClippingBudget}(Z, M, e))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.native_configuration_clipping_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The comparison emitter keeps the original finite carrier and every M.init and M.update kernel. It clamps the real read0 probability into [1/3,2/5] only at fourth(active s), gives the other read its complement, and retains the original emitter at all other controls. It is an analytic probability comparison and asserts no executable exact-real sampler or fixed-resource preservation. At every original p configuration with the correct active control, the read0 change is bounded by the sum of its complete raw-law TVs to the depth-one and depth-two endpoint p laws minus twice 1116529/22781250. At every original beta configuration the corresponding bound subtracts twice 239/6750. The immediate completion masses are u and 1-v. The p witness is disjoint from some[0]; the complement of the beta witness is disjoint from some[1]. The original endpoint event evaluations supply the gaps. These are configuration bounds before averaging. They do not by themselves bound the comparison emitter worst-history risk or establish the strict original-observer gap.

**Theorem 1.3 (Clamped emissions stay in the comparison interval).**

$$\forall t:Real, (\operatorname{ClampBox}(t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.clamp_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t, max(1/3,min(2/5,t)) lies in [1/3,2/5].

**Theorem 1.4 (The comparison next-read probability).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall z:Z, (\forall s:ActivePhase, (\forall hz:ActualActiveControl, (\operatorname{ClampReadZero}(Z, M, e, z, s, hz)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.clamp_read_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite measurable singleton carrier Z, Observer M, lawful emitter e, configuration z and active phase s whose actual projected control is fourth(active s), the real read0 probability of clampedEmitter M e at z equals clampEmission of the original real read0 probability. Other controls retain e.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.clamp_box`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.clamp_read_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.finite_event_clipping_budget`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping.native_configuration_clipping_budget`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator](ConstantSuspensionSeparator.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks](NativePaidHistoryCommonRowRisks.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration](NativeStoppedTailRegeneration.md)
