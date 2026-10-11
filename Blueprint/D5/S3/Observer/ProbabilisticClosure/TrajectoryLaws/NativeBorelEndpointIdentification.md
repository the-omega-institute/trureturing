# Full coordinates and the original stationary class

## Abstract

Identification of the surviving native law

F is an arbitrary original boxed Borel CommonFlow. All probability descriptors retain every finite legal tail and the infinite noncompletion coordinate. CRow(F,Q) is the original unweighted acquired return row, T=L/(6/25), and q is the decreasing limit of T to the power n applied to threeStepAverage. CoreAt asserts the original goodP conditions, h>=3/25, Th<=h, Tq=q, nonzero q implies zero excess, almost every B successor satisfies goodB, and almost every C edge preserves sixthFunctional. GoodP retains the full normalized B residual, its endpoint box, every coordinate recursion, the completion identity and bounds, and the third-step box; goodB retains the full normalized A residual and its endpoint box. AE denotes almost everywhere, sequence(n,x) the sequence with index n, nhds the neighborhood filter, and ite the indicated conditional value.

**Theorem 1.1 (An absorbing conull core).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \forall Q\in G, \operatorname{CoreAt}\left(F, Q\right)\land \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, R\in G\land \operatorname{sixthFunctional}\left(F, R\right)=\operatorname{sixthFunctional}\left(F, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_absorbing_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enclose the exceptional set in a measurable null set. Repeatedly intersect its complement with the states whose C row assigns zero mass to the previous complement. Stationarity makes every finite stage conull. Their countable intersection is conull and absorbing under the same C. The original full residuals and both endpoint boxes remain available there.

**Theorem 1.2 (Survival identifies the actual upper law).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land (\forall Q\in G, \operatorname{CoreAt}\left(F, Q\right)\land \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, R\in G\land \operatorname{sixthFunctional}\left(F, R\right)=\operatorname{sixthFunctional}\left(F, Q\right)\right))\land \forall Q\in G, (\operatorname{q}\left(F, Q\right)\neq 0)\iff Q=\operatorname{nativeEndpoint}\left(p, true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive sixth-functional class, acquired edge constancy makes the class absorbing and stationary localization gives g=9/25. In g=(1-u)*B(1-v), both factors are at least 3/5, so equality forces u=2/5 and v=2/5 on almost every actual B successor. Hence L=(6/25)C there. Induction identifies both letter coordinates at every depth; the original regular tail bound gives zero infinite-coordinate mass. Equality of all singleton masses on the complete countable legal-tail carrier identifies the full upper native probability measure. Conversely, at an actual upper native input every normalized g coordinate equals 9/25. The inequality g<=3*threeStepAverage forces a positive harmonic limit.

**Theorem 1.3 (The original pointwise and averaged limits).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{q}\left(F, Q\right)=\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{endpointCompletion}\left(\right), 0\right)\land \frac{\operatorname{q}\left(F, Q\right)}{\operatorname{threeStepAverage}\left(F, Q\right)}=\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), 1, 0\right)\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{Tendsto}\left(\operatorname{sequence}\left(n, \frac{\operatorname{coordinate}\left(n, 1, Q\right)}{{\operatorname{endpointRate}\left(\right)}^{n}}\right), atTop, \operatorname{nhds}\left(\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{endpointCompletion}\left(\right), 0\right)\right)\right)\right)\land \operatorname{Tendsto}\left(\operatorname{sequence}\left(n, \frac{\operatorname{lintegral}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{coordinate}\left(n, 1, Q\right)\right)}{{\operatorname{endpointRate}\left(\right)}^{n}}\right), atTop, \operatorname{nhds}\left(\operatorname{endpointCompletion}\left(\right) \cdot \operatorname{measure}\left(\operatorname{nuP}\left(F\right), \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_upper_endpoint_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the surviving class h=q=9/25. Elsewhere q=0 and 0<=T^n g<=3*T^n h tends to zero. The full coordinate recursion converts this into the original singleton ratio limit. The common bound 30 on all normalized iterates permits dominated convergence on the unchanged original margin. The integral of the native singleton indicator is its actual original marginal mass. These conclusions require neither finite support, mixing, reversibility nor deterministic successors.

**Theorem 1.4 (Actual beta and return successors).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\operatorname{q}\left(F, Q\right)\neq 0)\Rightarrow\operatorname{u}\left(Q\right)=\operatorname{upper}\left(\right)\land \operatorname{LRow}\left(F, Q\right)=\operatorname{smul}\left(\operatorname{endpointRate}\left(\right), \operatorname{CRow}\left(F, Q\right)\right)\land \operatorname{AE}\left(\operatorname{BRow}\left(F, Q\right), W, W=\operatorname{nativeEndpoint}\left(beta, true\right)\land \operatorname{AE}\left(\operatorname{ARow}\left(F, W\right), R, R=\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_transitions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual C row remains in the positive class, so almost every actual A successor on almost every B edge is the full upper p descriptor. The original normalized A residual is therefore exactly that native p law. Reconstruct the full suspended law from its stop mass and the image of its entire residual, including infinity. With v=2/5 this is the upper beta native descriptor. This identifies the given B/A successors rather than replacing their barycentres by sampled laws.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_absorbing_core`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_native`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_transitions`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_upper_endpoint_limits`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws](NativeBorelNativeLaws.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization](NativeBorelStationaryLocalization.md)
