# Full coordinates and the original stationary class

## Abstract

Identification of the surviving native law

## Actual native laws on the full legal carriers

**Theorem 1.1 (inclusion embedding).**

$$\forall s: ActivePhase, \operatorname{MeasurableEmbedding}\left(\operatorname{legalSubtypeInclusion}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.inclusion_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

legalSubtypeInclusion(s) is Subtype.val from ValidTail(s) to RawTail. Its injectivity and the countable measurable image give the exact comap interface used by complete continuous laws.

**Theorem 1.2 (stopped legal).**

$$\forall s: ActivePhase, \forall omega: Stream, \operatorname{Valid}\left(s, \operatorname{stoppedReadWord}\left(s, omega\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.stopped_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original stopped parser lands in the complete legal carrier, including the noncompletion outcome.

**Theorem 1.3 (geometric tail).**

$$\forall z: ENNReal, \forall D: ENNReal, \forall j: Nat, \operatorname{tsumRestrictedGeometric}\left(z, D, j\right)={z}^{j} \cdot \operatorname{tsumGeometric}\left(z, D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.geometric_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

tsumRestrictedGeometric(z,D,j) is the sum over n:Nat of D*z^n when j<=n and zero otherwise. tsumGeometric(z,D) is the sum over all n:Nat of D*z^n. The identity holds for all extended nonnegative parameters, including infinity. It is consumed by every continuous source tail.

**Theorem 1.4 (p atom tail).**

$$\forall j: Nat, \forall n: Nat, \forall i: Letter, \operatorname{member}\left(\operatorname{pAtom}\left(n, i\right), \operatorname{tailSet}\left(\operatorname{p}\left(\right), j\right)\right)\Leftrightarrow j\leq n$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.p_atom_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All p completion atoms have their original tail depth.

**Theorem 1.5 (beta atom tail).**

$$\forall j: Nat, \forall n: Nat, \forall i: Letter, \operatorname{member}\left(\operatorname{betaAtom}\left(n, i\right), \operatorname{tailSet}\left(\operatorname{beta}\left(\right), j\right)\right)\Leftrightarrow j\leq n$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.beta_atom_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same complete suspended atoms retain their original tail depth.

**Theorem 1.6 (beta stop not tail).**

$$\forall j: Nat, \operatorname{notMember}\left(\operatorname{betaStop}\left(\right), \operatorname{tailSet}\left(\operatorname{beta}\left(\right), j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.beta_stop_not_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The immediate suspended stop is outside each return tail.

native(s,r) is the comap of the actual explicitStoppedWordLaw(s,r) along legal subtype inclusion. The actual stopped-word map always lands in the legal range; that range has mass one. Thus native is a probability law, rather than an unnormalized comap. endpoint(false)=1/3 and endpoint(true)=2/5. nativeEndpoint(s,b) bundles this actual law with the exact Regular predicate.

**Theorem 1.7 (native coordinate).**

$$\forall s: ActivePhase, \forall r: UnitInterval, \forall t: ValidTail, \operatorname{mass}\left(\operatorname{native}\left(s, r\right), t\right)=\operatorname{mass}\left(\operatorname{explicitStoppedWordLaw}\left(s, r\right), \operatorname{val}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atom t ranges over ValidTail(s), including infinity. Measurable subtype inclusion is injective and comap evaluates its singleton image exactly.

**Theorem 1.8 (native atoms).**

$$\forall r: UnitInterval, (\forall n: Nat, \forall i: Letter, \operatorname{mass}\left(\operatorname{native}\left(\operatorname{p}\left(\right), r\right), \operatorname{pAtom}\left(n, i\right)\right)=\operatorname{markerCoefficient}\left(r, i\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{n})\land((\operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{betaStop}\left(\right)\right)=\operatorname{betaMass}\left(r\right))\land((\forall n: Nat, \forall i: Letter, \operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{betaAtom}\left(n, i\right)\right)=\operatorname{alphaMass}\left(r\right) \cdot \operatorname{markerCoefficient}\left(r, i\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{n})\land(\forall s: ActivePhase, \operatorname{mass}\left(\operatorname{native}\left(s, r\right), \operatorname{infinity}\left(s\right)\right)=0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_atoms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

markerCoefficient(r,i) means alphaMass(r) when i=0 and betaMass(r)^2 otherwise. alphaMass(r)=r and betaMass(r)=1-r as ENNReal masses. The complete list is pAtom(n,0): r z^n; pAtom(n,1): (1-r)^2 z^n; betaStop: 1-r; betaAtom(n,0): r^2 z^n; betaAtom(n,1): r(1-r)^2 z^n; infinity in either phase: zero.

**Theorem 1.9 (native tails).**

$$\forall r: UnitInterval, \forall j: Nat, (\operatorname{mass}\left(\operatorname{native}\left(\operatorname{p}\left(\right), r\right), \operatorname{tailSet}\left(\operatorname{p}\left(\right), j\right)\right)={\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{j})\land(\operatorname{mass}\left(\operatorname{native}\left(\operatorname{beta}\left(\right), r\right), \operatorname{tailSet}\left(\operatorname{beta}\left(\right), j\right)\right)=\operatorname{alphaMass}\left(r\right) \cdot {\operatorname{alphaMass}\left(r\right) \cdot \operatorname{betaMass}\left(r\right)}^{j})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Countable legal atom reconstruction, word injectivity and shifted geometric sums give every exact tail. The p normalization fixes the full series sum. At j=0 the suspended tail is r, not one.

**Theorem 1.10 (native endpoint residualA).**

$$\forall b: Bool, \operatorname{residualA}\left(\operatorname{nativeEndpoint}\left(\operatorname{beta}\left(\right), b\right)\right)=\operatorname{law}\left(\operatorname{nativeEndpoint}\left(\operatorname{p}\left(\right), b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_endpoint_residualA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

prependA sends every p completion atom to the corresponding beta atom and preserves infinity. Native atom evaluation gives its full comap law; the original nonzero alpha mass normalizes the entire residual.

For every theta in [0,1], the endpoint application uses unweighted marginals (1-theta) Dirac(native_a)+theta Dirac(native_b) and joint edge measures on the corresponding endpoint pairs. Deterministic Borel acquired kernels select the matching opposite endpoint. Singleton comap identities, including infinity, normalize both B and A residuals; each coordinate is one of the two comparison endpoints and hence satisfies the full min/max boxes. The upper native singleton has mass theta, including theta=0 and theta=1. This finite boundary application does not restrict the arbitrary Borel margins in the singleton-limit theorem.

F is an arbitrary original boxed Borel CommonFlow. All probability descriptors retain every finite legal tail and the infinite noncompletion coordinate. CRow(F,Q) is the original unweighted acquired return row, T=L/(6/25), and q is the decreasing limit of T to the power n applied to threeStepAverage. CoreAt asserts the original goodP conditions, h>=3/25, Th<=h, Tq=q, nonzero q implies zero excess, almost every B successor satisfies goodB, and almost every C edge preserves sixthFunctional. GoodP retains the full normalized B residual, its endpoint box, every coordinate recursion, the completion identity and bounds, and the third-step box; goodB retains the full normalized A residual and its endpoint box. AE denotes almost everywhere, sequence(n,x) the sequence with index n, nhds the neighborhood filter, and ite the indicated conditional value.

**Theorem 1.11 (An absorbing conull core).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \forall Q\in G, \operatorname{CoreAt}\left(F, Q\right)\land \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, R\in G\land \operatorname{sixthFunctional}\left(F, R\right)=\operatorname{sixthFunctional}\left(F, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_absorbing_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enclose the exceptional set in a measurable null set. Repeatedly intersect its complement with the states whose C row assigns zero mass to the previous complement. Stationarity makes every finite stage conull. Their countable intersection is conull and absorbing under the same C. The original full residuals and both endpoint boxes remain available there.

**Theorem 1.12 (Survival identifies the actual upper law).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land (\forall Q\in G, \operatorname{CoreAt}\left(F, Q\right)\land \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, R\in G\land \operatorname{sixthFunctional}\left(F, R\right)=\operatorname{sixthFunctional}\left(F, Q\right)\right))\land \forall Q\in G, (\operatorname{q}\left(F, Q\right)\neq 0)\iff Q=\operatorname{nativeEndpoint}\left(p, true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive sixth-functional class, acquired edge constancy makes the class absorbing and stationary localization gives g=9/25. In g=(1-u)*B(1-v), both factors are at least 3/5, so equality forces u=2/5 and v=2/5 on almost every actual B successor. Hence L=(6/25)C there. Induction identifies both letter coordinates at every depth; the original regular tail bound gives zero infinite-coordinate mass. Equality of all singleton masses on the complete countable legal-tail carrier identifies the full upper native probability measure. Conversely, at an actual upper native input every normalized g coordinate equals 9/25. The inequality g<=3*threeStepAverage forces a positive harmonic limit.

**Theorem 1.13 (The original pointwise and averaged limits).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{q}\left(F, Q\right)=\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{endpointCompletion}\left(\right), 0\right)\land \frac{\operatorname{q}\left(F, Q\right)}{\operatorname{threeStepAverage}\left(F, Q\right)}=\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), 1, 0\right)\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{Tendsto}\left(\operatorname{sequence}\left(n, \frac{\operatorname{coordinate}\left(n, 1, Q\right)}{{\operatorname{endpointRate}\left(\right)}^{n}}\right), atTop, \operatorname{nhds}\left(\operatorname{ite}\left(Q=\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{endpointCompletion}\left(\right), 0\right)\right)\right)\right)\land \operatorname{Tendsto}\left(\operatorname{sequence}\left(n, \frac{\operatorname{lintegral}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{coordinate}\left(n, 1, Q\right)\right)}{{\operatorname{endpointRate}\left(\right)}^{n}}\right), atTop, \operatorname{nhds}\left(\operatorname{endpointCompletion}\left(\right) \cdot \operatorname{measure}\left(\operatorname{nuP}\left(F\right), \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_upper_endpoint_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the surviving class h=q=9/25. Elsewhere q=0 and 0<=T^n g<=3*T^n h tends to zero. The full coordinate recursion converts this into the original singleton ratio limit. The common bound 30 on all normalized iterates permits dominated convergence on the unchanged original margin. The integral of the native singleton indicator is its actual original marginal mass. These conclusions require neither finite support, mixing, reversibility nor deterministic successors.

**Theorem 1.14 (Actual beta and return successors).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\operatorname{q}\left(F, Q\right)\neq 0)\Rightarrow\operatorname{u}\left(Q\right)=\operatorname{upper}\left(\right)\land \operatorname{LRow}\left(F, Q\right)=\operatorname{smul}\left(\operatorname{endpointRate}\left(\right), \operatorname{CRow}\left(F, Q\right)\right)\land \operatorname{AE}\left(\operatorname{BRow}\left(F, Q\right), W, W=\operatorname{nativeEndpoint}\left(beta, true\right)\land \operatorname{AE}\left(\operatorname{ARow}\left(F, W\right), R, R=\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_transitions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual C row remains in the positive class, so almost every actual A successor on almost every B edge is the full upper p descriptor. The original normalized A residual is therefore exactly that native p law. Reconstruct the full suspended law from its stop mass and the image of its entire residual, including infinity. With v=2/5 this is the upper beta native descriptor. This identifies the given B/A successors rather than replacing their barycentres by sampled laws.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.beta_atom_tail`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.beta_stop_not_tail`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_absorbing_core`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_native`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_transitions`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_upper_endpoint_limits`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.geometric_tail`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.inclusion_embedding`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_atoms`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_coordinate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_endpoint_residualA`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.native_tails`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.p_atom_tail`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.stopped_legal`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization](NativeBorelStationaryLocalization.md)
