# Marked Poisson Asymptotics on the Original Hypercube

## Abstract

Marked Poisson Asymptotics on the Original Hypercube

**Definition 1.1 (Cube).**

$$\forall d:Nat, \operatorname{Cube}(d)=\operatorname{Fin}(d+1)\to \operatorname{IntegerUnits}()$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.Cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original sign hypercube has dimension d+1, so each native parity class has M=2^d states. IntegerUnits is the two-element group of units of the integers, consisting of 1 and -1.

**Definition 1.2 (cubeEquiv).**

$$\forall d:Nat, \operatorname{cubeEquiv}(d)=\operatorname{parityTailBijection}(d)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parity-tail bijection sends x to its product parity and the index of its last d coordinates. The tail index is the finite enumeration of the 2^d sign tails. Positive parity selects inl and negative parity selects inr. The inverse recovers the first sign as the requested parity times the product of the tail signs.

**Definition 1.3 (positiveEquiv).**

$$\forall d:Nat, \forall x:\operatorname{PositiveCube}(d), \operatorname{cubeEquiv}(d, \operatorname{value}(x))=\operatorname{inl}(\operatorname{positiveEquiv}(d, x))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.positiveEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PositiveCube(d) is the subtype of Cube(d) with product parity 1. The displayed characterization fixes an equivalence to Fin(2^d), without an assumed transport map.

**Definition 1.4 (CubeSupport).**

$$\forall d,q:Nat, \operatorname{CubeSupport}(d, q)=\operatorname{fixedCardinalitySubsets}(\operatorname{PositiveCube}(d), q)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.CubeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source support is an arbitrary q-element finite subset of the positive parity class.

**Definition 1.5 (cubeSupportEquiv).**

$$\forall d,q:Nat, \forall S:\operatorname{CubeSupport}(d, q), \operatorname{cubeSupportEquiv}(d, q, S)=\operatorname{supportImage}(\operatorname{positiveEquiv}(d), S)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeSupportEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

supportImage maps every member of S through positiveEquiv. Its inverse maps through the inverse equivalence, preserving cardinality. All native and all original supports occur.

**Definition 1.6 (CubeObs).**

$$\forall d,s:Nat, \forall e:\operatorname{Experiment}(), \operatorname{CubeObs}(d, s, e)=\operatorname{cubeHistoryCarrier}(d, s, e)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.CubeObs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For pairs, cubeHistoryCarrier is Fin(s) -> Cube(d) x Cube(d). For paths it is Fin(s+1) -> Cube(d).

**Definition 1.7 (historyEquiv).**

$$\forall d,s:Nat, \forall e:\operatorname{Experiment}(), \operatorname{historyEquiv}(d, s, e)=\operatorname{endpointwiseEquivalence}(\operatorname{cubeEquiv}(d), s, e)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.historyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply cubeEquiv to both endpoints of every independent pair, or to every state of a complete continuous path. This preserves ordered edges.

**Definition 1.8 (cubeProfile).**

$$\forall d,q:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall x:\operatorname{Cube}(d), \operatorname{cubeProfile}(r, S, x)=\operatorname{supportedProfile}(r, S, x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

supportedProfile is r on S, minus r q/(2^d-q) on its positive complement, and zero on the negative class. The denominator uses the natural difference.

**Definition 1.9 (cubeKernel).**

$$\forall d,q:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:\operatorname{Bool}(), \forall x,y:\operatorname{Cube}(d), \operatorname{cubeKernel}(r, S, reverse, x, y)=\operatorname{orientedParityKernel}(r, S, reverse, x, y)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward kernel is (1+cubeProfile(r,S,x) parity(y))/2^(d+1). The reverse kernel interchanges x and y before evaluating this expression.

**Definition 1.10 (cubeProbability).**

$$\forall d,q,s:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:\operatorname{Bool}(), \forall e:\operatorname{Experiment}(), \forall o:\operatorname{CubeObs}(d, s, e), \operatorname{cubeProbability}(r, S, reverse, e, o)=\operatorname{cubeHistoryMass}(d, r, S, reverse, e, o)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For pairs this is the product of 2^(-(d+1)) times cubeKernel at each ordered pair. For paths it is 2^(-(d+1)) times the consecutive kernel product. The same S is used for every edge.

**Definition 1.11 (cubeCount).**

$$\forall d,s:Nat, \forall e:\operatorname{Experiment}(), \forall o:\operatorname{CubeObs}(d, s, e), \forall x:\operatorname{Cube}(d), \forall sigma:Real, \operatorname{cubeCount}(e, o, x, sigma)=\operatorname{markedCubeEdgeCount}(e, o, x, sigma)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count observed ordered edges departing from exactly x with destination parity sigma. Path endpoints are consecutive states; pair endpoints belong to the same sampled pair.

**Theorem 1.12 (hypercube history transport).**

$$\forall d,q,s:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:\operatorname{Bool}(), \forall e:\operatorname{Experiment}(), \forall x:\operatorname{Cube}(d), \operatorname{chi}(\operatorname{cubeEquiv}(d, x))=\operatorname{parity}(x) \land \forall x,y:\operatorname{Cube}(d), \operatorname{cubeKernel}(r, S, reverse, x, y)=\operatorname{nativeKernel}(r, \operatorname{cubeSupportEquiv}(d, q, S), reverse, \operatorname{cubeEquiv}(d, x), \operatorname{cubeEquiv}(d, y)) \land \forall o:\operatorname{CubeObs}(d, s, e), \operatorname{cubeProbability}(r, S, reverse, e, o)=\operatorname{nativeMass}(r, \operatorname{cubeSupportEquiv}(d, q, S), reverse, e, \operatorname{apply}(\operatorname{historyEquiv}(d, s, e), o)) \land \forall o:\operatorname{CubeObs}(d, s, e), \forall i:\operatorname{Fin}({2}^{d}), \forall sigma:Real, \operatorname{cubeCount}(e, o, \operatorname{inverse}(\operatorname{cubeEquiv}(d), \operatorname{inl}(i)), sigma)=\operatorname{count}(e, \operatorname{apply}(\operatorname{historyEquiv}(d, s, e), o), i, sigma) \land \forall E:\operatorname{Obs}({2}^{d}, s, e)\to Prop, \operatorname{cubeEventMass}(d, r, S, reverse, e, \operatorname{historyEquiv}(d, s, e), E)=\operatorname{nativeEventMass}(r, \operatorname{cubeSupportEquiv}(d, q, S), reverse, e, E)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_history_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All five clauses concern the same fixed original support, direction and experiment. Sstar denotes cubeSupportEquiv(d,q,S), H denotes historyEquiv(d,s,e), and v denotes cubeEquiv(d). nativeKernel and nativeMass select transition/probability forward and transposed transition/reverseProbability backward. Every native positive row i and every real destination parity sigma occurs in the count clause. The last clause ranges over every predicate E on complete native histories and sums exactly corresponding source history masses.

**Definition 1.13 (Logarithmic scale).**

$$\forall d:Nat, \operatorname{ell}(d)=\operatorname{log}({2}^{d})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index d denotes a cube of dimension d+1. Its parity classes each have M=2^d states, n=2M, and ell=log M. Letting d tend to infinity has exactly the original positive-dimension asymptotic meaning.

**Definition 1.14 (Exact observation scale).**

$$\forall s:Nat\to Nat, \forall d:Nat, \operatorname{observationScale}(s, d)=\frac{\operatorname{s}(d)}{(2) \cdot ({2}^{d})}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.observationScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation length s(d) is any natural number. L=s(d)/(2M) is real; the definitions and conclusions impose no divisibility or rounding of the observation length.

**Definition 1.15 (Original asymptotic hypotheses).**

$$\forall r,beta,alpha:Real, \forall q,s:Nat\to Nat, \operatorname{SourceRegime}(r, beta, alpha, q, s)=0<r \land r<1 \land \frac{1}{2}<beta \land beta<1 \land 0<alpha \land \exists delta:\operatorname{RealSequence}(), \operatorname{tendsToZero}(delta) \land \exists dimensionThreshold:Nat, \forall d:Nat, {dimensionThreshold\leq d} \Rightarrow \operatorname{q}(d)={{2}^{d}}^{1-beta+\operatorname{delta}(d)} \land \operatorname{tendsTo}(\operatorname{timeToLogRatioSequence}(s), alpha)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.SourceRegime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix 0<r<1, 1/2<beta<1 and alpha>0. timeToLogRatioSequence(s) is the sequence d mapped to observationScale(s,d)/ell(d). There is a real sequence delta(d) tending to zero such that q(d)=M^(1-beta+delta(d)) eventually, and L/ell tends to alpha. Both q and s are natural-valued sequences. No convergence rate is imposed. Positivity of q, q<M, small compensation, L>=1 and L/M tending to zero are consequences, rather than additional source assumptions.

**Definition 1.16 (Actual marked count vector).**

$$\forall d,s,k:Nat, \forall e:\operatorname{Experiment}(), \forall m:\operatorname{PositiveMarks}(d, k), \forall o:\operatorname{CubeObs}(d, s, e), \operatorname{sourceCountVector}(e, m, o)=\operatorname{pairOfParityDepartureCounts}(e, m, o)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceCountVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate type is Fin(k) plus Fin(k). The first copy counts departures from the selected positive-parity state m(j) to positive parity; the second counts departures to negative parity. All coordinates use the same complete history o. Any k-element set of positive states admits an injective enumeration of this form.

**Definition 1.17 (Actual count event mass).**

$$\forall d,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:Bool, \forall m:\operatorname{PositiveMarks}(d, k), \forall e:\operatorname{Experiment}(), \forall E:\operatorname{Set}(\operatorname{CountTuples}(k)), \operatorname{sourceEvent}(r, S, reverse, m, s, e, E)=\operatorname{sumHistoryMassOnCountEvent}(r, S, reverse, m, s, e, E)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the original cube history mass over precisely those histories whose entire marked count vector lies in E. The direction is the original kernel or its actual transpose. The experiment is independent stationary adjacent pairs or a continuous path with a uniform start. The true support S is fixed throughout each history.

**Definition 1.18 (Exact directional Poisson means).**

$$\forall d,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:Bool, \forall m:\operatorname{PositiveMarks}(d, k), \operatorname{sourceRates}(r, S, reverse, m, s)=\operatorname{nonnegativeParityRates}(\frac{(\frac{s}{(2) \cdot ({2}^{d})}) \cdot (1+\operatorname{directionalProfile}(reverse, r, S, m))}{2}, \frac{(\frac{s}{(2) \cdot ({2}^{d})}) \cdot (1-\operatorname{directionalProfile}(reverse, r, S, m))}{2})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceRates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed real values hold in the source regime at all sufficiently large dimensions. Globally sourceRates uses the nonnegative part of each displayed expression. The local theorem includes ExactDirectionalMeans, which proves these expressions equal the actual one-edge probabilities multiplied by the exact integer s. The comparison law is the genuine product of all 2k Poisson measures at these means.

**Definition 1.19 (One-edge probabilities and exact means).**

$$\forall d,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{CubeSupport}(d, q), \forall reverse:Bool, \forall m:\operatorname{PositiveMarks}(d, k), \operatorname{ExactDirectionalMeans}(r, S, reverse, m, s)=\forall j:\operatorname{Fin}(k), \forall sigma:\operatorname{Signs}(), \operatorname{actualOneEdgeProbability}(r, S, reverse, m, j, sigma)=\frac{1+(sigma) \cdot (\operatorname{directionalProfile}(reverse, r, S, m, j))}{(2) \cdot ((2) \cdot ({2}^{d}))} \land \operatorname{sourceRate}(r, S, reverse, m, s, j, sigma)=(s) \cdot (\operatorname{actualOneEdgeProbability}(r, S, reverse, m, j, sigma))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.ExactDirectionalMeans` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each j and destination parity sigma, sum n^(-1)K(m(j),y) over all original cube destinations y of parity sigma. This probability is (1+sigma b(m(j)))/(2n) forward and 1/(2n) backward. The corresponding sourceRates coordinate is s times that probability. The reverse calculation uses the zero sum of the compensated profile on the positive class; it does not assert independence along a reverse path.

**Theorem 1.20 (Uniform relative local masses).**

$$\forall r,alpha,C:Real, {0<r \land r<1 \land 0<alpha \land 0<C} \Rightarrow \exists A:Real, 0<A \land \forall beta:Real, \forall q,s:Nat\to Nat, {\operatorname{SourceRegime}(r, beta, alpha, q, s)} \Rightarrow \exists dimensionThreshold:Nat, \forall d:Nat, {dimensionThreshold\leq d} \Rightarrow \forall k:Nat, {\operatorname{oneOrTwo}(k)} \Rightarrow \forall S:\operatorname{CubeSupport}(d, \operatorname{q}(d)), \forall m:\operatorname{PositiveMarks}(d, k), {\operatorname{injective}(m)} \Rightarrow \forall reverse:Bool, \forall e:\operatorname{Experiment}(), \operatorname{ExactDirectionalMeans}(r, S, reverse, m, \operatorname{s}(d)) \land \forall n:\operatorname{CountTuples}(k), {\operatorname{total}(n)\leq (C) \cdot (\operatorname{ell}(d))} \Rightarrow 0<\operatorname{poissonEvent}(r, S, reverse, m, \operatorname{s}(d), \operatorname{singleton}(n)) \land \lvert \frac{\operatorname{sourceEvent}(r, S, reverse, m, \operatorname{s}(d), e, \operatorname{singleton}(n))}{\operatorname{poissonEvent}(r, S, reverse, m, \operatorname{s}(d), \operatorname{singleton}(n))}-1 \rvert\leq \frac{(A) \cdot ({\operatorname{ell}(d)}^{k+1})}{(2) \cdot ({2}^{d})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_marked_local_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed r, alpha and C>0, choose A>0 before beta and the natural support/time sequences, before the eventual dimension and before all true supports, distinct one or two marked positive states, directions, experiments and nonnegative count tuples. Every tuple of total count at most C ell has strictly positive comparison mass and relative error at most A ell^(k+1)/n. The all-zero tuple and rare point masses remain included. ExactDirectionalMeans is part of the conclusion. The proof uses the actual cube/native history correspondence, the directional signed PGF estimates, and the common coefficient normalization at exact real means.

**Theorem 1.21 (Every-D tails and all count events).**

$$\forall r,alpha,D:Real, {0<r \land r<1 \land 0<alpha \land 0<D} \Rightarrow \exists C:Real, \exists A:Real, 0<C \land 0<A \land \forall beta:Real, \forall q,s:Nat\to Nat, {\operatorname{SourceRegime}(r, beta, alpha, q, s)} \Rightarrow \exists dimensionThreshold:Nat, \forall d:Nat, {dimensionThreshold\leq d} \Rightarrow \forall k:Nat, {\operatorname{oneOrTwo}(k)} \Rightarrow \forall S:\operatorname{CubeSupport}(d, \operatorname{q}(d)), \forall m:\operatorname{PositiveMarks}(d, k), {\operatorname{injective}(m)} \Rightarrow \forall reverse:Bool, \forall e:\operatorname{Experiment}(), \operatorname{sourceEvent}(r, S, reverse, m, \operatorname{s}(d), e, \operatorname{totalExceeds}((C) \cdot (\operatorname{ell}(d))))+\operatorname{poissonEvent}(r, S, reverse, m, \operatorname{s}(d), \operatorname{totalExceeds}((C) \cdot (\operatorname{ell}(d))))\leq {{2}^{d}}^{0-D} \land \forall E:\operatorname{Set}(\operatorname{CountTuples}(k)), \lvert \operatorname{sourceEvent}(r, S, reverse, m, \operatorname{s}(d), e, E)-\operatorname{poissonEvent}(r, S, reverse, m, \operatorname{s}(d), E) \rvert\leq (\frac{(A) \cdot ({\operatorname{ell}(d)}^{k+1})}{(2) \cdot ({2}^{d})}) \cdot (\operatorname{poissonEvent}(r, S, reverse, m, \operatorname{s}(d), E))+{{2}^{d}}^{0-D}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_marked_tail_event_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed D>0 choose the cutoff C=(2(alpha+1)+D+2)/log 2 and a positive relative constant A before beta and the support/time sequences, before the eventual dimension and all supports, marks, directions, experiments and events. The actual and product-Poisson tails above C ell sum to at most M^(-D). Every count event E has absolute discrepancy at most A ell^(k+1)/n times its comparison probability plus M^(-D). The integer cutoff is floor(C ell) inside the proof; s is never rounded. A fixed exponential margin absorbs the prefactor and cutoff loss. Local and event comparisons retain the identical S, direction and actual history law.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.Cube`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.CubeObs`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.CubeSupport`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.ExactDirectionalMeans`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.SourceRegime`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeCount`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeEquiv`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeKernel`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeProbability`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeProfile`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.cubeSupportEquiv`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.ell`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.historyEquiv`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_history_transport`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_marked_local_asymptotics`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.hypercube_marked_tail_event_asymptotics`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.observationScale`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.positiveEquiv`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceCountVector`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceEvent`
- Truth anchor: `D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.sourceRates`
- Dependency: [D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison](MarkedPoissonEventComparison.md)
- Dependency: [D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates](ParityKernelSubcoordinates.md)
