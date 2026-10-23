# Rank-One Feedback and the First Read

## Abstract

Actual finite rank-one feedback, independent control, and response effects.

**Theorem 1.1 (Positivity of each basis projection).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall s:n,\operatorname{Matrix}.\operatorname{PosSemidef}(\operatorname{projector}(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.projector_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type with decidable equality and every index s, the basis projection projector s = Matrix.single s s 1 is positive semidefinite. The nonnegativity of terminal record masses follows by applying this projection to each read outcome; it also supplies positive basis inputs for the channel time-reversal contradiction.

**Theorem 1.2 (The actual finite protocol supremum).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall U:\operatorname{WaitFamily}(n),\forall X,Y:\operatorname{ComplexMatrix}(n),\operatorname{UnitaryWaits}(U)\land \operatorname{PSD}(X)\land \operatorname{PSD}(Y)\land \operatorname{Tr}(X)=\operatorname{Tr}(Y)\Rightarrow \operatorname{ProtocolTVSup}(U,X,Y)=\operatorname{FirstReadTVSup}(U,X,Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_tv_supremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unitary waiting semigroup on actual complex matrices is indexed by nonnegative real times. A finite protocol consists of Stop, a wait, or a complete rank-one Lueders read with one continuation per observed outcome. Terminal records retain all read outcomes.

Before the first read, waits merge by the semigroup law. No-read Stop has zero distinction for equal-trace inputs. At a first outcome s, the unnormalized branch is its probability times the basis projection. The suffix law starts at that projection and is defined even when the original first probability is zero. Its nonnegative mass sums to one, so the complete-record total variation is exactly that of the first read.

**Theorem 1.3 (Finite independent control and coarse output).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall U:\operatorname{WaitFamily}(n),\forall X,Y:\operatorname{ComplexMatrix}(n),\operatorname{UnitaryWaits}(U)\land \operatorname{PSD}(X)\land \operatorname{PSD}(Y)\land \operatorname{Tr}(X)=\operatorname{Tr}(Y)\Rightarrow \operatorname{RandomProtocolTVSup}(U,X,Y)=\operatorname{FirstReadTVSup}(U,X,Y)\land \\\forall R:\operatorname{RandomControl}(n),\forall m:\mathbb{N},\forall W:\operatorname{OutputKernel}(\operatorname{RandomRecord}(R),\operatorname{Fin}(m)),\operatorname{Stochastic}(W)\Rightarrow \operatorname{TV}(\operatorname{W}(\operatorname{randomLaw}(U,R,X)),\operatorname{W}(\operatorname{randomLaw}(U,R,Y)))\leq \operatorname{TV}(\operatorname{randomLaw}(U,R,X),\operatorname{randomLaw}(U,R,Y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.randomized_protocol_tv_supremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite control seed is sampled independently of the unknown input. It selects a finite feedback tree, whose later decisions use actual recorded outcomes. The complete record includes the seed. Its total variation is a convex combination of deterministic distinctions and is dominated by one deterministic tree. Arbitrary finite stochastic output kernels contract that law; their coefficients can depend on the recorded seed and history, but have no access to the unknown input.

**Theorem 1.4 (Arbitrary independent probability seeds).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall U:\operatorname{WaitFamily}(n),\forall X,Y:\operatorname{ComplexMatrix}(n),\forall S:Type,[\operatorname{MeasurableSpace}(S)],\forall mu:\operatorname{Measure}(S),\forall strategy:\operatorname{ProtocolFamily}(S,n),\forall event:\operatorname{FiniteEventFamily}(strategy),\operatorname{UnitaryWaits}(U)\land \operatorname{Density}(X)\land \operatorname{Density}(Y)\land \operatorname{ProbabilityMeasure}(mu)\land \operatorname{Integrable}(\operatorname{eventWeight}(U,strategy,event,X),mu)\land \operatorname{Integrable}(\operatorname{eventWeight}(U,strategy,event,Y),mu)\Rightarrow |\operatorname{Integral}(\operatorname{eventWeight}(U,strategy,event,X),mu)-\operatorname{Integral}(\operatorname{eventWeight}(U,strategy,event,Y),mu)|\leq \operatorname{FirstReadTVSup}(U,X,Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.arbitrary_random_control_event_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary probability space of independent seeds, each seed selects a finite feedback tree with arbitrary nonnegative real waits. An event can depend on the seed and the whole observed record. Whenever its two actual probability functions are integrable, its integrated probability gap is at most the first-read supremum. Thus arbitrary measurable random control has the same event bound; deterministic one-read protocols supply the reverse supremum bound.

**Theorem 1.5 (Actual histories supply exactly the first-read effect span).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall U:\operatorname{WaitFamily}(n),\operatorname{UnitaryWaits}(U)\Rightarrow \operatorname{RealSpan}(\operatorname{AllHistoryEffects}(U))=\operatorname{firstEffectSpan}(U)\land \\(\forall P:\operatorname{Protocol}(n),\forall X:\operatorname{ComplexMatrix}(n),\forall h:\operatorname{Record}(P),\operatorname{Re}(\operatorname{Tr}(\operatorname{recordEffect}(U,P,h)X))=\operatorname{ludersLaw}(U,P,X,h))\land \forall P:\operatorname{Protocol}(n),\forall h:\operatorname{Record}(P),\operatorname{PSD}(\operatorname{recordEffect}(U,P,h))\land \operatorname{PSD}(1-\operatorname{recordEffect}(U,P,h))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_effect_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complete history has an explicit complex Heisenberg effect obtained from the actual unitary waits and rank-one sandwiches. Its trace probability equals the operational Lueders law. Every actual history effect and its complement in the identity are positive semidefinite, by induction through unitary conjugations and rank-one sandwiches. The real span of all these effects equals the span of the identity and all first-read effects. Rank-one collapse and the semigroup identity prove the forward inclusion; Stop and one-read histories prove the reverse inclusion.

This explicit correspondence is required before any finite-dimensional readout-fiber supplier can be applied. It does not identify a product-generated algebra with the actual effect span. Measurement-relative compression and broader no-disturbance structure are prior work of Bluhm, Rauber and Wolf (arXiv:1708.04898v4) and Koashi and Imoto (quant-ph/0101144), respectively.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_effect_correspondence`
- Truth anchor: `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_tv_supremum`
- Truth anchor: `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.arbitrary_random_control_event_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.projector_positive`
- Truth anchor: `D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.randomized_protocol_tv_supremum`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/TotalVariation/DataProcessing](../../TotalVariation/DataProcessing.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
