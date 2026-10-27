# Regular signed lifts on compact Hausdorff quotients

## Abstract

Every finite signed measure with regular total variation has a regular total-variation-mass-preserving lift along a compact Hausdorff continuous surjection.

The carrier hypotheses are the exact TopologicalSpace, CompactSpace, T2Space, MeasurableSpace, and BorelSpace structures in the Lean telescope. K and L have independent universes and arbitrary compact Hausdorff Borel structures; either carrier may be empty. The input is an actual finite SignedMeasure mu on L whose totalVariation is explicitly regular. For every continuous surjection p there is an actual SignedMeasure nu on K with regular totalVariation, exact signed pushforward map(nu,p)=mu, and equal totalVariation mass.

**Theorem 1.1 (Order-unit positivity).**

$$\forall K: \operatorname{Type}\left(u\right), \operatorname{Compact}\left(K\right) \Rightarrow\forall Lambda: \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{ContinuousMap}\left(K, \operatorname{Real}\left(\right)\right)\right), \operatorname{norm}\left(Lambda\right) \le \operatorname{Lambda}\left(1\right) \Rightarrow\forall f: \operatorname{ContinuousMap}\left(K, \operatorname{Real}\left(\right)\right), 0 \le f \Rightarrow0 \le \operatorname{Lambda}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/RegularSignedLift.positive_of_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real continuous linear functional Lambda is positive when its norm is at most its value at the unit. For nonnegative f, set M=norm(f) and u=M*1-f. Then norm(u) is at most M, and Lambda(u)=M*Lambda(1)-Lambda(f) forces Lambda(f) to be nonnegative. No nonempty or Hausdorff premise is needed. restrictionPositive restricts a positive functional to compactly supported continuous functions.

**Theorem 1.2 (Positive regular lift by real Hahn–Banach and RMK).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \\\operatorname{TopologicalSpace}\left(K\right) \land \operatorname{CompactSpace}\left(K\right) \land \operatorname{T2Space}\left(K\right) \land \operatorname{MeasurableSpace}\left(K\right) \land \operatorname{BorelSpace}\left(K\right) \land \operatorname{TopologicalSpace}\left(L\right) \land \operatorname{CompactSpace}\left(L\right) \land \operatorname{T2Space}\left(L\right) \land \operatorname{MeasurableSpace}\left(L\right) \land \operatorname{BorelSpace}\left(L\right) \Rightarrow\\\forall p: K \to L, \operatorname{Continuous}\left(p\right) \land \operatorname{Surjective}\left(p\right) \Rightarrow\\\forall alpha: \operatorname{Measure}\left(L\right), \operatorname{IsFiniteMeasure}\left(alpha\right) \land \operatorname{Regular}\left(alpha\right) \Rightarrow\\\exists eta: \operatorname{Measure}\left(K\right), \operatorname{IsFiniteMeasure}\left(eta\right) \land \operatorname{Regular}\left(eta\right) \land \operatorname{map}\left(eta, p\right) = alpha \land \operatorname{measure}\left(eta, \operatorname{univ}\left(\right)\right) = \operatorname{measure}\left(alpha, \operatorname{univ}\left(\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/RegularSignedLift.exists_regular_measure_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

The pullback C(L,Real) to C(K,Real) is a unital real linear isometry by the compact supremum norm and surjectivity. Integration against alpha is transported to its range, extended by exists_extension_norm_eq, and shown positive from the bound norm(Lambda) <= Lambda(1) using M*1-h. PositiveLinearMap.mk₀ and CompactlySupportedContinuousMap.continuousMapEquiv feed RealRMK.rieszMeasure. The resulting finite regular measure has equal mass and equal integrals after pushforward; regular compactly-supported integral uniqueness gives map(p,eta)=alpha.

No nonemptiness, metric, zero-dimensionality, probability, positivity of the signed input, finite support, or abstract unrepresented functional is added. The regularity hypothesis is explicit because arbitrary compact Hausdorff Borel measures need not be regular.

The construction uses the pinned Mathlib real Hahn–Banach, positive real Riesz–Markov–Kakutani, regular restriction, continuous pushforward inner-regularity, and compactly-supported integral uniqueness declarations. The source attribution to the Talagrand route records the surrounding application; no external theorem is claimed as a project invention.

**Theorem 1.3 (Regularity of the Jordan parts).**

$$\begin{aligned}\forall L: \operatorname{Type}\left(v\right), \\\operatorname{TopologicalSpace}\left(L\right) \land \operatorname{CompactSpace}\left(L\right) \land \operatorname{T2Space}\left(L\right) \land \operatorname{MeasurableSpace}\left(L\right) \land \operatorname{BorelSpace}\left(L\right) \Rightarrow\\\forall mu: \operatorname{SignedMeasure}\left(L\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(mu\right)\right) \Rightarrow\\\operatorname{Regular}\left(\operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(mu\right)\right)\right) \land \operatorname{Regular}\left(\operatorname{negPart}\left(\operatorname{toJordanDecomposition}\left(mu\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/RegularSignedLift.regular_jordanParts_of_regular_totalVariation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mutually singular separator for the Jordan parts identifies the positive part with totalVariation restricted to the complement and the negative part with totalVariation restricted to the separator. Measure.Regular.restrict_of_measure_ne_top supplies both regularity conclusions.

**Theorem 1.4 (Signed lift with exact total variation mass).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \\\operatorname{TopologicalSpace}\left(K\right) \land \operatorname{CompactSpace}\left(K\right) \land \operatorname{T2Space}\left(K\right) \land \operatorname{MeasurableSpace}\left(K\right) \land \operatorname{BorelSpace}\left(K\right) \land \operatorname{TopologicalSpace}\left(L\right) \land \operatorname{CompactSpace}\left(L\right) \land \operatorname{T2Space}\left(L\right) \land \operatorname{MeasurableSpace}\left(L\right) \land \operatorname{BorelSpace}\left(L\right) \Rightarrow\\\forall p: K \to L, \operatorname{Continuous}\left(p\right) \land \operatorname{Surjective}\left(p\right) \Rightarrow\\\forall mu: \operatorname{SignedMeasure}\left(L\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(mu\right)\right) \Rightarrow\\\exists nu: \operatorname{SignedMeasure}\left(K\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(nu\right)\right) \land \operatorname{map}\left(nu, p\right) = mu \land \operatorname{totalVariation}\left(nu, \operatorname{univ}\left(\right)\right) = \operatorname{totalVariation}\left(mu, \operatorname{univ}\left(\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/RegularSignedLift.exists_regular_normPreserving_signedMeasure_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift the two actual Jordan parts by the positive theorem. Pulling the target separator back along p proves the two lifted positive measures are mutually singular. Their JordanDecomposition difference is the output signed measure, so its totalVariation is exactly the sum of the two regular lifts. The signed pushforward is proved by measurable-set extensionality using VectorMeasure.map_apply and Measure.toSignedMeasure_sub_apply, and the exact mass follows from the two positive mass equalities.

The theorem is a construction supplier for the existing NormPreservingLifts.arbitrary_lifts_tendsto consumer. It does not construct the CH recursion, supported clopen rows, fibre hypotheses, or any global solution of Kania–Kąkol Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/Measures/RegularSignedLift.exists_regular_measure_lift`
- Truth anchor: `D5/S3/Topology/Measures/RegularSignedLift.exists_regular_normPreserving_signedMeasure_lift`
- Truth anchor: `D5/S3/Topology/Measures/RegularSignedLift.positive_of_norm_le_one`
- Truth anchor: `D5/S3/Topology/Measures/RegularSignedLift.regular_jordanParts_of_regular_totalVariation`
