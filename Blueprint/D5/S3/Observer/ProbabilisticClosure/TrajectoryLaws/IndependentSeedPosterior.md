# Independent seeds and the fixed original target

## Abstract

Independent seeds and the fixed original target

The process law J is the original twelve-state joint law. The fixed target is the phase and residue modulo three of H(0). The radius-r past word reads exactly the emitted coordinates -r through -1, while keeping this target at time zero. Its information field is the comap of that word map. An independent seed has an arbitrary measurable space U and probability measure nu; the extended law is the genuine product J times nu. enlarged(m) is the product sigma algebra formed from the old process field m and the whole seed field.

**Theorem 1.1 (Conditional expectation after adjoining an independent whole seed).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.product_condExp`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.product_condExp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable process space Omega and seed space U, process probability mu, seed probability nu, sub-sigma-algebra m of the process field, and mu-integrable real f, the conditional expectation of f under mu given m, pulled back by the process projection, equals almost everywhere under mu times nu the conditional expectation of f pulled back by that projection given enlarged(m). This is the same product law and an arbitrary integrable process function. It is consumed both by the actual seeded-support theorem and by the completed-field posterior theorem.

**Theorem 1.2 (The native radius-zero conditional law is the actual marginal).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_empty_conditional_distribution`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_empty_conditional_distribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every one of the six labels a, the real singleton mass of condDistrib(target,pastWord(0),J) at the empty word equals J.real of target=a, and is strictly positive. The empty visible cylinder is the whole space with probability one. The same finite-atom conditional-ratio identity used at positive radii gives this actual marginal, and the empty endpoint support proves its positivity. No conditioning on a null atom occurs; this establishes the native radius-zero identity on the same original joint law.

**Theorem 1.3 (Actual finite-past conditional class distributions).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_conditional_distribution`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_conditional_distribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, every length-n+1 Boolean past word w with positive actual visible-cylinder mass on coordinates -(n+1) through -1, and every one of the six labels a, the real singleton mass assigned by condDistrib(target,pastWord(n+1),J) at w equals the original-law atomPosterior at start -(n+1) and representative(a). This singleton mass is strictly positive if and only if the phase of a is w(n). The representative has original index equal to the label residue in zero through two; future_classes identifies its two-lift future class with that label.

The map pastWord has exactly the visible-cylinder atoms. The joint map consisting of pastWord and target has exactly the original endpoint-class atoms, because -(n+1)+(n+1)=0 on the original clock. Mathlib's condDistrib_apply_of_ne_zero gives the exact conditional singleton as the joint atom divided by the observed atom. The positive observed mass is proved nonzero before this identity is used. The original endpoint-support theorem then supplies every positive entry and excludes every other phase. Neither an independent marginal posterior table nor a new hidden law is introduced.

**Theorem 1.4 (The actual posterior survives independent-seed enlargement).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_seeded_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_seeded_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed space U, every probability nu on U, every natural n, and every one of the six labels a, the J-conditional expectation of the indicator of target=a given pastField(n+1), pulled back by the process projection, equals almost everywhere under J times nu the product-law conditional expectation of that indicator given enlarged(pastField(n+1)). Almost everywhere under that same product law, the conditional expectation is positive exactly when the phase of a equals the last observed output, and is strictly less than one for every label. All quantities use the original target at time zero and the same product law.

For any integrable real process function f, the old conditional expectation pulled back by the first projection is integrable and measurable for the enlarged field. On a rectangle with an old-information event and an arbitrary seed event, Fubini factors both integrals by the same seed mass. The old conditional-expectation identity makes them equal. The rectangles form a pi system generating the product field. Complement and countable disjoint-union identities extend equality to every event in that field. Uniqueness of conditional expectation proves the product identity, which is applied to each actual target indicator.

The actual condDistrib identity supplies the three-class support on each positive observed atom; zero-mass observed atoms are excluded only on a null event. A second supported class gives strictly positive complement mass, so each singleton conditional probability is less than one. These facts pull back along the probability-preserving process projection. The conditional-expectation statement uses raw finite-past fields. FixedTargetStopping separately constructs their completed nested filtration and handles completed observable events through almost-everywhere representatives. No stopping rule is transferred from a forward moving target.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_conditional_distribution`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_empty_conditional_distribution`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.actual_seeded_support`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior.product_condExp`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStatePresentation](TwelveStatePresentation.md)
