# One original law through trimming and endpoint classification

## Abstract

One original law through trimming and endpoint classification

Fix an arbitrary original Presentation theta. retainedLaw theta selects the stationary original integer-time law constructed by OriginalMarkedLaw.original_law for trim theta. jointLaw theta is its actual measurable inclusion pushforward, and visibleLaw theta is the actual Prod.snd pushforward of jointLaw. These definitions fix one common realization for all the conclusions. They do not choose separate output laws or assume defining cylinders.

**Theorem 1.1 (Measurable original inclusion).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.inclusion_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.inclusion_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite Presentation theta with measurable hidden singletons, includePath(theta) is measurable from retained hidden/output paths to original hidden/output paths. It applies subtype inclusion at every integer hidden coordinate and preserves every output coordinate. Actual complete future conditional measures and full-half-line screening use this same inclusion.

**Theorem 1.2 (Actual original and retained laws with trimmed endpoint masses).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.same_law_trimming`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.same_law_trimming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite exact-real presentation with measurable singletons, jointLaw satisfies every original hidden/output cylinder equality and retainedLaw satisfies every trimmed one. The inclusion pushforward of retainedLaw equals jointLaw as a measure, and the visible pushforward of retainedLaw equals visibleLaw as a measure. jointLaw and visibleLaw are stationary under every integer translation. The visible cylinders have exactly the original lambda M(word) all-ones masses, including length zero, and visibleLaw is almost surely supported on the two-sided no11 space. The trimmed one-symbol matrix has entrywise zero square.

retainedEndpoint is an event on the original PathSpace. It observes the original emitted word and requires the endpoint hidden state to be the inclusion of a retained state in a specified future class. Its preimage under includePath is exactly the existing endpointEvent on the trimmed space. Ghost-state fibers are empty and have zero actual mass. This finite measurable event uses no conditional posterior or division.

Assume RowUnifilar only for the matrices of trim theta. Apply MarkedPredictiveQuotient.actual_endpoint_mass directly to the Producer whose hidden domain is Positive theta and whose parameter is trim theta, with retainedLaw and its proved cylinder equalities. Measure.map_apply and the endpoint preimage equality transfer the result to that same jointLaw on the original space. The resulting joint word/final-class mass is the sum over retained initial states of their original lambda weights times the quotient wordMass, restricted to quotient trajectories ending in the selected class. Zero symbols, zero words, empty words and original ghost rows remain in scope.

The original law has no all-row unifilarity assumption. The optional endpoint conclusion requires only post-trimming unifilarity and says nothing about discarded rows. The future classes here are the existing finite-word futureMass classes on retained states; their identification with complete conditional future measures remains a separate obligation. The full marked path pushforward, actual MAP error, universal screening, both full-opposite-half-line squared erasure bounds, common distinguishing length, strict affinity, contraction and all-stationary tail summability remain outside this result. The UnifilarPairSurvival audit status is unchanged.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.inclusion_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming.same_law_trimming`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw](OriginalMarkedLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation](PositiveSupportPresentation.md)
