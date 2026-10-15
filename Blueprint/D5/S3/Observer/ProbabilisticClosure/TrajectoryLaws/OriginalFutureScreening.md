# Complete actual future laws and universal screening

## Abstract

Complete actual future laws and universal screening

**Theorem 1.1 (The original state marginal at every cut).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.state_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.state_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stationary original cylinder law, every integer cut and every hidden state, the actual state-event real mass equals the original initial mass. The unchanged cylinder specialization is consumed by the actual output-ergodicity proof.

**Theorem 1.2 (Finite prefixes of the actual future kernel).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.futureLaw_readPrefix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.futureLaw_readPrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite stationary presentation, original probability law satisfying its complete marked cylinders, integer cut, positive stationary hidden state, arbitrary natural length and dependent Boolean word, the native actual future kernel maps that prefix singleton to the original futureMass. TwelveStateRadiusZero consumes it to compute the actual outgoing-bit conditional mean.

**Theorem 1.3 (A whole future measure after an original marked cylinder).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.cylinder_future_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.cylinder_future_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original cylinder ending at an integer cut, with positive stationary final state, its restricted-law pushforward to the complete future equals its actual cylinder mass times the final-state future kernel. This is a complete measure identity, obtained from the existing finite-cylinder uniqueness supplier. TwelveStateRadiusZero uses it on the actual two-edge paths to prove complete future-only posterior identities.

**Theorem 1.4 (The complete original past and future factor at a hidden state).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.full_past_future_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.full_past_future_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive stationary state, arbitrary measurable complete marked-past event and arbitrary measurable complete-future event, their actual intersection factors at that state under the original joint law. TwelveStateRadiusZero consumes the factorization for the retained whole-past posterior.

**Definition 1.5 (Finite prefixes of complete futures).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.readPrefix`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.readPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

readPrefix(n,x) is the first n coordinates of any natural-indexed sequence x.

**Theorem 1.6 (Original state and finite future joint mass).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.future_state_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.future_state_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite measurable Presentation theta, actual probability measure J satisfying all HasOriginalCylinders(theta), integer cut t, original state i, natural n and word w, the actual joint real mass of H(t)=i and the future prefix w equals theta.initial(i)*futureMass(theta.matrix,i,n,w). Zero initial masses and null words remain included. TwelveStateFutureRecovery consumes this exact original-cylinder factorization.

Fix any original finite exact-real Presentation theta. retainedLaw, jointLaw and visibleLaw are the selected actual laws of OriginalLawTrimming. jointLaw is the inclusion pushforward of retainedLaw, and visibleLaw is its actual visible pushforward. Every conditional distribution in this result is taken under these same measures. The original stationary vector can have zero entries, and the original matrices can be reducible, periodic or nonunifilar.

futureLaw(J,t) is Mathlib condDistrib of the complete future output sequence starting at t, given H(t), under J. It is a total Markov kernel, including null hidden-state fibers. retainState maps each positive original state to its retained subtype value and assigns a fixed retained value to a zero-mass state. originalClass applies the existing trimmed finite-word class map to retainState at H(t). It is a total measurable function on the entire original PathSpace. classFutureLaw selects the complete future conditional of a representative of each retained class under retainedLaw.

**Theorem 1.7 (Whole-half-line screening on the original realization).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.same_law_future_screening`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.same_law_future_screening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Presentation theta with a finite measurable hidden alphabet and measurable singletons, at every integer t, two positive stationary states i and j have the same existing trimmed finite-word futureMass class if and only if futureLaw(jointLaw(theta),t,i.val) equals futureLaw(jointLaw(theta),t,j.val) as complete probability measures on all natural-indexed future outputs. Equality is equality on the entire product sigma-algebra, including every measurable half-line event. The original, untrimmed futureSetoid relation on i.val and j.val is also equivalent to equality of their trimmed classes: every original finite-word profile is retained.

At every integer t, the actual complete future conditional given originalClass under jointLaw equals classFutureLaw for every class. The complete future function and complete past function are conditionally independent given the sigma-algebra generated by originalClass. Consequently the actual condDistrib of the complete future given the pair (originalClass,past) equals, almost everywhere for that pair's actual jointLaw pushforward, classFutureLaw extended to ignore the past. The latter extension is the total Markov kernel prodMkRight on the full class/past product, including impossible pairs.

The finite original cylinder factorization supplies the mass of every finite future cylinder after a fixed marked past cylinder. The actual condDistrib given a positive hidden state has exactly the futureMass cylinder values. Prefix-measure uniqueness extends the fixed-past identity to arbitrary measurable future events; a second application extends the past side to arbitrary measurable complete marked-past events. The same uniqueness theorem identifies equality of the finite-word profiles with equality of the actual complete future conditionals.

Partition an actual class event by its hidden states. Their complete future conditionals agree, so the whole-past factorization survives averaging within the class. Inclusion transfers these measurable event identities and the positive-state conditional measures to jointLaw on the original alphabet. Every retained class has positive actual mass. Mathlib's conditional-distribution and conditional-expectation identities give CondIndepFun, and condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight gives the conditional kernel identity after observing the entire past.

The result uses no row unifilarity, reversibility, time reversal, exact synchronization, irreducibility or ergodicity. Positivity is used only on the proved retained support. Zero original masses remain present through the actual inclusion and total class map. This theorem supplies the screening needed at both the cut zero and the cut r+1 in the two retained-exterior squared erasure comparisons. Those squared comparisons, exterior bit predictors, actual MAP errors, marked quotient dynamics and strict geometric allowance remain separate conclusions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.cylinder_future_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.full_past_future_factor`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.futureLaw_readPrefix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.future_state_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.readPrefix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.same_law_future_screening`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening.state_mass`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent](NativeBorelCEvent.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders](OriginalFutureCylinders.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming](OriginalLawTrimming.md)
