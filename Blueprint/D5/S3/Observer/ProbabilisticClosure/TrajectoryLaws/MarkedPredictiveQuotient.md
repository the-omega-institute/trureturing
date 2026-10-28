# Actual marked cylinders and predictive endpoint masses

## Abstract

The defining integer-time hidden/output cylinders determine the actual final predictive-class masses of a row-unifilar presentation.

**Theorem 1.1 (The original deterministic endpoint).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_last`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state carrier, successor function, natural word length, initial state and Boolean word, the last state of trajectory is endpoint of that same word and successor function. The retained hidden-information application uses this exact identity after original unifilar path support reconstructs the positive hidden path.

**Theorem 1.2 (Original and quotient trajectories have equal selected word weights).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.word_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.word_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden alphabet, nonnegative row-unifilar binary marked matrix M, natural word length n, initial state i, Boolean word w and future class a, select the original word weight when its final hidden state belongs to a, and zero otherwise. This equals the quotient word weight selected when its final quotient state is a. Positive symbol mass gives the quotient-successor identity; a zero symbol mass makes both selected weights zero. The identity connects actual twelve-state endpoint events to their original deterministic paths.

**Theorem 1.3 (row eq).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.row_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.row_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonnegative row-unifilar binary matrix family and every i,j,x, the entry is its symbol row sum when j is the selected successor and zero otherwise. OriginalUnifilarQuotient.row_group uses the exact original row identity.

**Theorem 1.4 (future step).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.future_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.future_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such family, state, symbol and word, a prefixed futureMass is the first symbol mass times the successor futureMass. OriginalUnifilarQuotient.word_class uses it.

**Theorem 1.5 (quotient mass mk).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_mass_mk`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_mass_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary matrix family, state and symbol, quotientMass at classOf(i) equals symbolMass at i. It is used in the actual marked path and word bridges.

**Theorem 1.6 (quotient successor mk).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_successor_mk`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_successor_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative row-unifilar family and nonzero symbolMass at i, the quotient successor of classOf(i) equals the class of the original successor. The zero case carries no such unweighted claim. The actual marked path and word bridges use it.

**Theorem 1.7 (path support).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative row-unifilar family, word and hidden tail, pathMass from initial i is zero unless the path equals its selected trajectory; on that trajectory it is wordMass. The full actual marked pushforward consumes this identity.

**Theorem 1.8 (trajectory first).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_first`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every deterministic finite trajectory begins at its specified initial state, including the empty word. The actual marked pushforward uses this to group initial masses.

A Presentation has an arbitrary finite hidden set H, a nonnegative probability row lambda and two nonnegative real edge-emission matrices M(false), M(true). Their sum is stochastic, lambda is stationary, and lambda M(true) squared times the all-ones column is zero. Producer carries this finite hidden domain, its Fintype data and the Presentation together. Every finite exact-real producer is represented by such data; normalization rules out an empty hidden domain. These are the entire finite exact-real producer constraints. They permit zero stationary masses, zero matrix entries, reducibility and periodicity. RowUnifilar is a separate assumption about the marked branch: each original row and symbol has at most one positive successor.

PathSpace H contains a hidden coordinate H(t) and an emitted Boolean X(t) for every original integer time t. HasOriginalCylinders J theta requires one probability measure J to have, for every integer start t, every natural length n, every hidden path h of length n+1 and every emitted word w of length n, cylinder mass lambda(h(0)) times the product of M(w(k))(h(k),h(k+1)). At n=0 this is the actual hidden marginal lambda. OriginalMarkedLaw.original_law constructs such a stationary J from every Presentation, using the repository inverse-limit extension supplier. OriginalLawTrimming.same_law_trimming constructs one original J together with its positive-support law and identifies their actual inclusion and visible pushforwards. No defining cylinder equality is an extra parameter assumption of those constructions.

wordMatrix multiplies the original matrices in emitted-word order, with the identity at length zero. futureMass is its row sum. futureSetoid identifies i and j precisely when their futureMass values agree for every natural length and every Boolean word. Thus FutureClass is the quotient by the actual original finite future-cylinder masses. OriginalFutureScreening constructs the complete future ProbabilityMeasure laws and identifies equality of those laws with this finite-cylinder relation on the selected retained realization.

symbolMass sums the original M(x) row. successor chooses its unique positive entry, when one exists, and otherwise keeps the source state. Nonnegativity and row unifilarity give M(x)(i,j) equal to symbolMass(i,x) when j is this successor and zero otherwise. No division is used. Equal future classes have equal first-symbol masses; at a nonzero common mass, cancellation in every prefixed word cylinder gives equal successor classes. quotientMass and quotientSuccessor use representatives of these exact classes. Their mass is independent of the representative; their successor class is independent on every positive symbol. At a zero symbol, any representative-dependent successor has zero contribution. If C(i,a) is the indicator that classOf(i)=a and T(x)(a,b) is quotientMass(a,x) times the indicator that quotientSuccessor(a,x)=b, summing the original row formula gives M(x) C = C T(x) entry by entry, including zero symbol rows. This is the actual original matrix relation. The same prefixed-word recursion gives futureMass(i,n,w) equal to the quotient wordMass from classOf(i), including the empty word. Stochasticity gives the sum over the two symbol masses equal to one in every quotient class. Induction over word length then gives nonnegative quotient word masses summing to one. Thus these are the normalized original finite future-word distributions, even when a symbol or word has zero mass; OriginalFutureScreening supplies their identification with the complete future ProbabilityMeasure laws.

**Theorem 1.9 (First transition of a marked path).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden type, binary matrix family, natural n, hidden path of length n+2 and emitted word of length n+1, pathMass is the first marked transition times the pathMass of the two tails. OriginalMarkedLaw uses this identity to sum unrestricted hidden paths into the original matrix word product; no unifilarity is used in that summation.

**Theorem 1.10 (Summing paths by their initial state).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden type, natural n and real function on paths of length n+1, the sum over paths is the sum over their first state and length-n tail. The equivalence Fin.consEquiv supplies this identity. It is used both for unifilar endpoint masses and for the universal original visible-cylinder sums in OriginalMarkedLaw.

**Theorem 1.11 (Joint word and final-class mass under the original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite H with measurable singletons, every Presentation theta satisfying RowUnifilar, every probability measure J satisfying HasOriginalCylinders, every integer t, every natural n, every emitted word w and every FutureClass a, the theorem computes J of the event that X(t) through X(t+n-1) equals w and the class of H(t+n) equals a. Its value is the sum over original initial states i of lambda(i) times the quotient wordMass from classOf(i), restricted to those quotient trajectories whose endpoint is a. The wordMass and endpoint functions are exactly those of UnifilarPairSurvival. The formula uses unnormalized joint masses, so null words and null classes contribute zero and require no posterior division.

The proof first shows by induction at every word length that an original hidden path has zero marked path mass unless it equals the unique successor trajectory from its first state. On that trajectory its path mass is the successive symbol-mass product. The actual endpoint event is a finite disjoint union of the defining original hidden-path cylinders. Finite measure additivity and the cylinder equalities therefore collapse the hidden-path sum onto those unique trajectories. A second induction transfers the weighted endpoint mass to the predictive quotient, cancelling a common mass only when it is nonzero and treating the zero branch separately. This connects the same original J to the final-class joint masses; it does not construct J.

Taking t=1 and n=r gives the unnormalized final-class masses needed to classify Q(r+1) from X(1:r). Grouping lambda by its actual class gives pi(a) equal to the sum of lambda(i) in that class. For each observed word, the MAP success contribution is the maximum of these final-class masses; its error contribution is their sum minus that maximum. The word/final-class endpoint events form a finite measurable partition of the original PathSpace. For every classifier m, its actual disagreement probability under J equals the sum over words of their total final-class mass minus the mass of the selected class m(w). A maximizing class exists for each word; choosing one minimizes this actual disagreement probability over every word classifier. No null posterior is divided. The same defining integer-interval cylinder equalities make this finite error independent of the interval start. Taking starts -r and 1 identifies classification of Q(0) from X(-r:-1) with classification of Q(r+1) from X(1:r), including r=0. These finite decision and original-clock consequences use the endpoint theorem directly; no extra named theorem wrapper is retained. OriginalMarkedLaw supplies full stationarity, and OriginalLawTrimming supplies the inclusion and visible measure identities. OriginalUnifilarQuotient.actual_marked_quotient identifies the entire marked predictive-class path pushforward.

The proved pair_survival_word_affinity applies directly with H equal to the finite actual predictive quotient, p equal to quotientMass and delta equal to quotientSuccessor. It then identifies the killed common-word pair matrix row sum with the affinity of the nonmerged quotient words. This is an algebraic consequence once the actual masses above are identified. Applying the proved Bhattacharyya.bhattacharyya_le_one to the nonnegative normalized quotient word distributions gives affinity at most one. OriginalUnifilarQuotient evaluates the attained current-class MAP cells on the same selected jointLaw by this endpoint formula, proves their nonmerged pair domination and applies UnifilarAffinityContraction for the common distinguishing length and strict block contraction. OriginalUnifilarErasureTail then joins the unrestricted squared erasure comparisons to the infinite-tail estimate.

The universal branch retains exterior sigma(X(j):j not equal to zero), the left field sigma(X(-r),...,X(-1),X(j):j at least 1), and the right field sigma(X(j):j at most -1,X(1),...,X(r)). OriginalFutureCylinders proves the finite original hidden-path factorization and OriginalFutureScreening extends it to every integer cut and the entire hidden/visible past, conditioned on the actual complete-future class. ScreenedBinaryPredictor supplies a total measurable bounded predictor on impossible fibers as well. OriginalErasureComparison applies this screening on the same selected J and visible pushforward P to prove both full-opposite-half-line squared comparisons, including conditional-expectation pullback and stationary right-cut MAP error equality. None of these universal suppliers requires unifilarity or time reversal.

PositiveSupportPresentation.trim proves normalization, stationarity, stochasticity and the original no11 condition after restricting to positive stationary mass; trim_no11 gives the stronger entrywise zero square. include_cylinders preserves every original hidden/output cylinder, including ghost-state cases. OriginalLawTrimming.same_law_trimming identifies the actual inclusion and visible measures and transfers this endpoint theorem from the retained law to the same original J. Its endpoint assumption is only RowUnifilar on the trimmed matrices. The present supplier itself retains its all-original-row unifilarity assumption. The source radius-zero caveat is retained: a one-sided field at radius zero can omit a forcing neighbor. Tails are extended nonnegative sums and may be infinite before a geometric bound. The one-class case and zero contraction case require their source conventions, including zero to the zeroth power equal to one. No summability, fixed-dimension uniform rate, attainment or finite-hidden separation follows solely from the endpoint-mass theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.future_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_support`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_mass_mk`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.quotient_successor_mk`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.row_eq`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_first`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.trajectory_last`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.word_quotient`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival](UnifilarPairSurvival.md)
