# Actual marked cylinders and predictive endpoint masses

## Abstract

The defining integer-time hidden/output cylinders determine the actual final predictive-class masses of a row-unifilar presentation.

A Presentation has an arbitrary finite hidden set H, a nonnegative probability row lambda and two nonnegative real edge-emission matrices M(false), M(true). Their sum is stochastic, lambda is stationary, and lambda M(true) squared times the all-ones column is zero. Producer carries this finite hidden domain, its Fintype data and the Presentation together. Every finite exact-real producer is represented by such data; normalization rules out an empty hidden domain. These are the entire finite exact-real producer constraints. They permit zero stationary masses, zero matrix entries, reducibility and periodicity. RowUnifilar is a separate assumption about the marked branch: each original row and symbol has at most one positive successor.

PathSpace H contains a hidden coordinate H(t) and an emitted Boolean X(t) for every original integer time t. HasOriginalCylinders J theta requires one probability measure J to have, for every integer start t, every natural length n, every hidden path h of length n+1 and every emitted word w of length n, cylinder mass lambda(h(0)) times the product of M(w(k))(h(k),h(k+1)). At n=0 this is the actual hidden marginal lambda. OriginalMarkedLaw.original_law constructs such a stationary J from every Presentation, using the repository inverse-limit extension supplier. OriginalLawTrimming.same_law_trimming constructs one original J together with its positive-support law and identifies their actual inclusion and visible pushforwards. No defining cylinder equality is an extra parameter assumption of those constructions.

wordMatrix multiplies the original matrices in emitted-word order, with the identity at length zero. futureMass is its row sum. futureSetoid identifies i and j precisely when their futureMass values agree for every natural length and every Boolean word. Thus FutureClass is the quotient by the actual original finite future-cylinder masses. Equality with a quotient by complete infinite future ProbabilityMeasure laws additionally needs existence and uniqueness of those future laws.

symbolMass sums the original M(x) row. successor chooses its unique positive entry, when one exists, and otherwise keeps the source state. Nonnegativity and row unifilarity give M(x)(i,j) equal to symbolMass(i,x) when j is this successor and zero otherwise. No division is used. Equal future classes have equal first-symbol masses; at a nonzero common mass, cancellation in every prefixed word cylinder gives equal successor classes. quotientMass and quotientSuccessor use representatives of these exact classes. Their mass is independent of the representative; their successor class is independent on every positive symbol. At a zero symbol, any representative-dependent successor has zero contribution. If C(i,a) is the indicator that classOf(i)=a and T(x)(a,b) is quotientMass(a,x) times the indicator that quotientSuccessor(a,x)=b, summing the original row formula gives M(x) C = C T(x) entry by entry, including zero symbol rows. This is the actual original matrix relation. The same prefixed-word recursion gives futureMass(i,n,w) equal to the quotient wordMass from classOf(i), including the empty word. Stochasticity gives the sum over the two symbol masses equal to one in every quotient class. Induction over word length then gives nonnegative quotient word masses summing to one. Thus these are the normalized original finite future-word distributions, even when a symbol or word has zero mass; identifying their complete future ProbabilityMeasure laws remains separate.

**Theorem 1.1 (First transition of a marked path).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden type, binary matrix family, natural n, hidden path of length n+2 and emitted word of length n+1, pathMass is the first marked transition times the pathMass of the two tails. OriginalMarkedLaw uses this identity to sum unrestricted hidden paths into the original matrix word product; no unifilarity is used in that summation.

**Theorem 1.2 (Summing paths by their initial state).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden type, natural n and real function on paths of length n+1, the sum over paths is the sum over their first state and length-n tail. The equivalence Fin.consEquiv supplies this identity. It is used both for unifilar endpoint masses and for the universal original visible-cylinder sums in OriginalMarkedLaw.

**Theorem 1.3 (Joint word and final-class mass under the original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite H with measurable singletons, every Presentation theta satisfying RowUnifilar, every probability measure J satisfying HasOriginalCylinders, every integer t, every natural n, every emitted word w and every FutureClass a, the theorem computes J of the event that X(t) through X(t+n-1) equals w and the class of H(t+n) equals a. Its value is the sum over original initial states i of lambda(i) times the quotient wordMass from classOf(i), restricted to those quotient trajectories whose endpoint is a. The wordMass and endpoint functions are exactly those of UnifilarPairSurvival. The formula uses unnormalized joint masses, so null words and null classes contribute zero and require no posterior division.

The proof first shows by induction at every word length that an original hidden path has zero marked path mass unless it equals the unique successor trajectory from its first state. On that trajectory its path mass is the successive symbol-mass product. The actual endpoint event is a finite disjoint union of the defining original hidden-path cylinders. Finite measure additivity and the cylinder equalities therefore collapse the hidden-path sum onto those unique trajectories. A second induction transfers the weighted endpoint mass to the predictive quotient, cancelling a common mass only when it is nonzero and treating the zero branch separately. This connects the same original J to the final-class joint masses; it does not construct J.

Taking t=1 and n=r gives the unnormalized final-class masses needed to classify Q(r+1) from X(1:r). Grouping lambda by its actual class gives pi(a) equal to the sum of lambda(i) in that class. For each observed word, the MAP success contribution is the maximum of these final-class masses; its error contribution is their sum minus that maximum. The word/final-class endpoint events form a finite measurable partition of the original PathSpace. For every classifier m, its actual disagreement probability under J equals the sum over words of their total final-class mass minus the mass of the selected class m(w). A maximizing class exists for each word; choosing one minimizes this actual disagreement probability over every word classifier. No null posterior is divided. The same defining integer-interval cylinder equalities make this finite error independent of the interval start. Taking starts -r and 1 identifies classification of Q(0) from X(-r:-1) with classification of Q(r+1) from X(1:r), including r=0. These finite decision and original-clock consequences use the endpoint theorem directly; no extra named theorem wrapper is retained. OriginalMarkedLaw supplies full stationarity, and OriginalLawTrimming supplies the inclusion and visible measure identities. Identification of the entire marked predictive-quotient path pushforward remains separate.

The frozen pair_survival_word_affinity applies directly with H equal to the finite actual predictive quotient, p equal to quotientMass and delta equal to quotientSuccessor. It then identifies the killed common-word pair matrix row sum with the affinity of the nonmerged quotient words. This is an algebraic consequence once the actual masses above are identified. Applying the frozen Bhattacharyya.bhattacharyya_le_one to the nonnegative normalized quotient word distributions gives affinity at most one. Strict affinity below one still needs their distinction at a common word length. The classifier-to-affinity inequality, that common distinguishing length and strict bound, the block contraction and the nonnegative infinite-tail estimate remain further obligations. A generic matrix estimate alone cannot identify an erasure defect.

The universal branch retains exterior sigma(X(j):j not equal to zero), left field sigma(X(-r),...,X(-1),X(j):j at least 1), and right field sigma(X(j):j at most -1,X(1),...,X(r)). Finite coordinate restrictions of each field increase to exactly that whole field: each fixed integer coordinate occurs once the cutoff reaches its absolute value. Pinned MeasureTheory.tendsto_eLpNorm_condExp supplies L1 convergence along these filtrations to the corresponding whole-field conditional expectation. The visible law P equal to J.map Prod.snd is a probability measure, so the same exact limit applies there. The model-specific missing finite identity is that, for every finite past event D and boundary state i, the mass of D intersected with H(t)=i and a future word w equals the mass of D intersected with H(t)=i times futureMass(i,w). Its unrestricted hidden-path sum is essential in the universal branch. Summing this identity within an actual future class would give the finite screening rectangles. The full hidden/visible past before t and the visible future from t are exactly the suprema of their absolute-coordinate-cutoff restrictions. Two applications of pinned ProbabilityTheory.condIndep_iSup_of_monotone extend conditional independence of every pair of those finite restrictions to these entire fields, conditioning on the same class of H(t). The required standard Borel structure is supplied by the finite hidden alphabet and the countable integer coordinates. This exact extension is conditional on the still-unproved finite screening statements; it imposes no unifilarity hypothesis and does not prove the original rectangle factorization. This convergence supplies neither that original cylinder-to-screening identity nor the finite classification-to-defect inequalities. Transferring L1 convergence to squared defects also needs the bounded conditional-mean estimates and the exact conditional-expectation pullback through Prod.snd. Both comparisons must be proved under this same J and visible pushforward, with no unifilarity in their universal hypotheses and no time reversal in the right comparison.

PositiveSupportPresentation.trim proves normalization, stationarity, stochasticity and the original no11 condition after restricting to positive stationary mass; trim_no11 gives the stronger entrywise zero square. include_cylinders preserves every original hidden/output cylinder, including ghost-state cases. OriginalLawTrimming.same_law_trimming identifies the actual inclusion and visible measures and transfers this endpoint theorem from the retained law to the same original J. Its endpoint assumption is only RowUnifilar on the trimmed matrices. The present supplier itself retains its all-original-row unifilarity assumption. The source radius-zero caveat is retained: a one-sided field at radius zero can omit a forcing neighbor. Tails are extended nonnegative sums and may be infinite before a geometric bound. The one-class case and zero contraction case require their source conventions, including zero to the zeroth power equal to one. No summability, fixed-dimension uniform rate, attainment or finite-hidden separation follows solely from the endpoint-mass theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.actual_endpoint_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.path_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.sum_paths`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival](UnifilarPairSurvival.md)
