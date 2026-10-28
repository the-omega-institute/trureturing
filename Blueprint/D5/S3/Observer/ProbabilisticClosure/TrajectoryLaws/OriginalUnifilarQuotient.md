# Actual marked quotient and geometric MAP error

## Abstract

Actual marked quotient and geometric MAP error

**Theorem 1.1 (Actual classification error from its full cell partition).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.error_real_cells`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.error_real_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability mu, measurable finite target q, measurable finite observation w and total classifier m, the real disagreement probability equals the sum over observations of total joint-cell mass minus the selected joint-cell mass. No maximization hypothesis is needed. TwelveStateFutureRecovery consumes the exact supplier with the original J.

**Theorem 1.2 (Exact quotient word masses).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.word_class`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.word_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite marked Presentation theta with row-unifilar original marked matrices, natural length n, original hidden state i and Boolean word w, wordMass on the predictive quotient starting in classOf(i) equals the original futureMass(theta.matrix,i,n,w). Zero symbol masses are included. TwelveStateTail consumes the unchanged original supplier on trim(parameter).

**Theorem 1.3 (Nonnegative quotient symbol masses).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Presentation theta, future class a and Boolean symbol x, quotientMass(theta.matrix,a,x) is nonnegative. This sums the actual nonnegative marked row. TwelveStateTail consumes the unchanged original supplier for its killed-pair estimates.

**Theorem 1.4 (Normalized quotient symbol masses).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_total`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Presentation theta and future class a, the sum over both Boolean quotientMass entries is one. This follows from the original stochastic row at the quotient representative. TwelveStateTail consumes the unchanged original supplier.

**Theorem 1.5 (The actual fixed-target MAP error and surviving pairs).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_map_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_map_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite measurable marked Presentation theta with row-unifilar retained matrices and every natural past radius r, the real value of classError(theta,r) is at most half the ordered sum over distinct retained future classes i,j of sqrt(classWeight(i)*classWeight(j)) times survivingAffinity at radius r. The target is originalClass(theta,0) on jointLaw(theta), observed through the actual past window. Equal final endpoints contribute zero, ties and zero groups are retained, and no posterior-table parameter is substituted. TwelveStateTail consumes the unchanged original supplier with its explicit two-step contraction.

Fix every original finite exact-real Presentation theta, with normalized nonnegative stationary initial row and nonnegative binary matrices whose sum is stochastic and whose stationary 11 mass is zero. Assume RowUnifilar only for trim(theta). Original zero-mass rows can have several positive successors. No irreducibility, aperiodicity, ergodicity, time reversal, reversibility or exact synchronization is assumed. H has its finite measurable-singleton structure.

Use exactly retainedLaw(theta), jointLaw(theta) and visibleLaw(theta) from OriginalLawTrimming. Write J=jointLaw(theta) and P=visibleLaw(theta). The actual Q(t)=originalClass(theta,t) is the quotient of positive-mass states by equality of their complete future output laws, identified by OriginalFutureScreening.same_law_future_screening with the existing all-finite-cylinder futureSetoid. Null original hidden states retain their same total measurable extension. No minimality among presentations is asserted.

For any finite initial index set S, a nonnegative real mass a(i), an arbitrary endpoint map f:S to C and a maximizing endpoint m, grouping the initial masses by f gives the unnormalized endpoint decision problem. C need not be finite in grouped_map_pair_bound; all zero groups and MAP ties are allowed. These finite sum and square-root estimates require no unifilarity. actual_map_pairs applies them to the actual same-law endpoint cells; actual_geometric_classification uses their stationary coefficient bound.

**Definition 1.6 (Unordered stationary pair coefficient).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pairWeight`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pairWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality and real mass function pi, pairWeight(pi) is half the sum over all ordered distinct i,j of sqrt(pi(i)*pi(j)). There is no ordering built into the definition. pair_weight_bound proves that it equals the sum over i<j for every linear ordering on S.

**Theorem 1.7 (Actual endpoint grouping discards merged pairs).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.grouped_map_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.grouped_map_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality, every target C with decidable equality, every nonnegative a:S to real, every f:S to C and every m:C maximizing all grouped sums, sum_i a(i) minus sum_{f(i)=m} a(i) is at most half the ordered sum of sqrt(a(i)*a(j)) over pairs satisfying f(i) != f(j). Equivalently, for any ordering it is at most the unordered nonmerged-pair sum.

For an initial i outside the maximizing endpoint, its mass is at most its own group mass and hence at most the maximizing group mass. The square of the sum of sqrt(a(i)*a(j)) over j in the maximizing group is at least a(i) times that group mass, using the finite nonnegative sum-of-squares inequality. Thus that sum dominates a(i). Summing the initial errors gives a star of cross-group pairs. The two orientations of that star are disjoint, symmetric and contained in the full nonmerged ordered pair sum. This proves the factor one half and omits every merged pair, including pairs with positive initial masses.

**Theorem 1.8 (Stationary coefficient and cardinal bound).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pair_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pair_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality and normalized nonnegative real pi, pairWeight(pi) is nonnegative and at most (card(S)-1)/2. For every linear ordering on S it equals sum_i sum_{j:i<j} sqrt(pi(i)*pi(j)).

The ordered off-diagonal sum equals (sum_i sqrt(pi(i))) squared minus one. Finite Cauchy-Schwarz bounds that square by card(S). Splitting distinct ordered pairs by their two orderings proves equality with twice the unordered sum. The cardinal bound controls the coefficient in actual_geometric_classification. In a singleton class space D=0.

**Definition 1.9 (Class stationary row).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite Presentation, classWeight(theta,a) sums the initial masses of all hidden i with classOf(matrix,i)=a. The actual quotient uses theta replaced by trim(theta), so pi(a)=classWeight(trim(theta),a).

**Definition 1.10 (Weighted predictive successor kernel).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite binary matrix family M, classMatrix(M,x,a,b) is quotientMass(M,a,x) if b=quotientSuccessor(M,a,x), and zero otherwise. The mass is independent of a representative. When M is nonnegative and satisfies RowUnifilar, the successor class at a positive symbol mass is independent of the representative too. At zero mass the arbitrary successor has no contribution.

**Theorem 1.11 (An original marked row groups to the actual quotient row).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.row_group`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.row_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Presentation theta with row-unifilar original matrix, original hidden state i, symbol x and future class b, the sum of theta.matrix(x,i,j) over all j with classOf(theta.matrix,j)=b equals classMatrix(theta.matrix,x,classOf(theta.matrix,i),b). Zero-probability symbols contribute zero. The exact row identity is consumed by the quotient stationarity proof and by the actual twelve-state quotient connectivity argument.

**Definition 1.12 (Coordinatewise marked class pushforward).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every M and every bilateral hidden/output path z, classPath(M,z) applies classOf(M) to every integer hidden coordinate and keeps every output coordinate. This map is used on the selected retained law.

**Definition 1.13 (Pushforward of the same original J).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original theta with measurable hidden singletons, markedLaw(theta) is the measure pushforward of the selected jointLaw(theta) under z maps to ((t maps to originalClass(theta,t,z)),z.output). Its output marginal is the same visibleLaw(theta).

**Theorem 1.14 (Every actual marked cylinder on one original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original theta and retained-row unifilarity, pi is nonnegative, sums to one and is stationary for classMatrix(false)+classMatrix(true). The classMatrix entries are nonnegative, their sum over both symbols and all destination classes is one in every row, and each symbol has at most one positive destination in each row. For every integer t, natural n, class path q of length n+1 and word w of length n, markedLaw assigns the cylinder exactly pi(q(0)) times the product of classMatrix(w(k),q(k),q(k+1)). markedLaw is stationary under every integer shift. Its visible marginal equals P as a measure, and each visible cylinder has the original sum_i lambda(i)*futureMass(original matrix,i,n,w). Empty words are included.

The proof uses the original cylinder law of retainedLaw and takes the finite disjoint union of all hidden cylinders lifting a class path. The exposed path_support and trajectory identities collapse this sum to the unique hidden trajectory. The weighted class_trajectory induction transports that trajectory to the same quotient; zero first-symbol masses are handled before any cancellation. Grouping retained initial masses gives pi and the exact classMatrix product. row_eq and the exposed quotient mass/successor identities separately give row grouping M(x)C=C T(x), whose stationary weighted sum proves pi stationarity.

The actual pushforward is identified with retainedLaw mapped by classPath through the proved includePath equality and the actual inclusion pushforward J. This is an equality of measures, not a separately chosen quotient law. Commutation of the coordinatewise map with integer shifts transfers stationarity. The visible projection commutes with the same map and preserves each original output cylinder. These all-interval marked cylinder equalities give the marked Markov path law with the specified stationary row and symbol kernel.

**Theorem 1.15 (Strict same-law current-class MAP allowance).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_geometric_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_geometric_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be the cardinality of FutureClass(trim(theta).matrix) and D=pairWeight(pi), equal to sum_{a<b} sqrt(pi(a)*pi(b)). Then 0<=D<=(K-1)/2. There exist one natural ell>=1 and 0<=rho<1 such that every distinct pair of actual quotient states has different length-ell word distributions and affinity at most rho; every survivingAffinity at original time r is at most rho^(r/ell), equivalently the killed-pair matrix row bound supplied by pair_survival_word_affinity; and the actual OriginalErasureComparison.classError(theta,r) is at most ENNReal.ofReal(D*rho^(r/ell)) for every natural r.

The quotient wordMass from classOf(i) equals the original trimmed futureMass from i at every length and word, by the exposed positive-symbol successor identity and separate zero-symbol case. The words are normalized by stochasticity. If all quotient word laws agreed for two representatives, futureSetoid would identify them. finite_distinguishing_contraction therefore applies to these actual distributions, producing the common length, strict common affinity bound and killed-pair contraction without changing J or P.

For radius r, actual_cell evaluates the actual joint mass of leftWord(r)=w and Q(0)=a by pulling it back along includePath. Its preimage is exactly the existing endpointEvent at integer start -r, so actual_endpoint_mass applies directly to retainedLaw and its proved cylinders. Grouping by the initial class gives sum_i pi(i)*wordMass(i,w) restricted to endpoint(i,w)=a. Ghost-state fibers have zero mass under J. This uses the already proved endpoint supplier and does not reconstruct it.

The existing current_map_error supplies an attained classifier m(w) and its actual joint-cell maximization under J. The existing error_mass_formula gives the attained disagreement probability as one minus its selected joint-cell masses. A finite measurable partition gives total joint-cell mass one; finite ENNReal-to-real conversion then expresses the real error as the sum over words of total endpoint mass minus the maximizing endpoint mass. Apply grouped_map_pair_bound with a_i=pi(i)*P_i(w) and f(i)=endpoint(i,w). Sum over actual words, factor sqrt(pi(i)*pi(j)), and invoke pair_survival_word_affinity on the same p=quotientMass and delta=quotientSuccessor. The nonmerged pair contraction bounds each term and gives D*rho^(r/ell). All finite errors remain the original ENNReal classError; converting to real is justified by its attained probability mass.

The original emitted-bit clock and radius zero are unchanged; r/ell is natural division, hence floor(r/ell). Zero symbols, null words, reducibility, periodicity and original ghost states remain included. The theorem provides a law-dependent symbolic rate, no fixed-N uniform rate, efficient length search, numerical computation, hidden minimality, exact synchronization, stopping rule or attainment result. OriginalUnifilarErasureTail joins the existing unrestricted full-half-line comparisons to this estimate.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_geometric_classification`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_map_pairs`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.error_real_cells`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.grouped_map_pair_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pairWeight`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.pair_weight_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.q_total`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.row_group`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.word_class`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalErasureComparison](OriginalErasureComparison.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction](UnifilarAffinityContraction.md)
