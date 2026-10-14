# Actual marked quotient and geometric MAP error

## Abstract

Actual marked quotient and geometric MAP error

Fix every original finite exact-real Presentation theta, with normalized nonnegative stationary initial row and nonnegative binary matrices whose sum is stochastic and whose stationary 11 mass is zero. Assume RowUnifilar only for trim(theta). Original zero-mass rows can have several positive successors. No irreducibility, aperiodicity, ergodicity, time reversal, reversibility or exact synchronization is assumed. H has its finite measurable-singleton structure.

Use exactly retainedLaw(theta), jointLaw(theta) and visibleLaw(theta) from OriginalLawTrimming. Write J=jointLaw(theta) and P=visibleLaw(theta). The actual Q(t)=originalClass(theta,t) is the quotient of positive-mass states by equality of their complete future output laws, identified by OriginalFutureScreening.same_law_future_screening with the existing all-finite-cylinder futureSetoid. Null original hidden states retain their same total measurable extension. No minimality among presentations is asserted.

**Definition 1.1 (Class stationary row).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite Presentation, classWeight(theta,a) sums the initial masses of all hidden i with classOf(matrix,i)=a. The actual quotient uses theta replaced by trim(theta), so pi(a)=classWeight(trim(theta),a).

**Definition 1.2 (Weighted predictive successor kernel).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite binary matrix family M, classMatrix(M,x,a,b) is quotientMass(M,a,x) if b=quotientSuccessor(M,a,x), and zero otherwise. The mass is independent of a representative; for a positive mass its successor class is independent too. At zero mass the arbitrary successor has no contribution.

**Definition 1.3 (Coordinatewise marked class pushforward).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every M and every bilateral hidden/output path z, classPath(M,z) applies classOf(M) to every integer hidden coordinate and keeps every output coordinate. This map is used on the selected retained law.

**Definition 1.4 (Pushforward of the same original J).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original theta with measurable hidden singletons, markedLaw(theta) is the measure pushforward of the selected jointLaw(theta) under z maps to ((t maps to originalClass(theta,t,z)),z.output). Its output marginal is the same visibleLaw(theta).

**Theorem 1.5 (Every actual marked cylinder on one original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original theta and retained-row unifilarity, pi is nonnegative, sums to one and is stationary for classMatrix(false)+classMatrix(true). The classMatrix entries are nonnegative, their sum over both symbols and all destination classes is one in every row, and each symbol has at most one positive destination in each row. For every integer t, natural n, class path q of length n+1 and word w of length n, markedLaw assigns the cylinder exactly pi(q(0)) times the product of classMatrix(w(k),q(k),q(k+1)). markedLaw is stationary under every integer shift. Its visible marginal equals P as a measure, and each visible cylinder has the original sum_i lambda(i)*futureMass(original matrix,i,n,w). Empty words are included.

The proof uses the original cylinder law of retainedLaw and takes the finite disjoint union of all hidden cylinders lifting a class path. The exposed path_support and trajectory identities collapse this sum to the unique hidden trajectory. The weighted class_trajectory induction transports that trajectory to the same quotient; zero first-symbol masses are handled before any cancellation. Grouping retained initial masses gives pi and the exact classMatrix product. row_eq and the exposed quotient mass/successor identities separately give row grouping M(x)C=C T(x), whose stationary weighted sum proves pi stationarity.

The actual pushforward is identified with retainedLaw mapped by classPath through the proved includePath equality and the actual inclusion pushforward J. This is an equality of measures, not a separately chosen quotient law. Commutation of the coordinatewise map with integer shifts transfers stationarity. The visible projection commutes with the same map and preserves each original output cylinder. These all-interval marked cylinder equalities give the marked Markov path law with the specified stationary row and symbol kernel.

**Theorem 1.6 (Strict same-law current-class MAP allowance).**

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
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.actual_marked_quotient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classMatrix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classPath`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.classWeight`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient.markedLaw`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalErasureComparison](OriginalErasureComparison.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction](UnifilarAffinityContraction.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination](UnifilarMapDomination.md)
