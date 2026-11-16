# Actual Markov trajectory prefixes and fixed-initial Doob scores

## Abstract

Actual Markov trajectory prefixes and fixed-initial Doob scores

**Theorem 1.1 (Actual archive and final-memory coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_archive_law`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_archive_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, arbitrary fixed phase history and any fixed positive stationary initial row pi of a reference chain R, independent of the source amplitude, the actual source circuit coefficient at register (Fin.cons i w,j), after n+1 gates, has Born mass pi(i) times the complete n+1-transition path product through the future word w followed by j. The source register equivalence is proved on these exact coordinates by recursion. Summing over j gives the n-transition prefix mass, since the last stochastic row sums to one. The full register and archive-only experiment therefore realize the respective probability families in completePathFisher and archiveFisher when q is varied along its actual Doob coordinate; pi remains fixed. This includes the one-gate archive with zero observed transitions.

**Theorem 1.2 (Discarding the last memory loses one transition of information).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.archive_information_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.archive_information_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite nonempty state space, irreducible row-stochastic P, directed reward g and fixed reference stationary initial row pi, archiveMass sums the actual n+1-transition global Doob path masses over the final state. Summing its last stochastic row gives exactly the n-transition prefix mass. Consequently archiveFisher=n v and completePathFisher(n+1)-archiveFisher(n)=v for every natural n, including n=0. Thus an N-gate source archive for N>=1 has (N-1)v Fisher. At zero gates the full initial observation has zero Fisher because pi is fixed. The result retains zero edges, singleton, periodic and nonreversible chains; it concerns classical observations.

**Theorem 1.3 (The actual trajectory prefix measure).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty state type with measurable singletons, the real stochastic matrix K determines a row PMF and an actual Markov kernel. Starting the homogeneous Kernel.trajMeasure at the fixed positive normalized stationary row pi of the reference matrix P, its first n+1 states have exactly the pushforward of initialPathPMF K n under (i,w) mapped to Fin.cons i w. The equality holds for every n including zero, every stochastic K, and every finite path, with zero transition masses retained. The proof applies the existing trajectory singleton product theorem and matches its n transition factors to the recursive path weight; finite measures are equal on all singleton masses.

**Theorem 1.4 (The global family has the corrected complete-path score).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty irreducible row-stochastic P and arbitrary directed reward g, the globally defined Doob kernel agrees near zero with the constructed implicit local family by normalized Perron uniqueness. On every path of positive base mass, the derivative at zero of the logarithm of its actual initialPathPMF mass is the sum of the corrected transition increments. The initial row pi is fixed throughout the family. This identifies the actual probability mass with the previously derived local score, without a moving-stationary-initial term or a quantum Fisher assertion.

**Theorem 1.5 (Actual integrability).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stochastic K, every n, and every real observable of its first n+1 states, the corresponding observable on the infinite trajectory space is integrable. This follows from a finite simple function composed with the measurable coordinate prefix; integrability is proved for the constructed probability law.

**Theorem 1.6 (Finite expectations on the infinite law).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual stationary trajectory law of P, integrating any function f(X0,(X1,...,Xn)) equals the previously defined stationaryExpectation. The proof transports through trajectory_prefix_eq, applies the PMF integral formula, and matches every weight including zeros. It counts n transitions and n+1 states.

**Theorem 1.7 (The actual corrected trajectory martingale).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_martingale`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_martingale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty state type, arbitrary irreducible row-stochastic real P and directed real g, trajectorySum(score) is a Mathlib Martingale for Filtration.piLE on the actual Kernel.trajMeasure. This filtration is the sigma algebra of the coordinate history through time n. The process is strongly adapted and each prefix observable is integrable. Mathlib condDistrib_trajMeasure identifies the next-state conditional law with the actual transition kernel. Integrating the corrected increment against that row gives zero by score_centered. The martingale predicate is then obtained from the vanishing conditional expectations of successive increments, with no reversibility, aperiodicity, symmetric support or mixing assumption.

**Theorem 1.8 (Actual corrected second moments).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of the squared corrected trajectory sum is exactly n times varianceRate, for every n including zero. The finite-prefix expectation adapter consumes corrected_second_moment; the combinatorial moment argument is reused.

**Theorem 1.9 (Actual trajectory variance bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib variance of trajectorySum g under the constructed infinite law differs from n times varianceRate by at most D squared plus 2 U square-root(v), with D the oscillation of the constructed centered Poisson corrector and U the oscillation of the constructed second corrector. The variance integral is transported to the finite stationary path variance before applying variance_uniform_bound. This includes singleton, deterministic, periodic and nonreversible cases.

**Theorem 1.10 (Actual variance convergence).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual trajectory variance divided by n converges to varianceRate. The proof consumes normalized_variance_tendsto through the exact measure and variance adapter; no covariance summability or limit interchange is assumed.

**Theorem 1.11 (Actual global complete-path Fisher information).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.completePathFisher_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.completePathFisher_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

completePathFisher uses the actual initialPathPMF of globalDoob(t), with the original initial pi fixed for every parameter. The actual base law agrees with P by the global-local Doob identification. Positive-base paths have the corrected score by globalDoob_path_score; paths with zero mass have zero summand, so no derivative of log(0) is assumed. Reusing pathFisher_eq proves completePathFisher=n v for all n, including zero.

**Theorem 1.12 (Variance compared with actual path information).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_fisher_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_fisher_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute difference between the actual trajectory variance and actual complete-path classical Fisher information is bounded by D squared plus 2 U square-root(v), uniformly in the transition length. This comparison consumes both the actual global PMF Fisher identity and the trajectory variance bound.

**Theorem 1.13 (Actual Born path and fixed-exterior block laws).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_path_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_path_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q strictly between zero and one, the already constructed PhaseHistoryBound source is realized by one sequence of unitary memory circuits. sourcePath identifies the source archive and final memory with an initial bit and n future states. Preparing the fixed stationary mixture pi over initial basis bits, the squared circuit coefficients weighted by pi equal the actual stationary n-transition path PMF. For a fixed initial basis l and final memory r, the m+1-gate squared coefficient for archive (l,w1,...,wm) equals MarkovBlockWeight.pathMass q m l w r. Thus the finite-prefix and finite-window weights are actual computational-basis Born probabilities. The full archive and memory are retained in the first statement; postselection normalization and Fisher information of the conditioned block are separate operations. The source theorem assumes 0<q<1; endpoints are outside that source realization theorem, while the general stochastic trajectory results retain their degenerate cases.

The Born consumer uses transition P(q)=[[1-q,q],[1,0]], arrival reward g(i,j)=j, and fixed pi=(1,q)/(1+q). The Poisson gauge h=(0,-q/(1+q)) has the same corrected increments as its centered version. Direct substitution gives m=q/(1+q) and v=q(1-q)/(1+q)^3. For the tilt T_t=[[1-q,q exp(t)],[1,0]], lambda(t)=((1-q)+sqrt((1-q)^2+4q exp(t)))/2 and Q_t=P(q(t)) with q(t)=1-(1-q)/lambda(t). Its activity satisfies q(t)/(1-q(t))^2=exp(t) q/(1-q)^2. The conditional count experiment uses the actual global Perron radius to define q(t); its eigen-equations determine the same source amplitude and activity. The formulas for m and v describe the two-state evaluation of the general stationary mean and variance rate.

For a full path X0,...,Xn, set A=sum(X1,...,Xn) and d=Xn-X0. Its fixed-pi likelihood ratio is exp(t A-(n+d) log(lambda(t))). The corrected score is A-(n+d)m and the full classical Fisher is n v. The actual archive contains X0,...,X(n-1); summing out final memory gives an (n-1)-transition law for n>=1, with Fisher (n-1)v. The source phase observable instead sums departures X0,...,X(n-1), which differs from A by the endpoint d. Varying only the source phases at fixed q leaves these Born probabilities unchanged and has zero classical Fisher. None of these statements is a quantum Fisher claim.

For a fixed-exterior block of m interior bits, L=m+1 transitions, initial basis l and final-memory postselection r, the success probability is B_t=(Q_t^L)(l,r)=sum_w pathMass(q(t),m,l,w,r). Only positive B_t can be conditioned on. For m>=1 and 0<q<1 every exterior pair admits an all-zero interior; for m=0 the exterior 11 has zero mass. Dividing actual squared coefficients by B_t produces the normalized block experiment. On the padded legal support its mass is proportional to z(q)^K exp(t K), where K counts interior ones and z(q)=q/(1-q)^2. Its score is K minus its conditional mean, and its Fisher is Var(K). Grouping words by K gives a count law, and uniform sampling within each nonempty legal-count fiber reconstructs the word law independently of t. Thus count is sufficient for this fixed-exterior experiment. The endpoint sum, its strict positivity, this normalized count family, its score and Fisher, and uniform reconstruction are established in ConditionalBornFisher. The same module retains the exact finite endpoint correction.

The finite boundary must remain: conditional Fisher at zero is (L+r-l)v plus the second t derivative of log(B_t) at zero. In particular it need not equal L v. The exact normalizer is B_t=pi(q(t))_r+(-q(t))^L(1[l=r]-pi(q(t))_r). With e=m+2-l-r, alpha=(1-q)/(1+q), and s=(-1)^(e-1)q^e, the ordinary calculation yields Fisher=L v+v((3q-1)/(1+q)-l-r)+R_e, where R_e=e^2 alpha^2 s/(1+s)^2-2 e v s/(1+s). Its absolute remainder is at most (e^2/(1+q)^2+2 e v/(1-q))q^e; normalized conditional Fisher therefore tends to v for each fixed interior q. This bound is not uniform near q=1. Conditioning a prior mixture also reweights components by their postselection success probabilities; the existing conditionalMixture with fixed weights describes a different experiment unless that reweighting has been performed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_archive_law`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.actual_circuit_path_laws`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.archive_information_loss`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.completePathFisher_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integrable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_integral`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_martingale`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_second_moment`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_fisher_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_variance_tendsto`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight](../LegalWords/MarkovBlockWeight.md)
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal](MarkovAdditiveGlobal.md)
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths](MarkovAdditivePaths.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](../../../Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.md)
- Dependency: [D5/S3/Quantum/Entanglement/PhaseHistoryBound](../../../Quantum/Entanglement/PhaseHistoryBound.md)
