# Residual demand under a common preselected law

## Abstract

One actual preselected hard-two catalog law imposes an arbitrary-length residual bound at a closed cap.

**Definition 1.1 (Chain words).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural L and t, chainWord L t at i in Fin L is true exactly when the numerical address i is less than t. For t from zero through L these are the words with t initial true replies followed by false replies. Address i is original prime index i+1.

**Definition 1.2 (Joint chain events).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainEvent`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural L,t,r, chainEvent first gives the endpoint t=L the event r=0. Otherwise t=1 has the pair event r=0 or r=2, and every other t has r=t+1. When L is at least three, H_0 is {1}, H_1 is {0,2}, H_t is {t+1} for 2 at most t less than L, and H_L is {0}. The endpoint branch has priority for degenerate lengths.

**Definition 1.3 (First false low reply).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.firstFalse`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.firstFalse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any L and low word b, firstFalse b is the least natural address where lowReply b is false. The lowReply convention is false outside Fin L, so L is the sentinel for the all-positive low word. On chainWord L t with t at most L, this first false address is t.

**Definition 1.4 (Full all-word selected target).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.finiteTarget`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.finiteTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, real amplitude sequence a and low word b, finiteTarget is a measure on Fin(L+1). If n=firstFalse b is less than L, it is ofReal(1-a(n)) times the Dirac mass at zero plus ofReal(a(n)) times the Dirac mass at n+1. Otherwise it is the Dirac mass at zero. Thus zero-based a(k) is original a_(k+1), while finite label r is original tape mark theta_r. For the original positive, nonincreasing sequence bounded by one these are probability measures. The target is defined at every low word, including words with several zeros.

**Definition 1.5 (Entire residual from original index three).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.residual`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural-indexed real sequence a and real cap epsilon, residual a epsilon is the infinite sum over k at least zero of max(a(k+2)-epsilon,0). This is original D_3, beginning at original amplitude a_3. When i<L is equivalent to epsilon<a(i), every term with k+2 at least L vanishes. Hence the sum is the finite sum over k<L-2, without any summability assumption on a. Equality a(i)=epsilon is inactive.

**Theorem 1.6 (Necessary residual bound).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.preselected_residual_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.preselected_residual_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L, real sequence a with a(i) at most one for every i, real epsilon at least zero, strict cutoff i<L if and only if epsilon<a(i), and one PMF w on the actual OriginalScheduledWitnessTables.Catalog false L, assume that every word b satisfies measurableTotalVariation between the pushforward of w by f maps to f(b) and finiteTarget L a b at most ofReal(epsilon). Then residual a epsilon is at most 3 epsilon+1-a(0). The common law is over whole tables, not separately chosen wordwise laws. Catalog membership supplies an actual chronological list of at most two requests, all below L, with table output factoring through its complete chronological view. Output labels are unrestricted; repeated requests and reversed schedules remain permitted.

For each represented table, let Q be the set of distinct requested addresses and let rho(t) count its addresses below t. Nested filtered sets of equal cardinality are equal. The original view_congr then gives equal complete chronological transcripts and equal table outputs at equal ranks, including every repeated occurrence. Assign a successful nonterminal chain index its rank in {0,1,2}; assign the terminal index L the slot two. Nonterminal events are disjoint, so equal slots force equal nonterminal indices. A collision with the endpoint would force rank two and equal output zero. The sole nonterminal event admitting zero is t=1, but the addresses below one form a subset of {0}, so its rank is at most one. This excludes the collision and proves the simultaneous three-slot bound on the actual table.

Averaging this tablewise bound under the single PMF gives a chain-event mass sum at most three. The original all-word TV cap tests the singleton at t=0, the independent pair at t=1, the singleton at each 2 at most t less than L, and the base event at t=L. Their lower bounds are a(0)-epsilon, 1-epsilon, max(a(t)-epsilon,0), and 1-epsilon respectively. Thus a(0)+2+D_3-3 epsilon is at most three. The pair bound uses the entire event {0,2}; the two singleton bounds alone do not imply it. If L is at most two, D_3 is zero and the upper bound on a(0) gives the conclusion directly. Epsilon=1 gives L=0 for the original sequence.

For the original source application, x=(r,g) has prime r, integer g between ceil(F_r/10) and floor(F_r/5), and static N(x)=1+F_r g. Natural address i tests divisibility by prime p_(i+1). Every finite answer pattern has an actual source witness, and the first absence is finite. The selected target is (1-a_n) delta(theta_0)+a_n delta(theta_n), with a(k)=a_(k+1). The carrier is the full disjoint union of original B and P interval blocks; theta_j is the B_1 point 1/(j+2). The original nonatomic targets and the same-source consumer are unchanged.

A positive nonincreasing sequence converging to zero and 0<epsilon at most one give the strict finite active cutoff. The existing original-to-finite transport uses the full-carrier measurable projection fixing theta_1 through theta_L and sending all other tapes to theta_0, actual finite-pattern witnesses, sourcewise almost-sure finite termination and common-catalog compactness. It supplies precisely the common law and all-word cap required here for every original preselected hard-two acquisition. There is no bounded-address, bounded-state, source distribution, source label, advice or extra observation assumption. Repetitions are charged as actual requests. The existing whole-table uniform sampling and OriginalScheduledRealization execution use one source-independent seed, preserve the actual read log and hand off the original tape to the unchanged consumer on the same source. The finite all-positive word is represented by actual sources with later zeros; it is not an infinite all-positive source.

The conclusion concerns the separately selected atomic laws. It is necessary for the original preselected class and therefore its increasing first-zero-stop subclass; it makes no universal comparison or synthesis assertion. A singleton schedule can score three. An adaptive depth-two rule on three coordinates can score four, and independent wordwise mixtures can hit all four chain events. These facts locate the role of the preselected common law; they do not assert cap feasibility for the adaptive rule. The counting argument and source application make no literature novelty claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainEvent`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.chainWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.finiteTarget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.firstFalse`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.preselected_residual_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound.residual`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables](OriginalScheduledWitnessTables.md)
