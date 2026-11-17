# Lower Cost for All Adaptive Circular Deletions

## Abstract

The hidden carrier is exactly all legal cycles circles A, queries are the supported-label subtype A, and each response is actual deletion from the same original. Assume at least four labels, deterministic unit-cost observations, pointwise termination, and exact zero error.

The hidden carrier is exactly all legal cycles circles A, queries are the supported-label subtype A, and each response is actual deletion from the same original. Assume at least four labels, deterministic unit-cost observations, pointwise termination, and exact zero error.

**Theorem 1.1 (Generic Partners Are Actual Double-Fibre Originals).**

$$\mathrm{paired}\left(x, B, z\right) = \mathrm{firstFibreOfAmbiguous}\left(x, B, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.distinct_paired` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the generic fibre(read A,carrier A,x,B) with FirstLift A x B using exact legal-carrier membership. A distinct second-label partner exists exactly when the actual two-entry candidateSet has cardinal at least two. R1 bounds it by two, so this is exactly cardinal two, the definition of ambiguous. This proves equality of the actual sets, rather than merely substituting m and r into an arithmetic inequality.

**Theorem 1.2 (All Second Queries Retain at Least Two Partners).**

$$2 \le \mathrm{card}\left(\mathrm{paired}\left(x, B, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.actual_paired_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every realized first fibre has exactly A.card-1 original cycles by deletion_fiber_card. If the second label differs, the set correspondence and the actual unique-double-fibre count give exactly two paired candidates. If it repeats the first label, all first-fibre answers coincide and every candidate has a distinct partner because A.card-1 is at least three. This covers every supported second query chosen by any adaptive history.

**Theorem 1.3 (Every Exact Terminating Policy Obeys the Mean Bound).**

$$2 + \frac{2}{\mathrm{sub}\left(\mathrm{card}\left(A\right), 1\right)} \le \mathrm{uniformMeanTraceLength}\left(A, tr\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.actual_history_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let policy map the entire dependent observation history to a supported query or terminal label. For each legal original C, tr(C) and lab(C) are from some actual completed execution; no uniform stopping depth is given. Require a decoder of lab(C) to equal C. Nonempty A supplies Nonempty Q; the actual first-fibre size and paired-set bound discharge all generic hypotheses with m=A.card-1 and r=2. The unpruned finite-history bridge then gives mean trace length at least 2+2/(A.card-1), preserving repeated queries and arbitrary history dependence.

UniformCycleAttainment supplies a correct strategy querying pairwise-distinct supported x,z,y and the matching exact mean. A transient exact check combines its correctness and attainment with this lower theorem; the final conjunction is not a retained application wrapper. The proof uses the entire carrier with uniform prior and makes no finite-example substitution or assumed desired count.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.actual_history_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.actual_paired_bound`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.distinct_paired`
- Dependency: [D5/S3/Combinatorics/CircularWords/UniformCycleAttainment](UniformCycleAttainment.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/TwoQueryAmbiguityCost](../../ConceptDynamics/Experiment/TwoQueryAmbiguityCost.md)
