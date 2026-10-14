# Grouped MAP loss and nonmerged initial pairs

## Abstract

Grouped MAP loss and nonmerged initial pairs

For any finite initial index set S, a nonnegative real mass a(i), an arbitrary endpoint map f:S to C and a maximizing endpoint m, grouping the initial masses by f gives the unnormalized endpoint decision problem. C need not be finite in grouped_map_pair_bound; all zero groups and MAP ties are allowed. This statement neither asserts an actual law nor assumes unifilarity. OriginalUnifilarQuotient supplies its actual same-law realization.

**Definition 1.1 (Unordered stationary pair coefficient).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pairWeight`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pairWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality and real mass function pi, pairWeight(pi) is half the sum over all ordered distinct i,j of sqrt(pi(i)*pi(j)). There is no ordering built into the definition. pair_weight_bound proves that it equals the sum over i<j for every linear ordering on S.

**Theorem 1.2 (Actual endpoint grouping discards merged pairs).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.grouped_map_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.grouped_map_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality, every target C with decidable equality, every nonnegative a:S to real, every f:S to C and every m:C maximizing all grouped sums, sum_i a(i) minus sum_{f(i)=m} a(i) is at most half the ordered sum of sqrt(a(i)*a(j)) over pairs satisfying f(i) != f(j). Equivalently, for any ordering it is at most the unordered nonmerged-pair sum.

For an initial i outside the maximizing endpoint, its mass is at most its own group mass and hence at most the maximizing group mass. The square of the sum of sqrt(a(i)*a(j)) over j in the maximizing group is at least a(i) times that group mass, using the finite nonnegative sum-of-squares inequality. Thus that sum dominates a(i). Summing the initial errors gives a star of cross-group pairs. The two orientations of that star are disjoint, symmetric and contained in the full nonmerged ordered pair sum. This proves the factor one half and omits every merged pair, including pairs with positive initial masses.

**Theorem 1.3 (Stationary coefficient and cardinal bound).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pair_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pair_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite S with decidable equality and normalized nonnegative real pi, pairWeight(pi) is nonnegative and at most (card(S)-1)/2. For every linear ordering on S it equals sum_i sum_{j:i<j} sqrt(pi(i)*pi(j)).

The ordered off-diagonal sum equals (sum_i sqrt(pi(i))) squared minus one. Finite Cauchy-Schwarz bounds that square by card(S). Splitting distinct ordered pairs by their two orderings proves equality with twice the unordered sum. The cardinal bound controls the coefficient in actual_geometric_classification. In a singleton class space D=0.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.grouped_map_pair_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pairWeight`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination.pair_weight_bound`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival](UnifilarPairSurvival.md)
