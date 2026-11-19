# Avoiding a hit at an unknown name

## Abstract

A finite adaptive query bound for uniformly named graphs.

**Theorem 1.1 (Hypergeometric bound for a finite query budget).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.fresh_guess_survival_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.fresh_guess_survival_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite simple graph, a finite name space and an injective reference naming. The initial names are a subset of the range of the reference naming. Choose uniformly from the injections that preserve the assignments of those initial names. A deterministic strategy queries one name at a time and receives either all neighbor names or a miss marker. Run the strategy for at most the given query budget. In each successful reply, the queried name and all returned names join the known set. The probability that every successful query uses a name already known when it is queried is at least the ratio of the binomial coefficient for the invalid names to the coefficient for all initially available names. In both coefficients the lower argument is the smaller of the query budget and the number of initially available names.

Partition the surviving namings by their query transcripts. The next query is fixed within each part. If it uses a fresh name, the conditional hit probability is the ratio of the remaining hidden vertices to the fresh names. Revealing additional valid names cannot increase the baseline hit bound, and the number of distinct failed names is at most the number of preceding queries. Summing over transcripts bounds the decrease in survival at each step. The product of the corresponding miss probabilities reduces to the stated binomial ratio.

**Theorem 1.2 (Distinct guesses attain the bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.exists_strategy_attaining_guess_survival`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.exists_strategy_attaining_guess_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same finite graph, initial naming and uniform distribution as in the preceding bound. There exists a deterministic strategy with depth at most the query budget whose probability of avoiding an unknown-name hit is exactly the binomial ratio. Fix a list of distinct initially unknown names with length equal to the smaller of the budget and the number of such names. Query in that order until the first hit or the end of the list. The run avoids an unknown-name hit precisely when the naming omits every listed name. Restricting to the unnamed vertices counts the surviving injections by a falling factorial. Dividing by the count of all compatible injections gives the stated ratio.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.exists_strategy_attaining_guess_survival`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.fresh_guess_survival_ge`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation](KnownNameSimulation.md)
- Dependency: [D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory](NamedNeighborhoodHistory.md)
- Dependency: [D5/S3/Combinatorics/Probability/PartialNameAssignment](../../Probability/PartialNameAssignment.md)
