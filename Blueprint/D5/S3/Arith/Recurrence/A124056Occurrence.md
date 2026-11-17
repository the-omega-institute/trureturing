# A124056 divisibility-count recurrence

## Abstract

A124056 divisibility-count recurrence

The sequence starts with one. Each later term counts all preceding indices whose values divide the immediately preceding value, including that preceding index and retaining multiplicities. The internal value term(n) is the source value a(n+1). Its finite tuple contains exactly the first n+1 terms. The positive-index sourceTerm(n)=term(n-1) is used only at n at least one; no value at zero enters its recurrence.

**Theorem 1.1 (Exact original initialization and recurrence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source sequence has sourceTerm(1)=1. For every positive natural n, sourceTerm(n+1) is the cardinality of the indices i in the closed interval from one to n for which sourceTerm(i) divides sourceTerm(n). The tuple consistency proof establishes the actual index dictionary, preserving the self index and repeated values. The initial values are 1,1,2; the only ones occur at internal indices zero and one, and all terms from internal index three onward are at least three.

**Theorem 1.2 (A global sublinear multiplicity estimate is impossible).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let count(N,d) count occurrences of d at internal indices less than N, and let prefixMax(N) be the maximum through internal index N, inclusive. There are no fixed positive real C and delta such that count(N,d) is at most C times prefixMax(N) to the power 1-delta for every N and every positive d. At repeated equal values the successors strictly increase, so the pair consisting of a value and its successor is injective and the sequence is unbounded. A proposed estimate and the classical divisor subpower bound at epsilon=delta/2 would bound every prefix maximum by one fixed constant, a contradiction.

**Theorem 1.3 (Infinitely many threes imply full positive occurrence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that for every natural B there is an internal index n at least B with term(n)=3. Then for every positive k there is a positive source index n with sourceTerm(n)=k. The exact successor of a three is two plus the number of threes through that occurrence. The count increases by zero or one, and the assumed cofinal occurrences make it unbounded. Its first crossing of each positive threshold therefore gives that exact count. This result explicitly retains the infinitely-many-threes hypothesis.

**Theorem 1.4 (Finitely many threes force one missing residue class).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the set of internal indices at which the value is three is finite, there is a natural q at least two such that every sequence value greater than one has remainder different from one modulo q. A seed is an internal index i at least two with no earlier divisor value at an index from two to i-1. Such a seed is equivalent to its successor having value three, so there are finitely many seeds. Their values have a finite LCM q, divisible by two. The earliest divisor index from two through any index n is a seed, providing a common divisor at least two of q and term(n). Such a value cannot have remainder one modulo q.

The unconditional assertion that every positive integer occurs remains open in this module. The missing implication is the uniform multiplicity estimate for prefixes avoiding a residue class. The ordinary route uses the divisor-list rank bound, ordered prime-word convolution, a fixed fractional exponent with finite Dirichlet moments for every exponent greater than one, and distinct predecessor values. None of these unproved estimates is installed as an axiom or used as an unconditional theorem.

## References

- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification`
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Divisors/DivisorSubpower.md)
