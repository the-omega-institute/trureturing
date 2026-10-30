# Incidence Dynamics of Fibonacci Substitution Words

## Abstract

Transport finite Fibonacci substitution words through their incidence matrix and additive observables.

**Definition 1.1 (The Boolean Parikh vector).**

Lean statement: `D5/S1/Words/FibonacciIncidence.parikh`

*Formalization.* `D5/S1/Words/FibonacciIncidence.parikh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite Boolean word, parikh records the number of occurrences of each Boolean letter as a function on the alphabet.

**Definition 1.2 (One Fibonacci substitution step).**

Lean statement: `D5/S1/Words/FibonacciIncidence.substitute`

*Formalization.* `D5/S1/Words/FibonacciIncidence.substitute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite-word substitution maps each letter by the Fibonacci substitution and concatenates the resulting images.

**Definition 1.3 (Iterated substitution).**

Lean statement: `D5/S1/Words/FibonacciIncidence.iterate`

*Formalization.* `D5/S1/Words/FibonacciIncidence.iterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

iterate n w applies the substitution n times, with the zeroth iterate equal to w.

**Definition 1.4 (The substitution incidence matrix).**

Lean statement: `D5/S1/Words/FibonacciIncidence.incidence`

*Formalization.* `D5/S1/Words/FibonacciIncidence.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix entry in output row b and input column a is the number of b letters in the substitution image of a.

**Definition 1.5 (An additive letter observable).**

Lean statement: `D5/S1/Words/FibonacciIncidence.weightedSum`

*Formalization.* `D5/S1/Words/FibonacciIncidence.weightedSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

weightedSum assigns a value to each letter and sums those values along a finite word in an arbitrary additive commutative monoid.

**Theorem 1.6 (Substitution acts by the incidence matrix).**

Lean statement: `D5/S1/Words/FibonacciIncidence.parikh_substitute`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.parikh_substitute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Boolean word, its Parikh vector after one substitution is the incidence matrix multiplied by its original Parikh vector.

**Theorem 1.7 (Iterated substitution acts by matrix powers).**

Lean statement: `D5/S1/Words/FibonacciIncidence.parikh_iterate`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.parikh_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After n substitution steps, the Parikh vector is obtained by applying the nth power of the incidence matrix.

**Theorem 1.8 (Additive observables factor through Parikh counts).**

Lean statement: `D5/S1/Words/FibonacciIncidence.weightedSum_eq_parikh`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.weightedSum_eq_parikh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every additive weighted sum equals the finite sum of each letter's weight scaled by its Parikh count.

**Theorem 1.9 (Weighted observables under iterated substitution).**

Lean statement: `D5/S1/Words/FibonacciIncidence.weighted_iterate`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.weighted_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the two transport laws expresses any weighted observable after n iterations using the incidence-matrix power and the initial Parikh vector.

**Theorem 1.10 (Finite Fibonacci words are substitution iterates).**

Lean statement: `D5/S1/Words/FibonacciIncidence.fibWord_eq_iterate`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.fibWord_eq_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's finite Fibonacci word at level n is the nth substitution iterate of the one-letter true seed.

**Theorem 1.11 (Exact letter counts in finite Fibonacci words).**

Lean statement: `D5/S1/Words/FibonacciIncidence.fibWord_parikh`

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciIncidence.fibWord_parikh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level n, the true letter occurs Nat.fib (n+1) times and the false letter occurs Nat.fib n times.

## References

- Truth anchor: `D5/S1/Words/FibonacciIncidence.fibWord_eq_iterate`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.fibWord_parikh`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.incidence`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.iterate`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.parikh`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.parikh_iterate`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.parikh_substitute`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.substitute`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.weightedSum`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.weightedSum_eq_parikh`
- Truth anchor: `D5/S1/Words/FibonacciIncidence.weighted_iterate`
- Dependency: [D5/S1/Words/GoldenGapPrefix](GoldenGapPrefix.md)
