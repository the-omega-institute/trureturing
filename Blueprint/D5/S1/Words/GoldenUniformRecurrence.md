# Uniform Recurrence of the Golden Word

## Abstract

Give an explicit linear window in which every finite golden-word factor recurs.

**Definition 1.1 (The recurrence window is an explicit Fibonacci quantity).**

Lean statement: `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound`

*Formalization.* `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a factor length n, let k be the greatest Fibonacci index with Fib(k) at most n, and define B(n) = 3 Fib(k+5). This bound is deliberately coarse; no optimality claim is made.

**Theorem 1.2 (Every factor recurs wholly inside every B(n)-window).**

$$\forall i,\ \exists j,\ i\le j \land j+n\le i+B(n) \land w=\operatorname{goldenFactor}(n,j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every starting coordinate i and every word w occurring as a length-n golden factor, there is a start j at or after i such that w begins at j and ends no later than i+B(n). The proof locates w inside one control supertile, then finds a complete copy of that supertile after the arbitrary starting coordinate.

**Theorem 1.3 (The explicit window is at most thirty-nine times the factor length).**

$$n>0 \Rightarrow B(n)\le39n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, Fib(k) is at most n and Fib(k+1) is at most 2n. The identity Fib(k+5) = 3 Fib(k) + 5 Fib(k+1) therefore gives B(n) at most 39n.

**Theorem 1.4 (Every positive-length factor recurs in a direct 39n window).**

$$\forall i,\ \exists j,\ i\le j \land j+n\le i+39n \land w=\operatorname{goldenFactor}(n,j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining uniform recurrence with the coarse linear estimate removes the auxiliary Fibonacci expression from the window endpoint.

## References

- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le`
- Dependency: [D5/S1/Words/GoldenWord](GoldenWord.md)
