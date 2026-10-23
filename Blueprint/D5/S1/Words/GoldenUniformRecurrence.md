# Uniform Recurrence of the Golden Word

## Abstract

Give an explicit linear window in which every finite golden-word factor recurs.

**Theorem 1.1 (Every truncated suffix is an infix).**

$$\forall alpha \in Type,\; \forall l \in List\left(alpha\right),\; \forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; IsInfix\left(take\left(n, drop\left(p, l\right)\right), l\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.take_drop_isInfix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type alpha, list l and natural p,n, taking n entries after dropping p entries yields an infix of l. No length assumption is needed.

**Theorem 1.2 (Locate a start inside a concatenated block).**

$$\forall alpha \in Type,\; \forall beta \in Type,\; \forall f \in Function\left(alpha, List\left(beta\right)\right),\; \forall l \in List\left(alpha\right),\; \forall p \in \mathbb{N},\; p < length\left(flatMap\left(f, l\right)\right) \Rightarrow \left(\exists pre \in List\left(alpha\right),\; \exists a \in alpha,\; \exists post \in List\left(alpha\right),\; l = append\left(pre, cons\left(a, post\right)\right) \land \left(length\left(flatMap\left(f, pre\right)\right) \le p \land p < length\left(flatMap\left(f, pre\right)\right) + length\left(f\left(a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.exists_flatMap_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types alpha and beta, a list-valued map f, a source list l and a natural p below the concatenated image length, there are lists pre and post and a letter a with l=pre++a::post, length(flatMap(f,pre)) at most p, and p strictly below that length plus length(f(a)). Images may be empty.

**Theorem 1.3 (Windows contained in the left list).**

$$\forall alpha \in Type,\; \forall x \in List\left(alpha\right),\; \forall y \in List\left(alpha\right),\; \forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; p + n \le length\left(x\right) \Rightarrow take\left(n, drop\left(p, append\left(x, y\right)\right)\right) = take\left(n, drop\left(p, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.take_drop_append_eq_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type alpha, lists x,y and natural p,n with p+n at most length(x), the window obtained from x++y by dropping p entries and taking n is exactly the corresponding window of x.

**Definition 1.4 (The recurrence window is an explicit Fibonacci quantity).**

Lean statement: `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound`

*Formalization.* `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a factor length n, let k be the greatest Fibonacci index with Fib(k) at most n, and define B(n) = 3 Fib(k+5). This bound is deliberately coarse; no optimality claim is made.

**Theorem 1.5 (Every factor recurs wholly inside every B(n)-window).**

$$\forall i,\ \exists j,\ i\le j \land j+n\le i+B(n) \land w=\operatorname{goldenFactor}(n,j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every starting coordinate i and every word w occurring as a length-n golden factor, there is a start j at or after i such that w begins at j and ends no later than i+B(n). The proof locates w inside one control supertile, then finds a complete copy of that supertile after the arbitrary starting coordinate.

**Theorem 1.6 (The explicit window is at most thirty-nine times the factor length).**

$$n>0 \Rightarrow B(n)\le39n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, Fib(k) is at most n and Fib(k+1) is at most 2n. The identity Fib(k+5) = 3 Fib(k) + 5 Fib(k+1) therefore gives B(n) at most 39n.

**Theorem 1.7 (Every positive-length factor recurs in a direct 39n window).**

$$\forall i,\ \exists j,\ i\le j \land j+n\le i+39n \land w=\operatorname{goldenFactor}(n,j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining uniform recurrence with the coarse linear estimate removes the auxiliary Fibonacci expression from the window endpoint.

## References

- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.exists_flatMap_block`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.take_drop_append_eq_left`
- Truth anchor: `D5/S1/Words/GoldenUniformRecurrence.take_drop_isInfix`
- Dependency: [D5/S1/Words/GoldenWord](GoldenWord.md)
