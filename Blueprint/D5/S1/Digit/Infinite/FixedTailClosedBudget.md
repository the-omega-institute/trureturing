# Fixed-tail closed budget

## Abstract

Fixed-tail closed budget.

**Definition 1.1 (Distance to a closed interval).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.intervalDistance`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.intervalDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonnegative distance outside the closed interval [l,u] is max(l-x,max(0,x-u)). Inside the interval it is zero.

**Definition 1.2 (The scalar action of a source word).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word fixes the terminal scalar. A source label acts by its offset minus g times the remaining scalar, following the original low-to-high word order.

**Definition 1.3 (Departure costs for a color word).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordCost`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost is the maximum closed-cell distance over every paired source-word suffix and departure color. An empty source word or empty color word contributes zero.

**Theorem 1.4 (Composition at an appended source word).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_append`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all source words u and v and every real x, the scalar action of u appended to v at x equals the action of u at the action of v at x.

**Theorem 1.5 (The common affine slope).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_affine`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source word w and every real terminal scalar x, its action equals its action at zero plus (-g) to the length of w times x.

**Theorem 1.6 (The scalar of an actual prefix).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.prefix_scalar`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.prefix_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the same actual legal source x has source prefix w and literal terminal address y, then kappa(x) equals the scalar action of w at kappa(y).

**Theorem 1.7 (Composition of legal source paths).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.path_append`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.path_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two lawful source paths with a common intermediate guard concatenate to a lawful path from the first incoming guard to the second outgoing guard.

**Theorem 1.8 (Costs of concatenated source and color words).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_append`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the first source word and its color word have equal length, the appended departure cost is the maximum of the first cost evaluated at the second scalar action and the second cost at the original terminal scalar.

**Theorem 1.9 (Endpoint control of departure cost).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_endpoint_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_endpoint_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source word and color word, a terminal scalar in [lo,hi] has departure cost at most the maximum of the costs at lo and hi.

**Definition 1.10 (Finite legal source paths).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.SourcePath`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.SourcePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source path is a finite list of actual three-bit source labels. Each edge obeys the incoming guard restriction and passes its highest bit to the next guard. The empty list preserves the guard. A legal terminal address determines a legal completion of the path through the source branch recursion.

**Definition 1.11 (Synchronous stems and return triples).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.FixedTailData`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.FixedTailData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each of two guards, choose a legal stem from guard zero and two legal return blocks. Both stems and their common color word have length a, where a may be zero. Each return block and its corresponding common color word have length L, with L at least one. The two return blocks of the first source are distinct. The two sources retain their own terminal addresses and future color records.

**Theorem 1.12 (The least budget for all finite return words).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every synchronous pair of stems and return triples, the two return maps have common slope (-g) to the power L. Their explicit minimal closed invariant intervals include the fixed points of the extreme translations when the slope is positive, and the alternating extreme two-block fixed points when it is negative.

Retain every stem suffix and every suffix of each of the four return blocks, together with its specified color. There are twice a plus four times L entries, including repetitions. The budget theta is the maximum distance of their two image endpoints from the unexpanded closed color cells. It is nonnegative and belongs to the field of rational linear combinations of one and the reciprocal golden ratio.

For every nonnegative real c, there exists one fixed pair of legal terminal addresses whose source completions satisfy the closed observations for every finite binary choice word if and only if theta is at most c. This includes the empty choice word and empty stems. Colors are read at departure coordinates; the terminal coordinate after all source edges is not observed.

At theta, every pair of legal terminal addresses with scalar coordinates in the two return intervals satisfies the entire family simultaneously. Conversely, a fixed pair outside those intervals cannot reduce the budget: repetition of extreme blocks or alternating extreme blocks sends either terminal coordinate to each endpoint. Continuity and closedness pass every finite-history constraint to the corresponding endpoint. Each entry may use its own sequence of finite choice words; the sufficient bound holds for the same two tails throughout.

## References

- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.FixedTailData`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.SourcePath`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_append`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.cost_endpoint_bound`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.intervalDistance`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.path_append`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.prefix_scalar`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordCost`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_affine`
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.wordScalar_append`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
