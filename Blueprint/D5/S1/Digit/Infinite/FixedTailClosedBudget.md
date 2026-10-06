# Fixed-tail closed budget

## Abstract

Fixed-tail closed budget.

**Definition 1.1 (Finite legal source paths).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.SourcePath`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.SourcePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source path is a finite list of actual three-bit source labels. Each edge obeys the incoming guard restriction and passes its highest bit to the next guard. The empty list preserves the guard. A legal terminal address determines a legal completion of the path through the source branch recursion.

**Definition 1.2 (Synchronous stems and return triples).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.FixedTailData`

*Formalization.* `D5/S1/Digit/Infinite/FixedTailClosedBudget.FixedTailData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each of two guards, choose a legal stem from guard zero and two legal return blocks. Both stems and their common color word have length a, where a may be zero. Each return block and its corresponding common color word have length L, with L at least one. The two return blocks of the first source are distinct. The two sources retain their own terminal addresses and future color records.

**Theorem 1.3 (The least budget for all finite return words).**

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
- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
