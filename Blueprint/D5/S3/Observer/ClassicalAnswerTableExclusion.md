# Double Exclusion of a Classical Answer Table

## Abstract

One preparation-independent deterministic answer table is excluded by both noncontextual and local witnesses.

**Theorem 1.1 (One preparation-independent answer table is doubly excluded).**

$$\forall T,\\ \neg \operatorname{Noncontextual}(T) \land \neg \operatorname{ReproducesBellCHSH}_{\mu}(T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ClassicalAnswerTableExclusion.noncontextual_and_local_double_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Fiber be finite and nonempty. One deterministic answer-table structure contains total answer functions covering every element of the two-dimensional window algebra and Alice's and Bob's two CHSH settings. These functions have no preparation argument. A finite preparation supplies only one nonnegative normalized weight on Fiber, shared by all four settings.

For the noncontextual branch, suppose that the values assigned by this same table at each fiber extend to one unital complex-algebra character on the complete window algebra. Choosing any fiber produces a character on the two-by-two matrix algebra, contradicting WindowCharacter.window_algebra_has_no_character at window size two.

For the local branch, localModel reads Alice's and Bob's Boolean answers from that same table instance. ClassicalFiberBound.classical_chsh_abs_le_two bounds the absolute weighted CHSH value by two. The frozen Bell witness is positive two times square root two, which is strictly greater than two, so the table cannot reproduce it.

The Lean conclusion is the conjunction of the two negations for one named table T, not a conjunction of unrelated witness facts. The theorem is limited to finite nonempty fibers, the complete size-two window algebra, and the fixed Bell-state CHSH witness. It asserts no general Kochen-Specker classification, infinite hidden-variable theorem, or quartic-context obstruction.

## References

- Truth anchor: `D5/S3/Observer/ClassicalAnswerTableExclusion.noncontextual_and_local_double_exclusion`
- Dependency: [D5/S3/Observer/WindowCharacter](WindowCharacter.md)
- Dependency: [D5/S3/QuantumBounds/ClassicalFiberBound](../QuantumBounds/ClassicalFiberBound.md)
