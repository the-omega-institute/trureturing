# Verdict Column Separation

## Abstract

Extending an implementation population can separate verdict columns that previously agreed.

**Theorem 1.1 (A new implementation can split two previously identical verdict columns).**

$$\forall I, T, V, r: I \to T \to V, t1, t2, (\operatorname{Nontrivial}(V) \land t1 \neq t2 \land \forall i, r(i, t1) = r(i, t2)) \Rightarrow \exists \widehat{r}, \widehat{r}: \operatorname{Option}(I) \to T \to V, (\forall i, t, \widehat{r}(\operatorname{some}(i), t) = r(i, t)) \land \widehat{r}(\operatorname{none}, t1) \neq \widehat{r}(\operatorname{none}, t2).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/VerdictColumnSeparation.verdict_columns_can_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r pair an arbitrary implementation population with an arbitrary test space and take values in a verdict type containing at least two distinct values. Suppose two distinct tests have identical verdict columns on every current implementation. After adjoining one implementation, r extends without changing any old verdict, while the new implementation assigns different verdicts to the two tests.

The construction uses the option type for the enlarged population. Existing implementations retain their original verdict rows; the new point receives one of two distinct verdicts according to whether the test is the first distinguished test.

Pinned Mathlib was searched for equal or identical columns, column splitting, population extension, and adjoining a point; no exact theorem was found. Function extension and option-recursion infrastructure were found, and the Lean proof gives the direct option extension.

This is an honest partial closure of clause (c) only. The double extensional quotient claim, the minimization characterization, and the engineering-history discussion carried by the source atom remain unresolved.

## References

- Truth anchor: `D5/S0/Naming/VerdictColumnSeparation.verdict_columns_can_split`
