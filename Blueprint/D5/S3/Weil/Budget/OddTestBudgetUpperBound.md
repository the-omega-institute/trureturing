# Odd-Test Budget Upper Bound

## Abstract

A feasible finite odd test bounds the budget of a negative rank-one pencil from above.

**Theorem 1.1 (One odd test requires a bounded budget).**

$$\begin{gathered}\forall n: \mathbb{N},\\{}B: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}),\\{}s, o: \operatorname{Fin}(n) \to \mathbb{C},\\{}R0, R: \mathbb{R},\\{}\langle s, o \rangle \neq 0 \land\\{}0 \le \operatorname{Re}(\langle o, \operatorname{mulVec}(B, o) \rangle) - (R - R0) \cdot \operatorname{normSq}(\langle s, o \rangle) \Rightarrow\\{}R \le R0 + \frac{\operatorname{Re}(\langle o, \operatorname{mulVec}(B, o) \rangle)}{\operatorname{normSq}(\langle s, o \rangle)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/OddTestBudgetUpperBound.odd_test_budget_at_most_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite complex matrix, boundary vector, and selected odd test construct the negative rank-one pencil inequality directly.

A nonzero boundary pairing makes its norm square positive. Dividing the pencil inequality by that quantity gives the displayed test-specific Rayleigh upper bound.

Repository, pinned-library, and public Lean searches found no exact budget theorem; the proof applies the pinned norm-square and positive-division lemmas.

## References

- Truth anchor: `D5/S3/Weil/Budget/OddTestBudgetUpperBound.odd_test_budget_at_most_upper`
