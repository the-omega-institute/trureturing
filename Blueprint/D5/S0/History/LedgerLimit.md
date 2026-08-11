# The Pointwise Ledger Limit

## Abstract

A finitely revised ledger has a unique pointwise terminal grading.

**Theorem 1.1 (Finite revisions determine a unique terminal grading).**

$$\operatorname{FiniteRevisions}(\sigma) \Rightarrow \exists! \sigma_{\infty}, \forall s, \exists N \geq e(s), \forall t \geq N, \sigma_{t}(s) = \sigma_{\infty}(s).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/LedgerLimit.ledger_limit_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A ledger history contains every eventually enrolled statement, its enrollment time, and its grade at every natural-number clock tick. The statements visible by time t are exactly those whose enrollment time is at most t, so the visible statement sets are append-only by construction. A revision time for a statement is a tick at or after enrollment where the next grade differs from the current grade.

Assume each statement has only finitely many revision times. The complement of that finite set is eventually universal on the natural clock, so there is a cutoff after which no adjacent pair of grades differs. Induction from the cutoff makes the entire tail constant. Two proposed terminal grades agree by evaluating both constant tails at the maximum of their cutoffs. Pointwise choice therefore produces one terminal grading on all statements, and pointwise uniqueness plus function extensionality proves that this grading is unique.

The primary declaration retains the source model's countable statement space and finite partially ordered grade space. The stabilization lemma is proved at the stronger type-generic scope because neither finiteness nor the order is needed once finite revision times are assumed. The word limit means eventual equality in this discrete grading model; no convergence claim for an arbitrary topology is made. The construction and proof are elementary and assembled in this repository, so the theorem is recorded as repository-derived.

**Theorem 1.2 (Permanent alternation has no terminal grade).**

$$\neg\exists g,N, \forall t \geq N, \operatorname{alternate}(t) = g.$$

*Proof.* Machine-checked in Lean as `D5/S0/History/LedgerLimit.alternating_grade_has_no_terminal_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-grade counterexample starts at false and negates its grade at every successor tick. Any claimed terminal cutoff would force the grades at that cutoff and its successor to equal the same terminal value, while the defining recursion proves those adjacent grades are unequal. The same argument, composed with the stabilization theorem, proves that the counterexample has infinitely many revision times. This discharges the source theorem's necessity clause rather than silently treating finite revision as cosmetic.

## References

- Truth anchor: `D5/S0/History/LedgerLimit.alternating_grade_has_no_terminal_value`
- Truth anchor: `D5/S0/History/LedgerLimit.ledger_limit_exists_unique`
