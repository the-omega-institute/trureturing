# Actual source prefix law

## Abstract

Actual renewal words and exact raw-past freshness.

**Theorem 1.1 (Finite words of the saved raw execution).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_words`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use exactly ActualRenewalStopping.run, sourceBit, clock and epoch. The effective update holds every terminal state fixed and otherwise calls the same raw sampler with the next bit and raw coin. The finite zero-word recursion uses the first k coins in chronological order and the word applies the closing tick using coin k. Induction on the original raw recursion proves that the first epoch is the initial wait word and that the next epoch is the next gap word starting from the same previous epoch. No transition law or replacement chain is assumed. Wait zero, gap zero, an initially terminal state and stopping within any zero segment remain in scope.

**Theorem 1.2 (Freshness after the exact raw history).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.random_cut_freshness`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.random_cut_freshness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive is an explicit realization interface for deterministic coordinates: for every finite gap tuple, fixed initial wait, fixed coin prefix length l and fixed adjacent block length r, their joint rectangle has the product mass from the initial measure eta, first-wait PMF w, iid-gap PMF f and iid base measure rho. Its statement contains neither a random cut nor an observer trajectory. Deriving this interface from the original source PMFs and a full product realization remains a separate obligation.

The raw past retains the initial wait, exactly K(0) through K(n-1), the actual initial state and every coin strictly before c(n). It excludes K(n) and the next coin. For each finite source tuple a, cut(a)=u+1+sum(K(j)+1) equals the saved clock; a past event is any measurable initial-state and coin-prefix event D(a) on that slice. The coin space can be arbitrary measurable and non-atomic.

The proof partitions over the countable finite source tuples. On each piece it proves the cut equality before applying Primitive at a deterministic offset. Appending K(n)=k multiplies the piece mass by f(k); its following k+1 original coins contribute their finite product measure. Countable additivity and nonnegative series factorization establish the displayed raw-past freshness equation. There is no conditioning by division, so null histories and zero entries are included.

The effective sampler row law and Primitive remain explicit realization interfaces. The actual initialization theorem integrates the finite words. ActualRenewalHistoryLaw consumes these results to derive ordinary-history locality, the ordinary-past row identity and all-length source/state cylinders on the same execution. Real matrix transport and the original source PMF specialization remain separate mathematical obligations, together with occupation, predictable payment, harmonic comparison and full original E4. No auxiliary W termination is used. Common eta, sampler, labels and rows must be retained when the theorem is applied to both targets; only w, f and the source probability law may vary.

**Theorem 1.3 (Integrating the actual first word).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_initial_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_initial_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a countable measurable-singleton state space and arbitrary measurable coin space, assume the common effective sampler maps rho to row A(s) on zero and C(s) on tick. The rows describe the absorbing effective update, including its identity rows at labels. The finite product of k+1 raw coins pushes the k-zero/tick word to zeroRow(A,k,s).bind(C). The induction splits the last original coin by the pinned finite-product measure equivalence and integrates each sampler row with Tonelli. Its base is the empty zero word and a point mass at s.

Integrating the same initial state under eta yields eta.bind(s => zeroRow(A,u,s).bind(C)) for the actual first u-zero/tick word. Primitive supplies its fixed-wait source slice. The countable partition by tau=u then proves that the actual epoch zero has the w-mixture of those rows. This derives initialization from the saved execution; it does not impose a law on Y(0), replace the first wait w by f, remove wait zero or condition on survival. No positivity or stopping premise is used.

zeroRow is only PMF row composition and defines no reference execution. ActualRenewalHistoryLaw supplies the all-prefix source-cylinder induction and ordinary-past consumer. Finite matrix identification with A^k C remains separate. The original f and w normalization and their joint realization have not been supplied by an abstract PMF interface.

**Theorem 1.4 (The actual next row on an exact raw-past event).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_past_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_past_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable exact raw-past event E that fixes the current actual epoch state s, intersect E with K(n)=k and the event that the next actual epoch lies in B. The actual-word identity replaces that last event by the event that the original k+1 next coins drive word(k,s) into B. Random-cut freshness and finite-word integration give P(E) times f(k) times the B-mass of zeroRow(A,k,s).bind(C). This is a conclusion about the saved raw execution; the deterministic state restriction does not assert any transition or cylinder law.

The formula includes every natural n,k, every measurable B, null histories, initially frozen labels, stops during zero updates and zero sampler entries. ActualRenewalHistoryLaw reconstructs each finite ordinary epoch history from its exact raw past, sums this fixed-gap identity over all k and derives both the ordinary-past integral identity and all-length cylinders, including the empty state prefix.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_initial_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_past_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_words`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.random_cut_freshness`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalStopping](ActualRenewalStopping.md)
