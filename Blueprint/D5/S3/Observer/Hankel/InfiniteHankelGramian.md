# InfiniteHankelGramian

## Abstract

Actual half-line observation and reachability construct an infinite l2 Hankel operator with the correct Markov blocks.

**Definition 1.1 (Signal).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.Signal`

*Formalization.* `D5/S3/Observer/Hankel/InfiniteHankelGramian.Signal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Square-summable Euclidean-valued signals on the entire nonnegative time axis.

**Definition 1.2 (future Output).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput`

*Formalization.* `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs every genuine future output and proves its l2 membership. Finite-dimensional continuity supplies the bounded operator.

**Theorem 1.3 (future Output apply).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kth coordinate is exactly C times A to the kth power applied to the original state.

**Theorem 1.4 (future Output norm sq).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies the norm of the actual infinite output sequence with the constructed Gramian quadratic form.

**Theorem 1.5 (future Output inner).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polarization proves the complete Gram bilinear identity, including all cross terms.

**Theorem 1.6 (future Output gramian).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_gramian`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_gramian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves that the infinite observation operator adjoint times itself is exactly the matrix Gramian on Euclidean coordinates.

**Definition 1.7 (past Input).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput`

*Formalization.* `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjoint of the actual dual future-output operator is the past-to-state map.

**Definition 1.8 (hankel).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel`

*Formalization.* `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual bounded infinite past-to-future operator, as observation after reachability.

**Theorem 1.9 (past Input gramian).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_gramian`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_gramian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies reachability times its adjoint with the actual control Gramian.

**Theorem 1.10 (past Input single).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_single`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One input of age j reaches the genuine state A to the jth power times B applied to that input.

**Theorem 1.11 (hankel single).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_single`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves every infinite Hankel block is C times A to the power i+j times B. Finite and infinite objects are not conflated.

**Theorem 1.12 (hankel has Sum).**

Lean statement: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All l2 inputs are norm limits of their single-input sums; the actual bounded operator transports those sums.

## References

- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.Signal`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_apply`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_gramian`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_inner`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.futureOutput_norm_sq`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_hasSum`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.hankel_single`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_gramian`
- Truth anchor: `D5/S3/Observer/Hankel/InfiniteHankelGramian.pastInput_single`
- Dependency: [D5/S3/Observer/Hankel/ExactGramianSeries](ExactGramianSeries.md)
