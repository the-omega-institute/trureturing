# Feasible original word kernels

## Abstract

Feasible original word kernels

**Definition 1.1 (Original word likelihood with an external message).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.message`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.message` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an original binary edge presentation theta, an n-letter emitted word w and a terminal vector z, message is the original word matrix multiplied by z. Arbitrary nonnegative z are permitted, including zero coordinates. An empty word leaves z unchanged.

**Definition 1.2 (A normalized original edge on feasible rows).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.transition`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an emitted bit x and a nonnegative next message z, the transition from s to t is M(x)(s,t) times z(t), divided by the original message M(x)z at s. A zero denominator gives a zero row under real division. Only rows with positive denominator are used as conditional probability rows.

**Definition 1.3 (Chronological matrix product).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardProduct`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Before each edge, compute its remaining original word likelihood from the same terminal message. Multiply the resulting normalized transition matrices in chronological order. The empty product is the identity. The construction does not replace structural zeros by positive entries.

**Definition 1.4 (Chronological probability of a hidden path).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardPath`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a specified original hidden path, multiply the same suffix-normalized edge transitions along that path. The product has value one at word length zero. Intermediate zero messages remain in the construction, and no condition requires them all to be positive.

**Theorem 1.5 (The product is the original word kernel on its feasible support).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.feasible_word_product`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.feasible_word_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original word, every nonnegative terminal vector z and every state s whose word likelihood is positive, the matrix product from s to t equals the original word entry from s to t times z(t), divided by the word likelihood at s. Its row sums to one and gives zero mass to every endpoint where z is zero. The weighted identity used to obtain this formula holds even when the initial word likelihood is zero. Its induction cancels a denominator only after proving that a zero sum of nonnegative edge-message contributions makes each such contribution zero. Thus no globally invertible diagonal message matrix is needed.

**Definition 1.6 (The actual word and future with a retained initial hidden state).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.startingRecord`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.startingRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At integer time t, startingRecord fixes H(t) to s and fixes the original emitted word followed by a finite future word. All hidden coordinates after the initial state are unobserved. The event belongs to the same original joint law.

**Theorem 1.7 (Actual conditional hidden-path probabilities).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.actual_conditioned_word_path`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.actual_conditioned_word_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be any probability measure satisfying the original marked-cylinder identities of theta. Fix an integer start t, an m-edge hidden path h, its emitted word w, and a following n-letter emitted word v. If startingRecord has positive J likelihood, then the J mass of the specified hidden and emitted m-edge cylinder together with v, divided by the J mass of startingRecord, equals forwardPath with terminal message equal to the original likelihood of v from each endpoint. The original cylinder factorization supplies both masses. The weighted path identity then yields the chronological product without an assumption that intermediate messages or stationary state masses are everywhere positive. The event at m zero is retained, and n zero supplies the constant terminal message one. This statement identifies an actual finite conditional probability under J, rather than postulating a conditional table.

On a positive-weight closed hidden class C, use nativeComponent and component_restriction to retain the original restricted matrices and original conditioned law, with state carrier C. The terminal message for the left comparison is the original A times the future word likelihood. The construction supplies the normalized word-product relation for this message, and permits its zero coordinates. The formulas for visible extra past, the reverse conditional kernels, the center-bit readouts, rectangular minorization and the ordered half-line completion are separate assertions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.actual_conditioned_word_path`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.feasible_word_product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardPath`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.forwardProduct`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.message`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.startingRecord`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels.transition`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening](../OriginalFutureScreening.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw](../PositiveRectangleLaw.md)
