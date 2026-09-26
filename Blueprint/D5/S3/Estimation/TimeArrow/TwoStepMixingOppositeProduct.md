# Two-Step Mixing Does Not Force Opposite Orthogonality

## Abstract

Two positive doubly stochastic kernels that both reach the uniform kernel in two steps need not have opposite-direction inner product one: on the square {-1, 1}^2 the kernel (1 + x_1 y_2 / 2)/4 and its transpose give 5/4.

**Definition 1.1 (Positive doubly stochastic kernel).**

$$\operatorname{P}(x, y)>0, \sum_{y} \operatorname{P}(x, y)=1, \sum_{x} \operatorname{P}(x, y)=1$$

*Formalization.* `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.PositiveDoublyStochastic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A kernel on a finite state space is positive and doubly stochastic when every entry is positive and every row and every column sums to one.

**Definition 1.2 (Two-step mixing).**

$$\sum_{y} \operatorname{P}(x, y) \operatorname{P}(y, z)= \frac{1}{\lvert X \rvert}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.MixesInTwoSteps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel mixes in two steps when its square is the uniform kernel Pi(x, z) = 1/|X|.

**Definition 1.3 (Opposite-direction inner product).**

$$\operatorname{I}(P, Q)= \frac{1}{\lvert X \rvert^{2}} \sum_{x,y} \lvert X \rvert \operatorname{P}(x, y) \lvert X \rvert \operatorname{Q}(y, x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.oppositeInnerProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-step inner product of the forward product |X| P(x_0, x_1) of P and the backward product |X| Q(x_1, x_0) of Q under the uniform law on pairs of states.

**Definition 1.4 (Kernel pairs).**

$$(X, P, Q)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.FiniteKernelPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite state space X together with two kernels P and Q on it.

**Definition 1.5 (Two-step mixing forces orthogonality).**

$$\forall (X, P, Q), \operatorname{PDS}(P), \operatorname{PDS}(Q), P^{2}=Q^{2}=\pi \Rightarrow \operatorname{I}(P, Q)=1$$

*Formalization.* `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asserts that for every finite state space and all positive doubly stochastic kernels P and Q whose squares are the uniform kernel, the opposite-direction inner product is one.

**Theorem 1.6 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the square {-1, 1}^2 take P(x, y) = (1 + r x_1 y_2)/4 with r = 1/2 and Q the transpose of P. All entries lie between 1/8 and 3/8, every row and column sums to one because y_2 and x_1 average to zero, and the square of P is uniform because the sum of y_1 y_2 over the square vanishes; the same holds for Q. Since Q(y, x) = P(x, y), the inner product is the average of (1 + r x_1 y_2)^2, which is 1 + r^2 = 5/4. For the kernels of the parity family the same inner product equals one; the example shows that this uses their common parity factor and not two-step mixing alone.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.FiniteKernelPair`
- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.MixesInTwoSteps`
- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.PositiveDoublyStochastic`
- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.claim`
- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.oppositeInnerProduct`
- Truth anchor: `D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.result`
