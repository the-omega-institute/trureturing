# Chain Response Selector Gap

## Abstract

Chain responses stay non-scalar at every length while their selector loss vanishes.

Eliminating the hidden chain leaves a two by two effective matrix that is diagonal with entries k minus b times eta and k. The quantity eta is the squared endpoint of the first inverse column divided by the common mass coefficient, and the endpoint is the reciprocal of an integer determinant obeying a three term recurrence. So the far boundary of the chain is visible in the principal part of the response, not merely in a remainder.

The selector objective at price one half is the log determinant minus half the trace. Its loss against the scalar matrix with entry two is the quantity studied here. All lengths, indices and matrix entries are as in the companion module, and the price one half is a chosen specialisation rather than a consequence of the surrounding theory; it lies strictly inside the window that the integer selector statement requires at k equal to two.

**Definition 1.1 (The loss at the chosen price).**

$$\forall n \in \mathbb{N}, \operatorname{L}\left(n\right) = -\operatorname{log}\left(1 - \frac{\operatorname{eta}\left(n\right)}{2}\right) - \frac{\operatorname{eta}\left(n\right)}{2}$$

*Formalization.* `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chainResponseLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expanding the objective at the effective matrix against its value at the scalar matrix leaves exactly this scalar expression in eta. Both matrices share the second diagonal entry, so only the first contributes.

**Lemma 1.2 (No length gives a scalar response).**

$$\forall n \in \mathbb{N}, \forall c \in \mathbb{R}, \operatorname{effective}\left(n, 2, 1\right) \neq \operatorname{diagonal}\left(c, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.effective_ne_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint is the reciprocal of a positive integer determinant and the mass coefficient is positive, so eta is positive at every length. The two diagonal entries of the effective matrix therefore differ, while a scalar diagonal matrix has them equal. This holds for every scalar, not only two.

**Lemma 1.3 (Two sided bound on the loss).**

$$\forall n \in \mathbb{N}, 0 \le \operatorname{L}\left(n\right) \land \operatorname{L}\left(n\right) \le \frac{\operatorname{eta}\left(n\right)^{2}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_loss_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y between zero and one half the remainder of the logarithm past its linear term is non-negative and at most twice y squared. The lower side applies the logarithm bound to one minus y; the upper side applies it to the reciprocal and then uses that the reciprocal of one minus y is at most two. Substituting half of eta gives the stated pair.

**Lemma 1.4 (The loss falls geometrically).**

$$\forall n \in \mathbb{N}, \operatorname{L}\left(n\right) \le \frac{1}{2} \cdot \frac{1}{81}^{n + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_loss_le_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass coefficient is at least one, so eta is at most the squared endpoint, which the companion module bounds by the reciprocal of nine to the length. Squaring and halving gives the reciprocal of eighty one to the length. This estimate is where the integer recurrence enters the conclusion.

**Theorem 1.5 (No uniform gap survives elimination).**

$$\forall e \in \mathbb{R}, 0 < e \implies \exists n \in \mathbb{N}, \operatorname{effective}\left(n, 2, 1\right) \neq \operatorname{diagonal}\left(2, 2\right) \land 0 \le \operatorname{L}\left(n\right) \land \operatorname{L}\left(n\right) < e$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_selector_gap_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a positive bound, choose a length at which the geometric estimate falls below it. The effective matrix at that length is still not scalar. So the positive gap that the integer statement gives for integer matrices does not transfer to the real responses obtained by elimination. The integer statement itself is untouched.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chainResponseLoss`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_loss_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_loss_le_geometric`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.chain_response_selector_gap_refuted`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.effective_ne_scalar`
- Dependency: [D5/S3/Arith/GoldenResource/ChainSchurResponse](ChainSchurResponse.md)
