# DyadicStatesFirstThree

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Definition 1.1 (state).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (n : \mathbb{N}) , \operatorname{state} d q n = \operatorname{fun} (i : \operatorname{Fin} d) \mapsto \operatorname{recur} q (n - (i : \mathbb{N}))$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.state` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.2 (recur pos).**

$$\forall (q : \operatorname{List} \mathbb{Z}) , \forall (N : \mathbb{N}) , (0 < N) \to \operatorname{recur} q N = \sum_{k \in \operatorname{Finset}.\operatorname{range} q.\operatorname{length}} \operatorname{if} k \le N \land 2 \mid N - k \operatorname{then} (\operatorname{List}.\operatorname{getD} q k 0) \cdot \operatorname{recur} q ((N - k) / 2) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.recur_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.3 (stateZ).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (n : \mathbb{N}) , \operatorname{stateZ} d q n = \operatorname{fun} (i : \operatorname{Fin} d) \mapsto \operatorname{zrecur} q ((n : \mathbb{Z}) - ((i : \mathbb{N}) : \mathbb{Z}))$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.4 (stateZ eq state).**

$$\forall (d : \mathbb{N}) , (d \le 6) \to \forall (q : \operatorname{List} \mathbb{Z}) , \forall (n : \mathbb{N}) , (6 \le n) \to \operatorname{stateZ} d q n = \operatorname{state} d q n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_eq_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.5 (stateZ step 1).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 1) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 1) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 1) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.6 (stateZ step 2).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 2) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 2) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 2) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.7 (stateZ step 3).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 3) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 3) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 3) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.recur_pos`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.state`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_eq_state`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_1`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_2`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesFirstThree.stateZ_step_3`
- Dependency: [D5/S1/Words/EvilOdious/MatrixBounds](MatrixBounds.md)
