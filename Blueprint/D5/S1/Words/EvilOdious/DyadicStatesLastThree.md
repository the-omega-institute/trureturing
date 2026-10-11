# DyadicStatesLastThree

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Theorem 1.1 (appendValue decompose).**

$$\forall (\operatorname{p0} : \mathbb{N}) , \forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} \operatorname{p0} w = \operatorname{p0} \cdot 2 ^{w.\operatorname{length}} + \operatorname{appendValue} 0 w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.appendValue_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.2 (stateZ step 4).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 4) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 4) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 4) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.3 (stateZ step 5).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 5) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 5) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 5) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.4 (stateZ step 6).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 6 (p 6) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 6 (p 6) b) . \operatorname{mulVec} (\operatorname{stateZ} 6 (p 6) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.5 (lowWord bound).**

$$\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} 0 w < 2 ^{w.\operatorname{length}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.lowWord_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.6 (word for low).**

$$\forall (m \operatorname{low} : \mathbb{N}) , \operatorname{low} < 2 ^{m} \to \exists (w : \operatorname{List} \operatorname{Bool}) , w.\operatorname{length} = m \land \operatorname{appendValue} 0 w = \operatorname{low}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.word_for_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Induction on the length constructs a binary word for every allowed low part, including leading zero bits.

**Theorem 1.7 (state dyadic bound).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , (\forall (n : \mathbb{N}) (b : \operatorname{Bool}) , \operatorname{stateZ} d q (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (M b) . \operatorname{mulVec} (\operatorname{stateZ} d q n)) \to \forall (K : \mathbb{N}) , (\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{matrixBound} (\operatorname{wordMatrix} M w) (K \cdot 16 ^{w.\operatorname{length}})) \to \forall (p m \operatorname{low} : \mathbb{N}) , \operatorname{low} < 2 ^{m} \to \operatorname{vectorBound} (\operatorname{stateZ} d q (p \cdot 2 ^{m} + \operatorname{low})) (K \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} d) . \operatorname{sup} (\operatorname{fun} (i : \mathbb{N}) \mapsto (\operatorname{zrecur} q ((p : \mathbb{Z}) - (i : \mathbb{Z}))) . \operatorname{natAbs}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.state_dyadic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Binary-word construction and the matrix estimate bound every dyadic extension by the largest seed coordinate.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.appendValue_decompose`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.lowWord_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_4`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_5`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_6`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.state_dyadic_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.word_for_low`
- Dependency: [D5/S1/Words/EvilOdious/DyadicStatesFirstThree](DyadicStatesFirstThree.md)
