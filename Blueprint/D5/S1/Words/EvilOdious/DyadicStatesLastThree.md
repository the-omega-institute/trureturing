# DyadicStatesLastThree

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Theorem 1.1 (stateZ step 4).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 4) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 4) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 4) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.2 (stateZ step 5).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 5) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 5) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 5) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.3 (stateZ step 6).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 6 (p 6) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 6 (p 6) b) . \operatorname{mulVec} (\operatorname{stateZ} 6 (p 6) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_4`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_5`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicStatesLastThree.stateZ_step_6`
- Dependency: [D5/S1/Words/EvilOdious/DyadicStatesFirstThree](DyadicStatesFirstThree.md)
