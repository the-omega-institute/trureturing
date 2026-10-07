# A complete box for signed Fibonacci carries

## Abstract

A complete box for signed Fibonacci carries

**Definition 1.1 (carryStep).**

$$\forall s \in tuple\left(\mathbb{Z}, \mathbb{Z}\right),\; \forall c \in \mathbb{Z},\; carryStep\left(s, c\right) = tuple\left(snd\left(s\right) + c, fst\left(s\right) + snd\left(s\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/CarryBounds.carryStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One most-significant signed digit updates the two Fibonacci residual coordinates.

**Theorem 1.2 (complete_carry_box).**

$$\forall before \in List\left(\mathbb{Z}\right),\; \forall after \in List\left(\mathbb{Z}\right),\; \left(\left(\forall c \in \mathbb{Z},\; mem\left(c, append\left(before, after\right)\right) \Rightarrow abs\left(real\left(c\right)\right) \le 2\right) \land fst\left(foldl\left(carryStep, tuple\left(0, 0\right), append\left(before, after\right)\right)\right) + 2 \cdot snd\left(foldl\left(carryStep, tuple\left(0, 0\right), append\left(before, after\right)\right)\right) = 1\right) \Rightarrow \left(0 - 4 \le fst\left(foldl\left(carryStep, tuple\left(0, 0\right), before\right)\right) \land \left(fst\left(foldl\left(carryStep, tuple\left(0, 0\right), before\right)\right) \le 4 \land \left(0 - 3 \le snd\left(foldl\left(carryStep, tuple\left(0, 0\right), before\right)\right) \land snd\left(foldl\left(carryStep, tuple\left(0, 0\right), before\right)\right) \le 3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/CarryBounds.complete_carry_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses concern the full signed word, and the conclusion concerns its specified prefix. Expanding and contracting golden-ratio coordinates give simultaneous strip bounds; integrality restricts the prefix carry to this finite box.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/CarryBounds.carryStep`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/CarryBounds.complete_carry_box`
