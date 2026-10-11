# SequenceCoefficients

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Definition 1.1 (r).**

$$\forall (j n : \mathbb{N}) , r j n = ((\operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple} j n) . \operatorname{filter} (\operatorname{fun} (x : \operatorname{Fin} j \to \mathbb{N}) \mapsto \forall (i : \operatorname{Fin} j) , \operatorname{thueMorse} (x i) = \operatorname{false})) . \operatorname{card}$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.r` (`✓ std3`).

*Citation.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Equation (2), page 2: “rⱼ(n) := |{(x₁, x₂, …, xⱼ) : n = ∑₁≤ᵢ≤ⱼ xᵢ and tₓᵢ = 0 for 1 ≤ i ≤ j}|” The carrier Fin j indexes ordered natural coordinates; false encodes zero and true encodes one. Zero is included, and repetitions are allowed.

**Definition 1.2 (s).**

$$\forall (j n : \mathbb{N}) , s j n = ((\operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple} j n) . \operatorname{filter} (\operatorname{fun} (x : \operatorname{Fin} j \to \mathbb{N}) \mapsto \forall (i : \operatorname{Fin} j) , \operatorname{thueMorse} (x i) = \operatorname{true})) . \operatorname{card}$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.s` (`✓ std3`).

*Citation.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Equation (3), page 2: “sⱼ(n) := |{(x₁, x₂, …, xⱼ) : n = ∑₁≤ᵢ≤ⱼ xᵢ and tₓᵢ = 1 for 1 ≤ i ≤ j}|,” The carrier Fin j indexes ordered natural coordinates; false encodes zero and true encodes one. Zero is included, and repetitions are allowed.

**Definition 1.3 (recur).**

$$\forall (q : \operatorname{List} \mathbb{Z}) , (\operatorname{recur} q 0 = 1) \land (\forall (n : \mathbb{N}) , \operatorname{recur} q (n + 1) = \sum_{k \in \operatorname{Finset}.\operatorname{range} q.\operatorname{length}} \operatorname{if} k \le n + 1 \land 2 \mid n + 1 - k \operatorname{then} (\operatorname{List}.\operatorname{getD} q k 0) \cdot \operatorname{recur} q ((n + 1 - k) / 2) \operatorname{else} 0)$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.recur` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.4 (zrecur).**

$$\forall (p : \operatorname{List} \mathbb{Z}) , \forall (n : \mathbb{Z}) , \operatorname{zrecur} p n = \operatorname{if} 0 \le n \operatorname{then} \operatorname{recur} p n.\operatorname{toNat} \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.zrecur` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.5 (p).**

$$p 1 = [1 , 3 , 2 , - 2 , - 3 , - 1] \land p 2 = [1 , 1 , - 2 , - 2 , 1 , 1] \land p 3 = [1 , - 1 , - 2 , 2 , 1 , - 1] \land p 4 = [1 , - 3 , 2 , 2 , - 3 , 1] \land p 5 = [1 , - 5 , 10 , - 10 , 5 , - 1] \land (\forall (j : \mathbb{N}) , (j = 0 \lor 6 \le j) \to p j = [1 , - 6 , 15 , - 20 , 15 , - 6 , 1])$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.p` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.6 (errorTerm).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (n : \mathbb{N}) , \operatorname{errorTerm} \operatorname{sigma} n = (\sum_{j \in \operatorname{Finset}.\operatorname{Icc} 1 5} \operatorname{sigma} ^{j} \cdot (\operatorname{Nat}.\operatorname{choose} 6 j : \mathbb{Z}) \cdot (\operatorname{recur} (p j) n)) + (\operatorname{recur} (p 6) n) - (\operatorname{recur} (p 6) (n - 1))$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.errorTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.7 (r difference).**

$$\forall (n : \mathbb{N}) , 1 \le n \to 64 \cdot ((r 6 n : \mathbb{Z}) - (r 6 (n - 1) : \mathbb{Z})) = ((n + 4) . \operatorname{choose} 4 : \mathbb{Z}) + \operatorname{errorTerm} 1 n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.r_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.8 (s difference).**

$$\forall (n : \mathbb{N}) , 1 \le n \to 64 \cdot ((s 6 n : \mathbb{Z}) - (s 6 (n - 1) : \mathbb{Z})) = ((n + 4) . \operatorname{choose} 4 : \mathbb{Z}) + \operatorname{errorTerm} (- 1) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.s_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.errorTerm`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.p`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.r`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.r_difference`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.recur`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.s`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.s_difference`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.zrecur`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](../Complexity/ThueMorseReducedAbelianOdd.md)
