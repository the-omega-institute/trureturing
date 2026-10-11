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

**Definition 1.9 (matrixBound).**

$$\forall (d : \mathbb{N}) (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) (B : \mathbb{N}) , \operatorname{matrixBound} A B \iff \forall (i : \operatorname{Fin} d) , \sum_{j : \operatorname{Fin} d} (A i j) . \operatorname{natAbs} \le B$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.matrixBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.10 (vectorBound).**

$$\forall (d : \mathbb{N}) (v : \operatorname{Fin} d \to \mathbb{Z}) (B : \mathbb{N}) , \operatorname{vectorBound} v B \iff \forall (i : \operatorname{Fin} d) , (v i) . \operatorname{natAbs} \le B$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.vectorBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.11 (matrix apply bound).**

$$\forall (d : \mathbb{N}) , \forall (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , \forall (v : \operatorname{Fin} d \to \mathbb{Z}) , \forall (B K : \mathbb{N}) , (\operatorname{matrixBound} A B) \to (\operatorname{vectorBound} v K) \to \operatorname{vectorBound} (A.\operatorname{mulVec} v) (B \cdot K)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.matrix_apply_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.12 (pz).**

$$\forall (p : \operatorname{List} \mathbb{Z}) , \forall (k : \mathbb{Z}) , \operatorname{pz} p k = \operatorname{if} 0 \le k \operatorname{then} (\operatorname{List}.\operatorname{getD} p k.\operatorname{toNat} 0) \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.pz` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.13 (stateMatrix).**

$$\forall (d : \mathbb{N}) (p : \operatorname{List} \mathbb{Z}) (b : \operatorname{Bool}) , \operatorname{stateMatrix} d p b = \operatorname{fun} (i a : \operatorname{Fin} d) \mapsto \operatorname{pz} p (2 \cdot (a : \mathbb{Z}) + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0) - (i : \mathbb{Z}))$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.stateMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.14 (words).**

$$\forall (n : \mathbb{N}) , \operatorname{words} n = (\operatorname{List}.\operatorname{replicate} n [\operatorname{false} , \operatorname{true}]) . \operatorname{sections}$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.15 (wordMatrix).**

$$\forall (d : \mathbb{N}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) (w : \operatorname{List} \operatorname{Bool}) , \operatorname{wordMatrix} M w = (w.\operatorname{map} M) . \operatorname{prod}$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.wordMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.16 (h matrix bound).**

$$\operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 1) \operatorname{false}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 1) \operatorname{true}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 2) \operatorname{false}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 2) \operatorname{true}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 3) \operatorname{false}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 3) \operatorname{true}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 4) \operatorname{false}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 4) \operatorname{true}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 5) \operatorname{false}) 16 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 5) \operatorname{true}) 16$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.h_matrix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.17 (wordsCheck).**

$$\forall (\operatorname{len} \operatorname{bound} : \mathbb{N}) , \operatorname{wordsCheck} \operatorname{len} \operatorname{bound} = (\operatorname{words} \operatorname{len}) . \operatorname{all} (\operatorname{fun} w \mapsto \operatorname{decide} (\operatorname{matrixBound} (\operatorname{wordMatrix} (\operatorname{stateMatrix} 6 (p 6)) w) \operatorname{bound}))$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.wordsCheck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.18 (c five checked).**

$$\operatorname{wordsCheck} 5 1019200 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.c_five_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.19 (c word bound).**

$$\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{matrixBound} (\operatorname{wordMatrix} (\operatorname{stateMatrix} 6 (p 6)) w) (2 \cdot 16 ^{w.\operatorname{length}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.c_word_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.20 (state).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (n : \mathbb{N}) , \operatorname{state} d q n = \operatorname{fun} (i : \operatorname{Fin} d) \mapsto \operatorname{recur} q (n - (i : \mathbb{N}))$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.state` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.21 (recur pos).**

$$\forall (q : \operatorname{List} \mathbb{Z}) , \forall (N : \mathbb{N}) , (0 < N) \to \operatorname{recur} q N = \sum_{k \in \operatorname{Finset}.\operatorname{range} q.\operatorname{length}} \operatorname{if} k \le N \land 2 \mid N - k \operatorname{then} (\operatorname{List}.\operatorname{getD} q k 0) \cdot \operatorname{recur} q ((N - k) / 2) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.recur_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.22 (stateZ).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (n : \mathbb{N}) , \operatorname{stateZ} d q n = \operatorname{fun} (i : \operatorname{Fin} d) \mapsto \operatorname{zrecur} q ((n : \mathbb{Z}) - ((i : \mathbb{N}) : \mathbb{Z}))$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.23 (stateZ eq state).**

$$\forall (d : \mathbb{N}) , (d \le 6) \to \forall (q : \operatorname{List} \mathbb{Z}) , \forall (n : \mathbb{N}) , (6 \le n) \to \operatorname{stateZ} d q n = \operatorname{state} d q n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_eq_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.24 (stateZ step 1).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 1) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 1) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 1) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.25 (stateZ step 2).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 2) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 2) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 2) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.26 (stateZ step 3).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 3) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 3) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 3) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.27 (appendValue).**

$$\forall (q : \mathbb{N}) (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} q w = \operatorname{Nat}.\operatorname{ofDigits} 2 (\operatorname{List}.\operatorname{append} (\operatorname{List}.\operatorname{map} \operatorname{Bool}.\operatorname{toNat} w) [q])$$

*Formalization.* `D5/S1/Words/EvilOdious/SequenceCoefficients.appendValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.28 (state word).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , (\forall (n : \mathbb{N}) (b : \operatorname{Bool}) , \operatorname{stateZ} d q (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (M b) . \operatorname{mulVec} (\operatorname{stateZ} d q n)) \to \forall (p : \mathbb{N}) (w : \operatorname{List} \operatorname{Bool}) , \operatorname{stateZ} d q (\operatorname{appendValue} p w) = (\operatorname{wordMatrix} M w) . \operatorname{mulVec} (\operatorname{stateZ} d q p)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.state_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Induction on the binary word composes each one-bit state transition into its matrix product.

**Theorem 1.29 (vector prefix bound).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , (\forall (n : \mathbb{N}) (b : \operatorname{Bool}) , \operatorname{stateZ} d q (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (M b) . \operatorname{mulVec} (\operatorname{stateZ} d q n)) \to \forall (K : \mathbb{N}) , (\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{matrixBound} (\operatorname{wordMatrix} M w) (K \cdot 16 ^{w.\operatorname{length}})) \to \forall (p : \mathbb{N}) (w : \operatorname{List} \operatorname{Bool}) (B : \mathbb{N}) , \operatorname{vectorBound} (\operatorname{stateZ} d q p) B \to \operatorname{vectorBound} (\operatorname{stateZ} d q (\operatorname{appendValue} p w)) (K \cdot 16 ^{w.\operatorname{length}} \cdot B)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.vector_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The matrix-word bound transfers the seed bound to every word extension.

**Theorem 1.30 (appendValue decompose).**

$$\forall (\operatorname{p0} : \mathbb{N}) , \forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} \operatorname{p0} w = \operatorname{p0} \cdot 2 ^{w.\operatorname{length}} + \operatorname{appendValue} 0 w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.appendValue_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.31 (stateZ step 4).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 4) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 4) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 4) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.32 (stateZ step 5).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 5 (p 5) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 5 (p 5) b) . \operatorname{mulVec} (\operatorname{stateZ} 5 (p 5) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.33 (stateZ step 6).**

$$\forall (n : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \operatorname{stateZ} 6 (p 6) (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (\operatorname{stateMatrix} 6 (p 6) b) . \operatorname{mulVec} (\operatorname{stateZ} 6 (p 6) n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.34 (lowWord bound).**

$$\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} 0 w < 2 ^{w.\operatorname{length}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.lowWord_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.35 (word for low).**

$$\forall (m \operatorname{low} : \mathbb{N}) , \operatorname{low} < 2 ^{m} \to \exists (w : \operatorname{List} \operatorname{Bool}) , w.\operatorname{length} = m \land \operatorname{appendValue} 0 w = \operatorname{low}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.word_for_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Induction on the length constructs a binary word for every allowed low part, including leading zero bits.

**Theorem 1.36 (state dyadic bound).**

$$\forall (d : \mathbb{N}) (q : \operatorname{List} \mathbb{Z}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , (\forall (n : \mathbb{N}) (b : \operatorname{Bool}) , \operatorname{stateZ} d q (2 \cdot n + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)) = (M b) . \operatorname{mulVec} (\operatorname{stateZ} d q n)) \to \forall (K : \mathbb{N}) , (\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{matrixBound} (\operatorname{wordMatrix} M w) (K \cdot 16 ^{w.\operatorname{length}})) \to \forall (p m \operatorname{low} : \mathbb{N}) , \operatorname{low} < 2 ^{m} \to \operatorname{vectorBound} (\operatorname{stateZ} d q (p \cdot 2 ^{m} + \operatorname{low})) (K \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} d) . \operatorname{sup} (\operatorname{fun} (i : \mathbb{N}) \mapsto (\operatorname{zrecur} q ((p : \mathbb{Z}) - (i : \mathbb{Z}))) . \operatorname{natAbs}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/SequenceCoefficients.state_dyadic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Binary-word construction and the matrix estimate bound every dyadic extension by the largest seed coordinate.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.appendValue`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.appendValue_decompose`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.c_five_checked`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.c_word_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.errorTerm`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.h_matrix_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.lowWord_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.matrixBound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.matrix_apply_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.p`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.pz`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.r`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.r_difference`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.recur`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.recur_pos`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.s`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.s_difference`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.state`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateMatrix`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_eq_state`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_1`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_2`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_3`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_4`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_5`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.stateZ_step_6`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.state_dyadic_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.state_word`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.vectorBound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.vector_prefix_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.wordMatrix`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.word_for_low`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.words`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.wordsCheck`
- Truth anchor: `D5/S1/Words/EvilOdious/SequenceCoefficients.zrecur`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](../Complexity/ThueMorseReducedAbelianOdd.md)
