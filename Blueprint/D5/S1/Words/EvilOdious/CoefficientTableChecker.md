# CoefficientTableChecker

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Definition 1.1 (tableValue).**

$$\forall (\operatorname{table} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})) (\operatorname{index} : \mathbb{N}) , \operatorname{tableValue} \operatorname{table} \operatorname{index} = \operatorname{match} \operatorname{table} \operatorname{with} | \operatorname{BinaryTree}.\operatorname{nil} \mapsto 0 | \operatorname{BinaryTree}.\operatorname{node} (\operatorname{key} , \operatorname{value}) \operatorname{left} \operatorname{right} \mapsto \operatorname{if} \operatorname{index} = \operatorname{key} \operatorname{then} \operatorname{value} \operatorname{else} \operatorname{if} \operatorname{index} < \operatorname{key} \operatorname{then} \operatorname{tableValue} \operatorname{left} \operatorname{index} \operatorname{else} \operatorname{tableValue} \operatorname{right} \operatorname{index}$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.2 (tableStep).**

$$\forall (q : \operatorname{List} \mathbb{Z}) , \forall (v : \mathbb{N} \to \mathbb{Z}) , \forall (n : \mathbb{N}) , \operatorname{tableStep} q v n = \operatorname{if} n = 0 \operatorname{then} 1 \operatorname{else} \sum_{k \in \operatorname{Finset}.\operatorname{range} q.\operatorname{length}} \operatorname{if} k \le n \land 2 \mid n - k \operatorname{then} (\operatorname{List}.\operatorname{getD} q k 0) \cdot v ((n - k) / 2) \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.3 (tableCheck).**

$$\forall (q : \operatorname{List} \mathbb{Z}) (\operatorname{table} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})) (\operatorname{bound} : \mathbb{N}) , \operatorname{tableCheck} q \operatorname{table} \operatorname{bound} = (\operatorname{List}.\operatorname{range} \operatorname{bound}) . \operatorname{all} (\operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{BEq}.\operatorname{beq} (\operatorname{tableValue} \operatorname{table} n) (\operatorname{tableStep} q (\operatorname{tableValue} \operatorname{table}) n))$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableCheck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.4 (tableCheck sound).**

$$\forall (q : \operatorname{List} \mathbb{Z}) , \forall (\operatorname{table} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})) , \forall (\operatorname{bound} : \mathbb{N}) , (\operatorname{tableCheck} q \operatorname{table} \operatorname{bound} = \operatorname{true}) \to \forall n , n < \operatorname{bound} \to \operatorname{recur} q n = \operatorname{tableValue} \operatorname{table} n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableCheck_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.5 (table1).**

$$\operatorname{table1} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 1. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.6 (table1 checked).**

$$\operatorname{tableCheck} (p 1) \operatorname{table1} 4096 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.7 (table1 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 1) n = (\operatorname{tableValue} \operatorname{table1}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.8 (table2).**

$$\operatorname{table2} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 2. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.9 (table2 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 2) n = (\operatorname{tableValue} \operatorname{table2}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table2_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.10 (table3).**

$$\operatorname{table3} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 3. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.11 (table3 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 3) n = (\operatorname{tableValue} \operatorname{table3}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table3_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.12 (table4).**

$$\operatorname{table4} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 4. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.13 (table4 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 4) n = (\operatorname{tableValue} \operatorname{table4}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table4_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.14 (table5).**

$$\operatorname{table5} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 5. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.15 (table5 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 5) n = (\operatorname{tableValue} \operatorname{table5}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table5_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.16 (table6).**

$$\operatorname{table6} : \operatorname{BinaryTree} (\mathbb{N} \times \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.table6` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The balanced binary tree stores 4096 exact integer entries for the polynomial system p 6. Its entries are checked against the recurrence by tableCheck_sound.

**Theorem 1.17 (table6 sound).**

$$\forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{recur} (p 6) n = (\operatorname{tableValue} \operatorname{table6}) n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.table6_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1_checked`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table1_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table2`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table2_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table3`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table3_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table4`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table4_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table5`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table5_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table6`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.table6_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableCheck`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableCheck_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableStep`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableValue`
- Dependency: [D5/S1/Words/EvilOdious/SequenceCoefficients](SequenceCoefficients.md)
