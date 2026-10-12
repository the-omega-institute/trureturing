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

**Definition 1.18 (tableH).**

$$\forall (j n : \mathbb{N}) , \operatorname{tableH} j n = \operatorname{if} j = 1 \operatorname{then} \operatorname{tableValue} \operatorname{table1} n \operatorname{else} \operatorname{if} j = 2 \operatorname{then} \operatorname{tableValue} \operatorname{table2} n \operatorname{else} \operatorname{if} j = 3 \operatorname{then} \operatorname{tableValue} \operatorname{table3} n \operatorname{else} \operatorname{if} j = 4 \operatorname{then} \operatorname{tableValue} \operatorname{table4} n \operatorname{else} \operatorname{tableValue} \operatorname{table5} n$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.19 (tableError).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (n : \mathbb{N}) , \operatorname{tableError} \operatorname{sigma} n = (\sum_{j \in \operatorname{Finset}.\operatorname{Icc} 1 5} \operatorname{sigma} ^{j} \cdot (\operatorname{Nat}.\operatorname{choose} 6 j : \mathbb{Z}) \cdot \operatorname{tableH} j n) + (\operatorname{tableValue} \operatorname{table6}) n - (\operatorname{tableValue} \operatorname{table6}) (n - 1)$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableError` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.20 (seedH).**

$$\forall (j n : \mathbb{N}) , \operatorname{seedH} j n = (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto (\operatorname{tableH} j (n - i)) . \operatorname{natAbs})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.21 (seedC).**

$$\forall (n : \mathbb{N}) , \operatorname{seedC} n = (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{tableValue} \operatorname{table6}) (n - i)) . \operatorname{natAbs})$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.22 (prefixB).**

$$\forall (n : \mathbb{N}) , \operatorname{prefixB} n = (\sum_{j \in \operatorname{Finset}.\operatorname{Icc} 1 5} \operatorname{Nat}.\operatorname{choose} 6 j \cdot \operatorname{seedH} j n) + 4 \cdot \operatorname{seedC} n$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.23 (tableH sound).**

$$\forall (j n : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (n < 4096) \to (\operatorname{recur} (p j) n) = \operatorname{tableH} j n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableH_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.24 (tableError sound).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{errorTerm} \operatorname{sigma} n = \operatorname{tableError} \operatorname{sigma} n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableError_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.25 (prefixChunk).**

$$\forall (\operatorname{base} \operatorname{len} : \mathbb{N}) , \operatorname{prefixChunk} \operatorname{base} \operatorname{len} = (\operatorname{List}.\operatorname{range} \operatorname{len}) . \operatorname{all} (\operatorname{fun} k \mapsto \operatorname{decide} (24 \cdot \operatorname{prefixB} (\operatorname{base} + k) < (\operatorname{base} + k) ^{4}))$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.26 (initialChunk).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (\operatorname{lower} \operatorname{base} \operatorname{len} : \mathbb{N}) , \operatorname{initialChunk} \operatorname{sigma} \operatorname{lower} \operatorname{base} \operatorname{len} = (\operatorname{List}.\operatorname{range} \operatorname{len}) . \operatorname{all} (\operatorname{fun} k \mapsto \operatorname{decide} (\operatorname{lower} \le \operatorname{base} + k \to 0 < ((\operatorname{Nat}.\operatorname{descFactorial} (\operatorname{base} + k + 4) 4 / 24 : \mathbb{N}) : \mathbb{Z}) + \operatorname{tableError} \operatorname{sigma} (\operatorname{base} + k)))$$

*Formalization.* `D5/S1/Words/EvilOdious/CoefficientTableChecker.initialChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.27 (prefixcertificate 0).**

$$\operatorname{prefixChunk} 2048 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixcertificate_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.28 (prefixcertificate checked).**

$$\forall (\operatorname{block} : \operatorname{Fin} 64) , \operatorname{prefixChunk} (2048 + 32 \cdot \operatorname{block}.\operatorname{val}) 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixcertificate_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.29 (c prefix).**

$$\forall (\operatorname{p0} : \mathbb{N}) , (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to \forall (w : \operatorname{List} \operatorname{Bool}) , ((\operatorname{recur} (p 6) (\operatorname{appendValue} \operatorname{p0} w))) . \operatorname{natAbs} \le 2 \cdot 16 ^{w.\operatorname{length}} \cdot \operatorname{seedC} \operatorname{p0} \land ((\operatorname{recur} (p 6) (\operatorname{appendValue} \operatorname{p0} w - 1))) . \operatorname{natAbs} \le 2 \cdot 16 ^{w.\operatorname{length}} \cdot \operatorname{seedC} \operatorname{p0}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.c_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.30 (seedH exact).**

$$\forall (j \operatorname{p0} : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (\operatorname{p0} < 4096) \to \operatorname{seedH} j \operatorname{p0} = (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p j) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedH_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.31 (seedC exact).**

$$\forall (\operatorname{p0} : \mathbb{N}) , (\operatorname{p0} < 4096) \to \operatorname{seedC} \operatorname{p0} = (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedC_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.32 (h dyadic).**

$$\forall (j \operatorname{p0} m \operatorname{low} : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to (\operatorname{low} < 2 ^{m}) \to ((\operatorname{recur} (p j) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low}))) . \operatorname{natAbs} \le 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p j) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.h_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.33 (c dyadic).**

$$\forall (\operatorname{p0} m \operatorname{low} : \mathbb{N}) , (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to (\operatorname{low} < 2 ^{m}) \to ((\operatorname{recur} (p 6) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low}))) . \operatorname{natAbs} \le 2 \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs}) \land ((\operatorname{recur} (p 6) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low} - 1))) . \operatorname{natAbs} \le 2 \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/CoefficientTableChecker.c_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.c_dyadic`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.c_prefix`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.h_dyadic`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.initialChunk`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixB`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixChunk`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixcertificate_0`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.prefixcertificate_checked`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedC`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedC_exact`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedH`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.seedH_exact`
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
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableError`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableError_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableH`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableH_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableStep`
- Truth anchor: `D5/S1/Words/EvilOdious/CoefficientTableChecker.tableValue`
- Dependency: [D5/S1/Words/EvilOdious/SequenceCoefficients](SequenceCoefficients.md)
