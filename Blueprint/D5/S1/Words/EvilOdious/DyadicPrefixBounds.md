# DyadicPrefixBounds

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Definition 1.1 (tableH).**

$$\forall (j n : \mathbb{N}) , \operatorname{tableH} j n = \operatorname{if} j = 1 \operatorname{then} \operatorname{tableValue} \operatorname{table1} n \operatorname{else} \operatorname{if} j = 2 \operatorname{then} \operatorname{tableValue} \operatorname{table2} n \operatorname{else} \operatorname{if} j = 3 \operatorname{then} \operatorname{tableValue} \operatorname{table3} n \operatorname{else} \operatorname{if} j = 4 \operatorname{then} \operatorname{tableValue} \operatorname{table4} n \operatorname{else} \operatorname{tableValue} \operatorname{table5} n$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.2 (tableError).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (n : \mathbb{N}) , \operatorname{tableError} \operatorname{sigma} n = (\sum_{j \in \operatorname{Finset}.\operatorname{Icc} 1 5} \operatorname{sigma} ^{j} \cdot (\operatorname{Nat}.\operatorname{choose} 6 j : \mathbb{Z}) \cdot \operatorname{tableH} j n) + (\operatorname{tableValue} \operatorname{table6}) n - (\operatorname{tableValue} \operatorname{table6}) (n - 1)$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableError` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.3 (seedH).**

$$\forall (j n : \mathbb{N}) , \operatorname{seedH} j n = (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto (\operatorname{tableH} j (n - i)) . \operatorname{natAbs})$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.4 (seedC).**

$$\forall (n : \mathbb{N}) , \operatorname{seedC} n = (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{tableValue} \operatorname{table6}) (n - i)) . \operatorname{natAbs})$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.5 (prefixB).**

$$\forall (n : \mathbb{N}) , \operatorname{prefixB} n = (\sum_{j \in \operatorname{Finset}.\operatorname{Icc} 1 5} \operatorname{Nat}.\operatorname{choose} 6 j \cdot \operatorname{seedH} j n) + 4 \cdot \operatorname{seedC} n$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.6 (tableH sound).**

$$\forall (j n : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (n < 4096) \to (\operatorname{recur} (p j) n) = \operatorname{tableH} j n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableH_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.7 (tableError sound).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (n : \mathbb{N}) , (n < 4096) \to \operatorname{errorTerm} \operatorname{sigma} n = \operatorname{tableError} \operatorname{sigma} n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableError_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.8 (prefixChunk).**

$$\forall (\operatorname{base} \operatorname{len} : \mathbb{N}) , \operatorname{prefixChunk} \operatorname{base} \operatorname{len} = (\operatorname{List}.\operatorname{range} \operatorname{len}) . \operatorname{all} (\operatorname{fun} k \mapsto \operatorname{decide} (24 \cdot \operatorname{prefixB} (\operatorname{base} + k) < (\operatorname{base} + k) ^{4}))$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.9 (initialChunk).**

$$\forall (\operatorname{sigma} : \mathbb{Z}) , \forall (\operatorname{lower} \operatorname{base} \operatorname{len} : \mathbb{N}) , \operatorname{initialChunk} \operatorname{sigma} \operatorname{lower} \operatorname{base} \operatorname{len} = (\operatorname{List}.\operatorname{range} \operatorname{len}) . \operatorname{all} (\operatorname{fun} k \mapsto \operatorname{decide} (\operatorname{lower} \le \operatorname{base} + k \to 0 < ((\operatorname{Nat}.\operatorname{descFactorial} (\operatorname{base} + k + 4) 4 / 24 : \mathbb{N}) : \mathbb{Z}) + \operatorname{tableError} \operatorname{sigma} (\operatorname{base} + k)))$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.initialChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.10 (prefixcertificate 0).**

$$\operatorname{prefixChunk} 2048 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixcertificate_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.11 (prefixcertificate checked).**

$$\forall (\operatorname{block} : \operatorname{Fin} 64) , \operatorname{prefixChunk} (2048 + 32 \cdot \operatorname{block}.\operatorname{val}) 32 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixcertificate_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.12 (appendValue).**

$$\forall (q : \mathbb{N}) (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} q w = \operatorname{Nat}.\operatorname{ofDigits} 2 (\operatorname{List}.\operatorname{append} (\operatorname{List}.\operatorname{map} \operatorname{Bool}.\operatorname{toNat} w) [q])$$

*Formalization.* `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.13 (appendValue cons).**

$$\forall (q : \mathbb{N}) , \forall (b : \operatorname{Bool}) , \forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} q (b :: w) = 2 \cdot \operatorname{appendValue} q w + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.14 (appendValue decompose).**

$$\forall (\operatorname{p0} : \mathbb{N}) , \forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} \operatorname{p0} w = \operatorname{p0} \cdot 2 ^{w.\operatorname{length}} + \operatorname{appendValue} 0 w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.15 (lowWord bound).**

$$\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{appendValue} 0 w < 2 ^{w.\operatorname{length}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.lowWord_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.16 (c prefix).**

$$\forall (\operatorname{p0} : \mathbb{N}) , (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to \forall (w : \operatorname{List} \operatorname{Bool}) , ((\operatorname{recur} (p 6) (\operatorname{appendValue} \operatorname{p0} w))) . \operatorname{natAbs} \le 2 \cdot 16 ^{w.\operatorname{length}} \cdot \operatorname{seedC} \operatorname{p0} \land ((\operatorname{recur} (p 6) (\operatorname{appendValue} \operatorname{p0} w - 1))) . \operatorname{natAbs} \le 2 \cdot 16 ^{w.\operatorname{length}} \cdot \operatorname{seedC} \operatorname{p0}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.c_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.17 (seedH exact).**

$$\forall (j \operatorname{p0} : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (\operatorname{p0} < 4096) \to \operatorname{seedH} j \operatorname{p0} = (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p j) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedH_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.18 (seedC exact).**

$$\forall (\operatorname{p0} : \mathbb{N}) , (\operatorname{p0} < 4096) \to \operatorname{seedC} \operatorname{p0} = (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedC_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.19 (h dyadic).**

$$\forall (j \operatorname{p0} m \operatorname{low} : \mathbb{N}) , (j \in \operatorname{Finset}.\operatorname{Icc} 1 5) \to (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to (\operatorname{low} < 2 ^{m}) \to ((\operatorname{recur} (p j) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low}))) . \operatorname{natAbs} \le 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 5) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p j) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.h_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.20 (c dyadic).**

$$\forall (\operatorname{p0} m \operatorname{low} : \mathbb{N}) , (2048 \le \operatorname{p0}) \to (\operatorname{p0} < 4096) \to (\operatorname{low} < 2 ^{m}) \to ((\operatorname{recur} (p 6) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low}))) . \operatorname{natAbs} \le 2 \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs}) \land ((\operatorname{recur} (p 6) (\operatorname{p0} \cdot 2 ^{m} + \operatorname{low} - 1))) . \operatorname{natAbs} \le 2 \cdot 16 ^{m} \cdot (\operatorname{Finset}.\operatorname{range} 6) . \operatorname{sup} (\operatorname{fun} i \mapsto ((\operatorname{recur} (p 6) (\operatorname{p0} - i))) . \operatorname{natAbs})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/DyadicPrefixBounds.c_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue_cons`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.appendValue_decompose`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.c_dyadic`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.c_prefix`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.h_dyadic`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.initialChunk`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.lowWord_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixB`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixChunk`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixcertificate_0`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.prefixcertificate_checked`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedC`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedC_exact`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedH`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.seedH_exact`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableError`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableError_sound`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableH`
- Truth anchor: `D5/S1/Words/EvilOdious/DyadicPrefixBounds.tableH_sound`
- Dependency: [D5/S1/Words/EvilOdious/CoefficientTableChecker](CoefficientTableChecker.md)
- Dependency: [D5/S1/Words/EvilOdious/DyadicStatesLastThree](DyadicStatesLastThree.md)
