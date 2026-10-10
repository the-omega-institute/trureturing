# CircularWords

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Lemma 1.1 (Split under reversal and transport).**

$$\forall (\operatorname{alpha}: \operatorname{Type}), \forall (\operatorname{beta}: \operatorname{Type}), \forall (\operatorname{r}: \operatorname{alpha} \to \operatorname{alpha} \to \operatorname{Bool}), \forall (\operatorname{s}: \operatorname{beta} \to \operatorname{beta} \to \operatorname{Bool}), \forall (\operatorname{f}: \operatorname{alpha} \to \operatorname{beta}), \forall (\operatorname{l}: \operatorname{List} \operatorname{alpha}), (\forall \operatorname{a} \in \operatorname{l} , \forall \operatorname{b} \in \operatorname{l} , \operatorname{s} (\operatorname{f} \operatorname{b}) (\operatorname{f} \operatorname{a}) = \operatorname{r} \operatorname{a} \operatorname{b}) \to ((\operatorname{l}.\operatorname{reverse}.\operatorname{map} \operatorname{f}) . \operatorname{splitBy} \operatorname{s} = (\operatorname{l}.\operatorname{splitBy} \operatorname{r}) . \operatorname{reverse}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto \operatorname{b}.\operatorname{reverse}.\operatorname{map} \operatorname{f}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.split_reverse_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Reversing each block and the block order preserves internal links and separating boundaries under the transported relation.

**Definition 1.2 (cycAdd).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), \operatorname{cycAdd} \operatorname{i} \operatorname{j} = (\operatorname{Fin}.\operatorname{ofNat} \operatorname{n} (\operatorname{i}.\operatorname{val} + \operatorname{j}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Adding a natural offset and reducing modulo the length gives the labelled circular position.

**Definition 1.3 (cycSub).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), \operatorname{cycSub} \operatorname{i} \operatorname{j} = (\operatorname{Fin}.\operatorname{ofNat} \operatorname{n} (\operatorname{i}.\operatorname{val} + \operatorname{n} - \operatorname{j}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.cycSub` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The predecessor offset uses natural subtraction before reduction modulo the length.

**Definition 1.4 (IsOneRunStart).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), \operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r} \iff (\operatorname{w} (\operatorname{cycSub} \operatorname{i} 1) = \operatorname{false} \land (\forall \operatorname{j} < \operatorname{r} , \operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{j}) = \operatorname{true}) \land \operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{r}) = \operatorname{false})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.IsOneRunStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The preceding and following letters are zero and all r intermediate letters are one. This predicate permits r=0. Genuine marks use IsMarkedStart, which requires positive r.

**Definition 1.5 (Admissible).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \operatorname{Admissible} \operatorname{w} \iff ((\operatorname{n} = 0 \lor \exists \operatorname{i} , \operatorname{w} \operatorname{i} = \operatorname{false}) \land \forall \operatorname{i} \operatorname{r} , \operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r} \to \forall \operatorname{j} \le \operatorname{r} , \operatorname{w} (\operatorname{cycAdd} (\operatorname{cycAdd} \operatorname{i} \operatorname{r}) \operatorname{j}) = \operatorname{false})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.Admissible` (`✓ std3`).

*Citation.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Wei and Yang, arXiv v1, pp. 3–4: “A string of 𝐁ₙ is called run-constrained-circularly if every run of 1s appearing in this string is immediately followed by a strictly longer run of 0s in a circular manner.” Positions are labelled Fin n and letters are Bool. The all-ones word is excluded for positive n; n=0 denotes the empty word.

**Definition 1.6 (flip).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{flip} \operatorname{w} \operatorname{i} = (\operatorname{Function}.\operatorname{update} \operatorname{w} \operatorname{i} (! \operatorname{w} \operatorname{i}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.flip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Updating one Boolean letter to its negation gives the one-bit neighbour.

**Definition 1.7 (degree).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \operatorname{degree} \operatorname{w} = ((\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{fun} \operatorname{i} : \operatorname{Fin} \operatorname{n} \mapsto \operatorname{Admissible} (\operatorname{CircularWords}.\operatorname{flip} \operatorname{w} \operatorname{i}))) . \operatorname{card})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.degree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Filtering all positions by admissibility of their one-bit neighbours counts the degree.

**Definition 1.8 (N).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{N} \operatorname{n} \operatorname{k} = ((\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{fun} \operatorname{w} : \operatorname{Fin} \operatorname{n} \to \operatorname{Bool} \mapsto \operatorname{Admissible} \operatorname{w} \land \operatorname{degree} \operatorname{w} = \operatorname{k})) . \operatorname{card})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.N` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Filtering labelled words by admissibility and degree gives the degree histogram.

**Lemma 1.9 (cycAdd sub one).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{cycAdd} \operatorname{i} (\operatorname{n} - 1) = \operatorname{cycSub} \operatorname{i} 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Positivity of the length identifies the offset n minus one with the predecessor.

**Lemma 1.10 (start large false).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), (\operatorname{n} \le \operatorname{r}) \to (\neg \operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.start_large_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A run of at least the full length would make its zero predecessor a one.

**Lemma 1.11 (cycAdd zero).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{cycAdd} \operatorname{i} 0 = \operatorname{i}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Reduction modulo the length leaves the original position unchanged at offset zero.

**Lemma 1.12 (cycAdd val).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), (\operatorname{cycAdd} \operatorname{i} \operatorname{j}) . \operatorname{val} = (\operatorname{i}.\operatorname{val} + \operatorname{j}) \operatorname{Nat}.\operatorname{mod} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The value of circular addition is the remainder of the sum of the labelled index and offset.

**Lemma 1.13 (cycAdd assoc).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{cycAdd} (\operatorname{cycAdd} \operatorname{i} \operatorname{j}) \operatorname{k} = \operatorname{cycAdd} \operatorname{i} (\operatorname{j} + \operatorname{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Remainder arithmetic identifies successive offsets with their sum.

**Lemma 1.14 (cycAdd inj).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), (\operatorname{j} < \operatorname{n}) \to ((\operatorname{k} < \operatorname{n}) \to (\operatorname{cycAdd} \operatorname{i} \operatorname{j} = \operatorname{cycAdd} \operatorname{i} \operatorname{k} \iff \operatorname{j} = \operatorname{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_inj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Offsets below the length are uniquely determined by their circular positions.

**Lemma 1.15 (zero admissible).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{Admissible} (\operatorname{Function}.\operatorname{const} (\operatorname{Fin} \operatorname{n}) \operatorname{false})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.zero_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The zero word has no positive run and satisfies every required zero-gap condition.

**Lemma 1.16 (zero degree).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{degree} (\operatorname{Function}.\operatorname{const} (\operatorname{Fin} \operatorname{n}) \operatorname{false}) = \operatorname{if} \operatorname{n} \le 2 \operatorname{then} 0 \operatorname{else} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.zero_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A singleton one is admissible precisely when the length exceeds two, determining every flip of the zero word.

**Definition 1.17 (offset).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{q}: \operatorname{Fin} \operatorname{n}), \operatorname{offset} \operatorname{i} \operatorname{q} = ((\operatorname{q}.\operatorname{val} + \operatorname{n} - \operatorname{i}.\operatorname{val}) \operatorname{Nat}.\operatorname{mod} \operatorname{n})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.offset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The remainder of the target index minus the starting index gives a bounded forward offset.

**Lemma 1.18 (cycAdd offset).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{q}: \operatorname{Fin} \operatorname{n}), \operatorname{cycAdd} \operatorname{i} (\operatorname{offset} \operatorname{i} \operatorname{q}) = \operatorname{q}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_offset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Adding the remainder offset recovers the target labelled position.

**Lemma 1.19 (offset lt).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{q}: \operatorname{Fin} \operatorname{n}), \operatorname{offset} \operatorname{i} \operatorname{q} < \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.offset_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The remainder defining an offset is strictly below the positive word length.

**Lemma 1.20 (cycAdd bijective).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{Function}.\operatorname{Bijective} (\operatorname{fun} \operatorname{j} : \operatorname{Fin} \operatorname{n} \mapsto \operatorname{cycAdd} \operatorname{i} \operatorname{j}.\operatorname{val})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The bounded offset gives an inverse to circular addition on all labelled positions.

**Definition 1.21 (linearize).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{linearize} \operatorname{w} \operatorname{i} = (\operatorname{List}.\operatorname{ofFn} (\operatorname{fun} \operatorname{j} : \operatorname{Fin} \operatorname{n} \mapsto \operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{j}.\operatorname{val})))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.linearize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Reading one complete circle from the marked position gives a linear Boolean list.

**Lemma 1.22 (linearize injective).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{Function}.\operatorname{Injective} (\operatorname{fun} \operatorname{w} : \operatorname{Fin} \operatorname{n} \to \operatorname{Bool} \mapsto \operatorname{linearize} \operatorname{w} \operatorname{i})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Every labelled position occurs in the linear reading, so equal readings determine equal words.

**Lemma 1.23 (linearize length).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), (\operatorname{linearize} \operatorname{w} \operatorname{i}) . \operatorname{length} = \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The finite list of labelled positions has exactly the word length.

**Lemma 1.24 (one run length unique).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{s}: \operatorname{Nat}), (\operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r}) \to ((\operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{s}) \to (\operatorname{r} = \operatorname{s}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.one_run_length_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The zero ending a run contradicts any longer run from the same start.

**Definition 1.25 (IsMarkedStart).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{IsMarkedStart} \operatorname{w} \operatorname{i} \iff (\exists \operatorname{r} , 0 < \operatorname{r} \land \operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.IsMarkedStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A mark records a one-run start with strictly positive run length.

**Lemma 1.26 (marked start true).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), (\operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}) \to (\operatorname{w} \operatorname{i} = \operatorname{true})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The zero offset in a positive run forces the marked letter to be one.

**Lemma 1.27 (marked start predecessor).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), (\operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}) \to (\operatorname{w} (\operatorname{cycSub} \operatorname{i} 1) = \operatorname{false})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The defining predecessor condition forces the letter before a mark to be zero.

**Lemma 1.28 (marked start iff).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{IsMarkedStart} \operatorname{w} \operatorname{i} \iff \operatorname{w} (\operatorname{cycSub} \operatorname{i} 1) = \operatorname{false} \land \operatorname{w} \operatorname{i} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A one after a zero extends to its first following zero, giving a positive marked run.

**Lemma 1.29 (cycAdd predecessor pos).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), (0 < \operatorname{j}) \to (\operatorname{cycSub} (\operatorname{cycAdd} \operatorname{i} \operatorname{j}) 1 = \operatorname{cycAdd} \operatorname{i} (\operatorname{j} - 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_predecessor_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Moving back one position from a positive offset agrees with adding the offset minus one.

**Lemma 1.30 (nonzero has marked start).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), (\exists \operatorname{p} , \operatorname{w} \operatorname{p} = \operatorname{false}) \to ((\exists \operatorname{q} , \operatorname{w} \operatorname{q} = \operatorname{true}) \to (\exists \operatorname{i} , \operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.nonzero_has_marked_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A least one encountered after a zero supplies a zero-to-one transition and hence a mark.

**Lemma 1.31 (admissible nonzero has marked start).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), (\operatorname{Admissible} \operatorname{w}) \to ((\exists \operatorname{q} , \operatorname{w} \operatorname{q} = \operatorname{true}) \to (\exists \operatorname{i} , \operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.admissible_nonzero_has_marked_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Admissibility supplies a zero, while a nonzero word supplies the one needed for a marked transition.

**Definition 1.32 (runCount).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \operatorname{runCount} \operatorname{w} = ((\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{IsMarkedStart} \operatorname{w})) . \operatorname{card})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.runCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Counting positive marked starts counts the circular runs of ones.

**Definition 1.33 (DegreeRunWords).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k} = (\{ \operatorname{w} : \operatorname{Fin} \operatorname{n} \to \operatorname{Bool} // \operatorname{Admissible} \operatorname{w} \land \operatorname{degree} \operatorname{w} = \operatorname{k} \land \operatorname{runCount} \operatorname{w} = \operatorname{ell} \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.DegreeRunWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype fixes admissibility, run count and degree for labelled words of a given length.

**Definition 1.34 (MarkedDegreeRunWords).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{MarkedDegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k} = ((\operatorname{w} : \operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k}) \times \{ \operatorname{i} : \operatorname{Fin} \operatorname{n} // \operatorname{IsMarkedStart} \operatorname{w}.\operatorname{val} \operatorname{i} \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.MarkedDegreeRunWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype pairs a degree-and-run-count word with one of its positive marked starts.

**Definition 1.35 (instFintypeDegreeRunWords).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{instFintypeDegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k} : \operatorname{Fintype} (\operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.instFintypeDegreeRunWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

This instance is inferInstanceAs for the subtype of Fin n → Bool satisfying Admissible, degree = k and runCount = ell.

**Definition 1.36 (instFintypeMarkedDegreeRunWords).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{instFintypeMarkedDegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k} : \operatorname{Fintype} (\operatorname{MarkedDegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.instFintypeMarkedDegreeRunWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

This instance is inferInstanceAs for the dependent pair of a DegreeRunWords n ell k word and a Fin n position satisfying IsMarkedStart.

**Theorem 1.37 (marked double count of equiv).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \forall (\operatorname{T}: \operatorname{Type}), [\operatorname{Fintype} \operatorname{T}], (\operatorname{MarkedDegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k} \equiv \operatorname{Fin} \operatorname{n} \times \operatorname{T}) \to (\operatorname{ell} \cdot \operatorname{Fintype}.\operatorname{card} (\operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k}) = \operatorname{n} \cdot \operatorname{Fintype}.\operatorname{card} \operatorname{T})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.marked_double_count_of_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

T is a finite type in an arbitrary universe. An equivalence between labelled marked words and Fin n × T gives the displayed double count without dividing by the number of runs.

**Definition 1.38 (rotateWord).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{rotateWord} \operatorname{w} \operatorname{i} = (\operatorname{fun} \operatorname{j} \mapsto \operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{j}.\operatorname{val}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Changing the starting labelled position reads the same circular word by circular addition.

**Theorem 1.39 (rotateWord admissible iff).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{Admissible} (\operatorname{rotateWord} \operatorname{w} \operatorname{i}) \iff \operatorname{Admissible} \operatorname{w}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord_admissible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Circular addition transports each run start and its following zero gap in both directions.

**Lemma 1.40 (rotateWord degree).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \operatorname{degree} (\operatorname{rotateWord} \operatorname{w} \operatorname{i}) = \operatorname{degree} \operatorname{w}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The bijection on positions transports legal one-bit flips and preserves their count.

**Theorem 1.41 (next one gap bound).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{a}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{z}: \operatorname{Nat}), (\operatorname{Admissible} \operatorname{w}) \to ((\operatorname{IsOneRunStart} \operatorname{w} \operatorname{a} \operatorname{r}) \to ((\operatorname{w} (\operatorname{cycAdd} \operatorname{a} (\operatorname{r} + \operatorname{z})) = \operatorname{true}) \to (\operatorname{r} < \operatorname{z})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.next_one_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A later one cannot occur inside the zero gap forced by admissibility of the preceding run.

**Theorem 1.42 (linearize move mark).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{p}: \operatorname{Nat}), \operatorname{linearize} \operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{p}) = (\operatorname{linearize} \operatorname{w} \operatorname{i}) . \operatorname{rotate} \operatorname{p}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_move_mark` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Moving the marked origin rotates the linear list by the corresponding bounded offset.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.Admissible`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.DegreeRunWords`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.IsMarkedStart`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.IsOneRunStart`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.MarkedDegreeRunWords`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.N`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.admissible_nonzero_has_marked_start`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_assoc`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_bijective`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_inj`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_offset`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_predecessor_pos`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_sub_one`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_val`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_zero`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.cycSub`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.degree`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.flip`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.instFintypeDegreeRunWords`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.instFintypeMarkedDegreeRunWords`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.linearize`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_injective`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_length`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.linearize_move_mark`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.marked_double_count_of_equiv`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_iff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_predecessor`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_true`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.next_one_gap_bound`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.nonzero_has_marked_start`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.offset`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.offset_lt`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.one_run_length_unique`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord_admissible_iff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.rotateWord_degree`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.runCount`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.split_reverse_map`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.start_large_false`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.zero_admissible`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/CircularWords.zero_degree`
