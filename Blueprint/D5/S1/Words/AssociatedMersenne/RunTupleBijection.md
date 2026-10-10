# RunTupleBijection

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Definition 1.1 (tupleList).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{tupleList} \operatorname{t} = ((\operatorname{t}.\operatorname{flatMap} (\operatorname{fun} \operatorname{b} \mapsto [ \operatorname{List}.\operatorname{replicate} \operatorname{b}.1 \operatorname{true} , \operatorname{List}.\operatorname{replicate} (\operatorname{b}.1 + 1 + \operatorname{b}.2) \operatorname{false} ])) . \operatorname{flatten})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Each positive run is followed by its compulsory longer zero block and its additional slack.

**Definition 1.2 (blockLengths).**

$$\forall (\operatorname{w}: \operatorname{List} \operatorname{Bool}), \operatorname{blockLengths} \operatorname{w} = ((\operatorname{w}.\operatorname{splitBy} (\operatorname{fun} \operatorname{a} \operatorname{b} \mapsto \operatorname{BEq.beq}\left(\operatorname{a}, \operatorname{b}\right))) . \operatorname{map} \operatorname{List}.\operatorname{length})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.blockLengths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Splitting at changes of Boolean value records the successive constant-block lengths.

**Lemma 1.3 (tupleList length).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = (\operatorname{t}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto 2 \cdot \operatorname{b}.1 + 1 + \operatorname{b}.2)) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The run and zero blocks contribute two times the run length plus one plus the slack.

**Definition 1.4 (decodeLengths).**

$$\begin{aligned}\operatorname{decodeLengths} [   ] = [   ]\\\forall (\operatorname{r} \operatorname{z} : \operatorname{Nat}) (\operatorname{rest} : \operatorname{List} \operatorname{Nat}) , \operatorname{decodeLengths} (\operatorname{r} :: \operatorname{z} :: \operatorname{rest}) = (\operatorname{r} , \operatorname{z} - (\operatorname{r} + 1)) :: \operatorname{decodeLengths} \operatorname{rest}\\\forall (\operatorname{r} : \operatorname{Nat}) , \operatorname{decodeLengths} [ \operatorname{r} ] = [   ]\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.decodeLengths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Successive one and zero block lengths determine a run length and its excess zero slack.

**Definition 1.5 (extractListTuple).**

$$\forall (\operatorname{w}: \operatorname{List} \operatorname{Bool}), \operatorname{extractListTuple} \operatorname{w} = (\operatorname{decodeLengths} (\operatorname{blockLengths} \operatorname{w}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractListTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Constant-block splitting followed by length decoding extracts the ordered run-and-slack tuple.

**Definition 1.6 (wordOfTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{hlen}: (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n}), \forall (\operatorname{q}: \operatorname{Fin} \operatorname{n}), \operatorname{wordOfTuple} \operatorname{i} \operatorname{t} \operatorname{hlen} \operatorname{q} = (\operatorname{tupleList} \operatorname{t}) [ \operatorname{offset} \operatorname{i} \operatorname{q} ]$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.wordOfTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The defining list access uses the bound obtained from hlen and offset_lt; proof arguments do not change the returned letter.

**Theorem 1.7 (linearize wordOfTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{hlen}: (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n}), \operatorname{linearize} (\operatorname{wordOfTuple} \operatorname{i} \operatorname{t} \operatorname{hlen}) \operatorname{i} = \operatorname{tupleList} \operatorname{t}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_wordOfTuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The inverse circular offset reads the reconstructed word as its original tuple list.

**Definition 1.8 (rawWord).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{rawWord} \operatorname{t} = ((\operatorname{t}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto \operatorname{List}.\operatorname{replicate} \operatorname{b}.1 \operatorname{true} ++ \operatorname{List}.\operatorname{replicate} \operatorname{b}.2 \operatorname{false})) . \operatorname{flatten})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Flattening alternating replicated one and zero blocks encodes the unadjusted run-and-gap lengths.

**Lemma 1.9 (rawWord cons).**

$$\forall (\operatorname{b}: \operatorname{Nat} \times \operatorname{Nat}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{rawWord} (\operatorname{b} :: \operatorname{t}) = \operatorname{List}.\operatorname{replicate} \operatorname{b}.1 \operatorname{true} ++ \operatorname{List}.\operatorname{replicate} \operatorname{b}.2 \operatorname{false} ++ \operatorname{rawWord} \operatorname{t}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The first raw pair contributes its replicated one block and zero block before the remaining pairs.

**Lemma 1.10 (rawWord append).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{u}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{rawWord} (\operatorname{t} ++ \operatorname{u}) = \operatorname{rawWord} \operatorname{t} ++ \operatorname{rawWord} \operatorname{u}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Flattening the block encoding transports concatenation of pair lists to concatenation of words.

**Lemma 1.11 (raw encoding marked).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), (\operatorname{t} \neq [   ]) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1 \land 0 < \operatorname{b}.2) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{rawWord} \operatorname{t}) \to (\operatorname{IsMarkedStart} \operatorname{w} \operatorname{i})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_marked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Positive first and last block lengths give a one at the origin and a zero at its predecessor.

**Lemma 1.12 (first raw run start).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{z}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{post}: \operatorname{List} \operatorname{Bool}), (0 < \operatorname{r}) \to ((0 < \operatorname{z}) \to ((\operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{List}.\operatorname{replicate} \operatorname{r} \operatorname{true} ++ \operatorname{List}.\operatorname{replicate} \operatorname{z} \operatorname{false} ++ \operatorname{post}) \to (\operatorname{IsOneRunStart} \operatorname{w} \operatorname{i} \operatorname{r}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.first_raw_run_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The first replicated one block and its adjacent zero blocks delimit the first run.

**Lemma 1.13 (linearize get optional).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{j}: \operatorname{Nat}), (\operatorname{j} < \operatorname{n}) \to (\operatorname{some} ((\operatorname{linearize} \operatorname{w} \operatorname{i}) [ \operatorname{j} ]) = \operatorname{some} (\operatorname{w} (\operatorname{cycAdd} \operatorname{i} \operatorname{j})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_get_optional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Optional list access equals some of the indexed letter. Since j<n and linearize has length n, the displayed ordinary indexing has the same value; the two occurrences of some retain the optional equality.

**Theorem 1.14 (marked admissible tuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), (\operatorname{Admissible} \operatorname{w}) \to ((\operatorname{IsMarkedStart} \operatorname{w} \operatorname{i}) \to (\exists \operatorname{t} : \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat}) , \operatorname{t} \neq [   ] \land (\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1) \land (\operatorname{t}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto 2 \cdot \operatorname{b}.1 + 1 + \operatorname{b}.2)) . \operatorname{sum} = \operatorname{n} \land \operatorname{tupleList} \operatorname{t} = \operatorname{linearize} \operatorname{w} \operatorname{i} \land \operatorname{extractListTuple} (\operatorname{linearize} \operatorname{w} \operatorname{i}) = \operatorname{t}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.marked_admissible_tuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Alternating positive blocks recover the raw pairs, and admissibility turns every excess gap into nonnegative slack.

**Theorem 1.15 (raw encoding admissible).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), (\operatorname{t} \neq [   ]) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1 \land \operatorname{b}.1 < \operatorname{b}.2) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{rawWord} \operatorname{t}) \to (\operatorname{Admissible} \operatorname{w})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Every marked run lies at a block boundary whose longer zero block fulfils the circular gap condition.

**Theorem 1.16 (raw encoding admissible iff).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), (\operatorname{t} \neq [   ]) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1 \land 0 < \operatorname{b}.2) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{rawWord} \operatorname{t}) \to (\operatorname{Admissible} \operatorname{w} \iff \forall \operatorname{b} \in \operatorname{t} , \operatorname{b}.1 < \operatorname{b}.2)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_admissible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The block-boundary run starts make admissibility equivalent to the strict inequality for each following gap.

**Definition 1.17 (pairPrefix).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{p}: \operatorname{Nat}), \operatorname{pairPrefix} \operatorname{t} \operatorname{p} = ((\operatorname{rawWord} (\operatorname{t}.\operatorname{take} \operatorname{p})) . \operatorname{length})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.pairPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Summing earlier pair lengths gives the labelled offset of a raw pair boundary.

**Definition 1.18 (rawPairs).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{rawPairs} \operatorname{t} = (\operatorname{t}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto (\operatorname{b}.1 , \operatorname{b}.1 + 1 + \operatorname{b}.2)))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Adding the compulsory run length plus one to the slack converts tuples into raw run-and-gap pairs.

**Lemma 1.19 (tupleList eq rawPairs).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{tupleList} \operatorname{t} = \operatorname{rawWord} (\operatorname{rawPairs} \operatorname{t})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList_eq_rawPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The compulsory zero lengths identify the slack encoding with the raw-pair encoding.

**Lemma 1.20 (tuple word admissible).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{hlen}: (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n}), (\operatorname{t} \neq [   ]) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1) \to (\operatorname{Admissible} (\operatorname{wordOfTuple} \operatorname{i} \operatorname{t} \operatorname{hlen})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tuple_word_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Every positive tuple run has its compulsory strictly longer zero block in the reconstructed word.

**Lemma 1.21 (tuple word marked).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{hlen}: (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n}), (\operatorname{t} \neq [   ]) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1) \to (\operatorname{IsMarkedStart} (\operatorname{wordOfTuple} \operatorname{i} \operatorname{t} \operatorname{hlen}) \operatorname{i}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tuple_word_marked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A nonempty positive tuple begins with a one and ends with a zero, marking its reconstruction origin.

**Definition 1.22 (GoodTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{GoodTuple} \operatorname{n} = (\{ \operatorname{t} : \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat}) // \operatorname{t} \neq [   ] \land (\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1) \land (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n} \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.GoodTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype fixes a nonempty positive-run tuple whose encoded length is the prescribed length.

**Definition 1.23 (MarkedWords).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{MarkedWords} \operatorname{n} = (\{ \operatorname{p} : (\operatorname{Fin} \operatorname{n} \to \operatorname{Bool}) \times \operatorname{Fin} \operatorname{n} // \operatorname{Admissible} \operatorname{p}.1 \land \operatorname{IsMarkedStart} \operatorname{p}.1 \operatorname{p}.2 \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.MarkedWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype records an admissible labelled word together with a positive marked start.

**Definition 1.24 (extractMarked).**

$$\begin{aligned}\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{x}: \operatorname{MarkedWords} \operatorname{n}), (\operatorname{extractMarked} \operatorname{x}) . 1 = \operatorname{x}.\operatorname{val}.2\\\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{x}: \operatorname{MarkedWords} \operatorname{n}), (\operatorname{extractMarked} \operatorname{x}) . 2 . \operatorname{val} = \operatorname{extractListTuple} (\operatorname{linearize} \operatorname{x}.\operatorname{val}.1 \operatorname{x}.\operatorname{val}.2)\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The first component is the labelled run mark. The second component has the displayed underlying list, with its nonemptiness, positivity and total-length proofs supplied by marked_admissible_tuple.

**Definition 1.25 (reconstructMarked).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{x}: \operatorname{Fin} \operatorname{n} \times \operatorname{GoodTuple} \operatorname{n}), (\operatorname{reconstructMarked} \operatorname{x}) . \operatorname{val} = (\operatorname{wordOfTuple} \operatorname{x}.1 \operatorname{x}.2.\operatorname{val} \operatorname{x}.2.\operatorname{property}.2.2 , \operatorname{x}.1)$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.reconstructMarked` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The displayed value is the underlying labelled word and mark. The subtype proof is supplied by tuple_word_admissible and tuple_word_marked.

**Definition 1.26 (markedTupleEquiv).**

$$\begin{aligned}\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{markedTupleEquiv} \operatorname{n} : \operatorname{MarkedWords} \operatorname{n} \equiv \operatorname{Fin} \operatorname{n} \times \operatorname{GoodTuple} \operatorname{n}\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{markedTupleEquiv} \operatorname{n}) . \operatorname{toFun} = \operatorname{extractMarked}\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{markedTupleEquiv} \operatorname{n}) . \operatorname{invFun} = \operatorname{reconstructMarked}\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.markedTupleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Extraction and reconstruction are inverse through constant-block decoding and the marked boundary conditions.

**Definition 1.27 (instFiniteGoodTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{instFiniteGoodTuple} \operatorname{n} : \operatorname{Finite} (\operatorname{GoodTuple} \operatorname{n})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.instFiniteGoodTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Finiteness is constructed by Finite.of_injective, using the map that sends a good tuple to its reconstructed List.Vector Bool n and the injectivity of that map.

**Definition 1.28 (instFintypeGoodTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{instFintypeGoodTuple} \operatorname{n} : \operatorname{Fintype} (\operatorname{GoodTuple} \operatorname{n})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.instFintypeGoodTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The enumerating instance is Fintype.ofFinite (GoodTuple n).

**Theorem 1.29 (runCount wordOfTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \forall (\operatorname{hlen}: (\operatorname{tupleList} \operatorname{t}) . \operatorname{length} = \operatorname{n}), (\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1) \to (\operatorname{runCount} (\operatorname{wordOfTuple} \operatorname{i} \operatorname{t} \operatorname{hlen}) = \operatorname{t}.\operatorname{length})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.runCount_wordOfTuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The distinct pair-prefix positions enumerate exactly the marked starts of the reconstructed word.

**Lemma 1.30 (extractMarked runs).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{x}: \operatorname{MarkedWords} \operatorname{n}), \operatorname{runCount} \operatorname{x}.\operatorname{val}.1 = (\operatorname{extractMarked} \operatorname{x}) . 2 . \operatorname{val}.\operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Reconstruction preserves the word, and the tuple length counts its marked run starts.

**Definition 1.31 (RunTuples).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{RunTuples} \operatorname{n} \operatorname{ell} = (\{ \operatorname{t} : \operatorname{GoodTuple} \operatorname{n} // \operatorname{t}.\operatorname{val}.\operatorname{length} = \operatorname{ell} \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/RunTupleBijection.RunTuples` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype restricts good tuples to a prescribed number of run-and-slack pairs.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.GoodTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.MarkedWords`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.RunTuples`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.blockLengths`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.decodeLengths`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractListTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked_runs`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.first_raw_run_start`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.instFiniteGoodTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.instFintypeGoodTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_get_optional`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_wordOfTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.markedTupleEquiv`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.marked_admissible_tuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.pairPrefix`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawPairs`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_append`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_cons`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_admissible`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_admissible_iff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_marked`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.reconstructMarked`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.runCount_wordOfTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList_eq_rawPairs`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList_length`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tuple_word_admissible`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.tuple_word_marked`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/RunTupleBijection.wordOfTuple`
- Dependency: [D5/S1/Words/AssociatedMersenne/CircularWords](CircularWords.md)
- Dependency: [D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums](../Compositions/ConstantBlocksDistinctRunSums.md)
