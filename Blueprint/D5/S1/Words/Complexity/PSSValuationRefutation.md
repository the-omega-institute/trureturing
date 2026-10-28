# Natural Valuations Cannot Preserve Every Abelian Complexity Function

## Abstract

A single ternary infinite word has fewer additive classes than original-symbol abelian classes at some positive length for every natural valuation.

An alphabet A is finite, and an infinite word is a function from Nat to A. A length-n factor starting at i is the function j ↦ w(i+j), for j in Fin n. The existing wordFactorSet is the finite subset of all functions Fin n → A which occur at natural starting indices. Thus only ordinary contiguous factors of the same one-sided infinite word are counted.

**Definition 1.1 (Original-symbol Parikh vectors).**

$$\forall A \in Type,\; \forall u \in List\left(A\right),\; \forall a \in A,\; parikh\left(u, a\right) = count\left(a, u\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.parikh` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

Section 2 defines the Parikh vector by its letter counts. Its coordinates are indexed by the original letters, even when two letters receive equal weights. List.perm_iff_count identifies equality of these vectors with permutation of the words, exactly the source's abelian equivalence.

**Definition 1.2 (Natural evaluation of a Parikh vector).**

$$\forall A \in Type,\; [Fintype\left(A\right)] \forall v \in A \to Nat,\; \forall p \in A \to Nat,\; weightedSum\left(v, p\right) = \sum_{a\in A} v\left(a\right)\cdot p\left(a\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.weightedSum` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

A valuation is any map v : A → Nat. The evaluation is the sum of v(a)p(a) over the finite alphabet. Finset.sum_list_map_count, extending its sum from the letter support to the alphabet, gives sum(map v u) = weightedSum v (parikh u). No injectivity or positivity of v is required.

**Definition 1.3 (Actual factor Parikh vectors).**

$$\forall A \in Type,\; [Fintype\left(A\right)] \forall w \in Nat \to A,\; \forall n \in Nat,\; parikhSet\left(w, n\right) = image\left(parikh\circ ofFn, wordFactorSet\left(w, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.parikhSet` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

The image of the finite factor set under parikh ∘ List.ofFn is a Finset. Every member is the Parikh vector of an actual length-n factor, and every such vector is included. Equal vectors are counted once.

**Definition 1.4 (Abelian complexity on the original alphabet).**

$$\forall A \in Type,\; [Fintype\left(A\right)] \forall w \in Nat \to A,\; \forall n \in Nat,\; abelianComplexity\left(w, n\right) = card\left(parikhSet\left(w, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.abelianComplexity` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

This is the number of distinct original-symbol Parikh vectors. It equals the number of abelian equivalence classes of the factors by the count characterization of List.Perm.

**Definition 1.5 (Actual weighted factor sums).**

$$\forall A \in Type,\; [Fintype\left(A\right)] \forall w \in Nat \to A,\; \forall n \in Nat,\; \forall v \in A \to Nat,\; sumSet\left(w, v, n\right) = \{sum\left(map\left(v, ofFn\left(u\right)\right)\right) \mid u \in wordFactorSet\left(w, n\right)\}$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.sumSet` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

The sums are taken over exactly the same actual factor set. Their Finset is also the image of parikhSet under weightedSum v, by the list-sum identity and Finset.image_image. Consequently additive equivalence classes are exactly the fibers of the weighted-sum map on original-symbol classes.

**Definition 1.6 (Additive complexity under a valuation).**

$$\forall A \in Type,\; [Fintype\left(A\right)] \forall w \in Nat \to A,\; \forall n \in Nat,\; \forall v \in A \to Nat,\; additiveComplexity\left(w, v, n\right) = card\left(sumSet\left(w, v, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.additiveComplexity` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

The additive complexity is the number of these distinct sums, as in Definitions 1 and 3. All counted collections are finite images of the finite set of functions Fin n → A. At n = 0 the unique empty factor gives the zero Parikh vector and the zero sum, so both complexities are one.

**Definition 1.7 (The full valuation-existence question).**

$$claim \Leftrightarrow \left(\forall A \in Type,\; [Fintype\left(A\right)] \forall w \in Nat \to A,\; \exists v \in A \to Nat,\; \forall n \in Nat,\; additiveComplexity\left(w, v, n\right) = abelianComplexity\left(w, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.claim` (`✓ std3`).

*Citation.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

Question 31 in arXiv:2410.02409v1, Section 5, PDF page 15, asks: "Given an alphabet A, is there a valuation such that the additive complexity of a given sequence is equal to its abelian complexity?" The same question is HTML Section 4 Question 30 and official FSTTCS Question 31. The closed proposition quantifies over every finite alphabet A : Type, every infinite word, and a natural valuation whose equality holds at every natural length. Finite sets are represented by their finite types; no global recurrence, automaticity, morphicity or balancedness hypothesis is present.

**Definition 1.8 (A fixed ternary infinite word).**

$$\forall i \in Nat,\; universalWord\left(i\right) = getD\left(block\left(K\left(i\right)\right), i-B\left(K\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S1/Words/Complexity/PSSValuationRefutation.universalWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

Decode k as a finite list over Fin 3 using the existing Encodable instance, using [] when decoding fails, and append [0] to obtain block k. Put B(0)=0 and B(k+1)=B(k)+length(block k). Every block is nonempty, so B is strictly increasing and B(k) ≥ k. Let K(i) be the least k with i < B(k+1). The displayed definition selects the letter at offset i-B(k) of that block; getD uses the displayed zero as its default. At every offset j below the block length, the least-boundary property yields universalWord(B(k)+j)=block(k)[j]. Decoding encode(u) returns u, so every finite ternary list u occurs contiguously at B(encode(u)). The same function universalWord is fixed before any valuation is chosen.

**Theorem 1.9 (A negative answer to the entire valuation-existence assertion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PSSValuationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pierre Popoli and Jeffrey Shallit and Manon Stipulanti (2024). *Additive word complexity and Walnut*. DOI: [10.4230/LIPIcs.FSTTCS.2024.32](https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32). URL: <https://arxiv.org/abs/2410.02409v1>.

*Commentary.*

Fix universalWord. For any valuation put a=v(0), b=v(1), c=v(2). If a=b=c, the two singleton factors [0] and [1] have different Parikh vectors and equal weighted sums at length one. Otherwise the two actual factors 0^b 1^c 2^a and 0^c 1^a 2^b have the same positive length a+b+c. Their Parikh vectors are (b,c,a) and (c,a,b). Equality would force a=b=c, while their weighted sums are always equal by commutativity of multiplication.

Both factors occur in the fixed word by its decoded-block construction. Hence weightedSum is noninjective on the finite Parikh set at that same length. Finset.card_image_le and Finset.card_image_iff imply that its image has strictly smaller cardinality. This proves that for every natural valuation v there exists n>0 with additiveComplexity universalWord v n < abelianComplexity universalWord n, contradicting the valuation supplied by claim for A=Fin 3 and this one fixed word. Zero and repeated weights are included. The obstruction uses unbounded factor counts; it imposes no additional restriction on the question and does not contradict the source's positive results for explicitly balanced or specially structured words.

## References

- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.abelianComplexity`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.additiveComplexity`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.claim`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.parikh`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.parikhSet`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.result`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.sumSet`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.universalWord`
- Truth anchor: `D5/S1/Words/Complexity/PSSValuationRefutation.weightedSum`
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
