# GreedyRenewal

## Abstract

Shortest borders, maximal block-palindrome width, and exact renewal counts.

**Definition 1.1 (IsBPFactorization).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (bs : \operatorname{List} (\operatorname{List} alpha)) , \forall (c : \operatorname{List} alpha) , \operatorname{IsBPFactorization} w bs c \iff (\forall b \in bs , b \neq [ ]) \land w = bs . \operatorname{reverse} . \operatorname{flatten} ++ c ++ bs . \operatorname{flatten}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsBPFactorization` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 2): “Let w be a non-empty word. A block palindrome factorization (or BP-factorization) of w is a factorization w = wₘ⋯w₁w₀w₁⋯wₘ of a word such that w₀ is a possibly empty word, and every other factor wᵢ is non-empty for all i with 1 ≤ i ≤ m.” Here bs is [w₁,…,wₘ] and c is w₀. The empty word has width zero.

**Definition 1.2 (bpWidth).**

$$\forall (alpha : \operatorname{Type}) , \forall (bs : \operatorname{List} (\operatorname{List} alpha)) , \forall (c : \operatorname{List} alpha) , \operatorname{bpWidth} bs c = 2 \cdot bs . \operatorname{length} + \operatorname{if} c = [ ] \operatorname{then} 0 \operatorname{else} 1$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.bpWidth` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 2): “We say that a BP-factorization wₘ⋯w₁w₀w₁⋯wₘ is of width t where t = 2m+1 if w₀ is non-empty and t = 2m otherwise.” Here m is bs.length and c is w₀.

**Definition 1.3 (largestBPWidth).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \operatorname{largestBPWidth} w = \operatorname{sSup} \{ t : \mathbb{N} \mid \exists (bs : \operatorname{List} (\operatorname{List} alpha)) (c : \operatorname{List} alpha) , \operatorname{IsBPFactorization} w bs c \land \operatorname{bpWidth} bs c = t \}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.largestBPWidth` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 2): “The largest BP-factorization of a word w is a BP-factorization w = wₘ⋯w₁w₀w₁⋯wₘ where m is maximized (i.e., where the width of the BP-factorization is maximized).” The supremum is over all valid widths and is bounded by w.length.

**Theorem 1.4 (largestBPWidth_le_length).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \operatorname{largestBPWidth} w \leq w . \operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.largestBPWidth_le_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.5 (IsBorder).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b \iff b \neq [ ] \land b . \operatorname{length} < w . \operatorname{length} \land \operatorname{List} . \operatorname{IsPrefix} b w \land \operatorname{List} . \operatorname{IsSuffix} b w$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsBorder` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 1): “A border of a word w is a non-empty word that is both a proper prefix and suffix of w.” Properness is expressed by b.length < w.length.

**Definition 1.6 (IsUnbordered).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \operatorname{IsUnbordered} w \iff \forall (b : \operatorname{List} alpha) , \neg \operatorname{IsBorder} w b$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsUnbordered` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 1): “A word is said to be bordered if it has a border. Otherwise, the word is said to be unbordered.”

**Definition 1.7 (IsShortestBorder).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (b : \operatorname{List} alpha) , \operatorname{IsShortestBorder} w b \iff \operatorname{IsBorder} w b \land \forall (c : \operatorname{List} alpha) , \operatorname{IsBorder} w c \Rightarrow b . \operatorname{length} \leq c . \operatorname{length}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsShortestBorder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of IsShortestBorder.

**Theorem 1.8 (shortest_border_unbordered).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (b : \operatorname{List} alpha) , (\operatorname{IsShortestBorder} w b) \Rightarrow (\operatorname{IsUnbordered} b)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_border_unbordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.9 (shortest_border_le_half).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (b : \operatorname{List} alpha) , (\operatorname{IsShortestBorder} w b) \Rightarrow (2 \cdot b . \operatorname{length} \leq w . \operatorname{length})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_border_le_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An overlapping border would produce a shorter nonempty border, so a shortest border occupies at most half of its word.

**Theorem 1.10 (unbordered_outer_shortest).**

$$\forall (alpha : \operatorname{Type}) , \forall (u : \operatorname{List} alpha) , \forall (v : \operatorname{List} alpha) , (u \neq [ ]) \Rightarrow ((\operatorname{IsUnbordered} u) \Rightarrow (\operatorname{IsShortestBorder} (u ++ v ++ u) u))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.unbordered_outer_shortest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.11 (maximal_outer_unbordered).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (c : \operatorname{List} alpha) , \forall (b : \operatorname{List} alpha) , \forall (bs : \operatorname{List} (\operatorname{List} alpha)) , (\operatorname{IsBPFactorization} w (bs ++ [ b ]) c) \Rightarrow ((\operatorname{bpWidth} (bs ++ [ b ]) c = \operatorname{largestBPWidth} w) \Rightarrow (\operatorname{IsUnbordered} b))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.maximal_outer_unbordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bordered outer block splits into matching nonempty outer blocks. This increases the width and contradicts maximality.

**Definition 1.12 (shortestBorder).**

$$\forall (alpha : \operatorname{Type}) (w : \operatorname{List} alpha) (hw : \exists b : \operatorname{List} alpha , \operatorname{IsBorder} w b) (chooseProof : \exists b : \operatorname{List} alpha , \operatorname{IsShortestBorder} w b) , \operatorname{shortestBorder} w hw = \operatorname{Classical} . \operatorname{choose} chooseProof$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortestBorder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Classical.choose selects a shortest border. The displayed choice proof has the exact existential type; proof irrelevance makes the chosen value independent of which proof of that existential is supplied.

**Theorem 1.13 (shortestBorder_spec).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b) , \operatorname{IsShortestBorder} w (\operatorname{shortestBorder} w hw)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortestBorder_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.14 (peeledCore).**

$$\forall (alpha : \operatorname{Type}) (w : \operatorname{List} alpha) (hw : \exists b : \operatorname{List} alpha , \operatorname{IsBorder} w b) (chooseProof : \exists v : \operatorname{List} alpha , w = \operatorname{shortestBorder} w hw ++ v ++ \operatorname{shortestBorder} w hw \land v . \operatorname{length} = w . \operatorname{length} - 2 \cdot (\operatorname{shortestBorder} w hw) . \operatorname{length}) , \operatorname{peeledCore} w hw = \operatorname{Classical} . \operatorname{choose} chooseProof$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Classical.choose selects the central word between the shortest matching outer borders. The existential contains both the concatenation identity and its exact length. Proof irrelevance makes the choice independent of the proof supplied.

**Theorem 1.15 (peeledCore_spec).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b) , w = \operatorname{shortestBorder} w hw ++ \operatorname{peeledCore} w hw ++ \operatorname{shortestBorder} w hw \land (\operatorname{peeledCore} w hw) . \operatorname{length} = w . \operatorname{length} - 2 \cdot (\operatorname{shortestBorder} w hw) . \operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.16 (peeledCore_shorter).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \forall (hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b) , (\operatorname{peeledCore} w hw) . \operatorname{length} < w . \operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore_shorter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.17 (peelWidth).**

$$\forall (alpha : \operatorname{Type}) (w : \operatorname{List} alpha) , \operatorname{peelWidth} w = \operatorname{if} hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b \operatorname{then} 2 + \operatorname{peelWidth} (\operatorname{peeledCore} w hw) \operatorname{else} \operatorname{if} w = [ ] \operatorname{then} 0 \operatorname{else} 1$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.peelWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion removes the shortest border pair until the remaining word is empty or unbordered. Every removal increases the width by two.

**Theorem 1.18 (largest_eq_peelWidth).**

$$\forall (alpha : \operatorname{Type}) , \forall (w : \operatorname{List} alpha) , \operatorname{largestBPWidth} w = \operatorname{peelWidth} w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.largest_eq_peelWidth` (`✓ std3`). ∎

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

Induction on word length shows that greedy shortest-border peeling realizes the largest factorization width.

**Theorem 1.19 (mem_words).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (w : \operatorname{List} (\operatorname{Fin} k)) , w \in (\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k))) \iff w . \operatorname{length} = n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.20 (card_words).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))) . \operatorname{card} = k ^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.card_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.21 (ubWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{ubWords} k n = ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))) . \operatorname{filter} \operatorname{IsUnbordered}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.ubWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of ubWords.

**Definition 1.22 (uCount).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{uCount} k n = (\operatorname{ubWords} k n) . \operatorname{card}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.uCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of uCount.

**Theorem 1.23 (mem_ubWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (w : \operatorname{List} (\operatorname{Fin} k)) , w \in \operatorname{ubWords} k n \iff w . \operatorname{length} = n \land \operatorname{IsUnbordered} w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_ubWords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.24 (outerWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (i : \mathbb{N}) , \operatorname{outerWords} k n i = ((\operatorname{ubWords} k i) \times ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} (n - 2 \cdot i) : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k))))) . \operatorname{image} (\operatorname{fun} p \mapsto p . 1 ++ p . 2 ++ p . 1)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.outerWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of outerWords.

**Theorem 1.25 (mem_outerWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (i : \mathbb{N}) , \forall (w : \operatorname{List} (\operatorname{Fin} k)) , w \in \operatorname{outerWords} k n i \iff \exists (u v : \operatorname{List} (\operatorname{Fin} k)) , u . \operatorname{length} = i \land \operatorname{IsUnbordered} u \land v . \operatorname{length} = n - 2 \cdot i \land w = u ++ v ++ u$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_outerWords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.26 (outerWords_disjoint).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (i : \mathbb{N}) , \forall (j : \mathbb{N}) , (0 < i) \Rightarrow ((0 < j) \Rightarrow ((i \neq j) \Rightarrow (\operatorname{Disjoint} (\operatorname{outerWords} k n i) (\operatorname{outerWords} k n j))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.outerWords_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.27 (borderedWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{borderedWords} k n = ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))) . \operatorname{filter} (\operatorname{fun} w \mapsto \neg \operatorname{IsUnbordered} w)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.borderedWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed-length words that have a nonempty proper border.

**Theorem 1.28 (shortest_partition).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{borderedWords} k n = (\operatorname{Finset} . \operatorname{Icc} 1 ((\operatorname{Nat} . \operatorname{div} n 2))) . \operatorname{biUnion} (\operatorname{outerWords} k n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every bordered word has one shortest border length. Unbordered words and these outer-block families partition the words of fixed length. Nat.div is division in the natural numbers, rounded down.

**Definition 1.29 (q).**

$$\forall (k : \mathbb{N}) , \forall (u : \mathbb{N} \to \mathbb{N}) , q k u = \sum'_{j : \mathbb{N}} (u (j + 1) : \mathbb{R}) / (k : \mathbb{R}) ^{2 \cdot (j + 1)}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of q.

**Theorem 1.30 (unbordered_q_lt_one).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (q k (\operatorname{uCount} k) < 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.unbordered_q_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.31 (peelPairs).**

$$\forall (alpha : \operatorname{Type}) (w : \operatorname{List} alpha) , \operatorname{peelPairs} w = \operatorname{if} hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b \operatorname{then} 1 + \operatorname{peelPairs} (\operatorname{peeledCore} w hw) \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.peelPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of peelPairs.

**Theorem 1.32 (core_of_unbordered_outer).**

$$\forall (alpha : \operatorname{Type}) , \forall (u : \operatorname{List} alpha) , \forall (v : \operatorname{List} alpha) , (u \neq [ ]) \Rightarrow ((\operatorname{IsUnbordered} u) \Rightarrow (\forall (hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} (u ++ v ++ u) b) , \operatorname{peeledCore} (u ++ v ++ u) hw = v))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.core_of_unbordered_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.33 (tailWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (r : \mathbb{N}) , \operatorname{tailWords} k n r = ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))) . \operatorname{filter} (\operatorname{fun} w \mapsto r \leq \operatorname{peelPairs} w)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.tailWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of tailWords.

**Theorem 1.34 (mem_tailWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (r : \mathbb{N}) , \forall (w : \operatorname{List} (\operatorname{Fin} k)) , w \in \operatorname{tailWords} k n r \iff w . \operatorname{length} = n \land r \leq \operatorname{peelPairs} w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_tailWords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.35 (renewal_tail_count).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (r : \mathbb{N}) , (\operatorname{tailWords} k n (r + 1)) . \operatorname{card} = \sum_{i \in \operatorname{Finset} . \operatorname{Icc} 1 ((\operatorname{Nat} . \operatorname{div} n 2))} \operatorname{uCount} k i \cdot (\operatorname{tailWords} k (n - 2 \cdot i) r) . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.renewal_tail_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word with at least r+1 peeled pairs has one shortest unbordered outer block and a centre with at least r peeled pairs. Different shortest lengths give disjoint families. Nat.div is division in the natural numbers, rounded down.

**Theorem 1.36 (tailWords_zero).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{tailWords} k n 0 = (\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.tailWords_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.37 (qCoeff).**

$$\forall (k : \mathbb{N}) , \forall (i : \mathbb{N}) , \operatorname{qCoeff} k i = \operatorname{if} i = 0 \operatorname{then} 0 \operatorname{else} (\operatorname{uCount} k i : \mathbb{R}) / (k : \mathbb{R}) ^{2 \cdot i}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of qCoeff.

**Theorem 1.38 (qCoeff_nonneg).**

$$\forall (k : \mathbb{N}) , \forall (i : \mathbb{N}) , 0 \leq \operatorname{qCoeff} k i$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.39 (qCoeff_summable).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\operatorname{Summable} (\operatorname{qCoeff} k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.40 (tsum_qCoeff).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow ((\sum'_{i : \mathbb{N}} \operatorname{qCoeff} k i) = q k (\operatorname{uCount} k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.tsum_qCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.41 (q_nonneg).**

$$\forall (k : \mathbb{N}) , 0 \leq q k (\operatorname{uCount} k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.42 (qCoeff_recurrence).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\forall (n : \mathbb{N}) , (0 < n) \Rightarrow (\operatorname{qCoeff} k n = (1 - \sum_{i \in \operatorname{Finset} . \operatorname{Icc} 1 ((\operatorname{Nat} . \operatorname{div} n 2))} \operatorname{qCoeff} k i) / (k : \mathbb{R}) ^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments. Nat.div is division in the natural numbers, rounded down.

## References

- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsBPFactorization`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsBorder`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsShortestBorder`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.IsUnbordered`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.borderedWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.bpWidth`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.card_words`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.core_of_unbordered_outer`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.largestBPWidth`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.largestBPWidth_le_length`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.largest_eq_peelWidth`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.maximal_outer_unbordered`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_outerWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_tailWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_ubWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.mem_words`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.outerWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.outerWords_disjoint`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.peelPairs`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.peelWidth`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore_shorter`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.peeledCore_spec`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.q`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_nonneg`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_recurrence`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.qCoeff_summable`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.q_nonneg`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.renewal_tail_count`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortestBorder`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortestBorder_spec`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_border_le_half`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_border_unbordered`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.shortest_partition`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.tailWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.tailWords_zero`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.tsum_qCoeff`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.uCount`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.ubWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.unbordered_outer_shortest`
- Truth anchor: `D5/S1/Words/BlockPalindromes/GreedyRenewal.unbordered_q_lt_one`
- Dependency: [D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality](../../../S0/Computability/Coding/DepthBudgetIidGreedyOptimality.md)
