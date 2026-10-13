# LargestFactorizationExpectedWidth

## Abstract

The expected largest block-palindrome width converges to the A274199 series.

**Definition 1.1 (tailProbability).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \forall (r : \mathbb{N}) , \operatorname{tailProbability} k n r = ((\operatorname{tailWords} k n r) . \operatorname{card} : \mathbb{R}) / (k : \mathbb{R}) ^{n}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.tailProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of tailProbability.

**Theorem 1.2 (renewal_tail_limit).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\forall (r : \mathbb{N}) , \operatorname{Tendsto} (\operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{tailProbability} k n r) \operatorname{atTop} (\operatorname{nhds} ((q k (\operatorname{uCount} k)) ^{r})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.renewal_tail_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact renewal recursion, summability of its coefficients, and dominated convergence give the r-th power of the unbordered-word mass as the limit.

**Definition 1.3 (peelCentre).**

$$\forall (alpha : \operatorname{Type}) (w : \operatorname{List} alpha) , \operatorname{peelCentre} w = \operatorname{if} hw : \exists (b : \operatorname{List} alpha) , \operatorname{IsBorder} w b \operatorname{then} \operatorname{peelCentre} (\operatorname{peeledCore} w hw) \operatorname{else} w$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.peelCentre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of peelCentre.

**Definition 1.4 (emptyWords).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{emptyWords} k n = ((\operatorname{DepthBudgetIidGreedyOptimality} . \operatorname{words} n : \operatorname{Finset} (\operatorname{List} (\operatorname{Fin} k)))) . \operatorname{filter} (\operatorname{fun} w \mapsto \operatorname{peelCentre} w = [ ])$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.emptyWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of emptyWords.

**Definition 1.5 (emptyProbability).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{emptyProbability} k n = ((\operatorname{emptyWords} k n) . \operatorname{card} : \mathbb{R}) / (k : \mathbb{R}) ^{n}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.emptyProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of emptyProbability.

**Definition 1.6 (QSeries).**

$$\forall (k : \mathbb{N}) , \operatorname{QSeries} k = \operatorname{PowerSeries} . \operatorname{mk} (\operatorname{qCoeff} k)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.QSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of QSeries.

**Definition 1.7 (ESeries).**

$$\forall (k : \mathbb{N}) , \operatorname{ESeries} k = \operatorname{PowerSeries} . \operatorname{mk} (\operatorname{fun} (m : \mathbb{N}) \mapsto \operatorname{emptyProbability} k (2 \cdot m))$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.ESeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of ESeries.

**Theorem 1.8 (empty_centre_powerSeries).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\operatorname{ESeries} k = (1 - \operatorname{QSeries} k) ^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.empty_centre_powerSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of degree m is the empty-centre probability at length 2m. Its convolution recursion gives the inverse of one minus the renewal series.

**Definition 1.9 (expectedWidth).**

$$\forall (k : \mathbb{N}) , \forall (n : \mathbb{N}) , \operatorname{expectedWidth} k n = \frac{\sum_{w : \operatorname{Fin} n \to \operatorname{Fin} k} (\operatorname{largestBPWidth} (\operatorname{List}.\operatorname{ofFn} w) : \mathbb{R})}{(k : \mathbb{R})^{n}}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.expectedWidth` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The source states (arXiv v2, p. 5): “From the definition of expected value, it follows that Eₙ,ₖ = (1/kⁿ)∑ᵢ₌₁ⁿ i·LBPₖ(n,i).” The cardinality counts length-n words whose largest BP-factorization has width i; the empty word has width zero.

**Theorem 1.10 (expectedWidth_limit).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\operatorname{Tendsto} (\operatorname{expectedWidth} k) \operatorname{atTop} (\operatorname{nhds} (2 / (1 - q k (\operatorname{uCount} k)) - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.expectedWidth_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The width equals twice the number of peeled pairs plus the indicator of a nonempty centre. Geometric domination of the tails and vanishing empty-centre probability give the stated limit.

**Definition 1.11 (claim).**

$$\operatorname{claim} \iff \forall (k : \mathbb{N}) , 2 \leq k \Rightarrow \exists (a : \mathbb{N} \to \mathbb{R}) , (\forall d , \operatorname{Tendsto} (\operatorname{fun} (N : \mathbb{N}) \mapsto (\operatorname{a274190} N (N - d) : \mathbb{R})) \operatorname{atTop} (\operatorname{nhds} (a d))) \land \operatorname{Summable} (\operatorname{fun} (i : \mathbb{N}) \mapsto 2 \cdot a (i + 1) / (k : \mathbb{R})^{i + 1}) \land \operatorname{Tendsto} (\operatorname{fun} n \mapsto \operatorname{expectedWidth} k n) \operatorname{atTop} (\operatorname{nhds} (1 + \sum'_{i : \mathbb{N}} 2 \cdot a (i + 1) / (k : \mathbb{R})^{i + 1}))$$

*Formalization.* `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.claim` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

Conjecture 5 (arXiv v2, §3, p. 5): “Let k ≥ 2. Then E_k = 1+∑_{i=1}^∞ a_i k^{-i} where the sequence (a_n/2)_{n≥1} is A274199 in the On-Line Encyclopedia of Integer Sequences (OEIS).” A274199(d) is the stabilized diagonal a274190 (2*d) d. The positive index is i+1, so the source expansion starts with coefficients 2,4,6,10.

**Theorem 1.12 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result` (`✓ std3`). ∎

*Resolves.* `Problems/gabric-shallit-2023-block-palindrome-expected-width` (proved) by `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gabric-shallit-2023-block-palindrome-expected-width","declaration_gid":"D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

For every alphabet size k≥2, every reverse-row coefficient converges, the positively indexed coefficient series is summable, and the expected largest width converges to one plus that series. The proof uses the exact renewal recursion and does not use the source Lemma 3.

## References

- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.ESeries`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.QSeries`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.claim`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.emptyProbability`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.emptyWords`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.empty_centre_powerSeries`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.expectedWidth`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.expectedWidth_limit`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.peelCentre`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.renewal_tail_limit`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result`
- Truth anchor: `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.tailProbability`
- Dependency: [D5/S1/Words/BlockPalindromes/CompositionInversion](CompositionInversion.md)
