# ForbiddenWordCounting

## Abstract

First-hit decompositions give the forbidden binary-word counting identity.

**Definition 1.1 (words).**

$$\forall m \in \mathbb{N},\; \operatorname{words}\left(m\right) = \operatorname{Finset}.\operatorname{image}(\operatorname{List}.\operatorname{ofFn}, (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right) \to Bool\right)))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.words` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of all functions from Fin m to Bool under List.ofFn is precisely the set of length-m binary lists, including the empty list when m is zero.

**Theorem 1.2 (mem_words).**

$$\forall m \in \mathbb{N},\; \forall u \in \operatorname{List}\left(Bool\right),\; (u \in \operatorname{words}\left(m\right)) \Leftrightarrow (\operatorname{List}.\operatorname{length}(u) = m)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.3 (omega).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{omega}\left(w, m\right) = \operatorname{Finset}.\operatorname{filter}((u:\operatorname{List}\left(Bool\right))\mapsto(\neg \operatorname{List}.\operatorname{IsInfix}(w, u)), \operatorname{words}\left(m\right))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.omega` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“For positive integer $n\geq1$ and any word $w$ of length $k$, denote by Ωₙʷ the set of words of length $n$ with no $w$ factor, i.e.” (Definition 2.1, p. 3.)

Words are List Bool, true is 1, and List.IsInfix is factor containment. The source definition at positive lengths is extended to length zero by the same filter.

**Theorem 1.4 (mem_omega).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall u \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; (u \in \operatorname{omega}\left(w, m\right)) \Leftrightarrow ((\operatorname{List}.\operatorname{length}(u) = m) \land (\neg \operatorname{List}.\operatorname{IsInfix}(w, u)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_omega` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.5 (rho).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{rho}\left(w, m\right) = \frac{\sum_{u \in \operatorname{omega}\left(w, m\right)} ((\operatorname{List}.\operatorname{count}(true, u):\mathbb{R}))}{(m:\mathbb{R}) \cdot (\operatorname{Finset}.\operatorname{card}(\operatorname{omega}\left(w, m\right)):\mathbb{R})}$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.rho` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“For any word $w$ and positive integer $n$, denote by $\rho_{n}^{w}$ the frequency of $1$s over all words in Ωₙʷ:” (Definition 2.4, pp. 3–4.) “Set $\rho^{w}=\lim_{n\to\infty} \rho_{n}^{w} \in [0,1]$ if it exists.” (p. 4.)

The quotient is the literal source sum divided by m times the number of avoiding words. List.count true counts ones. Counts are coerced into the reals; division is real division. The value at m = 0 is a totalization that has no effect on convergence.

**Definition 1.6 (IsBorder).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall b \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsBorder}\left(w, b\right)) \Leftrightarrow ((b \ne []) \land ((\operatorname{List}.\operatorname{IsPrefix}(b, w)) \land (\operatorname{List}.\operatorname{IsSuffix}(b, w))))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.IsBorder` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“Fix two words $v$, $w$ with $v \in \left\{0, 1\right\}^{k}$. Denote by $\mathcal{B}(v,w)$ the set of borders of $v$ and $w$:” (Definition 2.6, p. 4.)

The source border relation is specialized to v = w. Nonempty words are both a prefix and a suffix; the whole word is included.

**Definition 1.7 (BalancedBorders).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (\operatorname{BalancedBorders}\left(w\right)) \Leftrightarrow (\forall b \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsBorder}\left(w, b\right)) \Rightarrow (2 \cdot \operatorname{List}.\operatorname{count}(true, b) = \operatorname{List}.\operatorname{length}(b)))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.BalancedBorders` (`✓ std3`).

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“A word $w$ has balanced borders if for all $b \in \mathcal{B}(w,w)$, $|b| = 2|b|_{1}$.” (Definition 3.2, p. 9.)

The displayed equality has the two sides exchanged and uses List.count true for the number of ones.

**Theorem 1.8 (self_border).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow (\operatorname{IsBorder}\left(w, w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.self_border` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.9 (avoidCoeff).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{avoidCoeff}\left(w, m\right) = \sum_{u \in \operatorname{omega}\left(w, m\right)} (\operatorname{Polynomial}.\operatorname{X}^{\operatorname{List}.\operatorname{count}(true, u)})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.10 (avoidSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{avoidSeries}\left(w\right) = \operatorname{PowerSeries}.\operatorname{mk}(\operatorname{avoidCoeff}\left(w\right))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.11 (wordMonomial).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{wordMonomial}\left(w\right) = \operatorname{PowerSeries}.\operatorname{monomial}(\operatorname{List}.\operatorname{length}(w), \operatorname{Polynomial}.\operatorname{X}^{\operatorname{List}.\operatorname{count}(true, w)})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.wordMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.12 (avoidCoeff_zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow (\operatorname{avoidCoeff}\left(w, 0\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidCoeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty word is the unique length-zero word avoiding a nonempty forbidden word, and its weight is one.

**Definition 1.13 (letterSeries).**

$$\operatorname{letterSeries}\left(\right) = \operatorname{PowerSeries}.\operatorname{X} \cdot \operatorname{PowerSeries}.\operatorname{C}(1 + \operatorname{Polynomial}.\operatorname{X})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.letterSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.14 (borderLengths).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{borderLengths}\left(w\right) = \operatorname{Finset}.\operatorname{filter}((j:\mathbb{N})\mapsto((0 < j) \land (\operatorname{List}.\operatorname{IsSuffix}(\operatorname{List}.\operatorname{take}(j, w), w))), \operatorname{Finset}.\operatorname{range}(\operatorname{List}.\operatorname{length}(w) + 1))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.borderLengths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.15 (overlapSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{overlapSeries}\left(w\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} (\operatorname{PowerSeries}.\operatorname{monomial}(\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j), \operatorname{Polynomial}.\operatorname{X}^{\operatorname{List}.\operatorname{count}(true, \operatorname{List}.\operatorname{drop}(j, w))}))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.overlapSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.16 (countingIdentity).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (\operatorname{countingIdentity}\left(w\right)) \Leftrightarrow (\operatorname{avoidSeries}\left(w\right) \cdot \left(\left(1 - \operatorname{letterSeries}\left(\right)\right) \cdot \operatorname{overlapSeries}\left(w\right) + \operatorname{wordMonomial}\left(w\right)\right) = \operatorname{overlapSeries}\left(w\right))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.countingIdentity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.17 (imbalance).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall j \in \mathbb{N},\; \operatorname{imbalance}\left(w, j\right) = 2 \cdot (\operatorname{List}.\operatorname{count}(true, \operatorname{List}.\operatorname{take}(j, w)):\mathbb{Z}) - (\operatorname{List}.\operatorname{length}(\operatorname{List}.\operatorname{take}(j, w)):\mathbb{Z})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordCounting.imbalance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.18 (mem_borderLengths).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall j \in \mathbb{N},\; (j \in \operatorname{borderLengths}\left(w\right)) \Leftrightarrow ((0 < j) \land ((j \le \operatorname{List}.\operatorname{length}(w)) \land (\operatorname{List}.\operatorname{IsSuffix}(\operatorname{List}.\operatorname{take}(j, w), w))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_borderLengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.19 (forbidden_word_counting_identity).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow (\operatorname{avoidSeries}\left(w\right) \cdot \left(\left(1 - \operatorname{letterSeries}\left(\right)\right) \cdot \operatorname{overlapSeries}\left(w\right) + \operatorname{wordMonomial}\left(w\right)\right) = \operatorname{overlapSeries}\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.forbidden_word_counting_identity` (`✓ std3`). ∎

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

This is the cleared-denominator form of the generating function identity in Fact 2.9, p. 5. A word is either avoiding or has a unique first-hit prefix. Appending the forbidden word records an overlap with a border. The two decompositions give the identity coefficient by coefficient.

**Theorem 1.20 (full_mem_borderLengths).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow (\operatorname{List}.\operatorname{length}(w) \in \operatorname{borderLengths}\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.full_mem_borderLengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.21 (borderLengths_iff_border).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall b \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsBorder}\left(w, b\right)) \Leftrightarrow (\exists j \in \mathbb{N},\; (j \in \operatorname{borderLengths}\left(w\right)) \land (b = \operatorname{List}.\operatorname{take}(j, w)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.borderLengths_iff_border` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.22 (omega_nonempty).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; (w \ne []) \Rightarrow (\operatorname{Finset}.\operatorname{Nonempty}(\operatorname{omega}\left(w, m\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordCounting.omega_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

## References

- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.BalancedBorders`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.IsBorder`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidCoeff`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidCoeff_zero`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.avoidSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.borderLengths`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.borderLengths_iff_border`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.countingIdentity`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.forbidden_word_counting_identity`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.full_mem_borderLengths`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.imbalance`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.letterSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_borderLengths`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_omega`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.mem_words`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.omega`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.omega_nonempty`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.overlapSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.rho`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.self_border`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.wordMonomial`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordCounting.words`
