# BorderImbalanceExclusion

## Abstract

The longest nonzero border imbalance excludes cancellation at the growth root.

**Definition 1.1 (signedCoeff).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall j \in \mathbb{N},\; \operatorname{signedCoeff}\left(w, j\right) = \operatorname{ite}(j \in \operatorname{borderLengths}\left(w\right),(\operatorname{imbalance}\left(w, j\right):\mathbb{R}),0)$$

*Formalization.* `D5/S1/Words/Forbidden/BorderImbalanceExclusion.signedCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.2 (corrEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{corrEval}\left(w, x\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} (x^{j})$$

*Formalization.* `D5/S1/Words/Forbidden/BorderImbalanceExclusion.corrEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.3 (hEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{hEval}\left(w, x\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}(\operatorname{List}.\operatorname{length}(w) + 1)} (\operatorname{signedCoeff}\left(w, j\right) \cdot x^{j})$$

*Formalization.* `D5/S1/Words/Forbidden/BorderImbalanceExclusion.hEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.4 (balanced_iff_imbalance_zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (\operatorname{BalancedBorders}\left(w\right)) \Leftrightarrow (\forall j \in \mathbb{N},\; (j \in \operatorname{borderLengths}\left(w\right)) \Rightarrow (\operatorname{imbalance}\left(w, j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.balanced_iff_imbalance_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.5 (corrEval_ge_full).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; (w \ne []) \Rightarrow ((0 \le x) \Rightarrow (x^{\operatorname{List}.\operatorname{length}(w)} \le \operatorname{corrEval}\left(w, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.corrEval_ge_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.6 (root_equation_envelope).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; (w \ne []) \Rightarrow ((1 < x) \Rightarrow ((x < 2) \Rightarrow ((\left(2 - x\right) \cdot \operatorname{corrEval}\left(w, x\right) = x) \Rightarrow (\left(2 - x\right) \cdot x^{\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), 1)} \le 1))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.root_equation_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full-word border contributes x raised to the word length to the correlation sum. Positivity of all border contributions gives the displayed root envelope.

**Theorem 1.7 (hEval_eq_border_sum).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{hEval}\left(w, x\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} ((\operatorname{imbalance}\left(w, j\right):\mathbb{R}) \cdot x^{j})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.hEval_eq_border_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.8 (flip_flip).**

$$\forall u \in \operatorname{List}\left(Bool\right),\; \operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, \operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, u)) = u$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.flip_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.9 (flip_infix_iff).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall u \in \operatorname{List}\left(Bool\right),\; (\operatorname{List}.\operatorname{IsInfix}(\operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, w), \operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, u))) \Leftrightarrow (\operatorname{List}.\operatorname{IsInfix}(w, u))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.flip_infix_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.10 (count_flip).**

$$\forall u \in \operatorname{List}\left(Bool\right),\; \operatorname{List}.\operatorname{count}(true, \operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, u)) = \operatorname{List}.\operatorname{count}(false, u)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.count_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.11 (unbalanced_hEval_ne_zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; (\neg \operatorname{BalancedBorders}\left(w\right)) \Rightarrow ((1 < x) \Rightarrow ((x < 2) \Rightarrow ((\left(2 - x\right) \cdot x^{\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), 1)} \le 1) \Rightarrow (\operatorname{hEval}\left(w, x\right) \ne 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BorderImbalanceExclusion.unbalanced_hEval_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

Choose the longest border whose imbalance is nonzero and complement the bits to make its imbalance positive. Prefix count differences bound every shorter coefficient. The resulting lower polynomial is strictly positive under the root envelope, so mixed positive and negative border biases cannot cancel.

## References

- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.balanced_iff_imbalance_zero`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.corrEval`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.corrEval_ge_full`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.count_flip`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.flip_flip`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.flip_infix_iff`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.hEval`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.hEval_eq_border_sum`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.root_equation_envelope`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.signedCoeff`
- Truth anchor: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.unbalanced_hEval_ne_zero`
- Dependency: [D5/S1/Words/Forbidden/ForbiddenWordCounting](ForbiddenWordCounting.md)
