# BalancedBordersHalfFrequency

## Abstract

Balanced borders force exact half frequency; short unbalanced words exclude it.

**Theorem 1.1 (rho_nonneg).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; 0 \le \operatorname{rho}\left(w, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.rho_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.2 (rho_le_one).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; (w \ne []) \Rightarrow ((0 < m) \Rightarrow (\operatorname{rho}\left(w, m\right) \le 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.rho_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.3 (singleton_not_tendsto_half).**

$$\forall b \in Bool,\; \neg \operatorname{Tendsto}\left(\operatorname{rho}\left([b]\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.singleton_not_tendsto_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.4 (flip_tendsto_half_iff).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow ((\operatorname{Tendsto}\left(\operatorname{rho}\left(\operatorname{List}.\operatorname{map}(\operatorname{Bool}.\operatorname{not}, w)\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)) \Leftrightarrow (\operatorname{Tendsto}\left(\operatorname{rho}\left(w\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.flip_tendsto_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complementing every bit bijects the avoiding words and replaces each positive-length average by one minus that average. Half-frequency convergence is preserved.

**Theorem 1.5 (onesTotal11_bound).**

$$\forall k \in \mathbb{N},\; (3 \cdot \operatorname{avoidOnes}\left([true, true], k + 2\right) \le (k + 2:\mathbb{R}) \cdot \operatorname{avoidCount}\left([true, true], k + 2\right)) \land (3 \cdot \operatorname{avoidOnes}\left([true, true], k + 3\right) \le (k + 3:\mathbb{R}) \cdot \operatorname{avoidCount}\left([true, true], k + 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.onesTotal11_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The avoiding words for 11 split into a word prefixed by 0 and a shorter word prefixed by 10. Their disjoint count and one-count recurrences give the two inequalities simultaneously by induction.

**Theorem 1.6 (not_tendsto_half_11).**

$$\neg \operatorname{Tendsto}\left(\operatorname{rho}\left([true, true]\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.not_tendsto_half_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence estimate bounds all positive-length averages from length two onward by 1/3, excluding convergence to 1/2.

**Definition 1.7 (signedMoment).**

$$\forall f \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \operatorname{signedMoment}\left(f\right) = \operatorname{PowerSeries}.\operatorname{mk}((n:\mathbb{N})\mapsto(2 \cdot \operatorname{Polynomial}.\operatorname{eval}(1, \operatorname{Polynomial}.\operatorname{derivative}(\operatorname{PowerSeries}.\operatorname{coeff}(n, f))) - (n:\mathbb{Q}) \cdot \operatorname{Polynomial}.\operatorname{eval}(1, \operatorname{PowerSeries}.\operatorname{coeff}(n, f))))$$

*Formalization.* `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.8 (signedMoment_add).**

$$\forall f \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \forall g \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \operatorname{signedMoment}\left(f + g\right) = \operatorname{signedMoment}\left(f\right) + \operatorname{signedMoment}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.9 (signedMoment_sub).**

$$\forall f \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \forall g \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \operatorname{signedMoment}\left(f - g\right) = \operatorname{signedMoment}\left(f\right) - \operatorname{signedMoment}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.10 (signedMoment_mul).**

$$\forall f \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \forall g \in \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \operatorname{signedMoment}\left(f \cdot g\right) = \operatorname{signedMoment}\left(f\right) \cdot \operatorname{PowerSeries}.\operatorname{map}(\operatorname{Polynomial}.\operatorname{evalRingHom}(1), g) + \operatorname{PowerSeries}.\operatorname{map}(\operatorname{Polynomial}.\operatorname{evalRingHom}(1), f) \cdot \operatorname{signedMoment}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.11 (signedMoment_one).**

$$\operatorname{signedMoment}\left(1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.12 (signedMoment_monomial).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{signedMoment}\left(\operatorname{PowerSeries}.\operatorname{monomial}(n, \operatorname{Polynomial}.\operatorname{X}^{k})\right) = \operatorname{PowerSeries}.\operatorname{monomial}(n, 2 \cdot (k:\mathbb{Q}) - (n:\mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.13 (signedMoment_letterSeries).**

$$\operatorname{signedMoment}\left(\operatorname{letterSeries}\left(\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_letterSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.14 (signedMoment_sum).**

$$\forall I \in Type,\; \forall S \in \operatorname{Finset}\left(I\right),\; \forall f \in I \to \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right),\; \operatorname{signedMoment}\left(\sum_{i \in S} (\operatorname{f}\left(i\right))\right) = \sum_{i \in S} (\operatorname{signedMoment}\left(\operatorname{f}\left(i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.15 (avoidDenominator).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{avoidDenominator}\left(w\right) = \left(1 - \operatorname{letterSeries}\left(\right)\right) \cdot \operatorname{overlapSeries}\left(w\right) + \operatorname{wordMonomial}\left(w\right)$$

*Formalization.* `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.avoidDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.16 (balanced_signedMoment_avoidSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow ((\operatorname{BalancedBorders}\left(w\right)) \Rightarrow (\operatorname{signedMoment}\left(\operatorname{avoidSeries}\left(w\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.balanced_signedMoment_avoidSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.17 (balanced_tendsto_half).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow ((\operatorname{BalancedBorders}\left(w\right)) \Rightarrow (\operatorname{Tendsto}\left(\operatorname{rho}\left(w\right), atTop, \operatorname{nhds}\left(\frac{1}{2}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.balanced_tendsto_half` (`✓ std3`). ∎

*Citation.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

“In particular, if $w$ has balanced borders, then $\rho^{w}=q^{w}=\frac{1}{2}$.” (Proposition 3.3, p. 9.)

Only the rho consequence is displayed. The proof gives rho w m = 1/2 for every positive m.

## References

- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.avoidDenominator`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.balanced_signedMoment_avoidSeries`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.balanced_tendsto_half`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.flip_tendsto_half_iff`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.not_tendsto_half_11`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.onesTotal11_bound`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.rho_le_one`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.rho_nonneg`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_add`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_letterSeries`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_monomial`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_mul`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_one`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_sub`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.signedMoment_sum`
- Truth anchor: `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.singleton_not_tendsto_half`
- Dependency: [D5/S1/Words/Forbidden/BorderImbalanceExclusion](BorderImbalanceExclusion.md)
- Dependency: [D5/S1/Words/Forbidden/ForbiddenWordGrowth](ForbiddenWordGrowth.md)
