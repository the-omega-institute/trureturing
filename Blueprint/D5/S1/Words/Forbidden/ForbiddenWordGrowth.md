# ForbiddenWordGrowth

## Abstract

Avoidance growth and escaping weighted averages control the boundary limit.

**Definition 1.1 (avoidCount).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{avoidCount}\left(w, m\right) = (\operatorname{Finset}.\operatorname{card}(\operatorname{omega}\left(w, m\right)):\mathbb{R})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.2 (avoidCount_pos).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; (w \ne []) \Rightarrow (0 < \operatorname{avoidCount}\left(w, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.3 (avoidCount_submultiplicative).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{avoidCount}\left(w, m + n\right) \le \operatorname{avoidCount}\left(w, m\right) \cdot \operatorname{avoidCount}\left(w, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_submultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.4 (log_avoidCount_subadditive).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; (w \ne []) \Rightarrow (\operatorname{Subadditive}\left((m:\mathbb{N})\mapsto(\operatorname{Real}.\operatorname{log}(\operatorname{avoidCount}\left(w, m\right)))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.log_avoidCount_subadditive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.5 (growthRate).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \operatorname{growthRate}\left(w, hw\right) = \operatorname{Real}.\operatorname{exp}(\operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}((n:\mathbb{N})\mapsto(\frac{\operatorname{Real}.\operatorname{log}(\operatorname{avoidCount}\left(w, n\right))}{(n:\mathbb{R})}), \operatorname{Set}.\operatorname{Ici}(1))\right))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponential of the logarithmic Fekete limit is the avoidance growth rate. The proof argument hw certifies nonemptiness.

**Theorem 1.6 (growthRate_lower_power).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall m \in \mathbb{N},\; \operatorname{growthRate}\left(w, hw\right)^{m} \le \operatorname{avoidCount}\left(w, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate_lower_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.7 (growthRate_lt_two).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \operatorname{growthRate}\left(w, hw\right) < 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate_lt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.8 (weighted_avoidCount_summable).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall q \in \mathbb{N},\; \forall x \in \mathbb{R},\; (0 \le x) \Rightarrow ((\operatorname{growthRate}\left(w, hw\right) \cdot x < 1) \Rightarrow (\operatorname{Summable}\left((m:\mathbb{N})\mapsto((m:\mathbb{R})^{q} \cdot \operatorname{avoidCount}\left(w, m\right) \cdot x^{m})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.weighted_avoidCount_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside the reciprocal growth radius, the counts are eventually bounded by a larger exponential rate whose product with x is less than one. Polynomial length weights remain summable.

**Theorem 1.9 (avoidCount_summable).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall x \in \mathbb{R},\; (0 \le x) \Rightarrow ((\operatorname{growthRate}\left(w, hw\right) \cdot x < 1) \Rightarrow (\operatorname{Summable}\left((m:\mathbb{N})\mapsto(\operatorname{avoidCount}\left(w, m\right) \cdot x^{m})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.10 (weighted_tsum_tendsto).**

$$\forall T \in Type,\; \forall F \in \operatorname{Filter}\left(T\right),\; \forall p \in T \to \left(\mathbb{N} \to \mathbb{R}\right),\; \forall u \in \mathbb{N} \to \mathbb{R},\; \forall L \in \mathbb{R},\; \forall B \in \mathbb{R},\; (\forall t \in T,\; \forall n \in \mathbb{N},\; 0 \le \operatorname{p}\left(t, n\right)) \Rightarrow ((\forall t \in T,\; \operatorname{Summable}\left(\operatorname{p}\left(t\right)\right)) \Rightarrow ((\forall t \in T,\; \sum'_{n:\mathbb{N}} (\operatorname{p}\left(t, n\right)) = 1) \Rightarrow ((0 \le B) \Rightarrow ((\forall n \in \mathbb{N},\; \left|\operatorname{u}\left(n\right) - L\right| \le B) \Rightarrow ((\operatorname{Tendsto}\left(u, atTop, \operatorname{nhds}\left(L\right)\right)) \Rightarrow ((\forall N \in \mathbb{N},\; \operatorname{Tendsto}\left((t:T)\mapsto(\sum_{n \in \operatorname{Finset}.\operatorname{range}(N)} (\operatorname{p}\left(t, n\right))), F, \operatorname{nhds}\left(0\right)\right)) \Rightarrow (\operatorname{Tendsto}\left((t:T)\mapsto(\sum'_{n:\mathbb{N}} (\operatorname{p}\left(t, n\right) \cdot \operatorname{u}\left(n\right))), F, \operatorname{nhds}\left(L\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.weighted_tsum_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weights are nonnegative, summable and have total one. Their mass on every finite initial segment tends to zero along F. A uniformly bounded error and convergence of u give convergence of the weighted averages to L. No nontriviality assumption on F is required.

**Theorem 1.11 (avoidOnes_bounds).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; (0 \le \operatorname{avoidOnes}\left(w, m\right)) \land (\operatorname{avoidOnes}\left(w, m\right) \le (m:\mathbb{R}) \cdot \operatorname{avoidCount}\left(w, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidOnes_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total number of ones is nonnegative and at most the length times the number of avoiding words.

**Definition 1.12 (avoidOnes).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{avoidOnes}\left(w, m\right) = \sum_{u \in \operatorname{omega}\left(w, m\right)} ((\operatorname{List}.\operatorname{count}(true, u):\mathbb{R}))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidOnes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

## References

- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_pos`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_submultiplicative`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidCount_summable`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidOnes`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.avoidOnes_bounds`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate_lower_power`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.growthRate_lt_two`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.log_avoidCount_subadditive`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.weighted_avoidCount_summable`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordGrowth.weighted_tsum_tendsto`
- Dependency: [D5/S1/Words/Forbidden/ForbiddenWordCounting](ForbiddenWordCounting.md)
