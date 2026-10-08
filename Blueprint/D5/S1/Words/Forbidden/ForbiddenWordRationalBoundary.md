# ForbiddenWordRationalBoundary

## Abstract

The avoidance denominator vanishes at the reciprocal growth rate.

**Definition 1.1 (seriesEval).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{R}\right),\; \forall x \in \mathbb{R},\; \operatorname{seriesEval}\left(f, x\right) = \sum'_{m:\mathbb{N}} (\operatorname{PowerSeries}.\operatorname{coeff}(m, f) \cdot x^{m})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.seriesEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.2 (realCountSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{realCountSeries}\left(w\right) = \operatorname{PowerSeries}.\operatorname{mk}(\operatorname{avoidCount}\left(w\right))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realCountSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.3 (realImbalanceSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{realImbalanceSeries}\left(w\right) = \operatorname{PowerSeries}.\operatorname{mk}((m:\mathbb{N})\mapsto(2 \cdot \operatorname{avoidOnes}\left(w, m\right) - (m:\mathbb{R}) \cdot \operatorname{avoidCount}\left(w, m\right)))$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realImbalanceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.4 (overlapEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{overlapEval}\left(w, x\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} (x^{\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j)})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.5 (denomEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{denomEval}\left(w, x\right) = \left(1 - 2 \cdot x\right) \cdot \operatorname{overlapEval}\left(w, x\right) + x^{\operatorname{List}.\operatorname{length}(w)}$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.6 (overlapMomentEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{overlapMomentEval}\left(w, x\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} (\left(2 \cdot (\operatorname{List}.\operatorname{count}(true, \operatorname{List}.\operatorname{drop}(j, w)):\mathbb{R}) - (\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j):\mathbb{R})\right) \cdot x^{\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j)})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapMomentEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.7 (denomMomentEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{denomMomentEval}\left(w, x\right) = \left(1 - 2 \cdot x\right) \cdot \operatorname{overlapMomentEval}\left(w, x\right) + \left(2 \cdot (\operatorname{List}.\operatorname{count}(true, w):\mathbb{R}) - (\operatorname{List}.\operatorname{length}(w):\mathbb{R})\right) \cdot x^{\operatorname{List}.\operatorname{length}(w)}$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomMomentEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.8 (unbalanced_boundary_moment_ne_zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall z \in \mathbb{R},\; (3 \le \operatorname{List}.\operatorname{length}(w)) \Rightarrow ((\neg \operatorname{BalancedBorders}\left(w\right)) \Rightarrow ((\frac{3}{2} < z) \Rightarrow ((z < 2) \Rightarrow ((\left(2 - z\right) \cdot \operatorname{corrEval}\left(w, z\right) = z) \Rightarrow (\operatorname{denomMomentEval}\left(w, \frac{1}{z}\right) \ne 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.unbalanced_boundary_moment_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a correlation root between 3/2 and 2, reciprocal evaluation converts the nonzero signed border polynomial into a nonzero denominator moment.

**Theorem 1.9 (scalar_counting_identity).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall x \in \mathbb{R},\; (0 \le x) \Rightarrow ((\operatorname{growthRate}\left(w, hw\right) \cdot x < 1) \Rightarrow (\operatorname{seriesEval}\left(\operatorname{realCountSeries}\left(w\right), x\right) \cdot \operatorname{denomEval}\left(w, x\right) = \operatorname{overlapEval}\left(w, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_counting_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the first-hit identity at a nonnegative point inside the growth radius gives the count-series identity. The summability hypotheses are derived from avoidance growth.

**Definition 1.10 (lengthMoment).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{R}\right),\; \operatorname{lengthMoment}\left(f\right) = \operatorname{PowerSeries}.\operatorname{X} \cdot \operatorname{PowerSeries}.\operatorname{derivative}(\mathbb{R}, f)$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.lengthMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.11 (coeff_lengthMoment).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{R}\right),\; \forall m \in \mathbb{N},\; \operatorname{PowerSeries}.\operatorname{coeff}(m, \operatorname{lengthMoment}\left(f\right)) = (m:\mathbb{R}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}(m, f)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.coeff_lengthMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.12 (realLengthSeries).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{realLengthSeries}\left(w\right) = \operatorname{lengthMoment}\left(\operatorname{realCountSeries}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realLengthSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.13 (overlapLengthEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{overlapLengthEval}\left(w, x\right) = \sum_{j \in \operatorname{borderLengths}\left(w\right)} ((\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j):\mathbb{R}) \cdot x^{\operatorname{Nat}.\operatorname{sub}(\operatorname{List}.\operatorname{length}(w), j)})$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapLengthEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Definition 1.14 (denomLengthEval).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; \operatorname{denomLengthEval}\left(w, x\right) = -2 \cdot x \cdot \operatorname{overlapEval}\left(w, x\right) + \left(1 - 2 \cdot x\right) \cdot \operatorname{overlapLengthEval}\left(w, x\right) + (\operatorname{List}.\operatorname{length}(w):\mathbb{R}) \cdot x^{\operatorname{List}.\operatorname{length}(w)}$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomLengthEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.15 (scalar_length_identity).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall x \in \mathbb{R},\; (0 \le x) \Rightarrow ((\operatorname{growthRate}\left(w, hw\right) \cdot x < 1) \Rightarrow (\operatorname{seriesEval}\left(\operatorname{realLengthSeries}\left(w\right), x\right) \cdot \operatorname{denomEval}\left(w, x\right) + \operatorname{seriesEval}\left(\operatorname{realCountSeries}\left(w\right), x\right) \cdot \operatorname{denomLengthEval}\left(w, x\right) = \operatorname{overlapLengthEval}\left(w, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_length_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The length moment multiplies the coefficient of degree m by m. Its product rule turns the scalar count identity into the displayed length-weighted identity inside the growth radius.

**Theorem 1.16 (scalar_moment_identity).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall x \in \mathbb{R},\; (0 \le x) \Rightarrow ((\operatorname{growthRate}\left(w, hw\right) \cdot x < 1) \Rightarrow (\operatorname{seriesEval}\left(\operatorname{realImbalanceSeries}\left(w\right), x\right) \cdot \operatorname{denomEval}\left(w, x\right) + \operatorname{seriesEval}\left(\operatorname{realCountSeries}\left(w\right), x\right) \cdot \operatorname{denomMomentEval}\left(w, x\right) = \operatorname{overlapMomentEval}\left(w, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_moment_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed moment replaces each coefficient by twice the number of ones minus the total length. Its product rule gives the displayed signed identity inside the growth radius.

**Definition 1.17 (growthApproach).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall m \in \mathbb{N},\; \operatorname{growthApproach}\left(w, hw, m\right) = \frac{1 - \frac{1}{(m:\mathbb{R}) + 2}}{\operatorname{growthRate}\left(w, hw\right)}$$

*Formalization.* `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.18 (growthApproach_pos).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall m \in \mathbb{N},\; 0 < \operatorname{growthApproach}\left(w, hw, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.19 (growthApproach_inside).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall m \in \mathbb{N},\; \operatorname{growthRate}\left(w, hw\right) \cdot \operatorname{growthApproach}\left(w, hw, m\right) < 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_inside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.20 (growthApproach_tendsto).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \operatorname{Tendsto}\left(\operatorname{growthApproach}\left(w, hw\right), atTop, \operatorname{nhds}\left(\frac{1}{\operatorname{growthRate}\left(w, hw\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.21 (overlapEval_ge_one).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall x \in \mathbb{R},\; (w \ne []) \Rightarrow ((0 \le x) \Rightarrow (1 \le \operatorname{overlapEval}\left(w, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapEval_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.22 (countSeriesEval_growthApproach).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \forall m \in \mathbb{N},\; (m:\mathbb{R}) + 2 \le \operatorname{seriesEval}\left(\operatorname{realCountSeries}\left(w\right), \operatorname{growthApproach}\left(w, hw, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.countSeriesEval_growthApproach` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.23 (growthRadius_denominator_zero).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \operatorname{denomEval}\left(w, \frac{1}{\operatorname{growthRate}\left(w, hw\right)}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRadius_denominator_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miklós Bóna, Balázs Maga, Jacob Richey (2026). *Letter frequency in shifts of finite type with one forbidden word*. URL: <https://arxiv.org/abs/2606.06655v2>.

*Commentary.*

The lower bound on the counts forces the scalar series to diverge along growthApproach. The counting identity bounds its denominator by a quantity tending to zero. Continuity gives vanishing at the reciprocal growth rate, without a Pringsheim assumption.

**Theorem 1.24 (growthRate_root).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), \left(2 - \operatorname{growthRate}\left(w, hw\right)\right) \cdot \operatorname{corrEval}\left(w, \operatorname{growthRate}\left(w, hw\right)\right) = \operatorname{growthRate}\left(w, hw\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRate_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses the literal binary-word counts and border operations. All counts in real or rational arithmetic carry the displayed coercions. Nat.sub denotes truncated subtraction. All hypotheses and parameters have their displayed domains.

**Theorem 1.25 (growthRate_gt_three_halves).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall (hw:(w \ne [])), (3 \le \operatorname{List}.\operatorname{length}(w)) \Rightarrow (\frac{3}{2} < \operatorname{growthRate}\left(w, hw\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRate_gt_three_halves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For words of length at least three, a root lies strictly between 3/2 and 2. The convergent scalar counting identity excludes a larger reciprocal radius, placing the growth rate above that root.

## References

- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.coeff_lengthMoment`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.countSeriesEval_growthApproach`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomLengthEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.denomMomentEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_inside`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_pos`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthApproach_tendsto`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRadius_denominator_zero`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRate_gt_three_halves`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.growthRate_root`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.lengthMoment`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapEval_ge_one`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapLengthEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.overlapMomentEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realCountSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realImbalanceSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.realLengthSeries`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_counting_identity`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_length_identity`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.scalar_moment_identity`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.seriesEval`
- Truth anchor: `D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary.unbalanced_boundary_moment_ne_zero`
- Dependency: [D5/S1/Words/Forbidden/BalancedBordersHalfFrequency](BalancedBordersHalfFrequency.md)
