# Records of a two-term moving average

## Abstract

The record probability of two successive iid summands is at most 3/(2n) for every atomless real probability law and n at least 3.

**Definition 1.1 (The record probability).**

$$\forall mu \in \operatorname{MeasureTheory}.\operatorname{Measure}\left(\mathbb{R}\right),\; \forall n \in \mathbb{N},\; \operatorname{recordProb}\left(mu, n\right) = \operatorname{ENNReal}.\operatorname{toReal}\left(\operatorname{Measure}.\operatorname{pi}\left(\lambda (.:\operatorname{Fin}\left(n\right)) \mapsto mu\right)\left(\{x:\operatorname{Fin}\left(n\right) \to \mathbb{R} \mid \forall i \in \operatorname{Fin}\left(n\right),\; (1 \le \operatorname{val}\left(i\right)) \Rightarrow ((\operatorname{val}\left(i\right) + 2 \le n) \Rightarrow (x\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{val}\left(i\right) - 1\right):\operatorname{Fin}\left(n\right))\right) + x\left(i\right) < x\left((\operatorname{Fin}.\operatorname{mk}\left(n - 2\right):\operatorname{Fin}\left(n\right))\right) + x\left((\operatorname{Fin}.\operatorname{mk}\left(n - 1\right):\operatorname{Fin}\left(n\right))\right)))\}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.recordProb` (`✓ std3`).

*Citation.* C. Godrèche and J.-M. Luck (2020). *Records for the moving average of a time series*. DOI: [10.1088/1742-5468/ab5d08](https://doi.org/10.1088/1742-5468/ab5d08). URL: <https://arxiv.org/abs/1907.07598>.

*Commentary.*

Section 1, p. 2: "In the present work we investigate the statistics of records for sequences made of sums of p successive iid positive random variables, defined as follows. For p = 2," Equation (1.4) is Y₂=X₁+X₂, Y₃=X₂+X₃, …, Yₙ=Xₙ₋₁+Xₙ, …. Equation (1.7) is Qₙ=Prob(Yₙ>Lₙ₋₁). Page 3 specifies "where records are counted from the first complete sum Y₂ onwards." Thus Qₙ is the strict record probability of the terminal moving sum. In the displayed real-coordinate expression, x(i) is X_(i+1), and i runs from 1 through n−2. Measure.pi is the finite iid product measure. The anonymous dot in its lambda denotes an unused index. Fin.mk displays the value field of each finite index; proof fields are suppressed. The two index inequalities imply n≥3 and all constructor bounds. Subtraction in the index values is natural-number truncated subtraction. ENNReal.toReal gives a real probability for probability measures.

In the source notation, $Q_{n} = \operatorname{Pr}\left(Y_{n} > \max\left(Y_{2}, ..., Y_{n - 1}\right)\right)$.

**Definition 1.2 (The density upper-bound statement).**

$$claim = \left(\forall f \in \mathbb{R} \to \mathbb{R},\; (\operatorname{Continuous}\left(f\right)) \Rightarrow ((\forall x \in \mathbb{R},\; 0 \le f\left(x\right)) \Rightarrow (\forall mu \in \operatorname{MeasureTheory}.\operatorname{Measure}\left(\mathbb{R}\right),\; (mu = \operatorname{MeasureTheory}.\operatorname{volume}.\operatorname{withDensity}\left(\lambda (x:\mathbb{R}) \mapsto \operatorname{ENNReal}.\operatorname{ofReal}\left(f\left(x\right)\right)\right)) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure}\left(mu\right)) \Rightarrow ((mu\left(\operatorname{Set}.\operatorname{Iic}\left((0:\mathbb{R})\right)\right) = 0) \Rightarrow (\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow (\operatorname{recordProb}\left(mu, n\right) \le \frac{3}{2 \cdot (n:\mathbb{R})}))))))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.claim` (`✓ std3`).

*Citation.* C. Godrèche and J.-M. Luck (2020). *Records for the moving average of a time series*. DOI: [10.1088/1742-5468/ab5d08](https://doi.org/10.1088/1742-5468/ab5d08). URL: <https://arxiv.org/abs/1907.07598>.

*Commentary.*

Section 6.6, p. 31, after equation (6.33): "Finally, the data shown in figure 1 suggest that (6.33) provides an absolute upper bound for Qₙ." Equation (6.33) on p. 30 gives Qₙ=3/(2n) for n≥3 in the exponentially broad limit. Here `Continuous f` is the density restriction fixed by preregistration #15864; the public atomless theorem covers the paper's broader domain. The moving sums and record event are those of equations (1.4), (1.7) and the first-complete-sum sentence on p. 3. The displayed cast of n to the real numbers makes real division explicit.

**Theorem 1.3 (The atomless-law bound).**

$$\forall mu \in \operatorname{MeasureTheory}.\operatorname{Measure}\left(\mathbb{R}\right),\; [\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure}\left(mu\right)] (\operatorname{MeasureTheory}.\operatorname{NoAtoms}\left(mu\right)) \Rightarrow (\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow (\operatorname{recordProb}\left(mu, n\right) \le \frac{3}{2 \cdot (n:\mathbb{R})}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.movingAverage_record_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Godrèche and J.-M. Luck (2020). *Records for the moving average of a time series*. DOI: [10.1088/1742-5468/ab5d08](https://doi.org/10.1088/1742-5468/ab5d08). URL: <https://arxiv.org/abs/1907.07598>.

*Commentary.*

For n≥3, two distinct cyclic edge sums have a coordinate appearing in only one edge, so atomlessness makes their equality a null event. Rotation of the iid coordinates preserves their product measure and assigns probability 1/n to each position of the unique cyclic maximum. The record event splits, outside the null tie set, into a maximum at edge n−2 and a runner-up at edge n−2 below the maximum at edge n−1. Reversal fixes edge n−1 and exchanges edge n−2 with edge 0. These two runner-up events have equal probability and are disjoint within a maximum event of probability 1/n. Consequently the runner-up contribution is at most 1/(2n), giving 3/(2n). NoAtoms means every singleton has measure zero. Positivity and a density are unnecessary for this theorem.

**Theorem 1.4 (The density statement follows).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/godreche-luck-2020-moving-average-record-bound` (proved) by `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"godreche-luck-2020-moving-average-record-bound","declaration_gid":"D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Godrèche and J.-M. Luck (2020). *Records for the moving average of a time series*. DOI: [10.1088/1742-5468/ab5d08](https://doi.org/10.1088/1742-5468/ab5d08). URL: <https://arxiv.org/abs/1907.07598>.

*Commentary.*

A law obtained from Lebesgue measure by withDensity is atomless. Applying the atomless-law bound therefore proves claim. The continuity, nonnegativity and positive-support assumptions express the source's setting; the atomless estimate needs only the probability law.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.movingAverage_record_bound`
- Truth anchor: `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.recordProb`
- Truth anchor: `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result`
