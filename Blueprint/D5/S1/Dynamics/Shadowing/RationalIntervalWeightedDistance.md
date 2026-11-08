# Rational Interval Weighted Distance

## Abstract

The original all-integer geometric weighted sum is summable, continuous in the product topology, and bounded by its exact one-sided tail.

Let I=[0,1], S=(Z->I), and d be the inherited interval distance. At every integer j put w(j)=2^(-|j|)=(1/2)^|j|. Define D(x,y) as the infinite sum over all j in Z of w(j)d(x(j),y(j)). This is Artigue's original weighted-sum expression with the permitted parameter mu=1/2. All sums below are actual infinite sums; no coordinate cutoff or alternative product metric replaces D. The existing product topology suffices, and no new metric-space instance is installed.

**Theorem 1.1 (The complete integer weight series).**

$$\begin{aligned}HasSum(w,3)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.geometricWeight_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The nonnegative integer half has geometric sum two, and the strictly negative half has geometric sum one. The pinned integer HasSum decomposition joins these disjoint halves.

**Theorem 1.2 (Summability for every sequence pair).**

$$\begin{aligned}\forall x\in S, \forall y\in S, Summable((j\in \mathbb{Z}\mapsto w(j)d(x(j),y(j))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.weightedDistance_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Every interval distance is at most one. Thus the nonnegative series defining D is dominated by the summable original weight series.

**Theorem 1.3 (Product-topology continuity of the literal sum).**

$$\begin{aligned}\operatorname{Continuous}((x,y)\in S\times S\mapsto D(x,y))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.continuous_weightedDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Each weighted coordinate distance is continuous and uniformly bounded by w(j). The pinned continuous_tsum theorem applies with this summable majorant on S times S.

**Theorem 1.4 (Exact one-sided tail).**

$$\begin{aligned}\forall n\in \mathbb{N}, \sum_{j\in \mathbb{Z},j<-n}w(j)=\frac{1}{2}^{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.geometricWeight_negative_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The nonnegative integer half contributes zero. On j=-(k+1), the condition is n<=k and the weight is (1/2)^(k+1). Reuse the pinned geometric tail sum to obtain exactly (1/2)^n.

**Theorem 1.5 (Agreement on a half-line controls all earlier discrepancies).**

$$\begin{aligned}\forall n\in \mathbb{N}, \forall x\in S, \forall y\in S, (\forall j\in \mathbb{Z}, -n\le j\Rightarrow x(j)=y(j))\Rightarrow D(x,y)\le \frac{1}{2}^{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.weightedDistance_le_negative_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

All summands on j>=-n vanish. Every remaining distance is at most one, so comparison of genuinely summable series bounds D by the exact tail. This is the estimate needed for the original self-tuning antecedent once a counterwitness is shown to agree with its centered true orbit on that half-line. The counterwitness construction and its positive phase defect are not conclusions of this module.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.continuous_weightedDistance`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.geometricWeight_hasSum`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.geometricWeight_negative_tail`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.weightedDistance_le_negative_tail`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance.weightedDistance_summable`
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalAction](RationalIntervalAction.md)
