# Rare-Edge Waiting Time

## Abstract

The rare opposite-to-peak edge has an almost surely finite waiting time with an exact mean and rational survival generating function.

**Theorem 1.1 (Finiteness, mean, and generating function).**

$$\operatorname{chi}(x) \in \{\pm 1\}, \operatorname{chi}(z)=1, \lvert X \rvert=2 M, \lvert \{\operatorname{chi}(x)=1\} \rvert=M, M\geq 2, q=\frac{r}{M-1}, 0<r<1, p=\frac{1}{2\lvert X \rvert} \Rightarrow \forall T, 0\le s_{T},\quad s_{T+1}\le s_{T},\quad \lim _{T\to \infty} s_{T}=0,\quad \sum_{T\geq 0} s_{T}=2\lvert X \rvert -1-r,\quad 0\le u\le 1 \Rightarrow \sum_{T\geq 0} s_{T} u^{T}=\frac{1-p u-p r u^{2}}{1-u+p(1-r) u^{2}+p r u^{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeWaitingMean.survival_waiting_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume chi takes the values 1 and -1, chi(z) = 1, |X| = 2M with M positive signs, M >= 2, q = r/(M-1) and 0 < r < 1. Then every survival mass is nonnegative, the sequence is nonincreasing, and it converges to zero. Thus the rare edge is reached almost surely.

The sum of the survival masses is the tail-sum identity for the waiting-time mean. It equals 2|X| - 1 - r.

For every u in [0,1], weighting the cubic survival recurrence by u^(T+3) and summing its three shifted tails gives the displayed rational generating function. At u = 1 it reduces to the tail-sum mean.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeWaitingMean.survival_waiting_mean`
- Dependency: [D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival](SinglePeakRareEdgeSurvival.md)
