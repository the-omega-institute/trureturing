# Rank-Three Block Avoidance Counts

## Abstract

The distinct-closure incidence counts in the rank-three argument are inconsistent.

**Theorem 1.1 (Two uniform incidence counts cannot coexist).**

$$\forall (b : \mathbb{N}) , \forall (m : \mathbb{N}) , \forall (d : \mathbb{N}) , 2 \le b \land 2 \le m \land (b \cdot (d - 1)) = (m - 1) \land (((b + m) - 1) \cdot (d - 1)) = (m - 1) \implies False.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/RankThreeBlockAvoidance.incidence_count_contradiction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the distinct-closure branch, b is the size of an original block, m is the number of blocks, and d is the common number of closures through a point. The two counts are b(d-1)=m-1 and (b+m-1)(d-1)=m-1. If b and m are both at least two, subtracting the equations forces (m-1)(d-1)=0; each factor is then handled by the corresponding positivity hypothesis. This is the arithmetic core of the c=1 avoidance step; the matroid and duplicate-closure hypotheses remain outside this module.

## References

- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.incidence_count_contradiction`
