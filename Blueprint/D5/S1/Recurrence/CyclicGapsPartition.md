# Cyclic Gap Partition

## Abstract

Positive cyclic gaps partition the unit circle.

**Theorem 1.1 (Cyclic gaps partition the circle).**

$$\forall S\subseteq[0,1)\ \text{finite},\ S\neq\emptyset,\ (\forall x\in\mathbb{R},\ g_S(x)=\begin{cases}(1-x)+\min S,&x=\max S\\\operatorname{succ}_S(x)-x,&x\neq\max S\end{cases}):\ (\forall x\in S,\ \operatorname{succ}_S(x)\in S)\ \land\ (\forall x\in S,\ g_S(x)>0)\ \land\ \sum_{x\in S}g_S(x)=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CyclicGapsPartition.cyclic_gaps_partition_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite subset of the half-open unit interval, each cyclic successor remains in the subset and every clockwise gap is strictly positive. The successor and predecessor are inverse permutations of the subset, so successor terms cancel against the original points in the total sum. The unique wrap correction then contributes exactly one, and all gaps sum to the circumference.
