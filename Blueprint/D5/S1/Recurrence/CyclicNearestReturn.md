# Cyclic Nearest Returns

## Abstract

Finite linear orders carry mutually inverse cyclic nearest-return maps.

**Theorem 1.1 (Cyclic nearest-return specification).**

$$\forall S\subseteq\alpha\ \text{finite},\ S\neq\emptyset:\ (\forall x\in S,\ \operatorname{succ}_S(x)\in S)\ \land\ (\forall x\in S,\ \operatorname{pred}_S(x)\in S)\ \land\ (\forall x\in S,\ \operatorname{pred}_S(\operatorname{succ}_S(x))=x)\ \land\ (\forall x\in S,\ \operatorname{succ}_S(\operatorname{pred}_S(x))=x)\ \land\ (\forall x,y\in S,\ x<y\Rightarrow\neg\,(y<\operatorname{succ}_S(x)))\ \land\ (\forall x,y\in S,\ y<x\Rightarrow\neg\,(\operatorname{pred}_S(x)<y))\ \land\ \operatorname{succ}_S(\max S)=\min S\ \land\ \operatorname{pred}_S(\min S)=\max S$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CyclicNearestReturn.cyclic_nearest_return_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty finite subset of a linear order has a cyclic successor and predecessor. Both maps remain in the subset and are mutual inverses there. Away from the boundary they select the nearest point in the requested direction; at the maximum and minimum they wrap explicitly to the opposite endpoint.

## References

- Truth anchor: `D5/S1/Recurrence/CyclicNearestReturn.cyclic_nearest_return_spec`
