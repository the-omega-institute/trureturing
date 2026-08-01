# Cyclic Nearest Returns

## Abstract

Finite linear orders carry mutually inverse cyclic nearest-return maps.

**Theorem 1.1 (Cyclic nearest-return specification).**

$$\operatorname{pred}_S(\operatorname{succ}_S(x))=x,\qquad \operatorname{succ}_S(\operatorname{pred}_S(x))=x,\qquad \operatorname{succ}_S(\max S)=\min S,\qquad \operatorname{pred}_S(\min S)=\max S.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CyclicNearestReturn.cyclic_nearest_return_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty finite subset of a linear order has a cyclic successor and predecessor. Both maps remain in the subset and are mutual inverses there. Away from the boundary they select the nearest point in the requested direction; at the maximum and minimum they wrap explicitly to the opposite endpoint.
