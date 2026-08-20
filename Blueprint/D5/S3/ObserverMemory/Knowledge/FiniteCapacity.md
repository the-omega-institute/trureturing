# Finite Knowledge Capacity

## Abstract

Finite readout knowledge has dimension equal to the number of realized classes.

**Theorem 1.1 (Finite knowledge capacity counts realized readout classes).**

$$\forall X, Y_{0}, Y_{1}, q_{0}, q_{1}, h,\ (\operatorname{Finite}\left(X\right) \land \operatorname{Finite}\left(Y_{0}\right) \land \operatorname{Finite}\left(Y_{1}\right) \land q_{1} = h \circ q_{0}) \Rightarrow\\(\operatorname{dim}_{C} \operatorname{K}\left(q_{0}\right) = \lvert\operatorname{range}\left(q_{0}\right)\rvert \land\\\operatorname{dim}_{C} \operatorname{K}\left(q_{1}\right) = \lvert\operatorname{range}\left(q_{1}\right)\rvert \land\\\operatorname{dim}_{C} \operatorname{K}\left(q_{1}\right) \le \operatorname{dim}_{C} \operatorname{K}\left(q_{0}\right) \land\\\operatorname{dim}_{C} \operatorname{K}\left(q_{0}\right) - \operatorname{dim}_{C} \operatorname{K}\left(q_{1}\right) = \lvert\operatorname{range}\left(q_{0}\right)\rvert - \lvert\operatorname{range}\left(q_{1}\right)\rvert).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/FiniteCapacity.finite_knowledge_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X, Y0, and Y1 be finite types. A complex-valued world observable belongs to the knowledge space of q exactly when it is constant on every q-fiber, equivalently when it factors through q.

The pullback from all complex functions on the realized range of q is injective and has exactly that knowledge space as its range. Its dimension is therefore the cardinality of the realized range.

If q1 is obtained from q0 by a further readout map, the induced map from the realized q0 range onto the realized q1 range is surjective. Thus the later dimension cannot increase, and the dimension loss is the difference of the two realized-range cardinalities.

Loogle and pinned Mathlib returned exact hits LinearMap.finrank_range_of_inj, Module.finrank_fintype_fun_eq_card, Fintype.card_le_of_surjective, and Function.FactorsThrough. The Lean proof applies all four; no exact complete capacity theorem was found in Mathlib or the repository.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/FiniteCapacity.finite_knowledge_capacity`
