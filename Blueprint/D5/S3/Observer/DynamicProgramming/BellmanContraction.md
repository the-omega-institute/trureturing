# Bellman Contraction

## Abstract

The discounted Bellman operator is a strict contraction with prediction distance as its unique fixed point.

**Theorem 1.1 (The Bellman operator contracts to the prediction distance).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall \gamma\in(0, 1), \forall a, b\in O, 0\leq d_{O}(a, b)\leq D \Rightarrow \operatorname{Contracting}(T_{\gamma}, \gamma) \land \forall p, (T_{\gamma}(p)=p \Leftrightarrow p=d_{\gamma}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/BellmanContraction.bellman_operator_contracting_unique_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite nonempty state space. Fix an update, a readout, and a nonnegative real discrepancy bounded by D. For a discount factor gamma strictly between zero and one, the Bellman operator takes the maximum of the current discrepancy and the discounted continuation value.

The max operation is nonexpansive, while the continuation term multiplies uniform distance by gamma. Hence the operator is a strict contraction. The previously established Bellman equation makes discounted prediction distance a fixed point, and contraction uniqueness identifies it as the only fixed point.

Pinned Mathlib and Loogle supplied ContractingWith.fixedPoint_unique' and abs_max_sub_max_le_abs, both applied by the module. Repository search found the Bellman equation but no contraction or unique fixed-point theorem for this operator. LeanSearch returned HTTP 404.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/BellmanContraction.bellman_operator_contracting_unique_fixed_point`
