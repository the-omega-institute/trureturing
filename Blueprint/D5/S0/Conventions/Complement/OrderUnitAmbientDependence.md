# Order-Unit Ambient Dependence

## Abstract

An effect complement is relative to an explicit ambient order unit.

**Theorem 1.1 (Order-unit complement depends on its ambient total).**

$$\begin{gathered}V: \operatorname{OrderedVectorSpace}_{\mathbb{R}}, u, v, e\in V,\\{}{0 \leq u \land \forall x\in V, \exists r\in \mathbb{R}, 0 < r \land -ru \leq x \land x \leq ru} \land {0 \leq v \land \forall x\in V, \exists r\in \mathbb{R}, 0 < r \land -rv \leq x \land x \leq rv},\\{}e\in [0, u] \land e\in [0, v] \Rightarrow\\{}(c_u(e) \neq c_v(e) \iff u \neq v),\\{}c_u(e) := u - e.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/Complement/OrderUnitAmbientDependence.order_unit_complement_depends_on_ambient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a real ordered vector space. The public hypotheses state the order-unit role of u and v as two-sided domination by a positive real multiple, and require the effect e to lie in both closed intervals from zero to the corresponding ambient total.

For c_u(e) = u - e, the two complement values differ exactly when u and v differ. Thus the operation does not supply an ambient-free notion of complement; the total is an explicit part of its typed data.

The repository family definition ComplementEncoding.complement is imported directly. Pinned Mathlib provides IsOrderedModule, IsOrderedAddMonoid, Set.Icc, and sub_left_inj. Exact-name and case-insensitive searches found no OrderUnit or IsOrderUnit predicate, so the order-unit property remains an explicit public hypothesis rather than a silently weakened carrier.

## References

- Truth anchor: `D5/S0/Conventions/Complement/OrderUnitAmbientDependence.order_unit_complement_depends_on_ambient`
- Dependency: [D5/S0/Conventions/ComplementEncoding](../ComplementEncoding.md)
