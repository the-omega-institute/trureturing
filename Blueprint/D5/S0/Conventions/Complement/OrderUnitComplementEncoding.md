# Order-Unit Complement Encoding

## Abstract

Effect-interval subtraction complement encodes its order-unit total.

**Theorem 1.1 (Order-unit complement encoding).**

$$\begin{gathered}V: \operatorname{OrderedVectorSpace}_{\mathbb{R}}, u, e\in V,\\{}{0 \leq u \land \forall x\in V, \exists r\in \mathbb{R}, 0 < r \land -ru \leq x \land x \leq ru} \land e\in [0, u] \Rightarrow\\{}c_u(0) = u \land\\{}c_u(u) = 0 \land\\{}c_u(c_u(e)) = e \land\\{}\forall v\in V, c_v = c_u \Rightarrow v = u,\\{}c_a(x) := a - x.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/Complement/OrderUnitComplementEncoding.order_unit_complement_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a real ordered vector space, let u satisfy the explicit order-unit domination condition, and let e lie in the effect interval from zero to u. Define c_u(x) = u - x.

The complement sends zero to u and u to zero, is involutive at e, and uniquely determines u: every candidate v inducing the same complement operation equals u. These are exactly the four conclusion leaves of the Lean declaration.

The declaration imports the repository's canonical complement and projects the endpoint, involution, and uniqueness laws from the frozen complement-encoding theorem. The ordered carrier conditions restrict the theorem to the source effect interval.

## References

- Truth anchor: `D5/S0/Conventions/Complement/OrderUnitComplementEncoding.order_unit_complement_encoding`
- Dependency: [D5/S0/Conventions/ComplementEncoding](../ComplementEncoding.md)
