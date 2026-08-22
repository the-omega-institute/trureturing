# Ambient Complement Dependence

## Abstract

Subtraction complement is defined only relative to an explicit ambient total.

**Theorem 1.1 (Absolute complement requires an ambient total).**

$$\begin{gathered}\forall G, u, v, e\in G,\\{}(c_u(e) = c_v(e) \iff u = v) \land\\{}(c_u = c_v \iff u = v),\\{}c_u(x) := u - x.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/AmbientComplementDependence.absolute_complement_requires_ambient_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be an additive commutative group and let c_u(e) = u - e. At every fixed argument e, two complement values agree exactly when their ambient totals agree.

The same equivalence holds for the whole complement operations. The reverse direction applies the frozen complement-encoding theorem, which recovers the ambient total by evaluating the operation at zero.

Thus the formal operation always carries an explicit total parameter; there is no additional untyped complement term in this statement.

## References

- Truth anchor: `D5/S0/Conventions/AmbientComplementDependence.absolute_complement_requires_ambient_total`
- Dependency: [D5/S0/Conventions/ComplementEncoding](ComplementEncoding.md)
