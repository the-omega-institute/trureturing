# Complement Encoding

## Abstract

Subtraction complement is involutive and determines its total.

**Theorem 1.1 (Complement encoding).**

$$\forall G, u, e\in G,\ c_u(0)=u \land c_u(u)=0 \land c_u(c_u(e))=e \land (\forall v, c_v=c_u \Rightarrow v=u),\ c_u(x):=u-x.$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/ComplementEncoding.complement_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an additive commutative group, complementing e relative to u is the subtraction u - e. The theorem records the endpoint values, the involution law, and recovery of u from the value at zero.

Pinned Mathlib was searched before proving. The exact algebraic hits were sub_zero, sub_self, and sub_sub_self; the proof is a direct application of these library lemmas. Repository searches found no existing declaration for this total-recovery complement statement.

This deposit closes only the complement-encoding clause at qdo-v1 theorem/38.1 for atom qdo-residual-ef4826943d8848ca382a11dd9ef8e07ab2930ca795c5645aeb15b92f5a4c0662. No claim is made about other residual clauses.

## References

- Truth anchor: `D5/S0/Conventions/ComplementEncoding.complement_encoding`
