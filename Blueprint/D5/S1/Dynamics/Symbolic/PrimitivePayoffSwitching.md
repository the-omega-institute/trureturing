# Finite Endpoint Costs for Switching Payoffs

## Abstract

Reweighted switching costs bound mechanical endpoint minima and force bounded discrepancy.

A binary H window of length n is paired with a G response p of n + 1 Boolean vertices. The cost adds the signed discrepancy contribution of each source vertex and charges two for a switch. The sign σ takes values −1 and +1. The mechanical word M has slope α and intercept ρ. Its centered fractional part Q is evaluated at the path boundaries.

**Theorem 1.1 (Lower bound for every reweighted path).**

$$\forall (\alpha: \mathbb{R}), \forall (\rho: \mathbb{R}), (0 \le \alpha \land \alpha < 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (i: \mathbb{N}), \forall (p: Fin\left(n + 1\right) \to Bool), sign\left(p\left(0\right)\right) \cdot Q\left(\alpha, \rho, i\right) - sign\left(p\left(n\right)\right) \cdot Q\left(\alpha, \rho, i + n\right) \le cost\left(\alpha, M\left(\alpha, \rho, i, n\right), p\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.mechanical_cost_ge_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transferring the signed potential across each edge gives a telescoping correction. Each reweighted term is zero on a constant edge and at least one on a switch. The path cost is therefore bounded below by the initial signed potential minus the final one.

**Theorem 1.2 (Constant paths attain the diagonal minima).**

$$\forall (\alpha: \mathbb{R}), \forall (\rho: \mathbb{R}), (0 \le \alpha \land \alpha < 1) \Rightarrow (\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (i: \mathbb{N}), \forall (s: Bool), endpointMinimum\left(\alpha, M\left(\alpha, \rho, i, n\right), s, s\right) = sign\left(s\right) \cdot discrepancy\left(\alpha, M\left(\alpha, \rho, i, n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.mechanical_endpointMinimum_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a response returning to vertex s, the constant path attains the potential bound. The diagonal minimum is σ(s) times the mechanical discrepancy. The two diagonal minima are negatives of each other. The endpoint-pair comparison rules out a strict increase in both.

**Theorem 1.3 (Discrepancy bound for nonimprovable windows).**

$$\forall (\alpha: \mathbb{R}), (0 \le \alpha \land \alpha < 1) \Rightarrow (\forall (n: \mathbb{N}), (2 \le n) \Rightarrow (\forall (w: Fin\left(n\right) \to Bool), (Nonimprovable\left(\alpha, w\right)) \Rightarrow (\left|discrepancy\left(\alpha, w\right)\right| \le 7)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.nonimprovable_abs_discrepancy_le_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mechanical endpoint minima are all at least −1. A window with absolute discrepancy above seven admits a favorable interior sign. Patching the prescribed endpoints adds at most six to the constant-sign cost, so all its endpoint minima are below −1. A single mechanical window strictly improves every entry.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.mechanical_cost_ge_boundary`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.mechanical_endpointMinimum_diagonal`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.nonimprovable_abs_discrepancy_le_seven`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](../../Words/Mechanical/MechanicalBalance.md)
