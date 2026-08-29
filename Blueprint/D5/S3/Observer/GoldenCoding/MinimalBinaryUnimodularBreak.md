# Minimal Binary Unimodular Expansion

## Abstract

Nonnegative integral binary matrices have sharp expansion floors determined by the sign of their unimodular determinant.

**Theorem 1.1 (The Fibonacci matrix realizes both sharp determinant-sign bounds).**

$$\begin{aligned}\forall M: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{N}), lambda: \mathbb{R},\\{}1 < lambda \land \operatorname{IsRoot}(\operatorname{charpoly}(\operatorname{cast}(\mathbb{R}, M)), lambda) \Rightarrow\\{}(\operatorname{det}(\operatorname{cast}(\mathbb{Z}, M)) = -1 \Rightarrow \varphi \leq lambda) \land\\{}(\operatorname{det}(\operatorname{cast}(\mathbb{Z}, M)) = 1 \Rightarrow \varphi^{2} \leq lambda) \land\\{}(let F := \operatorname{matrix2}(1, 1, 1, 0), \operatorname{det}(\operatorname{cast}(\mathbb{Z}, F)) = -1 \land \operatorname{cast}(\mathbb{R}, F) = fibonacciSubstitution \land 1 < \varphi \land \operatorname{IsRoot}(\operatorname{charpoly}(\operatorname{cast}(\mathbb{R}, F)), \varphi)) \land\\{}(let F := \operatorname{matrix2}(1, 1, 1, 0), let F2 := F^{2}, F2 = \operatorname{matrix2}(2, 1, 1, 1) \land \operatorname{det}(\operatorname{cast}(\mathbb{Z}, F2)) = 1 \land 1 < \varphi^{2} \land \operatorname{IsRoot}(\operatorname{charpoly}(\operatorname{cast}(\mathbb{R}, F2)), \varphi^{2})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/MinimalBinaryUnimodularBreak.minimal_binary_unimodular_break` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix M has nonnegative integral entries, and lambda is a real characteristic root above one. In determinant sign minus one, the integral trace is at least one; in determinant sign one, it is at least three. Factoring the corresponding quadratics gives the two displayed lower bounds.

The public equality clauses use the integral Fibonacci matrix itself. Its real cast is the repository's canonical Fibonacci substitution, while direct finite arithmetic identifies its square and verifies both determinants and characteristic roots.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/MinimalBinaryUnimodularBreak.minimal_binary_unimodular_break`
- Dependency: [D5/S1/Eigenstructure/FibonacciMatrixDiscriminant](../../../S1/Eigenstructure/FibonacciMatrixDiscriminant.md)
