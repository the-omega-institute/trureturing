# Coordinate Mutation of the Cubic Equation

## Abstract

A coordinate mutation preserves the defining cubic equation.

**Theorem 1.1 (The coordinate mutation preserves the equation).**

$$\forall R,\ [\operatorname{CommRing}(R)],\ \forall x,y,z\in R,\ x^{2}+y^{2}+z^{2}=3xyz \Rightarrow x^{2}+y^{2}+(3xy-z)^{2}=3xy(3xy-z).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/MarkovEquationMutation.markov_equation_mutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source displays the equation x^2 + y^2 + z^2 = 3xyz and says its integer solutions form a tree. This partial closure isolates the standard edge operation: replace z by 3xy - z while leaving x and y fixed. The conclusion states that the resulting triple satisfies the same equation.

Expansion of the new square introduces 9x^2y^2 - 6xyz. Substituting the original equation and collecting terms gives 3xy(3xy - z). Because this calculation uses only commutative-ring identities, the declaration is freely generalized beyond the intended integer specialization.

This deposit does not prove independence of the real quadratic fields, classify or enumerate the full solution tree, identify the complete worst-approximable spectrum, or establish the source's extremality and branch-position claims. Those subitems remain unresolved.

## References

- Truth anchor: `D5/S3/Factorization/MarkovEquationMutation.markov_equation_mutation`
