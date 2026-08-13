# Metallic Family

## Abstract

The explicit quadratic-family value has reciprocal equal to its shift by the integer parameter.

**Theorem 1.1 (A quadratic-family value and its reciprocal).**

$$\forall n\in\mathbb{N}, metallicValue(n)=\frac{n+\sqrt(n^{2}+4)}{2} \land \frac{1}{metallicValue(n)}=metallicValue(n)-n.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetallicFamily.metallic_family_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean proof expands the displayed radical definition, uses the standard square-root nonnegativity and square identities from Mathlib, and clears the positive denominator by elementary ring arithmetic.

This is an honest partial closure of the metal-family clause in source theorem 5.7. The reciprocity law for the cotangent series, convergence assertions, special-value reductions, and all numerical certificates remain unresolved subitems of the source atom.

## References

- Truth anchor: `D5/S0/Asymptotics/MetallicFamily.metallic_family_value`
