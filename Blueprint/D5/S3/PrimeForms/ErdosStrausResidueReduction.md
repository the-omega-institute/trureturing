# Erdos--Straus Residue Reduction

## Abstract

Integral and reciprocal formulations connect five explicit families to a reduction modulo twenty-four.

**Definition 1.1 (Division-free Erdos--Straus solvability).**

$$\forall n \in \mathbb{N},\\{}\operatorname{ESSolvable}(n) \iff \exists x, y, z \in \mathbb{N},\\{}0 < x \land 0 < y \land 0 < z \land 4 \cdot x \cdot y \cdot z = n \cdot (x \cdot y + x \cdot z + y \cdot z).$$

*Formalization.* `D5/S3/PrimeForms/ErdosStrausResidueReduction.ESSolvable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural n is solvable when positive natural denominators x, y, and z satisfy the integer equation obtained by clearing denominators.

**Theorem 1.2 (Reciprocal equivalence and positive scaling).**

$$(\forall n \in \mathbb{N},\\{}(\operatorname{ESSolvable}(n)) \Leftrightarrow (\exists x, y, z \in \mathbb{N},\\{}0 < x \land 0 < y \land 0 < z \land \frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z})) \land (\forall n , m \in \mathbb{N},\\{}(\operatorname{ESSolvable}(n) \land 1 \leq m) \Rightarrow\\{}(\operatorname{ESSolvable}(n \cdot m))).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_integer_reciprocal_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, integer solvability is equivalent to the existence of positive natural denominators satisfying the rational reciprocal equation.

A solution for n scales to one for nm for every positive natural multiplier m by multiplying all three denominators by m.

**Theorem 1.3 (Reduction to one residue class modulo twenty-four).**

$$(\forall n \in \mathbb{N},\\{}(2 \leq n \land n \bmod 24 \neq 1) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\forall n \in \mathbb{N},\\{}(n \bmod 24 = 1) \Rightarrow\\{}(\neg (2 \mid n \lor 3 \mid n \lor n \bmod 3 = 2 \lor n \bmod 4 = 3 \lor n \bmod 8 = 5))).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_mod_24_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, a residue other than one modulo twenty-four is routed through one of the five frozen witness families and is therefore solvable.

The second conjunct states that any natural with residue one modulo twenty-four satisfies none of the five family predicates. This theorem does not assert the six-class modulus-840 reduction or the full Erdos--Straus conjecture.

## References

- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.ESSolvable`
- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_integer_reciprocal_scaling`
- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_mod_24_reduction`
- Dependency: [D5/S3/Arith/Congruence/ErdosStrausModularWitnesses](../Arith/Congruence/ErdosStrausModularWitnesses.md)
