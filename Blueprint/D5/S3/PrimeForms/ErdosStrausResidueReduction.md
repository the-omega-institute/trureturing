# Erdos-Straus Residue Reduction

## Abstract

Explicit Egyptian-fraction identities reduce the Erdos-Straus conjecture to the residue class one modulo twenty-four.

**Definition 1.1 (Division-free Erdos-Straus solvability).**

$$\forall n \in \mathbb{N},\\{}\operatorname{ESSolvable}(n) \iff \exists x, y, z \in \mathbb{N},\\{}0 < x \land 0 < y \land 0 < z \land 4 \cdot x \cdot y \cdot z = n \cdot {x \cdot y + x \cdot z + y \cdot z}.$$

*Formalization.* `D5/S3/PrimeForms/ErdosStrausResidueReduction.ESSolvable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural denominator n is solvable when positive natural denominators x, y, and z satisfy the equation obtained by clearing the three reciprocal denominators.

**Theorem 1.2 (Reciprocal equivalence and positive scaling).**

$$(\forall n , x , y , z \in \mathbb{N},\\{}(n \neq 0 \land 0 < x \land 0 < y \land 0 < z) \Rightarrow\\{}((\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}) \Leftrightarrow (4 \cdot x \cdot y \cdot z = n \cdot {x \cdot y + x \cdot z + y \cdot z}))) \land (\forall n , m \in \mathbb{N},\\{}(\operatorname{ESSolvable}(n) \land 1 \leq m) \Rightarrow\\{}(\operatorname{ESSolvable}(n \cdot m))).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_integer_reciprocal_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n and positive x, y, and z, clearing denominators is reversible over the rationals and gives exactly 4xyz = n(xy+xz+yz).

A solution scales from n to nm for every positive natural multiplier m by replacing each denominator with xm, ym, and zm.

**Theorem 1.3 (Five constructive congruence families).**

$$(\forall n \in \mathbb{N},\\{}(n \bmod 2 = 0 \land 1 \leq n) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\forall n \in \mathbb{N},\\{}(n \bmod 3 = 0 \land 1 \leq n) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\forall n \in \mathbb{N},\\{}(n \bmod 3 = 2 \land 1 \leq n) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\forall n \in \mathbb{N},\\{}(n \bmod 4 = 3 \land 1 \leq n) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\forall n \in \mathbb{N},\\{}(n \bmod 8 = 5 \land 1 \leq n) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\operatorname{ESSolvable}(2)) \land (\operatorname{ESSolvable}(5)) \land (\operatorname{ESSolvable}(7)).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_explicit_residue_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five displayed conjuncts cover even n, multiples of three, and the residue classes 2 modulo 3, 3 modulo 4, and 5 modulo 8. Each conclusion retains the positive-input premise from Lean.

The latter three families use explicit parametric denominators. The final three conjuncts record concrete witnesses at n = 2, 5, and 7.

**Theorem 1.4 (Reduction to one residue class modulo twenty-four).**

$$(\forall n \in \mathbb{N},\\{}(2 \leq n \land n \bmod 24 \neq 1) \Rightarrow\\{}(\operatorname{ESSolvable}(n))) \land (\neg{1 \bmod 2 = 0 \lor 1 \bmod 3 = 0 \lor 1 \bmod 3 = 2 \lor 1 \bmod 4 = 3 \lor 1 \bmod 8 = 5}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_mod_24_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, a residue other than one modulo twenty-four falls into one of the five constructive families and is therefore solvable.

The second conjunct checks that the literal residue one satisfies none of those five predicates. This theorem does not assert the six-class modulus-840 reduction and does not prove the full Erdos-Straus conjecture.

## References

- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.ESSolvable`
- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_explicit_residue_families`
- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_integer_reciprocal_scaling`
- Truth anchor: `D5/S3/PrimeForms/ErdosStrausResidueReduction.es_mod_24_reduction`
