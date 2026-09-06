# Rotation-Sum Power Pattern Avoidance

## Abstract

Powers of direct sums of cyclic rotations admit an exact 2143-avoidance criterion.

**Definition 1.1 (Direct sum of cyclic rotations).**

$$\forall d: List\left(\mathbb{N}\right), rotationSumPerm\left(d\right): Perm\left(Fin\left(\sum_{i \in Fin\left(length\left(d\right)\right)} d_{val\left(i\right)}\right)\right) := finSigmaFinEquiv_{length\left(d\right), (i: Fin\left(length\left(d\right)\right) \mapsto d_{val\left(i\right)})} \circ sigmaCongrRight\left(i \mapsto finRotate\left(d_{val\left(i\right)}\right)\right) \circ symm\left(finSigmaFinEquiv_{length\left(d\right), (i: Fin\left(length\left(d\right)\right) \mapsto d_{val\left(i\right)})}\right).$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a list d of block sizes, e is the canonical finSigmaFinEquiv flattening from block-tagged positions to the finite interval. The subscript displays its two implicit Mathlib parameters. The defining expression conjugates sigmaCongrRight of the rotations finRotate(d_i) by e, hence is the direct sum of the rotations epsilon_(d_i) on Fin(sum_i d_i). In the displayed defining formula, mod is natural-number remainder and finRotate(m) is the atom rotation epsilon_m.

$$
\forall m: \mathbb{N}, \forall x: Fin\left(m\right), val\left(finRotate\left(m\right)\left(x\right)\right) = \left(val\left(x\right) + 1\right) \bmod m.
$$

**Definition 1.2 (Containment of the pattern 2143).**

$$\forall n: \mathbb{N}, \forall f: Fin\left(n\right) \to Fin\left(n\right), Contains2143\left(f\right) \iff \exists a, b, c, e: Fin\left(n\right), (a < b \land b < c \land c < e \land f\left(b\right) < f\left(a\right) \land f\left(a\right) < f\left(e\right) \land f\left(e\right) < f\left(c\right)).$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.Contains2143` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six displayed inequalities are the defining expression: four increasing positions whose values have relative order 2143.

**Theorem 1.3 (All-power 2143-avoidance criterion).**

$$\forall d: List\left(\mathbb{N}\right), \forall r: \mathbb{N}, (\forall i: Fin\left(length\left(d\right)\right), 0 < d_{val\left(i\right)}) \implies ((\neg Contains2143\left(rotationSumPerm\left(d\right)^{r}\right)) \Leftrightarrow (card\left(\{i \in Fin\left(length\left(d\right)\right) : \neg d_{val\left(i\right)} \mid r\}\right) \leq 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm_pow_avoids_2143_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every block has positive size. The powered direct sum avoids 2143 exactly when at most one index has block size not dividing r. The proof uses the unique cyclic cut in each block: one block cannot contain both required descents, while any two nonidentity blocks supply them. This repository theorem resolves the all-power criterion motivated by Archer and Bourne's 2143 conjecture. The conjecture and the proved avoider-composition bijection are due to Archer and Bourne (2026), arXiv:2505.05218, DOI 10.46298/dmtcs.17199. The counting equality follows only by combining the cube criterion with that paper's proved bijection. This module does not formalize the bijection or the counting equality; the counting bridge remains residual-open.

**Theorem 1.4 (Cube 2143-avoidance criterion).**

$$\forall d: List\left(\mathbb{N}\right), (\forall i: Fin\left(length\left(d\right)\right), 0 < d_{val\left(i\right)}) \implies ((\neg Contains2143\left(rotationSumPerm\left(d\right)^{3}\right)) \Leftrightarrow (card\left(\{i \in Fin\left(length\left(d\right)\right) : d_{val\left(i\right)} \neq 1 \land d_{val\left(i\right)} \neq 3\}\right) \leq 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm_cube_avoids_2143_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent three, a positive block size divides the exponent exactly when it is one or three. This is the composition condition in the Archer-Bourne conjecture. The conjecture and the proved avoider-composition bijection are due to Archer and Bourne (2026), arXiv:2505.05218, DOI 10.46298/dmtcs.17199. The counting equality follows only by combining the cube criterion with that paper's proved bijection. This module does not formalize the bijection or the counting equality; the counting bridge remains residual-open.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.Contains2143`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm_cube_avoids_2143_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.rotationSumPerm_pow_avoids_2143_iff`
