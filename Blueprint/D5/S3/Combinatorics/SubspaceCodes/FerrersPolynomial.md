# Linearized polynomial rank

## Abstract

The root bound for a four-term linearized polynomial gives rank at least nine.

**Definition 1.1 (Linearized evaluation map).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] \forall a \in \operatorname{Fin}\left(4\right) \to E,\; (\operatorname{evaluateLinearized}\left(F, E, a\right) : \operatorname{LinearMap}\left(F, E, E\right)) = \sum_{i\in \operatorname{Fin}\left(4\right)} a\left(i\right) \cdot \operatorname{frobenius}\left(F, E\right)^{\operatorname{val}\left(i\right)}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each power of the Frobenius denotes iteration, starting with the identity. The sum uses the scalar action of E on the space of F-linear maps.

**Theorem 1.2 (Evaluation by Frobenius powers).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] \forall a \in \operatorname{Fin}\left(4\right) \to E,\; \forall x \in E,\; \operatorname{evaluateLinearized}\left(F, E, a\right)\left(x\right) = \sum_{i\in \operatorname{Fin}\left(4\right)} a\left(i\right) \cdot x^{\operatorname{card}\left(F\right)^{\operatorname{val}\left(i\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the linear map to x gives the scalar polynomial formula.

**Theorem 1.3 (Rank bound in degree twelve).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] [\operatorname{Finite}\left(E\right)] (\operatorname{finrank}\left(F, E\right) = 12) \Rightarrow (\forall a \in \operatorname{Fin}\left(4\right) \to E,\; (a \ne 0) \Rightarrow (9 \le \operatorname{finrank}\left(F, \operatorname{range}\left(\operatorname{evaluateLinearized}\left(F, E, a\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.finrank_range_evaluateLinearized_ge_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero polynomial has distinct exponents 1, q, q² and q³, where q is the order of F. Its degree is at most q³, so its kernel has at most q³ elements and dimension at most three.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized_apply`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.finrank_range_evaluateLinearized_ge_nine`
