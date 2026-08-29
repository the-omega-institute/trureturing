# Common-Denominator Polynomial Basis

## Abstract

Distinct finite Cayley scales give a common-denominator polynomial basis.

**Theorem 1.1 (The common-denominator family is a basis).**

$$\begin{aligned}\forall m: \mathbb{N}, r: \operatorname{Fin}(m) \to \mathbb{C}, depth: \operatorname{Fin}(m) \to \mathbb{N},\\referenceDepth: \mathbb{N},\\rNonzero: \forall i \in \operatorname{Fin}(m),\; r(i) \neq 0, rInjective: \operatorname{Injective}(r),\\rInDisk: \forall i \in \operatorname{Fin}(m),\; \operatorname{norm}(r(i)) < 1,\\\operatorname{let}(multiplicity: \operatorname{Fin}(m) \to \mathbb{N}, \forall i: \operatorname{Fin}(m), multiplicity(i) = depth(i) + 1\;q: \mathbb{N} = \operatorname{sum}(\operatorname{Fin}(m), (i: \operatorname{Fin}(m) \mapsto multiplicity(i)))\;factor: \operatorname{Fin}(m) \to \operatorname{Polynomial}(\mathbb{C}), \forall i: \operatorname{Fin}(m), factor(i) = 1 + \operatorname{C}(r(i)) \cdot X\;D: \operatorname{Polynomial}(\mathbb{C}) = \operatorname{prod}(\operatorname{Fin}(m), (i: \operatorname{Fin}(m) \mapsto \operatorname{pow}(factor(i), multiplicity(i))))\;I: \operatorname{Type}() = \operatorname{Sum}(\operatorname{Sigma}(\operatorname{Fin}(m), (i: \operatorname{Fin}(m) \mapsto \operatorname{Fin}(multiplicity(i)))), \operatorname{Fin}(referenceDepth + 1))\;p: I \to \operatorname{Polynomial}(\mathbb{C}), \forall i: \operatorname{Fin}(m), j: \operatorname{Fin}(multiplicity(i)), p(\operatorname{inl}(i, j)) = \operatorname{pow}(X + \operatorname{C}(r(i)), j) \cdot \operatorname{pow}(factor(i), depth(i) - j) \cdot \operatorname{prodExcept}(\operatorname{Fin}(m), i, (k: \operatorname{Fin}(m) \mapsto \operatorname{pow}(factor(k), multiplicity(k))))\;\forall j: \operatorname{Fin}(referenceDepth + 1), p(\operatorname{inr}(j)) = D \cdot \operatorname{pow}(X, j)),\\\operatorname{LinearIndependent}(\mathbb{C}, p) \land \operatorname{span}(\mathbb{C}, \operatorname{range}(p)) = \operatorname{degreeLT}(\mathbb{C}, q + referenceDepth + 1).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis.common_denominator_polynomial_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family is constructed from the supplied distinct nonzero complex parameters, their multiplicities, and the common polynomial denominator.

A local affine transport of the Bernstein family proves independence within each scale. Uniqueness of partial fractions then separates the scale blocks.

The reference block supplies the remaining top degrees. Independence and the matching finite dimension identify the span with the full bounded-degree polynomial subspace.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis.common_denominator_polynomial_basis`
