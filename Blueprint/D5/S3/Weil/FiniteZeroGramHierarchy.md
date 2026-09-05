# Finite Zero Gram Hierarchy

## Abstract

A finite positive-weighted zero-resolvent kernel is a Gram matrix whose determinant is one exact nonnegative Cauchy--Binet contribution.

**Theorem 1.1 (Finite zero-resolvent Gram determinants are nonnegative).**

$$\forall I \in Type, z \in I \to \operatorname{Complex}\left(\right), gamma \in I \to \operatorname{Real}\left(\right), m \in I \to \operatorname{Real}\left(\right),\; \left(\operatorname{Fintype}\left(I\right) \land \left(\operatorname{DecidableEq}\left(I\right) \land \left(\left(\forall a \in I,\; 0 < \operatorname{im}\left(z\left(a\right)\right)\right) \land \left(\forall k \in I,\; 0 \le m\left(k\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall a \in I, k \in I,\; \operatorname{ofReal}\left(gamma\left(k\right)\right) - z\left(a\right) \ne 0\right) \land \left(\left(\forall a \in I, b \in I,\; \operatorname{finiteZeroGramMatrix}\left(z, gamma, m\right)\left(a, b\right) = \operatorname{sum}\left(k, I, \operatorname{zeroResolventMatrix}\left(z, gamma\right)\left(a, k\right) \cdot \operatorname{ofReal}\left(m\left(k\right)\right) \cdot \operatorname{conj}\left(\operatorname{zeroResolventMatrix}\left(z, gamma\right)\left(b, k\right)\right)\right)\right) \land \left(\operatorname{PosSemidef}\left(\operatorname{finiteZeroGramMatrix}\left(z, gamma, m\right)\right) \land \left(\operatorname{det}\left(\operatorname{finiteZeroGramMatrix}\left(z, gamma, m\right)\right) = \operatorname{prod}\left(k, I, \operatorname{ofReal}\left(m\left(k\right)\right)\right) \cdot \operatorname{det}\left(\operatorname{zeroResolventMatrix}\left(z, gamma\right)\right) \cdot \operatorname{conj}\left(\operatorname{det}\left(\operatorname{zeroResolventMatrix}\left(z, gamma\right)\right)\right) \land 0 \le \operatorname{det}\left(\operatorname{finiteZeroGramMatrix}\left(z, gamma, m\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/FiniteZeroGramHierarchy.finite_zero_gram_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sampling nodes lie in the open upper half-plane, so no real ordinate can make a resolvent denominator zero. Nonnegative real weights define the diagonal middle factor of the Gram matrix.

Mathlib's positive-semidefinite diagonal and congruence lemmas prove positivity. Multiplicativity of the determinant, the diagonal determinant formula, and conjugate-transpose compatibility give the displayed weighted determinant square.

The source's infinite subset expansion is not asserted because it omits enumeration and convergence hypotheses. The reverse implication to the Riemann hypothesis is also omitted: a Gram construction is positive for every real ordinate family and therefore cannot locate zeta zeros on the critical line.

A companion Lean theorem shows sharpness at determinant zero using two distinct ordinates, positive weights, and a repeated upper-half-plane sampling node.

## References

- Truth anchor: `D5/S3/Weil/FiniteZeroGramHierarchy.finite_zero_gram_hierarchy`
