# An isolated failure of a linear increment bound

## Abstract

Strict translation Gram positivity from an isolated singularity

**Theorem 1.1 (Strict positivity on every finite distinct configuration).**

$$\forall V \in \operatorname{Type},\; [\operatorname{NormedAddCommGroup}\left(V\right)], \forall k \in V \to \mathbb{C},\; \left(\forall m \in \mathbb{N},\; \forall y \in \operatorname{Fin}\left(m\right) \to V,\; \operatorname{PosSemidef}\left(i, j \mapsto k\left(y\left(j\right) - y\left(i\right)\right)\right)\right) \Rightarrow \left(\left(\forall r \in V,\; r \ne 0 \Rightarrow \operatorname{IsBigO}\left(\operatorname{nhds}\left(0\right), h \mapsto k\left(r + h\right) - k\left(r\right), h \mapsto h\right)\right) \Rightarrow \left(\neg \operatorname{IsBigO}\left(\operatorname{nhds}\left(0\right), h \mapsto k\left(0 + h\right) - k\left(0\right), h \mapsto h\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to V,\; \operatorname{Injective}\left(x\right) \Rightarrow \operatorname{PosDef}\left(i, j \mapsto k\left(x\left(j\right) - x\left(i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity.posDef_of_isolated_non_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a complex valued function on a normed additive commutative group V. Assume that for every natural number m and every map x from Fin m to V, the matrix with entry k(x_j-x_i) is positive semidefinite. At every nonzero base point r assume the increment k(r+h)-k(r) is O(h) as h tends to zero. At zero assume k(h)-k(0) is not O(h). Equivalently, at each nonzero r there are finite constants C_r and delta_r>0 such that norm(k(r+h)-k(r))<=C_r*norm(h) whenever norm(h)<delta_r, whereas no such constants exist at zero. The constants may depend on r. No continuity assumption is imposed.

For every natural number n and every injective map x from Fin n to V, the matrix with entry k(x_j-x_i) is positive definite over the complex numbers. Thus its Hermitian quadratic form is strictly positive on every nonzero complex coefficient vector. The empty configuration is included; the assertion there is vacuous. There is no diameter restriction.

To prove the conclusion, take a vector c in the kernel of the finite Gram matrix and append an arbitrary node t. Extend c by a zero coordinate. Its quadratic form for the augmented positive semidefinite Gram matrix is zero. The positive semidefinite null-vector identity therefore makes the entire augmented matrix-vector product zero. In particular its new row gives sum_i k(x_i-t)*c_i=0 for every t in V, including repeated nodes.

If c is nonzero, choose j with c_j nonzero. Subtract the translate relation at t=x_j from the relation at t=x_j-h. The j term is c_j*(k(h)-k(0)); each other term is c_i*(k(x_i-x_j+h)-k(x_i-x_j)). Injectivity gives x_i-x_j nonzero for i different from j. Finite sums and constant multiplication preserve the O(h) bounds, and division by the nonzero coefficient c_j forces the forbidden O(h) bound at zero. Hence the matrix has trivial kernel; positive semidefiniteness then gives positive definiteness.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity.posDef_of_isolated_non_lipschitz`
