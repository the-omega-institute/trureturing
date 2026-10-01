# Finite Box Determinant Trace

## Abstract

The ordinary logarithm of a finite determinant product records common-divisor power traces.

**Theorem 1.1 (Common-divisor traces of actual actions).**

$$\begin{aligned}D_{g,N} = \prod_{1\le m,n\le N} \operatorname{det}(I-p^{m}q^{n}\rho_{m,n}(g))\\\forall a,b,N, a,b\ge1, N\ge\operatorname{max}(a,b) \implies [p^{a}q^{b}](-\log D_{g,N}) = \sum_{k\mid\operatorname{gcd}(a,b)} \frac{\operatorname{tr}(\rho_{\frac{a}{k},\frac{b}{k}}(g^{k}))}{k}\\\forall a,b,N,M, a,b\ge1, N,M\ge\operatorname{max}(a,b) \implies [p^{a}q^{b}](-\log D_{g,N}) = [p^{a}q^{b}](-\log D_{g,M})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/FiniteBoxDeterminantTrace.finite_box_trace_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a group and let W(m,n) be finite-dimensional rational G-representations. Only positive bidegrees occur in the finite box. The group may in particular be finite. Dimensions can vary with the bidegree and can be zero. The action matrix is the matrix of the given representation in a finite basis.

D(g,N) is the literal product of det(I-p^m q^n rho(m,n)(g)) for 1 <= m,n <= N. Each matrix determinant equals the intrinsic determinant of I-p^m q^n times the action after extension of scalars to the bivariate rational series ring. Thus the product is independent of the finite bases. Its constant coefficient is one. The negative logarithm is the ordinary formal series log(1+X) substituted at D(g,N)-1 and negated.

For a rational matrix A, its formal resolvent has coefficient A^k in degree k. The first-order Taylor determinant identity applied at I-XA gives its logarithmic derivative. Integration with zero constant term yields trace(A^k)/k as every positive coefficient of -log det(I-XA). This uses no diagonalization and also applies to the empty matrix.

Writing the bivariate ring as iterated series preserves ordinary logarithm substitution. Over the inner coefficient ring, the logarithmic derivative proves that the logarithm of a finite product is the sum of the factor logarithms. Substitution of p^m q^n leaves precisely exponents (km,kn). Reindexing these contributions by divisors of gcd(a,b) gives the displayed formula. Every required quotient bidegree lies in each box with N >= max(a,b), proving stability.

This is a finite-dimensional algebraic identity for the supplied actions. It constructs no infinite product and asserts no Monster root-space, vertex-algebra, or conformal-field structure.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/FiniteBoxDeterminantTrace.finite_box_trace_formula`
- Dependency: [D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery](MonsterPrimitiveMobiusRecovery.md)
