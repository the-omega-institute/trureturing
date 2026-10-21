# The product-cone inclusion

## Abstract

The generalized doubly nonnegative cone inclusion for orthant and Lorentz products.

**Theorem 1.1 (The dual approximation preserves extreme rays).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative orthant dimension p, every finite number r of Lorentz blocks, and every family of positive spatial block dimensions, the dual of the zeroth homogeneous sum of squares approximation is contained in the positive semidefinite cone whose matrices send every extreme ray generator of the dual product cone into the product cone.

Every symmetric rank-one matrix supplies a single-square quartic test, forcing positive semidefiniteness of a matrix in the dual approximation. For two product-cone vectors u and v, the two pullbacks along the Jordan square are sums of squares of homogeneous linear polynomials. Multiplying the certificates gives a homogeneous quartic sum of squares for half the sum of uv-transpose and vu-transpose. Dual trace positivity therefore gives a nonnegative pairing of u with Xv. Product-cone self-duality gives Xv in the cone for every cone vector v. Every extreme ray generator of the dual cone is a cone vector by this same self-duality.

The cone-preservation proof applies to the entire dual cone and also allows zero spatial dimensions. The stated inclusion retains the positive spatial dimensions in the fixed claim. Symmetry, the Euclidean coordinate pairing, and the homogeneous quartic convex-hull definition are used exactly as specified.

## References

- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Result.result`
- Dependency: [D5/S3/QuadraticForms/ConicGDNN/Duality](Duality.md)
