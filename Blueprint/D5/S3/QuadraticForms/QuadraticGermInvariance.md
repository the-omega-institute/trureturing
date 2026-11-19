# Symmetries of a Quadratic Germ

## Abstract

A scalar function's quadratic expansion determines the bilinear form preserved by its linear symmetries.

**Theorem 1.1 (The coefficient on a ray).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall f \in E \to \mathbb{R},\; \forall B \in \operatorname{BilinForm}\left(\mathbb{R}, E\right),\; \operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (Z: E \mapsto f\left(Z\right) - \left(1 - \frac{B\left(Z, Z\right)}{2}\right)), (Z: E \mapsto \left\lVert Z \right\rVert^{2})\right) \Rightarrow \left(\forall X \in E,\; \operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (t: \mathbb{R} \mapsto f\left(\operatorname{smul}\left(t, X\right)\right) - \left(1 - \frac{B\left(X, X\right) \cdot t^{2}}{2}\right)), (t: \mathbb{R} \mapsto t^{2})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/QuadraticGermInvariance.quadratic_germ_on_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a real normed vector space, B a real bilinear form, and f a real-valued function. The quadratic-germ hypothesis means that f(X) minus 1 plus B(X,X)/2 is little-o of the square of the original norm in the full neighborhood filter at zero, including the value at zero. For every fixed X, restriction to t times X has remainder little-o of t squared and quadratic term minus B(X,X)t squared/2. This includes X=0 and requires neither symmetry of B nor finite dimension.

The restriction follows by composing the original remainder with the continuous ray and using the exact identity that the squared norm of t times X equals t squared times the squared norm of X.

**Theorem 1.2 (A linear symmetry preserves the quadratic form).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall f \in E \to \mathbb{R},\; \forall B \in \operatorname{BilinForm}\left(\mathbb{R}, E\right),\; \left(\forall U \in E,\; \forall V \in E,\; B\left(U, V\right) = B\left(V, U\right)\right) \Rightarrow \left(\operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (Z: E \mapsto f\left(Z\right) - \left(1 - \frac{B\left(Z, Z\right)}{2}\right)), (Z: E \mapsto \left\lVert Z \right\rVert^{2})\right) \Rightarrow \left(\forall T \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \left(\forall X \in E,\; f\left(T\left(X\right)\right) = f\left(X\right)\right) \Rightarrow \left(\forall X \in E,\; \forall Y \in E,\; B\left(T\left(X\right), T\left(Y\right)\right) = B\left(X, Y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/QuadraticGermInvariance.bilinear_invariant_of_quadratic_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume additionally that B is symmetric. Every real linear map T satisfying f(TX)=f(X) for all X preserves B on every pair: B(TX,TY)=B(X,Y). T need not be invertible, and no continuity assumption on f away from the quadratic germ is imposed.

The expansions on the rays through X and TX are expansions of the same scalar function, so their quadratic coefficients agree. A nonzero constant multiple of t squared cannot be little-o of t squared on the punctured neighborhood of zero. The polarization identity then recovers every mixed value of B from diagonal values.

**Theorem 1.3 (Exponential conjugation has skew infinitesimal action).**

$$\forall A \in Type,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall L \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right),\; \forall f \in L \to \mathbb{R},\; \forall B \in \operatorname{BilinForm}\left(\mathbb{R}, L\right),\; \left(\forall U \in L,\; \forall V \in L,\; B\left(U, V\right) = B\left(V, U\right)\right) \Rightarrow \left(\operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (Z: L \mapsto f\left(Z\right) - \left(1 - \frac{B\left(Z, Z\right)}{2}\right)), (Z: L \mapsto \left\lVert Z \right\rVert^{2})\right) \Rightarrow \left(\left(\forall C \in L,\; \forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{exp}\left(\operatorname{smul}\left(t, C\right)\right) \cdot X \cdot \operatorname{exp}\left(-\operatorname{smul}\left(t, C\right)\right) \in L \land f\left(\operatorname{exp}\left(\operatorname{smul}\left(t, C\right)\right) \cdot X \cdot \operatorname{exp}\left(-\operatorname{smul}\left(t, C\right)\right)\right) = f\left(X\right)\right) \Rightarrow \left(\forall C \in L,\; \forall X \in L,\; \forall Y \in L,\; B\left([C,X], Y\right) + B\left(X, [C,Y]\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/QuadraticGermInvariance.ad_invariant_of_exp_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complete finite-dimensional real normed unital associative algebra and L a real Lie subalgebra for the commutator bracket. Let f on L have quadratic germ B, where B is symmetric. For every C and X in L and real t, assume that q(C,t,X)=exp(tC)X exp(-tC) belongs to L and f(q(C,t,X))=f(X). Then B([C,X],Y)+B(X,[C,Y])=0 for every C,X,Y in L.

Each q(C,t,.) is a linear symmetry, hence preserves B by the preceding result. Its derivative at zero is the original commutator [C,X]; the calculation takes place in A and passes to the inherited topology on L. Finite dimension makes B continuous, so differentiating the invariant bilinear value gives the stated identity. No derivative of f beyond its prescribed quadratic expansion is used.

These are consequences of quadratic expansion uniqueness, polarization and differentiation of the algebra exponential. They assert no classification of Lie algebras or groups, no positivity of B, and no empirical interpretation of the scalar function.

## References

- Truth anchor: `D5/S3/QuadraticForms/QuadraticGermInvariance.ad_invariant_of_exp_conjugation`
- Truth anchor: `D5/S3/QuadraticForms/QuadraticGermInvariance.bilinear_invariant_of_quadratic_germ`
- Truth anchor: `D5/S3/QuadraticForms/QuadraticGermInvariance.quadratic_germ_on_ray`
