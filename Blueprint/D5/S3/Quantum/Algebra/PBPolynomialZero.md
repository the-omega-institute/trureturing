# All polynomial pairs under the original symmetry rows

## Abstract

On the same original real Jordan carrier, the full PB identity and the explicit rotation, oddness and affine-zero rows imply zero response for every pair of polynomials in one generator.

**Definition 1.1 (Evaluation by the original Jordan powers).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)][\operatorname{NormedSpace}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall u \in E,\; \forall x \in E,\; \forall p \in \operatorname{Polynomial}\left(\mathbb{R}\right),\; \operatorname{eval}\left(J, u, x, p\right) = \sum_{k\in \operatorname{support}\left(p\right)}{\operatorname{smul}\left(\operatorname{coeff}\left(p, k\right), \operatorname{npow}\left(J, u, x, k\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Algebra/PBPolynomialZero.eval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E is any real normed vector space, J is its specified real bilinear product, and u and x are specified original elements. The finite coefficient sum defines a real-linear evaluation map. The existing JBAlgebra.npow has zeroth power u and successor J(x,power). No algebra law is required for this definition. When JBAlgebra.Data holds, its existing power_mul theorem proves that this evaluation also preserves multiplication. All resulting labels remain in E.

**Theorem 1.2 (The full formal-degree induction).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)][\operatorname{NormedSpace}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall u \in E,\; \forall D \in \operatorname{Function}\left(E, E, E\right),\; \left(\left(\left(\left(\left(\operatorname{Data}\left(E, J, u\right) \land \operatorname{PB}\left(J, D\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \forall theta \in \mathbb{R},\; \operatorname{apply}\left(D, \operatorname{smul}\left(\operatorname{cos}\left(theta\right), a\right) - \operatorname{smul}\left(\operatorname{sin}\left(theta\right), b\right), \operatorname{smul}\left(\operatorname{sin}\left(theta\right), a\right) + \operatorname{smul}\left(\operatorname{cos}\left(theta\right), b\right)\right) = \operatorname{apply}\left(D, a, b\right)\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(D, -a, b\right) = -\operatorname{apply}\left(D, a, b\right)\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(D, a, -b\right) = -\operatorname{apply}\left(D, a, b\right)\right)\right) \land \left(\forall a \in E,\; \forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, a\right), \operatorname{smul}\left(t, u\right) + \operatorname{smul}\left(v, a\right)\right) = 0\right)\right) \Rightarrow \left(\forall x \in E,\; \forall p \in \operatorname{Polynomial}\left(\mathbb{R}\right),\; \forall q \in \operatorname{Polynomial}\left(\mathbb{R}\right),\; \operatorname{apply}\left(D, \operatorname{eval}\left(J, u, x, p\right), \operatorname{eval}\left(J, u, x, q\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBPolynomialZero.polynomial_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

JBAlgebra.Data(E,J,u) supplies symmetry, the unit law, the Jordan identity, product norm domination, the square norm identity and square norm monotonicity for this same J and norm. No completeness, nonzero-space, dimension, spectrum or representation condition is imposed. D is an arbitrary total map from E squared to E. The hypotheses on D are exactly the full PB identity and the SO(2) rotation, each-slot oddness and same-axis affine-zero rows of source 185.1. The square row and a separate unit row are unnecessary inputs. These rows are hypotheses here; their derivation from raw P2 and PB is not supplied by this theorem.

For complex scalar polynomials P, take their coefficientwise real and imaginary parts h,k and put Phi(P)=D(eval(h),eval(k)). Complex coefficients record two real labels; D never receives a complex argument. The rotation hypothesis gives Phi(zP)=Phi(P) for every unit complex scalar z. Oddness gives Phi(-P)=Phi(P) and Phi(conjugate(P))=-Phi(P). Neither additivity nor arbitrary scalar homogeneity of D or Phi is inferred.

Strong induction uses an arbitrary natural bound on the formal degree of P. Degrees at most one follow from the affine-zero row with generator eval(T), including the zero polynomial and all constants. Otherwise the complex fundamental theorem of algebra factors P as kappa times the product of T-z over the list of roots, with repeated roots retained at their multiplicities. The nonzero leading coefficient kappa is a scalar, independent of possible collapse under evaluation.

To reflect one nonreal root z=r+it, set a=(T-r)/t and W=-it Q, where Q contains kappa and all the other root factors, including the already reflected prefix. The real and imaginary parts of W have strictly smaller formal degree; a has degree at most one. Applying the induction hypothesis to (a,Re(W)) and (a,Im(W)) pays the two actual inner responses D(A,B)=D(A,C)=0, where A=eval(a), B=eval(Re(W)) and C=eval(Im(W)).

The same original PB now compares exactly D(B-J(A,C),C+J(A,B)) and D(B+J(A,C),C-J(A,B)). Its full right side is twice the difference between J(B,J(A,C)) and J(C,J(A,B)); evaluation multiplicativity and the associativity of scalar polynomial multiplication make this zero. The two outer pairs are exactly the real labels of (1+ia)W=(T-z)Q and (1-ia)W=-(T-conjugate(z))Q. Simultaneous negation removes the second sign, so reflecting this root preserves the actual response. No unexplained root-invariance premise is used.

Real roots are unchanged. Induction along the finite root list therefore reflects every indexed factor and gives kappa times the coefficient-conjugate monic product. This equals kappa/conjugate(kappa) times conjugate(P). That scalar has norm one. Phase invariance and second-slot oddness give Phi(P)=-Phi(P), and real scalar cancellation forces zero. Only nonzero real t and nonzero complex conjugate(kappa) are divided by; no root or inverse is taken inside E.

The theorem quantifies all formal degrees without a bound. Zero real or imaginary parts, repeated roots, real roots, an empty root list, scalar generators, noninjective evaluation and the zero algebra remain included. There is no additivity, homogeneity, continuity, measurability, covariance or completion extension assumption on D.

For the original source 3.1, restrict the supplied JB laws on X through the original isometric Jordan inclusion i:E to X: symmetry, unit and Jordan equations descend by injectivity, and the three norm laws descend by isometry and preservation of J and u. Apply the displayed theorem to exactly that original E,J,u,D and PB. Density, completeness of X, the original cone and evaluation family, directed P2 and all zero, unequal and subnormalised masses are retained by this application and are not used to derive the symmetry rows here. Thus this supplies the all-degree induction conditional on 185.1. The general original-unit and raw 185.1 derivations remain required for the unconditional source 3.1 conclusion. No response on a quotient, C* replacement, finite-spectrum restriction or transport of D to X is introduced.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBPolynomialZero.eval`
- Truth anchor: `D5/S3/Quantum/Algebra/PBPolynomialZero.polynomial_zero`
- Dependency: [D5/S3/Quantum/Algebra/PBActualOuterBudget](PBActualOuterBudget.md)
- Dependency: [D5/S3/Topology/JBAlgebra](../../Topology/JBAlgebra.md)
