# Pure states under original quadratic deformation

## Abstract

Normalized quadratic pullback preserves purity on the original complete real JB carrier. A pure state with zero first moment and positive second moment has nearby pure states with nonzero first moment, converging in the continuous dual norm.

Let X be a complete real normed vector space, with specified bilinear product S, unit u, and the six laws Data(X,S,u): symmetry, unit multiplication, the Jordan identity, product norm domination, the square norm identity, and square norm monotonicity. No specialness, JC representation, finite dimension, separability, minimal projection or bidual is assumed. The zero algebra is included; it has no normalized state satisfying the hypotheses.

Let B be the continuous real functionals beta with beta(u)=1 and beta(S(x,x))>=0 for every x in the same X. Pure means membership in the real extreme points of B. Put L(h)z=S(h,z), U(a)z=2S(a,S(a,z))-S(S(a,a),z), Q(t)=I+2t L(h)+t^2 U(h)=U(u+th), and beta(t)=beta(Q(t)(u))^(-1) beta composed with Q(t). The scalar denominator is the actual transformed unit mass, not a fixed external normalization.

An algebraic positive normalized functional has abs(beta(x))<=norm(x): evaluate it on the original squares norm(x)u+x and norm(x)u-x. It therefore bundles as a continuous functional with precisely the same values and norm at most one. If it is extreme among the algebraic positive normalized functionals, every continuous convex decomposition is also such an algebraic decomposition, so the bundled functional belongs to the extreme points of B. No continuity premise is added to the original algebraic state by this representation.

**Theorem 1.1 (Pure deformation with positive mass and norm convergence).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; \forall A \in Data\left(X, S, u\right),\; \forall beta \in ContinuousRealDual\left(X\right),\; mem\left(beta, extremePoints\left(Real, states\left(S, u\right)\right)\right) \Rightarrow \left(\forall h \in X,\; beta\left(h\right) = 0 \Rightarrow \left(0 < beta\left(S\left(h, h\right)\right) \Rightarrow \left(\left(\exists epsilon \in Real,\; 0 < epsilon \land \left(\forall t \in Real,\; \left(abs\left(t\right) < epsilon \land t \ne 0\right) \Rightarrow \left(\left(\exists a \in X,\; S\left(a, a\right) = add\left(u, smul\left(t, h\right)\right)\right) \land \left(Bijective\left(U\left(S, add\left(u, smul\left(t, h\right)\right)\right)\right) \land \left(0 < beta\left(U\left(S, add\left(u, smul\left(t, h\right)\right), u\right)\right) \land \left(mem\left(deformation\left(A, beta, h, t\right), extremePoints\left(Real, states\left(S, u\right)\right)\right) \land \left(apply\left(deformation\left(A, beta, h, t\right), h\right) = divide\left(add\left(multiply\left(2, t, beta\left(S\left(h, h\right)\right)\right), multiply\left(square\left(t\right), beta\left(S\left(h, S\left(h, h\right)\right)\right)\right)\right), add\left(1, multiply\left(square\left(t\right), beta\left(S\left(h, h\right)\right)\right)\right)\right) \land apply\left(deformation\left(A, beta, h, t\right), h\right) \ne 0\right)\right)\right)\right)\right)\right)\right) \land TendstoInDualNormAtZero\left(deformation\left(A, beta, h\right), beta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBPureDeformation.pure_deformation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume beta is pure, beta(h)=0, and q=beta(S(h,h))>0. For every sufficiently small nonzero real t, u+th is an actual square in X, U(u+th) is bijective on X, its transformed mass is positive, and beta(t) is pure. Writing r=beta(S(h,S(h,h))), its value on h is (2tq+t^2r)/(1+t^2q), which is nonzero for such t. The function beta(t) converges to beta in the norm of the continuous dual, hence also on each fixed target of X.

The nonlinear normalization is handled by reweighting convex decompositions. For a cone C with strictly positive linear mass m on its nonzero elements, let T be a linear cone automorphism and x an extreme point of the mass-one base. If T(x)/m(T(x))=a y+b z, pull back y,z and normalize each separately. The new coefficients are m(T(x)) a m(T^(-1)y) and m(T(x)) b m(T^(-1)z). They are positive and sum to one by the original mass identity. Extremality forces both normalized pullbacks to equal x, and applying T and the mass identity forces y=z=T(x)/m(T(x)). This uses no affine transport claim for the normalized map.

For the original JB square cone, positive functionals have positive unit mass unless they vanish: apply them to the actual squares norm(x)u+x and norm(x)u-x. Every U(a) preserves squares. If U(a) is bijective, choose b with U(a)b=u. The fundamental identity gives U(a) U(b) U(a)=I, so its inverse is U(b) U(a), which also preserves squares. Pullback on the continuous dual is therefore an actual linear cone automorphism, and the reweighting argument applies.

The polynomial Q(t) is continuous in operator norm and equals I at zero. Openness of the units gives its local bijectivity. The original square-root criterion supplies u+th as a square near zero. The mass equals 1+t^2q. The numerator on h factors as t(2q+tr), with the second factor positive near zero. Continuous composition and inverse scalar mass give convergence in dual norm.

In the original dense-domain response setting, take h to be the embedded original output D(mu u,b), and test the fixed target b Jordan h. This result changes only the mathematical state used to read that fixed target; it changes neither the original preparation family nor the total response or its domain. To infer a zero target reading one must separately prove the nonzero-first-moment contact approximation for every deformed pure state. Minimal pure-state support in the JB bidual, bounded original signed-square approximation, pure-state separation, the full unit row and its continuation remain separate obligations. The argument is a classical cone-base transport construction applied to the original JB quadratic map and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/Topology/JBPureDeformation.pure_deformation`
- Dependency: [D5/S3/Topology/JBComplexification](JBComplexification.md)
