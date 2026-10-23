# Actual Costs and Partial Absorption

## Abstract

Exact nonnegative coding values give opposite endpoint slopes and interior minima on the rotating dictionary slice.

Let E be any real inner-product space and u,v orthogonal unit vectors. The dictionary D(alpha) has first column u and second column cos(alpha)u+sin(alpha)v. Set I=[pi/4,pi/2] and w=(u+v)/sqrt(2). No completeness or finite dimensionality is required. Codes have two nonnegative real coordinates. The energy E(x,D,c) is norm(x-Dc)^2/2+lambda(c0+c1), C(x,D) is its infimum over all such codes, and J(alpha)=pA C(u,D(alpha))+pAB C(u+v,D(alpha))+pB C(v,D(alpha)).

Write g=cos(alpha), s=sin(alpha), m=g+s-lambda, k=1-g squared, and h=1-lambda-g m. The function activeMass(lambda,alpha) is max(0,h), and V(lambda,alpha)=1-m squared/2-max(0,h) squared/(2k). On I the denominator k is positive. The co-occurring sample has an optimal code a=max(0,h)/k, b=m-g a. For every competing nonnegative code (A,B), square completion gives its energy as 1-m squared/2+(B+g A-m) squared/2+k A squared/2-h A. If h<=0 the minimum has A=0; if h>0, completing the remaining square gives A=h/k. The second coordinate is nonnegative in both cases, since m-g(1-lambda)=s-lambda+lambda g>0.

The child sample v has optimal code (0,s-lambda), with value 1/2-(s-lambda) squared/2. The excess energy of (A,B) over this value is (B+g A-(s-lambda)) squared/2+k A squared/2+(lambda+g(s-lambda))A. Each summand is nonnegative. For the parent sample u, the existing radial alignment criterion gives lambda-lambda squared/2. The existing nonnegative cost bounds give C(0,D)=0. Thus these attained values concern the same infima that define J.

**Theorem 1.1 (Exact slopes and every attained minimum).**

$$\forall E \in RealInnerProductSpaces , \forall u , v \in E , ( norm ( u ) = 1 \land norm ( v ) = 1 \land \langle u , v \rangle = 0 ) \implies \forall \lambda , pA , pAB , pB \in \mathbb{R} , ( 0 < \lambda < \frac{1}{\sqrt{2}} \land 0 < pAB \land 0 < pB ) \implies \  d2 ( \frac{\pi}{4} ) = w \land d2 ( \frac{\pi}{2} ) = v \land ( \forall \alpha \in I , \forall p0 \in \mathbb{R} , p0 C ( 0 , D ( \alpha ) ) + pA C ( u , D ( \alpha ) ) + pAB C ( u + v , D ( \alpha ) ) + pB C ( v , D ( \alpha ) ) = J ( \alpha ) ) \land ( \forall \alpha \in I , C ( u , D ( \alpha ) ) = \lambda - \frac{{\lambda}^{2}}{2} \land ( \exists c \in {\mathbb{R}}^{2} , c \ge 0 \land E ( u + v , D ( \alpha ) , c ) = V ( \lambda , \alpha ) \land ( \forall d \in {\mathbb{R}}^{2} , d \ge 0 \implies V ( \lambda , \alpha ) \le E ( u + v , D ( \alpha ) , d ) ) \land C ( u + v , D ( \alpha ) ) = V ( \lambda , \alpha ) ) \land ( \exists c \in {\mathbb{R}}^{2} , c \ge 0 \land E ( v , D ( \alpha ) , c ) = \frac{1}{2} - \frac{{sin ( \alpha ) - \lambda}^{2}}{2} \land ( \forall d \in {\mathbb{R}}^{2} , d \ge 0 \implies \frac{1}{2} - \frac{{sin ( \alpha ) - \lambda}^{2}}{2} \le E ( v , D ( \alpha ) , d ) ) \land C ( v , D ( \alpha ) ) = \frac{1}{2} - \frac{{sin ( \alpha ) - \lambda}^{2}}{2} ) ) \land ContinuousOn ( J , I ) \land Eventually ( N ( I , \frac{\pi}{4} ) , \alpha \mapsto DifferentiableWithinAt ( \mathbb{R} , J , I , \alpha ) ) \land Eventually ( N ( I , \frac{\pi}{2} ) , \alpha \mapsto DifferentiableWithinAt ( \mathbb{R} , J , I , \alpha ) ) \land H ( J , - \frac{pB ( \frac{1}{\sqrt{2}} - \lambda )}{\sqrt{2}} , I , \frac{\pi}{4} ) \land H ( J , pAB \lambda ( 1 - \lambda ) , I , \frac{\pi}{2} ) \land - \frac{pB ( \frac{1}{\sqrt{2}} - \lambda )}{\sqrt{2}} < 0 \land 0 < pAB \lambda ( 1 - \lambda ) \land ( \exists \alpha \in I , IsMinOn ( J , I , \alpha ) ) \land ( \forall \alpha \in I , IsMinOn ( J , I , \alpha ) \implies \frac{\pi}{4} < \alpha < \frac{\pi}{2} )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/ActualCostEndpoints.partial_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<lambda<1/sqrt(2), pAB>0 and pB>0, the parent weight pA may be any real number. The zero weight p0 is arbitrary in the expectation identity. In particular this includes all nonnegative normalized four-point laws on 0,u,u+v,v, including pA=0 and p0=0. The two existential codes in the displayed statement attain the indicated energy. Every feasible competing code has energy at least that attained value. Coordinatewise inequalities on real two-vectors express feasibility. The notation N_I(x) denotes relative neighborhoods in I; H(J,q,I,x) denotes HasDerivWithinAt J q I x. The displayed d2 is the second column; the two Lean code slots are indexed by 0 and 1.

At pi/4 the residual h is strictly negative, so the co-occurring and child samples both use only the rotating column throughout a relative neighborhood. Differentiation gives the negative left endpoint slope. At pi/2, h=1-lambda is strictly positive. Both co-occurring coordinates are active throughout a relative neighborhood. Its value is 1-Q/2, where Q=((1-lambda) squared-2g(1-lambda)m+m squared)/(1-g squared). At this endpoint Q'=-2lambda(1-lambda), while the child value has derivative zero.

The positive-part formula for V is continuous across the active-set transition, so J is continuous on the entire closed interval. Compactness gives an attained minimum. At a constrained endpoint minimum the derivative applied to every inward tangent direction is nonnegative. The negative slope at pi/4 and positive slope at pi/2 violate this necessary condition at their respective endpoints. Every interval minimizer therefore has pi/4<alpha<pi/2, placing its second atom strictly between w and v.

This concerns exact inner coding and a dictionary slice whose first column is fixed. It asserts no uniqueness, continuous or monotone dependence on probability ratios, optimum when both columns are free, decoder bias result, amortized encoder result or empirical sparse autoencoder result. The classical radial cost is reused; the endpoint calculation and its attained two-coordinate value relation are stated here without a claim of literature novelty.

## References

- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/ActualCostEndpoints.partial_absorption`
- Dependency: [D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching](TwoAtomMatching.md)
