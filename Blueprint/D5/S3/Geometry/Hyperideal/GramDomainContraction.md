# Contractibility of the full Gram determinant domain

## Abstract

The full six-coordinate Gram determinant domain contracts to the all-two point while fixing that point.

Let x=(a,b,c,d,e,f) be six independent real coordinates in edge order (12,13,14,34,24,23). Define the symmetric matrix G(x) by its rows (1,-a,-b,-c), (-a,1,-f,-e), (-b,-f,1,-d), and (-c,-e,-d,1), and put Delta(x)=-det(G(x)). The space X is the full set of x for which every coordinate is strictly greater than one and Delta(x)>0, with the subspace topology inherited from the product of six copies of the real line.

**Theorem 1.1 (An explicit center-fixing contraction).**

$$ContractibleSpace\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/GramDomainContraction.full_domain_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant has a quantitative radial bound. For any x with every coordinate at least one and any 0<=s<=1, Delta(1+s*(x-1))>=min(16,Delta(x)), with the affine expression interpreted coordinatewise. To obtain this bound, expand the determinant in s as 16+c1*s+c2*s^2+c3*s^3+c4*s^4. For nonnegative offsets, c1 and c2 are nonnegative. If c4 is nonnegative, the same offsets imply c3>=0, so the expansion is at least 16. If c4<0, the expansion is at least 16*(1-s^3)+s^3*Delta(x), which is at least the displayed minimum.

A second determinant estimate controls a fixed cube. If every offset y_i lies in [0,1], then Delta(1+y)>=1. The same expansion at s=1 has c1,c2>=0, c3>=-12 and c4>=-3 on this cube, giving the lower bound 16-12-3=1. In particular, the all-two point p belongs to X.

For x in X define M(x)=max(1,x_0-1,x_1-1,x_2-1,x_3-1,x_4-1,x_5-1) and eta(x)=1/M(x). Then 0<eta(x)<=1 and 0<eta(x)*(x_i-1)<=1 for every coordinate. The finite maximum is continuous and is bounded below by one, so eta is continuous. The compression map has coordinates C(x)_i=1+eta(x)*(x_i-1); it is continuous, and the radial bound places it in X.

The first stage, for 0<=t<=1, is H_r(t,x)_i=1+(1-t*(1-eta(x)))*(x_i-1). Its scale 1-t*(1-eta(x)) lies in [eta(x),1]. Thus every coordinate remains strictly greater than one, and the radial bound keeps Delta strictly positive. This formula is jointly continuous in t and x, starts at x, and ends at C(x).

The second stage is H_c(t,x)_i=1+(1-t)*(eta(x)*(x_i-1))+t for 0<=t<=1. Its offsets lie in (0,1], so the cube estimate gives Delta(H_c(t,x))>=1 throughout. The formula is jointly continuous, starts at the same C(x), and ends at the all-two point p.

Concatenating these two homotopies gives an identity-to-constant contraction of X. Since eta(p)=1, both stages fix p at every time. The construction also defines a HomotopyRel from the identity to the constant map at p relative to the singleton {p}. Therefore X is contractible, without any additional radial, cube, orientation or convexity hypothesis on its points.

There is a direct application in positive length coordinates. Let L_Delta consist of the six-tuples l with l_i>0 for all i and Delta(cosh(l_0),...,cosh(l_5))>0. The coordinatewise map l_i -> cosh(l_i) is a homeomorphism from L_Delta to X, with inverse x_i -> arcosh(x_i). Indeed, positive l_i give cosh(l_i)>1; conversely x_i>1 give arcosh(x_i)>0, and cosh(arcosh(x_i))=x_i. These are restrictions of the finite product of the positive cosh/arcosh homeomorphisms. Thus the same contraction makes L_Delta contractible.

The determinant condition also exactly identifies the strict source-formula domain. For a single common vector x with every x_i>1, write N_q(x), A_q(x), B_q(x) for the numerator and the two radicands in the original q-th FourCycleCurvature frame, so rawCos(x,q)=N_q(x)/(sqrt(A_q(x))*sqrt(B_q(x))). In every one of the six original frames, A_q and B_q are positive and A_q*B_q-N_q^2=(x_q^2-1)*Delta(x). Since x_q^2-1>0, positive Delta is equivalent to N_q^2<A_q*B_q, hence to -1<rawCos(x,q)<1. All slots use the same x and Delta; the equivalence does not combine separately chosen realizations.

Consequently L_Delta equals the set L_phi of positive length vectors for which all six original rawCos values at x_i=cosh(l_i) lie strictly between -1 and 1. In these coordinates Delta(cosh(l)) is exactly minus the determinant of LengthGramBody.lengthGram(l), in the original edge order. The same restricted cosh/arcosh homeomorphism therefore makes L_phi contractible as well. Both domains retain their determinant or equivalent strict formula conditions; the entire positive length orthant is not identified with X.

The domain in this theorem is defined directly by six independent matrix entries and the determinant inequality. Identifying it with a domain of native hyperideal edge lengths, or proving a geometric realization under the substitution x_i=cosh(l_i), is a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/GramDomainContraction.full_domain_contractible`
