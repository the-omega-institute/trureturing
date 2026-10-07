# The Exact Positive Laplace Three-Point Approximation Error of the Actual Curvature

## Abstract

The literal Phi curvature has an exact positive-measure Laplace approximation error at every three-point midpoint triple in one positive interval, with a positive single atom attaining the bound.

Use the same actualPhi(v)=exp(integral from 0 to 1 of (1-exp(-v*b))/b), and the literal curvature B=deriv(deriv actualPhi). Exact derivatives at zero supply one common positive interval before endpoints, the positive scalar, or a measure are selected.

**Theorem 1.1 (Literal zero values, a joint interval, and a sharp attained three-point error).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal curvature has B(0)=1/2 and B'(0)=B''(0)=-1/6. There exists eta>0 such that every 0<v<eta has B(v)>0, B'(v)<0, and B''(v)<0. The same actual interval supports strict decrease and strict concavity.

For any 0<a<b<eta and c>0 put m=(a+b)/2, x=c*B(a), y=c*B(m), z=c*B(b), and K=(y*y-x*z)/(2*y+x+z). Then K>0. For every positive measure mu on the real line with exp(-a*t), exp(-b*t), and exp(-m*t) genuinely integrable, at least one of the three absolute errors between those exponential integrals and x,y,z is at least K. The comparison class has no total-mass or support restriction.

The same result constructs tau>0 and w>0. The explicit positive measure ENNReal.ofReal(w) times the Dirac measure at tau has genuinely integrable exponential kernels at every real parameter v, and its integral equals w*exp(-v*tau). At a,m,b all three absolute errors equal the same K. Since tau>0, an atom on the positive axis already attains the unrestricted lower bound.

Private actual moments with all-real derivatives M_j'=-M_(j+1) bind the literal second, third and fourth derivatives. At zero the exact moments give 1/2,-1/6,-1/6. Continuity supplies the entire joint interval, using a genuine compact-input bound for parameter differentiation.

For the prospective measure, integrate the nonnegative square of s*exp(-b*t/2)-exp(-a*t/2). The three explicit integrability hypotheses pay the polynomial expansion. Its discriminant is nonpositive, giving L(m)^2<=L(a)*L(b) without differentiating the measure or dividing by its mass.

Actual strict concavity pays y*y>x*z and K>0. The sharp formula gives y-K>0 and (y-K)^2=(x+K)*(z+K). If every error were less than K, the midpoint square would exceed the endpoint product, contradicting the integral inequality. Strict decrease gives x>z, so tau=log((x+K)/(z+K))/(b-a) is positive. With w=(x+K)*exp(a*tau), the atom takes values x+K,y-K,z+K and attains all three errors.

PrimorialGlobalLaplaceEnvelope supplies the literal Phi, actual rate, first derivative and zero value. The private dominated moment derivative body extends PrimePrefixPhiCurvature, originally supplied by PrimorialFirstOrderConcentrationCounterexample. Mathlib supplies dominated interval differentiation, derivative criteria for strict concavity and decrease, quadratic discriminants, and actual Dirac measure integrals. These private bridges are consumed by the one actual-object result.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction.result`
- Dependency: [D5/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope](PrimorialGlobalLaplaceEnvelope.md)
