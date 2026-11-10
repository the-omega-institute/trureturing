# A finite second-order Gaussian envelope for the original returns

## Abstract

Finite logarithmic moments identify a second-order coefficient for the complete original odd-wrap count ratio, with an explicit fourth-order error.

**Theorem 1.1 (The original normalized ratio differs from G(s)+H(s)/p^2 by at most 1/(5p^4)).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder.actual_gaussian_second_order_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder.actual_gaussian_second_order_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p>=5 odd, 2<=t<=p and 24p<=25t. Put n=p(6t-1), s=4p^2/(n+1), G(s)=exp(s)+exp(-9s), and H(s)=(s^3/48)(5exp(s)-405exp(-9s)). The theorem states |2W19/W33-G(s)-H(s)/p^2|<=1/(5p^4). The counts are the complete original_return_pair at length n.toNat, with W19 in role 0 and W33 in role 1. All odd p>=5, including composites, and all equality endpoints allowed by the band are retained.

Set A=choose(n,3pt), B=choose(n,3pt+p), and D=choose(n,3pt+4p), with the source's exact integer-to-natural index conversions. The native count identities are W19=2(A+D) and W33=4B, and B>0, so 2W19/W33=(A+D)/B. This is the same original count family used by the Gaussian envelopes; no substitute states or unrelated numerical readouts enter the statement.

Write R=n+1, x_i=(p+2i+1)/R for 0<=i<p, and y_j=(3p+2j+1)/R for 0<=j<3p. The exact adjacent-binomial products give L=log(A/B) and M=log(B/D). Their linear logarithmic parts sum exactly as 2*sum_i x_i=s and 2*sum_j y_j=9s. Since D/B is the reciprocal of B/D, its leading block is exp(-9s). The exponent nine is the squared ratio of the two finite displacements, connecting the original count geometry to the existing order-nine Perron root. These exact sums concern the linear parts; the complete logarithms retain the cubic and higher remainders controlled here. Their cubic moments are X3=2p^2(5p^2-1)/R^3 and Y3=18p^2(45p^2-1)/R^3. Finite logarithmic remainders yield L=s+(2/3)X3+EL and M=9s+(2/3)Y3+EM. In particular (2/3)X3=(5/48)s^3/p^2-s^3/(48p^4), while (2/3)Y3=(135/16)s^3/p^2-3s^3/(16p^4). The leading cubic coefficients have ratio (135/16)/(5/48)=81=3^4, while the finite p^-4 correction coefficients have ratio (3/16)/(1/48)=9=3^2. Both powers come from the same finite displacement geometry. Thus the exact coefficients 5/48 and 135/16 determine H after exponentiating the two blocks.

On the full band, R>=28p^2/5, 2/3<=s<=5/7, 0<=x_i<=3/28 and 0<=y_j<=9/28. A finite cubic logarithm remainder, retaining its parameter-dependent fifth-order tail, gives |L-s-(5/48)s^3/p^2|<=1/(30p^4) and |M-9s-(135/16)s^3/p^2|<=27/p^4. The finite exponential estimates |exp(u)-1-u|<=(3/4)u^2 for 0<=u<=1 and |exp(-u)-1+u|<=u^2/2 for u>=0 then control the two displacements. The bounds exp(s)<9/4 and exp(-9s)<1/300 keep the negative block small.

After multiplication by p^4, the two block errors are at most 777/10000 and 2569/21600. Their sum is 106183/540000<1/5, giving the stated finite error after exact Nat/Int transport and the original-count bridge. There is no asymptotic premise. Retaining H(s)/p^2 resolves the coefficient hidden by the earlier error of order p^-2; this is the quantitative input that permits the corrected threshold center to be controlled on the p^-3 scale.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder.actual_gaussian_second_order_envelope`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope](BajnokBeattyOddWrapGaussianEnvelope.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope](BajnokBeattyOddWrapGaussianUpperEnvelope.md)
