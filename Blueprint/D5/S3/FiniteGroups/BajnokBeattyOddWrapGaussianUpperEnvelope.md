# Finite Gaussian upper envelope for the original quotient returns

## Abstract

A finite logarithmic remainder gives a strict Gaussian upper envelope for the complete original odd-wrap return counts.

**Theorem 1.1 (The exact normalized count ratio lies strictly below G(s)+1/(10p^2) in the stated band).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope.actual_gaussian_upper_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope.actual_gaussian_upper_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p>=5 odd, 2<=t<=p and 24p<=25t. Put s=4p^2/(p(6t-1)+1) and G(s)=exp(s)+exp(-9s). For the same complete original quotient return counts at m=6t-1 and length (p*m).toNat, the theorem proves 2W19/W33<G(s)+1/(10p^2). Composite odd p and every equality endpoint allowed by the constraints are retained. Together with actual_gaussian_envelope this gives G(s)<2W19/W33<G(s)+1/(10p^2) throughout this band.

Reuse the same exact binomial quotient (A+D)/B, adjacent-binomial products and cubic moment X3. The band gives R>=28p^2/5, s<=5/7<3/4 and 0<=x_i<=3/28. The finite logarithm remainder gives 0<=delta=log(A/B)-s<=((2/3)+(18/775))*X3, with delta*p^2<=10025/255192<1/25 and delta<=1/625. The second block supplies log(B/D)>=9s and hence D/B<=exp(-9s).

Convexity of exp on [0,1/10], together with an exact finite endpoint certificate, yields exp(delta)<=1+(11/10)*delta. Another finite certificate gives exp(s)<9/4. Consequently (A+D)/B<=G(s)+(99/40)*delta, and the exact delta bound makes this last error strictly smaller than 1/(10p^2). Every remainder is bounded on the full stated integer band; no asymptotic replacement is used.

The existing original count formulas identify (A+D)/B=2W19/W33 with all original integer-to-natural index conversions. The additional assumptions p>=5 and 24p<=25t belong to this upper theorem and must be retained when applying it. This finite error estimate supplies no exact threshold or ceiling formula, and no literature novelty or complete open-problem settlement is claimed.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope.actual_gaussian_upper_envelope`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope](BajnokBeattyOddWrapGaussianEnvelope.md)
