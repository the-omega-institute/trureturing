# A second-order threshold bracket with an explicit coefficient

## Abstract

The finite second-order count coefficient determines a corrected center and a K=1 bracket for the same complete original threshold.

**Theorem 1.1 (The unique original threshold satisfies c_p-p^-3<T<=ceil(c_p+p^-3)).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapSecondOrderThresholdBracket.actual_odd_wrap_second_order_threshold_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapSecondOrderThresholdBracket.actual_odd_wrap_second_order_threshold_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd integer p>=5, there is exactly one natural T>2 with the complete original sign criterion: W33<W19 for every natural 2<=t<T, W19<=W33 at T, and W19<W33 for every natural t>T. Every count is the native original_return_pair at p,t and length (p(6t-1)).toNat. In addition, c_p-p^-3<T and (T as an integer)<=ceil(c_p+p^-3), where c_p=alpha*p+1/6+b/p. The lower bound is strict and real; the upper bound is an integer ceiling comparison. Composite odd p are included, and the sign criterion ranges over every natural t>=2.

Use the same positive order-nine d-bonacci Perron root beta9=dbonacciPerronRoot 9, sigma=log(beta9), and alpha=2/(3sigma). Its existing identity beta9+beta9^(-9)=2 gives G(sigma)=2 for G(s)=exp(s)+exp(-9s). The public definition beta_correction supplies b=-1/6+(5sigma/72)(41beta9-81)/(5beta9-9), and this theorem consumes b in both bounds. It is a coefficient definition, with no separate theorem description attached to it.

For integer states in the original band, W19=2(A+D) and W33=4B with A=choose(n,3pt), B=choose(n,3pt+p), D=choose(n,3pt+4p), and n=p(6t-1). Hence 2W19/W33=(A+D)/B. The finite second-order envelope places this ratio within 1/(5p^4) of Q_p(s)=G(s)+H(s)/p^2, where s=4p^2/(n+1) and H(s)=(s^3/48)(5exp(s)-405exp(-9s)). Its two logarithmic moment coefficients 5/48 and 135/16, finite log/exp remainders and combined constant 106183/540000<1/5 provide this error uniformly, without an asymptotic premise.

Put d=b+1/6, g=exp(sigma)-9exp(-9sigma), and k=sigma*d/alpha. The bound 0<d<=1/10 gives -1/6<b<=-1/15, so the corrected center alpha*p+1/6+b/p is strictly below the uncorrected center. The exact Gaussian-coordinate crossing lies at alpha*p+1/6-1/(6p). Positive d raises the corrected center above that coordinate crossing by d/p, while negative b keeps it below the naive centered line. This explains how the simple centered ceiling can fail in a narrow near-integer rounding window, as in the certified p=57425 example; no infinite family of counterexamples or exact ceiling formula for the corrected center follows. The coefficient identity is g*k=H(sigma). For the rational coordinate v=t-1/6+1/(6p), the center is v_c=alpha*p+d/p; write s(v)=2p/(3v) and s_c=s(v_c). The finite cancellation gives |Q_p(s_c)-2|<=1/(10p^4): the displacement of G from its root cancels the leading correction H(sigma)/p^2. This explains why the coefficient changes the threshold estimate, beyond merely bounding the previous error of order p^-2.

On 2/3<=s<=5/7, the corrected function Q_p has secant lower slope 98/75; the proof uses the Gaussian secant bound and the nonnegative secants of H. Shifting v_c by plus or minus p^-3 changes the parameter s by at least 2/(3p^4). The resulting gain dominates both the center residual 1/(10p^4) and the count-envelope error 1/(5p^4), with positive surplus 257/(450p^4). Thus Q_p(s(v_c-p^-3))>2+1/(5p^4) and Q_p(s(v_c+p^-3))<2-1/(5p^4). These are estimates of exponential functions and rational coordinates; the count envelope is applied subsequently at integer states.

The proof first reuses the original unique single crossing, positive cone and coarse bound to put the actual integer T in the band. A T at or below c_p-p^-3 would force 2W19/W33>2, contradicting W19<=W33 at T. For U=ceil(c_p+p^-3), U>=p is covered by T<=p; otherwise U is an admissible integer in the band, the envelope gives W19<W33 at U, and the original before criterion forces T<=U. Counts and binomial identities are used only at integer T and U. All continuous estimates concern exponential functions and rational coordinates; no continuous binomial extension is used.

The result preserves the entire original criterion and adds the finite K=1 bracket. It asserts neither T=ceil(c_p) nor equality of counts at T.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapSecondOrderThresholdBracket.actual_odd_wrap_second_order_threshold_bracket`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope](BajnokBeattyOddWrapGaussianEnvelope.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot](BajnokBeattyOddWrapGaussianRoot.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder](BajnokBeattyOddWrapGaussianSecondOrder.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope](BajnokBeattyOddWrapGaussianUpperEnvelope.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket](BajnokBeattyOddWrapThresholdBracket.md)
