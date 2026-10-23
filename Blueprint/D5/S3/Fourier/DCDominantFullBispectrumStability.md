# DC Dominant Full Bispectrum Stability

## Abstract

Source DC dominance gives explicit stability and signal-ball uniqueness from uncalibrated full complex bispectra.

**Theorem 1.1 (Uncalibrated recovery with a closed error threshold).**

Lean statement: `D5/S3/Fourier/DCDominantFullBispectrumStability.full_bispectrum_stability_dc_dominant`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DCDominantFullBispectrumStability.full_bispectrum_stability_dc_dominant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tamir Bendory, Nicolas Boumal, Chao Ma, Zhizhen Zhao, Amit Singer (2017). *Bispectrum Inversion with Application to Multireference Alignment*. DOI: [10.1109/TSP.2017.2775591](https://doi.org/10.1109/TSP.2017.2775591). URL: <https://arxiv.org/abs/1705.00641v2>.

*Commentary.*

Let N be any positive natural number and let f and g be arbitrary complex signals on ZMod N. Write F and J for their unnormalized negative-exponent discrete Fourier transforms. For real m and epsilon, assume m>0, 0<=epsilon<=m^3/4, and m<=|F(k)|<=|F(0)| for every k. For every pair k,l, assume the raw complex full bispectrum error |J(k)J(l)conj(J(k+l))-F(k)F(l)conj(F(k+l))|<=epsilon. No equality of the DC coefficients or their phases is assumed.

Set R=2 epsilon/m^2. There exists an actual cyclic parameter t in ZMod N such that the counting squared signal error sum_x |g(x)-f(x-t)|^2 is at most R^2, and every coefficient error |J(k)-exp(-2 pi i k t/N)F(k)| is at most R. Every s in ZMod N satisfying only sum_x |g(x)-f(x-s)|^2<=R^2 equals t. Thus uniqueness ranges over all translations in the signal ball. The order-one group, epsilon=0, and the closed endpoint epsilon=m^3/4 are included.

For alpha=|F(0)|, beta=|J(0)|, r=|F(k)| and s=|J(k)|, the zero rows give |beta^3-alpha^3|<=epsilon and |beta s^2-alpha r^2|<=epsilon. Cubic factorization gives beta>=3 alpha/4 and 2 alpha^2 |beta-alpha|<=epsilon. The mixed bound implies beta(r+s)>=3 alpha r/2. Since r<=alpha, the DC amplitude error contributes at most epsilon/2 to the squared-amplitude comparison. Hence m^2 |s-r|<=epsilon, s>=3r/4>0, and rs>=3m^2/4.

Normalize the nonzero coefficients to phases and set w(k)=phase(J(k))conj(phase(F(k))), p(k)=|F(k)||J(k)| and q=3m^2/4. The existing raw weighted defect estimate bounds p(k)p(l)p(k+l)|w(k)w(l)-w(k+l)|^2 by epsilon^2. Since each weight is at least q, the ordinary squared defect is at most 4/27. Weighted character correction selects one genuine additive character chi with p(k)|w(k)-chi(k)|^2<=9 epsilon^2/(4m^4). The radial identity combines this with the amplitude error to give coefficient error squared at most 13 epsilon^2/(4m^4), which is bounded by R^2.

The cyclic character equivalence supplies t as minus the inverse image of chi, matching the translation f(x-t). Counting Parseval turns the average squared coefficient error into the counting squared signal error without a dimension factor. Distinct source translations have squared distance at least 2m^2. Two signal errors at most R^2 would give distance at most 4R^2<=m^2, a contradiction.

DC dominance holds for nonnegative real source signals by the triangle inequality, but nonnegativity does not ensure a nonvanishing spectrum. The positive lower bound on every source coefficient remains essential to these hypotheses.

A genuine noisy uncalibrated instance is N=2, f=(1,0), g=(0,a), a=1+i/8, m=1 and epsilon=1/4. Here F=(1,1), J=(a,-a), every source bispectrum entry is 1 and every target entry is 65/64+i 65/512. Each residual has square 4289/262144, strictly between zero and epsilon^2. Both the magnitude and phase of the DC coefficient change. The selected translation is t=1, with squared signal error 1/64<=R^2=1/4 and each Fourier error 1/8. This is the closed tolerance endpoint; the raw residual does not saturate that tolerance.

The cited local inverse theorem uses source-dependent constants and Frobenius error on an estimated bispectrum matrix. Its index convention agrees after the permutation (k1,k2)=(k,k+l), as detailed in the literature note. The present statement concerns the true full bispectrum of an actual candidate signal g. It constructs no estimator for arbitrary noisy matrices and provides no optimization or acquisition guarantee. The calibrated theorem remains applicable to sources without DC dominance; neither set of hypotheses contains the other.

## References

- Truth anchor: `D5/S3/Fourier/DCDominantFullBispectrumStability.full_bispectrum_stability_dc_dominant`
- Dependency: [D5/S3/Fourier/FullBispectrumStability](FullBispectrumStability.md)
