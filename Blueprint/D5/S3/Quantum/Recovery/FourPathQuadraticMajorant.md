# Four-path quadratic majorant

## Abstract

A quadratic majorant for the four-path record at every complex pair.

**Theorem 1.1 (The complete complex quadratic majorant).**

$$\forall xi \in \mathbb{C}, eta \in \mathbb{C},\; \left(\frac{\operatorname{norm}\left(xi + eta\right) + \operatorname{norm}\left(xi - eta\right)}{\operatorname{sqrt}\left(2\right)} + \operatorname{norm}\left(\operatorname{cos}\left(\frac{\pi}{8}\right) \cdot xi + i \cdot \operatorname{sin}\left(\frac{\pi}{8}\right) \cdot eta\right) + \operatorname{norm}\left(\operatorname{cos}\left(\frac{\pi}{8}\right) \cdot xi - i \cdot \operatorname{sin}\left(\frac{\pi}{8}\right) \cdot eta\right)\right)^{2} \le \left(\operatorname{sqrt}\left(2\right) + 2 \cdot \operatorname{cos}\left(\frac{\pi}{8}\right)\right)^{2} \cdot \operatorname{norm}\left(xi\right)^{2} + \left(\operatorname{sqrt}\left(2\right) + 2 \cdot \operatorname{sin}\left(\frac{\pi}{8}\right)\right)^{2} \cdot \operatorname{norm}\left(eta\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathQuadraticMajorant.four_path_quadratic_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variables xi and eta range independently over all complex numbers. The constants are the actual cosine and sine of pi/8; i denotes the imaginary unit and norm denotes complex modulus. The estimate includes the zero pair, both coordinate axes, every relative phase and every scale.

For nonnegative u and v with u squared plus v squared equal to two, the paired response u+v is at most 2-(u squared-v squared) squared/16. Applying this estimate to the two pairs of norms retains separate deficits in the real and imaginary parts of xi times the conjugate of eta.

After normalization, put p=|xi| squared, q=|eta| squared, x=Re(xi conjugate(eta)), y=Im(xi conjugate(eta)), a=sqrt(c squared p+s squared q), m=cp+sq and L=sqrt(2+4a squared+4sqrt(2)m). Then x squared+y squared=pq. The two deficits are x squared/sqrt(2) and y squared/(8a cubed).

The difference sqrt(2)+2a-L equals 4sqrt(2)(c-s) squared pq divided by (a+m)(sqrt(2)+2a+L). Lower bounds on this positive denominator make the difference at most each of pq/sqrt(2) and pq/(8a cubed). The second bound uses m at least 9a/10 and positivity on [0,15/16] of the concave polynomial 19sqrt(2)/5+361t/50-32(sqrt(2)-1)t squared. Combining the complementary deficits gives the required bound by L. Squaring and homogeneous rescaling prove the displayed inequality.

This estimate is the pointwise analytic ingredient in the four-path full-record recovery bound. It does not assert a channel diamond optimum or an attaining feedback protocol.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathQuadraticMajorant.four_path_quadratic_majorant`
