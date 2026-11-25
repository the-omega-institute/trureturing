# Gaussian principal coefficient of the moving Fejer integral

## Abstract

A growing fourth-moment window captures the Gaussian principal contribution of the Fejer integral.

For finite families of real frequencies g_n and real weights w_n, let S_n(t) be their complex Fourier score, W_n their total weight, and M_n(k) the sum over ordered pairs of w_n(i)w_n(j)(g_n(i)-g_n(j))^k. Set s_n=sqrt(n M_n(2)/2), R_n=M_n(4)/(n M_n(2)^2), and P_n(u)=|S_n(u/s_n)|^(2n). For real sequences rho and A, write I(n) for 1/(2 pi) times the oriented integral of sinc(rho(n)u/2)^2 P_n(u) from -A(n) to A(n).

**Theorem 1.1 (Central Gaussian integral limit).**

$$\left(\left(\operatorname{Eventually}\left(\operatorname{PairNonnegative}\left(w\right)\right) \land \left(\operatorname{Eventually}\left(W = 1\right) \land \operatorname{Eventually}\left(0 < \operatorname{M}\left(2\right)\right)\right)\right) \land \left(\left(\lim_{n \to \infty} \operatorname{rho}\left(n\right) = 0 \land \lim_{n \to \infty} \operatorname{A}\left(n\right) = \infty\right) \land \operatorname{Eventually}\left(\operatorname{A}\left(n\right)^{2} \cdot \operatorname{M}\left(4\right) \le 6 \cdot n \cdot \operatorname{M}\left(2\right)^{2}\right)\right)\right) \Rightarrow \lim_{n \to \infty} \operatorname{I}\left(n\right) = \frac{1}{2 \cdot \sqrt{\pi}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal.central_fejer_gaussian_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume eventually all pair products are nonnegative, W_n=1, M_n(2)>0, and A(n)^2 M_n(4)<=6 n M_n(2)^2. Assume also rho tends to zero and A tends to positive infinity. The window condition implies 0<=R_n<=6/A(n)^2 eventually, so R_n tends to zero. The central power limit gives pointwise convergence of P_n to exp(-u^2), and the sinc factor tends to one at every fixed u. On the inner half-window the global fourth-moment estimate provides an integrable Gaussian envelope. Extend by zero outside this half-window and apply dominated convergence. On either outer half-window the score power is bounded by exp(-u^2(1-u^2/A(n)^2)), which is at most exp(-(A(n)/4)(A(n)-|u|)). The sinc factor has square at most one. Integrating the two outer halves gives a total bound of 8/A(n), tending to zero. The integral of exp(-u^2) is sqrt(pi), yielding the coefficient 1/(2 sqrt(pi)). For any eventually nonnegative R tending to zero, the choice A(n)=1/sqrt(R(n)+1/(n+1)) tends to positive infinity and eventually A(n)^2 R(n)<1, furnishing an admissible window.

With physical resolution eta_n>0 and scale s_n>0, the angular Fejer kernel is K_eta(t)=eta/(2 pi) sinc(eta t/2)^2. Substituting u=s_n t and rho_n=eta_n/s_n identifies I(n) with s_n/eta_n times the kernel-weighted score-power integral on [-A(n)/s_n,A(n)/s_n]. Contributions outside this interval require independent control.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal.central_fejer_gaussian_limit`
- Dependency: [D5/S3/Analytic/Fourier/AngularFejerKernel](../../Analytic/Fourier/AngularFejerKernel.md)
- Dependency: [D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit](FinitePairGaussianLimit.md)
