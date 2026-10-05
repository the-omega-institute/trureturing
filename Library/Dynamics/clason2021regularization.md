---
bibkey: clason2021regularization
authors: Christian Clason
year: 2021
title: Regularization of Inverse Problems
doi: null
url: https://arxiv.org/abs/2001.00617v2
claim: The linear Tikhonov normal equation applies to the actual compact theta-translation map in the negative-edge metric. Fitted-source convergence is distinct from coefficient convergence and from a uniform projection error rate.
strata_touched: []
license: citation-only
triage: anchor
---

# Regularization of Inverse Problems

## Source contract

The inspected [arXiv v2 lecture notes](https://arxiv.org/pdf/2001.00617v2)
identify the version on the title page. Section 6, printed pp.58–60,
Lemma 6.3 and equation (6.1), give the normal equation for arbitrary
Hilbert-space data $y$ and positive $\alpha$:

$$(L^*L+\alpha I)x_\alpha=L^*y.$$

The section uses the filter $1/(\lambda+\alpha)$ and residual
$\alpha/(\lambda+\alpha)$. Theorem 5.6, printed p.48, asserts
coefficient convergence only for data in the pseudoinverse domain;
Corollaries 6.1–6.2, printed p.59, require source conditions for rates.
Neither supplies an unconditional coefficient limit or a rate for the
project's theta inputs. The inspected PDF SHA-256 is
`696b4f580464ec0e1da6a1863b91d9142aa58b8b841b8ea437b5944152cd649e`.
The generic normal equation, filters and resolvent identity are reused.

The following is a conditional paper application under the
[actual theta form, critical-family and negative-edge metric premises](../Weil/lagarias2004li.md).
Use its $c_*=11/2500$ on the centered even space $\mathcal H_0$,
$B=C_-^*C_-$ and closed critical source $N$. The source supplies no
arithmetic half-bound, original-operator spectral estimate or Lean
certification. This application preserves the original $\nu$ and both
edge maps. It constructs a regularized coefficient problem, without
claiming a certified finite numerical solution.

## Actual theta translations generate the critical source

Take r=1/16, I=[-r,r] with Lebesgue measure, and define

$$w_t(x)=\frac{\Phi(x+t)+\Phi(x-t)}{2\Phi(x)}-\cosh(t/2).\tag{R1}$$

For real t in I, w_t is even and nu-centered: shift the two integrals against cosh(x/2). On the complex box |Re z|,|Im z|<1/8, the inherited theta series and positive real first-term lower bound give a common squared-ratio majorant on either tail,

$$C e^{5|x|}\exp\{-\pi[2e^{-1/4}\cos(1/4)-1]e^{2|x|}\}.$$

The bracket is positive (e^-1/4>=3/4 and cos(1/4)>=31/32). On compact x intervals Phi has a positive minimum. Thus z->w_z is an H_0-valued holomorphic function on a neighborhood of I, and

$$w_t=\sum_{k\ge1}\frac{t^{2k}}{(2k)!}v_k,\qquad\overline{\operatorname{span}\{w_t:t\in I\}}=N.\tag{R2}$$

The first inclusion uses norm convergence of the Taylor series; the reverse uses Hilbert-valued difference quotients at zero. This does not use all real translations or a characterization by the complete zero set.

Define F:L2(I)->H_0 by Fq=integral_I w_t q(t)dt. It is Hilbert–Schmidt, its range closure is N, and every actual Fq lies in N and hence in the accepted form domain. Its adjoint is F*g(t)=<w_t,g> with the usual inner product antilinear in the first variable. The positive compact coefficient Gram K=F*BF has the actual kernel

$$\kappa(s,t)=\langle C_-w_s,C_-w_t\rangle
=\frac14\iint a(x,y)\overline{\Delta w_s(x,y)}\Delta w_t(x,y)d\nu(x)d\nu(y).\tag{R3}$$

## An explicit regularized common-source correction

For epsilon>0 and h in the actual form domain, h_0=h-nu(h)1, solve the bounded-window Fredholm normal equation

$$(K+\varepsilon I)q_\varepsilon=F^*Bh_0,\qquad n_\varepsilon=Fq_\varepsilon.\tag{R4}$$

The coefficient inverse has norm<=1/epsilon and involves no exact P_N. It is the standard Tikhonov fit for L=B^(1/2)F and datum g=B^(1/2)h_0. Its fitted signal, not necessarily its coefficient vector, converges to P_M g, M=B^(1/2)N (closed because B>=c_*I on H_0). Thus n_epsilon converges in H_0 and in both critical edge norms to the same n_h=G^-1 P_N Bh_0 from G4. Coefficients q_epsilon need not converge: g's projection may lie only in the closure of Ran L. Each n_epsilon belongs to N, so q(h-n_epsilon)=q(h) exactly.

For A=L L*, with spectral measure E_A, its remaining paired-edge error is exactly

$$\|C_\pm(n_h-n_\varepsilon)\|^2
=\int_{(0,\|A\|]}\left(\frac\varepsilon{\lambda+\varepsilon}\right)^2d\langle E_A(\lambda)g,g\rangle.\tag{R5}$$

The zero eigencomponent is excluded. Since M is infinite dimensional while A is compact, eigenvalues on M tend to zero. The fitted-filter error has operator norm 1 on M for every epsilon>0. Strong convergence therefore provides no uniform rate over all unit inputs, and no actual source condition or small-spectral-value mass bound has been proved for the required input class. The source's Theorem 5.6 applies only on the pseudoinverse domain; it is not used to infer bounded convergence of these coefficient vectors.

## A finite-epsilon approximation bound with the same source

Suppose F_m maps L2(I) into a finite span of actual w_t, ||F-F_m||<=delta, and ||F||<=M_F. Define K_m=F_m* B F_m and n_epsilon,m=F_m(K_m+epsilon I)^-1 F_m*Bh_0. The usual resolvent identity for A and A_m=B^(1/2)F_mF_m*B^(1/2) gives

$$\|C_\pm(n_\varepsilon-n_{\varepsilon,m})\|
\le\frac{\delta(2M_F+\delta)}{2\sqrt2\,\varepsilon}\|h_0\|.\tag{R6}$$

Both differences lie in N, so this is a common paired edge norm bound; the source norm bound is R6 divided by sqrt(c_*). With m equal cells of I and midpoint w_t samples, one may take delta<=L_w(2r)^(3/2)/(sqrt(12)m), where L_w is an independently validated upper bound for sup_I||w'_t||. The [directed small-window bounds](../../docs/reports/theta-mixed-matrix/theta-translation-bounds.md) supply numerical M_F and L_w for this interface. No finite Fredholm matrix has been certified here. R6 controls discretization for fixed epsilon; it does not pay the regularization error R5.

## Finite epsilon does not erase the old exact raw Schur obstruction

Let P_epsilon=F(K+epsilon I)^-1 F*B on H_0. The classical Woodbury identity gives

$$(I-P_\varepsilon)^{-1}=I+\varepsilon^{-1}FF^*B.\tag{R7}$$

Extend $P_\varepsilon$ by zero on constants, equivalently $P_\varepsilon h=P_\varepsilon(h-\nu(h)1)$; the inverse in (R7) extends by identity on constants. This agrees with the ambient formula because $B1=0$. Both operators preserve the actual form domain because their correction has range in $N$ and is bounded into its form norm. Suppose an ordinary measurable kernel $S$ has a finite, strictly positive weighted absolute Schur certificate of product at most one and exactly reconstructs $C_-(I-P_\varepsilon)h$ from $C_+(I-P_\varepsilon)h$ for every original core input. Schur supplies boundedness of $S$, so core density first extends that identity to the actual form domain. Equation (R7) then gives exact reconstruction of the original raw $C_\pm$ there. The already accepted theta-Schur obstruction excludes this certificate. This is reuse of that obstruction, not another fiber proof. Approximate reconstruction, absolute products>1 tending to1 and better actual norm estimates remain distinct possibilities.

The concrete new interface is R1–R4: it replaces an unspecified P_N primitive by a small-window integral kernel and a regularized normal equation, with the separately controlled discretization error R6. The outstanding estimate is the actual input's small-spectral-value error R5, or a directly certified complementary residual B(h-n)-w with w in N-perp, followed by a jointly reconstructed and norm-bounded projected transfer. No half-bound, RH/Robin proof, complete zero-set characterization or executable full-space approximation algorithm is claimed.


## Numerical inputs for the fixed-parameter discretization bound

The [actual-theta translation norm computation](../../docs/reports/theta-mixed-matrix/theta-translation-bounds.md)
uses the existing derivative supplier and the full original probability
measure, including both spatial tails. Its outward interval bounds give

$$L_w<9/2,\qquad \|F\|\le\|F\|_{\mathrm{HS}}<3/50,\qquad
\|F-F_m\|\le\frac{3}{50m}.$$

Substitution into R6 yields, for every positive epsilon and m equal
midpoint cells, the same-source bound

$$\|C_\pm(n_\varepsilon-n_{\varepsilon,m})\|
\le\frac{9}{5000\sqrt2\,\varepsilon}
\left(\frac2m+\frac1{m^2}\right)\|h_0\|.$$

At epsilon=1/100 and m=256, its coefficient is strictly below 1/1000.
This pays the fixed-parameter discretization term only. The actual-input
regularization error R5, kernel-entry quadrature, a uniform complementary
residual on the required input class and the projected reconstruction/norm estimate
remain unresolved. No new original-energy lower bound or Lean
certification is supplied.

## One fixed quadratic-input complementary residual

The [direct actual-operator enclosure](../../docs/reports/theta-mixed-matrix/theta-common-residual-bounds.md)
uses seven finite critical directions and eight individual certified real
Xi-zero witnesses for h=x^2. Under the inherited actual-model and
numerical-supplier premises it supplies
||B(h-n)-w||<9/8000, with n in N and w in N-perp. The accepted inverse
constant c*=11/2500 converts this to ||n_h-n||<=45/176 and paired edge
errors <=9/(160 sqrt(11)). The 512 retained point rows are reused;
derivative transport, all theta series and full spatial tails are paid.
This is a bounded-B input calculation, without asserting original
form-domain membership of x^2. Its upper enclosure does not reach 1e-4
and is not a lower bound on attainable residuals. It supplies neither
R5 on the required input class nor the projected transfer/norm comparison,
original half-bound, Robin or RH, and has no new Lean certification.
