---
bibkey: platttrudgian2021rh
authors: Dave Platt and Tim Trudgian
year: 2021
title: The Riemann hypothesis is true up to 3·10^12
doi: 10.1112/blms.12460
url: https://arxiv.org/abs/2004.09765v1
claim: Published verification supplies the finite-height RH premise. Exact heat-loss factorization and the complete arithmetic block bound give a whole-source negative allowance of order (log T)^(-4) in the original sixth moment; fixed height still leaves a negative allowance.
strata_touched: []
license: citation-only
triage: anchor
---

# Verified zero height and the complete heat loss

## Published suppliers and the additional application

Platt--Trudgian, *The Riemann hypothesis is true up to
$3\cdot10^{12}$*, Bulletin of the London Mathematical Society **53**
(2021), no. 3, 792--797, DOI
[10.1112/blms.12460](https://doi.org/10.1112/blms.12460).
Theorem 1 of the [arXiv v1 primary](https://arxiv.org/pdf/2004.09765v1),
printed p.2, states verification through height $3000175332800$.
This published computation is reused, without repeating or independently
certifying it.

For $T\ge3$, write $\mathsf{RH}(T)$ for the assertion that every
nontrivial zeta zero with $|\Im\rho|\le T$, including the height
boundary, lies on $\Re\rho=1/2$. The source supplies this premise at
$T_0=3\cdot10^{12}$; it does not supply unbounded verified heights.

The [existing actual-source account](suzuki2026screw.md#a-finite-verified-zero-height-controls-the-entire-actual-negative-allowance),
W359 and W365--W371, supplies the exact full-form identification,
weighted profile bounds and entire signed zero tail. Its allowance is
$O(M(F)(\log T)^{-1/3})$. These results are reused unchanged.
The general two-pole arithmetic interface is already owned by
[the non-even localization account](frankliebseiringer2006hardy.md#ordinary-windows-require-both-poles).
The strip transport below reuses
[Tao, Proposition 3(i)](../Fourier/tao2021stripfourier.md), with its
integrable strip-decay hypothesis verified on a smooth compact core.
[Trudgian, Theorem 1](trudgian2014pnt.md) supplies the all-prime-power
Chebyshev bound. None of these suppliers is reproved as new content.

The additional, repo-derived application factors the ENTIRE heat loss
into the same arithmetic form evaluated on an odd auxiliary test.
The positive logarithmic Gamma part then pays its complete quadratic
arithmetic debit, with no mixed-error estimate. The ingredients are
classical contour transport, weighted block estimates and scalar
minimization. No new general Fourier or explicit-formula theorem,
literature-priority claim or Lean/kernel certification is made.

## The original full-source allowance

Retain W317's actual domain $\mathcal V$, COMPLETE energy
$\mathfrak E(F)$ and original sixth moment $M(F)$, and W338's even
profile $g_F$. There is a finite absolute $C$, independent of $T$,
source, scalar field, coefficients, count, width and support, such that

$$
\mathsf{RH}(T)\quad\Longrightarrow\quad
\mathfrak E(F)\ge-\frac{C M(F)}{(\log T)^4}
\qquad(T\ge3,\ F\in\mathcal V).
\tag{VHR1}
$$

It suffices to consider $\mathfrak E(F)\le0$: positive-energy sources
already satisfy this lower bound. If $M(F)=0$, the source is zero.
Otherwise put $M=M(F)>0$, $g=g_F$, $b=5/2$, and write

$$
\|v\|_a^2=\int_{\mathbb R}e^{2a|x|}|v(x)|^2dx,
\qquad
\mathcal L(v)=\int_{\mathbb R}\log(2+|\tau|)
                         |\widehat v(\tau)|^2d\tau.
$$

Use the unitary Fourier convention with kernel $e^{-i\tau x}$.
W366, ONLY on this nonpositive-energy class, gives
$\|g\|_b^2+\mathcal L(g)\le CM$. W359 gives exactly
$\mathfrak E(F)=\alpha\mathcal Q_W(g)$,
$\alpha=2/\sqrt\pi>0$. No Gamma bound from the moment alone is assumed.

### Factor the complete filtering loss with an analytic signed root

Define

$$
j(z)=\frac{1-e^{-2z^2}}{z^2},\quad j(0)=2.
$$

Its nonzero zeros satisfy $z^2=\pi i k$, $k\in\mathbb Z\setminus\{0\}$.
Thus it has no zero on the simply connected strip
$|\Im z|<\sqrt{\pi/2}$. Let $s$ be the holomorphic square root there
with $s(0)=\sqrt2$, and set $m(z)=zs(z)$. Uniqueness makes $s$ even
and Schwarz-real, so $m$ is odd and Schwarz-real, and

$$
m(z)^2=1-e^{-2z^2},\qquad
|m(z)|^2\le1+e^{2(\Im z)^2},\qquad |m(\tau)|\le1
\quad(\tau\in\mathbb R).
\tag{VHR2}
$$

This is the SIGNED analytic root on the real line, rather than its
nonnegative absolute value, which is not analytic at zero.
Fix $0<\eta<\sqrt{\pi/2}$ and restrict to sufficiently small
$\epsilon>0$ that $\sqrt\epsilon\,b<\eta$. Define

$$
\widehat h(\tau)=e^{-\epsilon\tau^2}\widehat g(\tau),
\qquad
\widehat u(\tau)=m(\sqrt\epsilon\,\tau)\widehat g(\tau).
\tag{VHR3}
$$

The multiplier in the second formula is holomorphic on a neighborhood
of the closed strip $|\Im\tau|\le b$ and bounded there by a constant
depending only on $\eta$, uniformly in small $\epsilon$.
For smooth compactly supported $g$, the product with $\widehat g$
has rapid decay on every smaller closed strip. Apply the cited
strip-translation identity to this product, with angular-frequency
normalization, and then Plancherel on the two lines $\Im\tau=\pm b$:

$$
\begin{aligned}
\|e^{\pm bx}u\|_2
&=\|m(\sqrt\epsilon(\tau\pm ib))
             \widehat g(\tau\pm ib)\|_2\\
&\le C_\eta\|e^{\pm bx}g\|_2.
\end{aligned}
$$

The margin beyond $b$ verifies the source theorem's open-strip
hypothesis. Since $e^{2b|x|}$ and $e^{2bx}+e^{-2bx}$ are comparable,
smooth compact approximation in the weighted $L^2$ norm extends this
estimate to every present $g$. Real-axis contraction also gives
$\mathcal L(u)\le\mathcal L(g)$. The existing weighted heat bound
supplies the same domain control for $h$. Consequently

$$
\|u\|_b^2+\|h\|_b^2+\mathcal L(u)+\mathcal L(h)\le CM.
\tag{VHR4}
$$

The auxiliary $u$ is ODD, also for complex even $g$. Neither $u$ nor
$h$ is asserted to be another actual source profile.

### Keep both poles in the exact loss identity

For arbitrary tests in this weighted logarithmic form domain, use the
existing full arithmetic expression

$$
\begin{aligned}
\mathcal Q_{\rm full}(v)
&=\Gamma_q(v)-2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}R_v(\log n)
                  +P_{\rm full}(v),\\
\Gamma_q(v)&=\int q(\tau)|\widehat v(\tau)|^2d\tau,
\quad q(\tau)=\Re\operatorname{digamma}(1/4+i\tau/2)-\log\pi,\\
R_v(t)&=\Re\int v(x)\overline{v(x-t)}dx,\\
A_\pm(v)&=\int e^{\pm x/2}v(x)dx,
\qquad P_{\rm full}(v)=2\Re(A_+(v)\overline{A_-(v)}).
\end{aligned}
$$

Here $\Lambda$ includes EVERY prime power. This agrees with
$\mathcal Q_W$ on even tests. Absolute arithmetic convergence follows
from the block estimate below, and the Gamma integrals are finite by
VHR4, so all three displayed values are defined.

Plancherel and VHR2--VHR3 give
$R_g(t)-R_h(t)=R_u(t)$ for every shift $t$, and the Gamma difference
is exactly $\Gamma_q(u)$. At the poles, Fourier--Laplace transport
on the interior lines $\Im\tau=\pm1/2$ gives

$$
A_\pm(h)=e^{\epsilon/4}A_\pm(g),\qquad
A_\pm(u)=m(\pm i\sqrt\epsilon/2)A_\pm(g).
$$

Schwarz symmetry and VHR2 imply

$$
A_+(u)\overline{A_-(u)}
=(1-e^{\epsilon/2})A_+(g)\overline{A_-(g)}.
$$

Thus the pole difference also matches, and

$$
\boxed{\mathcal Q_W(g)-\mathcal Q_W(h)=\mathcal Q_{\rm full}(u).}
\tag{VHR5}
$$

In particular, the odd $u$ has a nonpositive pole term; an even-only
positive pole square would give a false identity. The formula uses
the full ARITHMETIC form on $u$, without asserting a new non-even
zero-side explicit formula or an equality of operator domains.

### Bound the entire arithmetic debit at its block endpoint

For $I_j=[j,j+1)$ and $0<c<b$, put

$$
a_j(v)=\|v\|_{L^2(I_j)},\qquad
\mathcal A_c(v)=\sum_{j\in\mathbb Z}e^{c|j|}a_j(v).
$$

The classical two-norm split gives

$$
\mathcal A_c(v)\le C_{b,c}
             \|v\|_0^{1-c/b}\|v\|_b^{c/b}.
\tag{VHR6}
$$

For completeness, split at an integer $N\ge0$. Cauchy--Schwarz and
geometric sums bound the central and tail sums by
$C_{b,c}(e^{cN}\|v\|_0+e^{-(b-c)N}\|v\|_b)$; the weighted block
squared norm is comparable with $\|v\|_b^2$. Choose $N$ within one
of $b^{-1}\log(\|v\|_b/\|v\|_0)$, with the zero case separate.
This proves the displayed application without a limiting
$c\downarrow1/2$ constant or an extra logarithmic factor.

The cited all-prime-power theorem gives $\Psi(X)\le CX$ for $X\ge2$;
its explicit error factor is bounded and the remaining bounded range
is absorbed in $C$. It follows that, for integers $d$,

$$
\sum_{\substack{n\ge2\\\log n\in[d-1,d+1]}}
       \frac{\Lambda(n)}{\sqrt n}\le Ce^{|d|/2}.
$$

For a fixed block pair $(j,k)$, the correlation of
$v\mathbf1_{I_j}$ and $w\mathbf1_{I_k}$ is supported in
$t\in[j-k-1,j-k+1]$ and bounded by $a_j(v)a_k(w)$.
Tonelli and $|j-k|\le|j|+|k|$ therefore give

$$
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 \left|\int v(x)\overline{w(x-\log n)}dx\right|
\le C\mathcal A_{1/2}(v)\mathcal A_{1/2}(w).
$$

The negative shifts have the same bound. Both exponential pole
functionals have absolute value at most $C\mathcal A_{1/2}(v)$.
Writing $\mathcal B_{\rm full}$ for the complete prime-and-pole part,
VHR6 with $c=1/2$, $b=5/2$ consequently gives

$$
|\mathcal B_{\rm full}(v,v)|
\le C\|v\|_0^{8/5}\|v\|_b^{2/5}.
\tag{VHR7}
$$

This is an absolute bound on the entire prime-and-pole part, with all prime powers
and both poles. It assumes no favorable arithmetic sign.

### Pay this quadratic loss from the same Gamma contribution

Set $H=\log(1/\epsilon)$ and split frequency at
$R=\epsilon^{-1/4}$. Since
$|m(\sqrt\epsilon\,\tau)|^2=1-e^{-2\epsilon\tau^2}$ on the real line,

$$
\int_{|\tau|<R}|\widehat u(\tau)|^2d\tau
\le2\sqrt\epsilon\,\|g\|_0^2\le C\sqrt\epsilon M.
$$

The owned digamma bounds give $q\ge q_0=q(0)$ everywhere and
$q(\tau)\ge cH$ for $|\tau|\ge R$ when $H$ is sufficiently large.
Keeping the high-frequency contribution and paying the low part yields

$$
\Gamma_q(u)\ge cH\|u\|_0^2-CH\sqrt\epsilon M.
$$

Put $r=\|u\|_0^2/M$. VHR4--VHR7, all on the SAME actual $g$ and
its ONE loss test $u$, give

$$
\mathcal Q_W(g)\ge\mathcal Q_W(h)
 +M[cHr-Cr^{4/5}-CH\sqrt\epsilon].
\tag{VHR8}
$$

Direct minimization over the one real variable $r\ge0$ gives
$cHr-Cr^{4/5}\ge-C'H^{-4}$; the minimizer is proportional to
$H^{-5}$. Also $He^{-H/2}=O(H^{-4})$. Hence

$$
\mathcal Q_W(g)\ge\mathcal Q_W(h)-CMH^{-4}.
\tag{VHR9}
$$

The auxiliary quadratic loss, rather than a mixed comparison with
$g-h$, is what permits this absorption. No desired full-form sign
has been assumed.

### Reuse the signed zero tail and return to original sources

Under $\mathsf{RH}(T)$, W369--W370 already give, for $\epsilon=1/T$,

$$
\mathcal Q_W(h)\ge-CM\sqrt T\log(2+T)e^{-T}.
\tag{VHR10}
$$

Only the inclusively verified zero head is replaced by nonnegative
squares. The entire remaining signed conjugate pairing, multiplicities
and domain passage are reused unchanged. VHR9--VHR10 and W359 prove
VHR1 for large $T$. W317's uniform $\mathfrak E(F)\ge-CM(F)$ pays
the bounded range $3\le T\le T_*$ by enlarging one absolute constant.

The original-source normalization W257 and the completed minima in
W371 consequently give, under the SAME premise,

$$
\begin{gathered}
e_K\ge-\frac{CK}{(\log T)^4}\quad(K>1),\qquad
-\frac{4C}{(\log T)^4}\le e_4\le0,\\
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
\ge-\frac{C}{(\log T)^4}Q_{6,A}(\sigma).
\end{gathered}
\tag{VHR11}
$$

These are the original source, full form and sixth moment, with
arbitrary admitted count, width and real or complex coefficients.
No auxiliary source is normalized or substituted for the actual one.

The constants have not been numerically evaluated, so this is an
asymptotic rate improvement, without a claimed numerical improvement
at $T_0$. No optimality of exponent $4$ is asserted. A fixed verified
height still leaves a negative allowance. Removing it requires
unbounded verified heights or an independent signed estimate.
VHR1--VHR11 establish neither $e_4=0$, all-source positivity, RH,
the same-integer signed Robin tail bound nor strict Robin for every
integer $n>5040$. The application remains a paper derivation, without
Lean/kernel certification.
