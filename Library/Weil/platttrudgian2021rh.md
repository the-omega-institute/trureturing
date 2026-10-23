---
bibkey: platttrudgian2021rh
authors: Dave Platt and Tim Trudgian
year: 2021
title: The Riemann hypothesis is true up to 3·10^12
doi: 10.1112/blms.12460
url: https://arxiv.org/abs/2004.09765v1
claim: Published verification supplies the finite-height RH premise. Exact heat-loss factorization and the complete arithmetic block bound give a whole-source negative allowance of order (log T)^(-4) in the original sixth moment; fixed height still leaves a negative allowance. A support-independent Gamma-only lower bound for the prime Hankel form fails on all compact half-line tests. An even actual-source partition controls the joint metric defect and bounds supporting multipliers of negative cap-four minima from below, up to the finite-height signed zero tail. Its null supporting vector bootstraps every fixed logarithmic order below five and recovers individual branch moments with an explicit inverse-multiplier cost; separation of the finite reconstruction intervals replaces its N-fold Fourier-tail payment by a harmonic factor, giving every fixed joint-metric exponent below five on actual negative minima and a fifth-power rate with a log-log factor on nonpositive-energy sources under RH(T), without improving the general exponent-four negative allowance. For hypothetical unit negative cap-four minimizers with a positive supporting multiplier, retaining the errors' own moments also gives every finite logarithmic order and arbitrary fixed logarithmic-power branch rates. A bounded analytic Sobolev regularizer gives positive-order regularity by commuting with the complete energy and paying both original metric defects; its constants deteriorate exponentially as the multiplier tends to zero and do not improve the uniform negative allowance. The same regularity controls finite physical dilation in the complete energy and both original metrics, including the source error itself, with explicit multiplier costs; the resulting sublinear squared-norm rate gives no dilation derivative or uniform allowance improvement. Directly retaining the regularizer's original moment coordinate then improves the squared-error range to every rho < 2s, with a larger inverse-multiplier cost and still no first-order or uniform allowance conclusion. A fixed actual source with every subcritical Sobolev order has a signed critical metric defect of order (log N)^2 while its regularized original moment is O(log N), excluding a universal endpoint absorption when lambda differs from mu even for unit original sources in any prescribed moment cap K>1; no negative/null-minimizer obstruction is inferred. The same global null equation gives weighted Gamma control at nonnegative multiplier and additional original physical moments at positive multiplier, retaining every theta dilation and the complete mixed debit. Direct physical truncation of the same negative minimizer then preserves its normalized cap and approximates its complete energy at any fixed rate exp(-2 sigma L), sigma<1/4, with constants independent of the supporting multiplier on the bounded branch; a negative deficit delta has a completed physical core of radius O_p(delta^(-p)) for every p>2. No positivity, Gaussian atom-count or uniform allowance improvement follows.
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

## A Gamma-only bound cannot pay the prime Hankel term on all compact tests

The odd loss in VHR3 motivates separating the one-sided translation
and reflection channels. The corresponding even split is already
owned by W338--W340, and W284/W313 already retain and bound the
complete prime Hankel correction. A new copy of those interfaces is
unnecessary. There is, however, an obstruction to replacing their
weighted allowance by a uniform Gamma-plus-$L^2$ lower bound on ALL
compact half-line tests.

This is a repo-derived application of the classical Dirichlet series
for $-\zeta'/\zeta$, the nonnegative Laplace-transform abscissa theorem
and the existence of a nonzero critical-line zero. The Laplace supplier
is the same Landau--Widder theorem already consumed by
[the fixed-shape detector](tlas2020bump.md#connect-the-average-to-the-existing-sign-detector):
Widder, *The Laplace Transform*, Chapter II, Theorem 5b, also explicitly
used in [Suzuki, arXiv:2209.12832v1, section 3](https://arxiv.org/pdf/2209.12832v1),
printed pp.3--4. These classical results are reused, not reproved or
claimed as new Hankel theory. The following argument has not been
Lean/kernel certified and carries no literature-priority claim.

For a real $v\in C_c^\infty((0,\infty))$, let $v^{\rm odd}$ be its
odd full-line extension and retain EVERY prime power in

$$
H_p(v)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       \int_0^{\log n}v(x)v(\log n-x)dx.
$$

This sum is finite for each such $v$. Set

$$
\Gamma_+(w)=\int_{\mathbb R}[q(\tau)-q(0)]
                              |\widehat w(\tau)|^2d\tau\ge0.
$$

There is NO finite constant $K\ge0$ such that

$$
H_p(v)\ge-K\bigl(\|v\|_2^2+\Gamma_+(v^{\rm odd})\bigr)
\qquad\text{for every real }v\in C_c^\infty((0,\infty)).
\tag{VHO1}
$$

In particular, no fixed finite coefficients on Gamma and $L^2$ can
provide the proposed bound without a further source-dependent term
or a restriction of the source domain.

### Translate a fixed test and retain its exact Laplace transform

Suppose the lower bound in VHO1 held for a fixed $K$. Fix real $f\in C_c^\infty((0,L))$, put
$v_R(x)=f(x-R)$ for $R\ge0$, and define

$$
F(z)=\int_{\mathbb R}e^{zx}f(x)dx,\qquad
\kappa=f*f,\qquad h_f(R)=H_p(v_R).
$$

Choose $F(1/2)=0$. Reflection invariance, the nonnegative even Gamma
multiplier and the Fourier triangle inequality give

$$
\Gamma_+(v_R^{\rm odd})\le4\Gamma_+(f),\qquad
h_f(R)\ge-K_f,\qquad
K_f=K\bigl(\|f\|_2^2+4\Gamma_+(f)\bigr).
\tag{VHO2}
$$

The bound is uniform in $R$. Chebyshev gives $h_f(R)=O_f(e^R)$.
For $\Re s>1$, absolute convergence and the substitution
$t=\log n-2R$ give exactly

$$
\begin{aligned}
D_f(s)&:=\int_0^\infty e^{-sR}h_f(R)dR\\
&=\frac12F(s/2)^2
    \left(-\frac{\zeta'}{\zeta}\right)((s+1)/2)+E_f(s),\\
E_f(s)&=-\frac12\sum_{\log n<2L}\Lambda(n)n^{-(s+1)/2}
              \int_{\log n}^{2L}e^{st/2}\kappa(t)dt.
\end{aligned}
\tag{VHO3}
$$

The endpoint correction is entire because its sum is finite.
The factor $F(1/2)^2$ cancels the pole at $s=1$.
The right side is analytic near every positive real $s$ and near
$s=0$: zeta has no real zero in $[1/2,1)$ or $(1,\infty)$.
Since $h_f+K_f\ge0$, the cited nonnegative Laplace theorem forces
its convergence abscissa to be at most zero. Thus its actual integral
converges and is holomorphic on $\Re s>0$, where it agrees with
$D_f(s)+K_f/s$.

Already this consequence would exclude any zero with $\Re\rho>1/2$:
it would give a pole at $s=2\rho-1$ unless $F(\rho-1/2)=0$.
For any designated such zero, choosing
$f=(d/dx+1/2)w$ with a sufficiently short nonnegative smooth bump $w$
gives $F(z)=(1/2-z)\int e^{zx}w(x)dx$ and avoids that cancellation.
The following boundary argument gives a contradiction even using
only an already known critical-line zero.

### A known boundary pole contradicts a support-independent constant

Fix a nonzero critical-line zero $\rho_0=1/2+i\gamma_0$ of
multiplicity $m_0\ge1$. VHO3 has residue
$-m_0F(i\gamma_0)^2$ at $s=2i\gamma_0$.
Positivity of the same Laplace integral gives, for $\eta>0$,

$$
\eta\left|D_f(\eta+2i\gamma_0)
               +\frac{K_f}{\eta+2i\gamma_0}\right|
\le\eta D_f(\eta)+K_f.
$$

Letting $\eta\downarrow0$, analyticity at zero and that exact residue
therefore imply

$$
m_0|F(i\gamma_0)|^2\le K_f.
\tag{VHO4}
$$

Now choose real $\chi\in C_c^\infty((1,2))$ with
$\int\chi\ne0$ and, for $a\ge1$, put

$$
w_a(x)=\chi(x/a)\cos(\gamma_0x),\qquad
f_a=(d/dx+1/2)w_a.
$$

Integration by parts gives $F_a(1/2)=0$, while
Riemann--Lebesgue and the fixed-frequency derivative bounds give

$$
\begin{aligned}
|F_a(i\gamma_0)|^2
&\sim\frac{(1/4+\gamma_0^2)(\int\chi)^2}{4}\,a^2,\\
\|f_a\|_2^2+\Gamma_+(f_a)&=O_{\gamma_0,\chi}(a).
\end{aligned}
\tag{VHO5}
$$

For the second estimate it suffices to use the owned digamma bound
$0\le q(\tau)-q(0)\le C(1+\tau^2)$ and
$\|f_a\|_{H^1}^2=O_{\gamma_0,\chi}(a)$.
For each fixed $a$, use $L=2a$ in VHO3 and take
$\eta\downarrow0$ first; only afterwards let $a\to\infty$. No bound
on $E_{f_a}$ uniform in $a$ is needed.
VHO4 would bound a positive multiple of $a^2$ by $O_K(a)$,
a contradiction. No selection of simultaneous phases of all zeros,
new zero computation or full non-even zero-side form identity is used.

### What this obstruction leaves open

VHO1 concerns ALL compact tests and has no original-moment remainder.
It does not refute a bound restricted to the actual VHR3 loss family
with $\mathfrak E(F)\le0$, or one retaining $M(F)\eta(H)$.
Long supports and translations can have exponentially large weighted
moments even when their Gamma and unweighted norms have the estimates
above. Such a remainder cannot be discarded in this argument.
No negative value of the complete Weil form, RH counterexample or
improvement of VHR1 follows. A usable improvement still needs a
joint estimate on the SAME actual loss test, including its original
moment and a sufficiently small quantified remainder.

## Keep the heat partition inside the actual source range

The VHR loss is odd, so the actual even-source variational inequality
cannot be applied to it. A fixed positive shift in the heat symbol
instead gives two EVEN actual profiles. The useful estimate is a
JOINT defect of the ORIGINAL moment and norm, on the bounded
Gamma/moment class. A moment-only uniform defect would be false.

Reuse VHR2--VHR5's full-form splitting calculation, W324's actual
inverse, W338's forward profile comparison, W359's complete-form
identity, and W331--W332's
small-interval and arithmetic-boundary bounds. The ordinary binomial
series, Gaussian convolution and supporting lines of finite convex
functions are classical inputs. The additional application below
keeps both reconstructed sources and both original metrics in one
variational comparison. All statements in this section are paper
derivations, without Lean/kernel certification or a literature-priority
claim.

### An even partition retains both pole terms exactly

Fix $c>5/2$ and, for sufficiently small $\epsilon>0$, put

$$
 a_\epsilon(z)=e^{-\epsilon(z^2+c^2)},\qquad
 b_\epsilon(z)=\sqrt{1-e^{-2\epsilon(z^2+c^2)}}.
$$

Choose the square root positive on the real axis. Its first zeros are
$\pm ic$; the others solve
$z^2=-c^2+\pi i k/\epsilon$, $k\ne0$, and have imaginary part of
absolute value greater than $c$. Thus it is an EVEN Schwarz-real
holomorphic function on $|\Im z|<c$. Both multipliers are uniformly
bounded on each smaller closed strip. For $g=g_F$ define

$$
 \widehat h=a_\epsilon\widehat g,\qquad
 \widehat v=b_\epsilon\widehat g.
$$

Both profiles are even, including for complex $F$. Their weighted and
logarithmic norms are finite. Recover their actual features $F_h,F_v$
using the EXISTING inverse: for $j=h,v$, set

$$
 \beta_j(t)=j(t/2),\quad
 u_j(t)=\beta_j(t)+\frac32\int_0^\infty e^{s/4}\beta_j(t+s)\,ds,
 \quad
 U_j(x)=x^{-9/4}u_j(\log(x/\pi)),\quad F_j=\mathscr S U_j.
$$

The positive exponential weight makes the integral bounded and W324
supplies the actual inverse. Domain membership is checked BEFORE
using W359. For each fixed $\epsilon$, the heat multiplier and
$1-b_\epsilon$ decay rapidly at high real frequency on smaller
closed strips. Their convolutions with $g$ have weighted $H^1$
regularity. The inverse Volterra integral preserves that regularity:
if $Y(t)=\int_0^\infty e^{s/4}\beta_j(t+s)ds$, then
$Y'=-\beta_j-Y/4$, with $Y$ bounded in the positive exponential
weight. Hence the reconstructed $u_h$ and $u_{g-v}$ are $H^1$ on the
closed positive half-line. Their zero extensions have at most one
jump. Subtracting the trace times $e^{-t}\mathbf1_+$ leaves a
full-line $H^1$ function; the jump term's Fourier transform is a
constant times $(1+i\xi)^{-1}$. Both have finite logarithmic Gamma
form, so $F_h,F_{g-v}\in\mathcal V$. Set $F_v=F-F_{g-v}$.
The forward identity $B B^{-1}\beta_j=\beta_j$ now proves
$g_{F_h}=h$ and $g_{F_v}=v$. This is an explicit range check, not a
converse assumed from W338 or a bare unweighted Volterra inverse.

On the real axis $a_\epsilon^2+b_\epsilon^2=1$. At BOTH pole
frequencies $\pm i/2$ the two multipliers are real and satisfy the
same identity. Consequently VHR5's Gamma and every prime-power
correlation split, and the pole squares split with them:

$$
 \mathfrak E(F)=\mathfrak E(F_h)+\mathfrak E(F_v).
 \tag{VHP1}
$$

No odd loss is identified with an actual even profile. The fixed
shift costs a scalar $e^{-\epsilon c^2}$ in the heat branch and
removes the previous root's zero at the origin.

### Pay the two metric defects on the same bounded-energy source

Write $\mathcal H(F)=\|F\|_H^2$ and
$L_\epsilon=\log(1/\epsilon)$. There is a fixed $C$, depending on the
chosen $c$, such that for every $F\in\mathcal V$ with
$M(F)+\mathcal P(F)\le D$,

$$
 \begin{aligned}
 |M(F_h)+M(F_v)-M(F)|
 +|\mathcal H(F_h)+\mathcal H(F_v)-\mathcal H(F)|
 &\le CD L_\epsilon^{-2/5},\\
 \|F_h-F\|_H&\le C\sqrt D L_\epsilon^{-1/5},\\
 M(F_h)+M(F_v)&\le CM(F).
 \end{aligned}
 \tag{VHP2}
$$

Here the first line controls a joint defect; it does not assert that
$M(F_v)$ tends to zero uniformly over that class.
The last line is a moment-only bound on all actual sources, without
the Gamma hypothesis. It follows from the full-line reconstruction
and boundedness of both exponentially weighted filters below.

Use $q=5/4$, the even full-line function $\beta(t)=g(t/2)$, and
$w(t)=e^{qt}\beta(t)$. On the full line let

$$
 S=\sum_{n\ge1}\mu(n)n^{-3}T_{2\log n},\quad
 (T_af)(t)=f(t+a),\quad
 K=I+\tfrac32J_1,\quad
 (J_1f)(t)=\int_0^\infty e^{-s}f(t+s)\,ds,\quad X=KS w.
$$

All these are bounded on full-line $L^2$, and $S,K$ commute with
full-line Fourier multipliers. Their restrictions for $t\ge0$ are
exactly the owned source reconstruction, since all shifts are forward:

$$
 M(F)=\pi^{-7/2}\|\mathbf1_+X\|_2^2,\qquad
 \mathcal H(F)=\pi^{-7/2}\int_0^\infty e^{-6t}|X(t)|^2dt.
 \tag{VHP3}
$$

Also $\|w\|_2+\|X\|_2\le C\sqrt{M(F)}$. Apply the Fourier
partition with symbols $a_\epsilon(2\xi),b_\epsilon(2\xi)$ to this
full-line representation. Conjugating either filter by $e^{qt}$
changes it in operator norm by at most
$C\sqrt\epsilon\log(2+1/\epsilon)$. Thus its reconstructed $X_j$
differs from the corresponding filter applied to $X$ by at most this
factor times $\sqrt{M(F)}$.

For completeness, the kernel estimates needed here follow directly
from the ordinary binomial expansion

$$
 b_\epsilon(2D)=I-k_\epsilon*,\qquad
 k_\epsilon=\sum_{m\ge1}d_m e^{-2m\epsilon c^2}K_{8m\epsilon},
 \qquad
 d_m=\frac{\binom{2m}{m}}{4^m(2m-1)}>0,
 \quad \sum_m d_m=1,
$$

where $K_t$ is the normalized heat kernel. Since $d_m=O(m^{-3/2})$
and $c>2q$, Gaussian integration gives

$$
 \int(e^{q|s|}-1)k_\epsilon(s)\,ds
 \le C\sqrt\epsilon\log(2+1/\epsilon),\qquad
 \int_{|s|>r}k_\epsilon(s)\,ds\le C\sqrt\epsilon/r
 \quad(r\ge\sqrt\epsilon).
 \tag{VHP4}
$$

The heat branch satisfies the same bounds. For the second estimate,
sum $d_m\min(1,m\epsilon/r^2)$; for the first, split the Gaussian
exponential moment sum at $m=1/\epsilon$. These are estimates for the
actual filters, not an assumed multiplier-domain separation.

Let $P_+$ be multiplication by $\mathbf1_+$. For either filter $A$,
its commutator on $X$ obeys

$$
 \|[P_+,A]X\|_2\le
 C\|\mathbf1_{[-r,r]}X\|_2+C\sqrt\epsilon\,r^{-1}\|X\|_2.
 \tag{VHP5}
$$

Split the input into that interval and its complement; on the latter,
any kernel crossing the cut has displacement greater than $r$.
For multiplication by $\mathbf1_+e^{-6t}$ there is additionally a
$C\sqrt\epsilon\log(2+1/\epsilon)\|X\|_2$ term, since
$e^{-6\max(t,0)}$ is bounded and Lipschitz.

The remaining local mass is the SAME arithmetic-boundary estimate
already paid in W332. W338 and W332's frequency split give
$\|\mathbf1_I\beta\|_2^2\le CD/\log(1/r)$ on every interval of
length $2r$. For $n\le N$ near $t=0$ the factor
$n^{-3}e^{q(2\log n)}$ is $n^{-1/2}$, so their triangle sum is at
most $C\sqrt{DN/\log(1/r)}$. The rest of $S$ has norm at most
$CN^{-2}$. Finally $J_1:L^2\to L^\infty$ is bounded. Hence

$$
 \|\mathbf1_{[-r,r]}X\|_2
 \le C\sqrt D\left[
 \sqrt{N/\log(1/r)}+N^{-2}+\sqrt r\right].
 \tag{VHP6}
$$

Choose $r=\epsilon^{1/4}$ and
$N$ comparable to $L_\epsilon^{1/5}$. Equations VHP4--VHP6 give
$C\sqrt D L_\epsilon^{-2/5}$ for the commutators. The identity
$A^2+B^2=I$ for the real-axis filters turns each metric defect into
$\langle X,(A[P_+,A]+B[P_+,B])X\rangle$, with the indicated bounded
weight for $\mathcal H$. The exponential-conjugation error has the
smaller order already stated. This proves the first line
of VHP2 while retaining the sharp arithmetic boundary.

For its second line, the same frequency split as W331 gives
$\|h-g\|_0^2\le CD/L_\epsilon$, while their weight-$5/2$ norms
remain bounded by $C\sqrt D$. Interpolate to weight $3/2$ in $r$,
or $3/4$ in $t$. At that weight the displayed Volterra inverse is
bounded, and W331's EXISTING $H_5$ Möbius inverse has norm at most
$\zeta(2)$. This gives the asserted original-$H$ error.

The Gamma hypothesis cannot be dropped from the first line of VHP2.
For a nonzero real $\phi\in C_c^\infty(-2,-1)$, concentrate
$\beta_s(t)=s^{-1/2}\phi((t-2\log2)/s)$ on the positive half-line,
evenly extend it, and take $s=2\sqrt\epsilon$. Recover its actual
source by the same inverse. The original packet lies below the first
nontrivial Möbius shift. After filtering, the $n=2$ channel crosses
$t=0$. Its limit gives

$$
 \frac{\Delta_M}{M(F_s)}\longrightarrow
 \frac{2^{-6}}{\|\phi\|_2^2}\int_0^\infty
 \left[|e^{-D^2}\phi|^2+
 |\sqrt{1-e^{-2D^2}}\,\phi|^2\right]dt>0.
 \tag{VHP6a}
$$

In the weighted coordinates above, $J_1$ applied to these concentrated
packets tends to zero in $L^2$. The $n=1,2$ outputs concentrate at
different locations; each fixed $n\ge3$ output vanishes on the positive
half-line and the remaining tail is bounded by $CN^{-2}$. These facts
justify the displayed limit. Here $\mathcal P(F_s)/M(F_s)$ grows as
$\log(1/s)$; this family is not a counterexample on the nonpositive
complete-energy class used below.

### Consume the joint defect at an actual negative minimum

Suppose $e_4=-\delta<0$, and choose its actual unit minimizer $F$.
The usual supporting multiplier can be taken GLOBAL, not merely as
a weak stationary equation:

$$
 Q_\lambda(G):=\mathfrak E(G)+\lambda M(G)-\mu\mathcal H(G)\ge0
 \quad(G\in\mathcal V),\qquad
 Q_\lambda(F)=0,\quad
 \mu=-\delta+4\lambda,\quad
 0\le\lambda\le\frac{\delta}{4-\kappa_\circ}.
 \tag{VHP7}
$$

Indeed the existing real extraction and imaginary mixing used in
W345/W351 show that the finite function $K\mapsto e_K$ is convex
and nonincreasing for $K>1$: mix two real minimizers with coefficients
$\sqrt\theta,i\sqrt{1-\theta}$, then extract at the SAME moment.
A classical supporting line at $K=4$ supplies $-\lambda$. Its bound
at the actual minimizer gives complementary slackness, and testing
on W350's unit null vector gives the upper bound in VHP7. No
unconfined self-adjoint operator or negative penalized eigenvalue
is assumed.

W317 gives $M(F)+\mathcal P(F)\le C$ on these minimizers. With
$\Delta_M=M(F_h)+M(F_v)-M(F)$ and the corresponding $\Delta_H$,
VHP1, VHP2 and VHP7 give

$$
 0\le Q_\lambda(F_h),Q_\lambda(F_v),\qquad
 Q_\lambda(F_h)+Q_\lambda(F_v)
 =\lambda\Delta_M-\mu\Delta_H
 \le C\delta L_\epsilon^{-2/5}.
 \tag{VHP8}
$$

The crucial factor $\delta$ multiplies the metric error; no
$\lambda^{-1}$ or lower-multiplier premise was used.

Now assume $\mathsf{RH}(T)$, take $\epsilon=1/T$, and put
$\eta_T=\sqrt T\log(2+T)e^{-T}$. W369--W370, already used in
VHR10, apply to the scalar-shifted heat branch and give
$\mathfrak E(F_h)\ge-C\eta_T$. For all sufficiently large $T$,
VHP2 also gives $\mathcal H(F_h)\ge1/2$, while always
$M(F_h)\ge\mathcal H(F_h)$. Therefore

$$
 \boxed{\quad
 \lambda\ge
 \left[\frac13-C(\log T)^{-2/5}\right]\delta-C\eta_T.
 \quad}
 \tag{VHP9}
$$

To check the direction, VHP8 and the height bound imply
$(\delta-3\lambda)\mathcal H(F_h)
 \le C\delta(\log T)^{-2/5}+C\eta_T$.
Dividing by its positive norm proves VHP9.
In particular, at a sufficiently large starting height depending
only on the fixed $c$,

$$
 \lambda\le\delta/6\quad\Longrightarrow\quad
 \delta\le C\sqrt T\log(2+T)e^{-T}.
 \tag{VHP10}
$$

This includes the previously allowed zero multiplier. Outside that
exponentially small allowance the actual supporting multiplier has
a positive lower bound proportional to $\delta$, as well as the
existing upper bound. The constants and starting height have not
been numerically evaluated.

VHP9--VHP10 do not improve VHR1's allowance for the remaining
positive-multiplier case. They supply the lower-multiplier premise
needed by such a case's future estimates, up to the displayed height
tail. They neither establish higher-log regularity nor remove the
negative allowance in the original complete form. Full RH and strict
Robin for every integer $n>5040$ remain unproved.

## Bootstrap the actual minimizing source before paying its moment loss

The global supporting form in VHP7 supplies more than a lower
multiplier: it gives a source-specific logarithmic bootstrap. The
following repo-derived application reuses VHP's actual even branches,
W331's weighted inverse and W338's full Gamma comparison. No generic
nonlocal eigenfunction regularity theorem is substituted for these
interfaces. All estimates concern the SAME hypothetical negative
cap-four minimizer. They remain paper derivations without Lean/kernel
certification or a priority claim.

### Square the local mass in the joint metric defect

For $k\ge1$ put

$$
 \mathcal L_k(g)=\int_{\mathbb R}
       [\log(2+|\tau|)]^k|\widehat g(\tau)|^2d\tau,
 \qquad L=\log(1/\epsilon).
$$

On the actual class $M(F)+\mathcal L_k(g_F)\le D$, the same branches
as VHP satisfy the stronger joint estimate

$$
 |\Delta_M|+|\Delta_H|\le C_kD L^{-4k/5}.
 \tag{VHB1}
$$

The range check in VHP is unchanged; $\mathcal L_k$ with $k\ge1$
pays its logarithmic domain. To improve the estimate, use the
self-adjoint defect of the REAL-axis filters $A=a_\epsilon(2D)$ and
$B=b_\epsilon(2D)$ in VHP3:

$$
 D_P=APA+BPB-P=A[P,A]+B[P,B],\qquad P=\mathbf1_+.
$$

For $Z_r=\mathbf1_{|t|\ge r}$, VHP4's cross-cut kernel bound gives
$\|D_PZ_r\|\le C\sqrt\epsilon/r$. Since $D_P=D_P^*$ and
$\|D_P\|\le C$, splitting $X=(1-Z_r)X+Z_rX$ gives

$$
 |\langle X,D_PX\rangle|
 \le C\|\mathbf1_{[-r,r]}X\|_2^2
        +C\sqrt\epsilon\,r^{-1}\|X\|_2^2.
 \tag{VHB2}
$$

Both mixed terms use the SAME $D_PZ_r$ estimate. For
$P e^{-6\max(t,0)}$ the bounded Lipschitz factor adds only
$C\sqrt\epsilon\log(2+1/\epsilon)\|X\|_2^2$ by VHP4. The
exponential-conjugation errors have this same smaller order.

A Fourier split on $\beta(t)=g(t/2)$ now gives local squared mass
$C_kD/[\log(1/r)]^k$. Reuse VHP6's finite Möbius reconstruction,
without replacing its arithmetic coefficients:

$$
 \|\mathbf1_{[-r,r]}X\|_2^2
 \le C_kD\left[
       \frac{N}{[\log(1/r)]^k}+N^{-4}+r\right].
$$

Take $r=\epsilon^{1/4}$ and $N$ comparable to $L^{k/5}$.
This proves VHB1. It is the self-adjoint quadratic defect, rather
than the norm of its first commutator alone, that retains the
squared local mass.

### Keep the reconstruction just above its critical weight

Fix $0<\eta<2$, and set

$$
 \theta_\eta=\frac{4-2\eta}{5}>0,\qquad d=F-F_h.
$$

On the same class, the actual original-source errors satisfy

$$
 \mathcal N(d)^2+\mathcal N(F_v)^2
 \le C_{k,\eta}D L^{-\theta_\eta k}.
 \tag{VHB3}
$$

Indeed both profile differences $(1-a_\epsilon)\widehat g$ and
$b_\epsilon\widehat g$ have unweighted squared norm at most
$C_kD L^{-k}$ by splitting at $|\tau|=\epsilon^{-1/4}$.
Their weight-$5/2$ norms remain bounded by $C\sqrt{M(F)}$, as in
VHP. In the $t$ coordinate interpolate to the positive exponential
weight $a_\eta=1/4+\eta/2$, below $q=5/4$. The resulting squared
norm has exponent
$k(1-a_\eta/q)=\theta_\eta k$.

Here the ACTUAL Volterra inverse is bounded because
$a_\eta>1/4$. This is precisely the source space
$H_{4+\eta}$, with squared norm
$\int_\pi^\infty(x/\pi)^{4+\eta}|F(x)|^2dx$.
The actual Möbius inverse has norm at most $\zeta(1+\eta)$ there,
since its $n$th dilation has norm $n^{-1-\eta}$. Finally
$\mathcal N(G)^2\le C_\eta\|G\|_{H_{4+\eta}}^2$.
This proves VHB3 without an endpoint $H_4$ inverse. The constants
may diverge as $\eta\downarrow0$; no endpoint assertion is made.

### Use the null supporting vector to gain logarithmic regularity

Let $F$ be an actual unit minimizer with $e_4=-\delta<0$ and use
VHP7's global $Q_\lambda$. The existing complete-energy floor gives
$\delta\le C$ and $M(F)+\mathcal P(F)\le C$. Thus W338 supplies
$\mathcal L_1(g_F)\le C$. Suppose at some stage that
$\mathcal L_k(g_F)\le C_k$, uniformly on these minimizing vectors.
VHP1 and VHB1 give

$$
 0\le Q_\lambda(F_h),Q_\lambda(F_v)
 \le C_k\delta L^{-4k/5}.
$$

Since $Q_\lambda$ is nonnegative and $Q_\lambda(F)=0$, its
polarized pairing with $F$ vanishes. In particular
$Q_\lambda(d)=Q_\lambda(F_h)$. Applying W317's COMPLETE debit
bound to $d$ and $F_v$, using VHB3 and
$|\mu|\le C\delta\le C$, proves

$$
 \begin{aligned}
 &\mathcal P(d)+\mathcal P(F_v)
       +\lambda\bigl[M(d)+M(F_v)\bigr]\\
 &\hspace{2em}\le C_{k,\eta}L^{-\theta_\eta k}.
 \end{aligned}
 \tag{VHB4}
$$

No division by $\lambda$ is used in the Gamma estimate. W338 applied
to the ACTUAL difference $d$ bounds its full logarithmic profile
norm by $C[\mathcal P(d)+\mathcal N(d)^2]$. On
$|\tau|\ge\epsilon^{-1/2}$ the factor $1-a_\epsilon(\tau)$ is
bounded below by a fixed positive constant. Therefore

$$
 \int_{|\tau|\ge R}\log(2+|\tau|)
                |\widehat g_F(\tau)|^2d\tau
 \le C_{k,\eta}[\log(2+R)]^{-\theta_\eta k}.
$$

Layer integration gives $\mathcal L_{k'}(g_F)\le C_{k'}$ for
every $k'<1+\theta_\eta k$. Starting at $k=1$, choose $\eta>0$
so that $1/(1-\theta_\eta)$ exceeds a given target $k_*<5$,
and iterate a finite number of STRICT gains. Consequently

$$
 \boxed{\quad
 \mathcal L_k(g_F)\le C_k\qquad(1\le k<5).
 \quad}
 \tag{VHB5}
$$

The constants depend on the chosen exponent and fixed $c$, but not
on $\delta$, $\lambda$ or the minimizing vector. No $k=5$ or
$k>5$ claim follows by taking a limit of these constants.

### Retain the actual sixth moment and expose its remaining cost

For each fixed $0<s<4$, choose $k<5$ and $\eta>0$ with
$\theta_\eta k>s$. VHB1 and VHB3--VHB5 give

$$
 \begin{gathered}
 |\Delta_M|+|\Delta_H|\le C_sL^{-s},\qquad
 Q_\lambda(F_h),Q_\lambda(F_v)\le C_s\delta L^{-s},\\
 \mathcal P(d)+\mathcal P(F_v)
 +\lambda[M(d)+M(F_v)]\le C_sL^{-s},\\
 |\mathcal H(F_h)-1|\le C_sL^{-s},\\
 \lambda>0\quad\Longrightarrow\quad
 M(F_v)+|M(F_h)-M(F)|\le C_s\lambda^{-1}L^{-s}.
 \end{gathered}
 \tag{VHB6}
$$

The fourth line uses the joint $H$ defect together with
$\mathcal H(F_v)\le C\mathcal N(F_v)^2$, keeping all terms on the
same source. The last line uses the joint $M$ defect and
$\lambda M(F_v)\le C_sL^{-s}$; the uniform upper bound on
$\lambda$ absorbs its harmless factor $1+\lambda^{-1}$.
For $\lambda>0$, complementary slackness gives $M(F)=4$.
Under the same finite-height premise as VHP9, at sufficiently large
$T$ depending on the fixed $s,c$, this also improves that multiplier
comparison to

$$
 \lambda\ge[1/3-C_s(\log T)^{-s}]\delta-C\eta_T
 \qquad(0<s<4).
 \tag{VHB7}
$$

This is a genuine single-minimizer moment recovery, unlike a
sum-of-moments defect alone. Under $\mathsf{RH}(T)$, for $\delta\ge C_0\eta_T$, with
$C_0$ sufficiently large and $T$ sufficiently large, VHP9 permits $\lambda^{-1}\le C\delta^{-1}$, so the final moment
error still costs $C_s\delta^{-1}L^{-s}$. Inserting it into the
heat-branch supporting equation only yields a negative allowance
of order $L^{-s}$ for $s<4$. It does NOT improve the already owned
VHR1 exponent $4$. An estimate beyond the critical logarithmic tail, or a new signed
joint estimate, is still required. Full RH and strict Robin for every
integer $n>5040$ remain unproved.

### Use the verified height to reach a conditional boundary endpoint

The same finite-height premise supplies an endpoint estimate for the
actual boundary defect. This is not a limit of VHB5's constants.
Let $F\in\mathcal V$, $\mathfrak E(F)\le0$, and assume
$\mathsf{RH}(T)$, with $T$ sufficiently large depending on fixed $c$.
Write $L=\log T$, retain $\eta_T$ from VHP9, and use the SAME
actual branches at any $T^{-1}\le\sigma\le\sigma_0$, where
$\sigma_0<1$ is fixed and sufficiently small. Put
$s_\sigma=\|g_{F_{v,\sigma}}\|_0^2$ and
$L_\sigma=\log(1/\sigma)$. Then

$$
 s_\sigma\le CM(F)\left[
 L_\sigma^{-5}+\sqrt\sigma+\eta_T/L_\sigma\right].
 \tag{VHB8}
$$

Indeed the finite-height heat-tail argument of VHP9 is uniform over
these COARSER filters. For a zero frequency $z=u+iv$, $|v|<1/2$,

$$
 |a_\sigma(z)^2|
 =e^{-2\sigma(u^2+c^2-v^2)}\le e^{-2u^2/T}.
$$

Thus the existing signed zero-tail majorant gives
$\mathfrak E(F_{h,\sigma})\ge-CM(F)\eta_T$.
The exact energy partition and the original nonpositive energy imply
$\mathfrak E(F_{v,\sigma})\le CM(F)\eta_T$; the high-pass branch
is NOT assumed to have nonpositive energy. Its weighted profile norm
is bounded by $C\sqrt{M(F)}$ by VHP's full-$M$ branch bound.
On $|\tau|\le\sigma^{-1/4}$ its squared Fourier mass is at most
$CM(F)\sqrt\sigma$. Retain the Gamma contribution on the complement
and apply the EXISTING complete prime-and-pole bound VHR7 to obtain

$$
 aL_\sigma s_\sigma
 \le B M(F)^{1/5}s_\sigma^{4/5}
       +CM(F)L_\sigma\sqrt\sigma+CM(F)\eta_T,
 \qquad a>0.
$$

Young's inequality absorbs half the left side at cost
$CM(F)L_\sigma^{-4}$. Division by $L_\sigma$ proves VHB8.
This uses the full arithmetic debit and never applies W366's
nonpositive-energy hypothesis to the high-pass branch.

At the TARGET scale $\epsilon=1/T$, the actual joint metric defect
satisfies the endpoint

$$
 |\Delta_M|+|\Delta_H|\le CM(F)L^{-4}.
 \tag{VHB9}
$$

To pay the arithmetic boundary, take the coarser
$\sigma=T^{-1/4}$, set $r=T^{-1/4}$ and $R=T^{1/8}$, and retain
$\beta(t)=g_F(t/2)$. The symbol $b_\sigma(2\xi)^2$ is bounded below
on $|\xi|\ge R$. VHB8 therefore gives Fourier-tail squared mass
$CM(F)L^{-5}$ there. The low-frequency projection has local squared
mass at most $CrR M(F)$ on every interval of length $2r$.
Consequently the finite actual reconstruction used in VHP6 gives

$$
 \|\mathbf1_{[-r,r]}X\|_2^2
 \le CM(F)\left[NL^{-5}+N^{-4}+Nr^{1/2}+r\right].
$$

Choose $N$ comparable to $L$. The SQUARED local mass in VHB2,
together with the smaller kernel and exponential-conjugation errors,
proves VHB9. This is a conditional estimate on the original
nonpositive-energy class, not a vanishing defect on the full $M$
domain.

For the SAME hypothetical unit negative cap-four minimizer,
VHP7 and VHB9 give, under $\mathsf{RH}(T)$ at sufficiently large $T$,

$$
 \begin{gathered}
 0\le Q_\lambda(F_h),Q_\lambda(F_v)\le C\delta L^{-4},\\
 \lambda\ge[1/3-CL^{-4}]\delta-C\eta_T.
 \end{gathered}
 \tag{VHB10}
$$

The last line uses the existing $\mathcal H(F_h)\ge1/2$ and
$M(F_h)\ge\mathcal H(F_h)$ in VHP9's supporting-form comparison.
No new multiplier argument or source normalization is needed.

Finite $T$ in VHB8 does not give a strong logarithmic fifth moment,
or a fifth-order Fourier-tail rate continuing uniformly as the
frequency tends to infinity. VHB9--VHB10 supply a conditional
boundary endpoint; they do not remove the inverse-multiplier cost
in original-moment recovery or improve VHR1's general fourth-power
negative allowance. A new signed arithmetic estimate is still
required. These applications remain paper derivations without
Lean/kernel certification.


## Pay one Fourier tail across the separated reconstruction intervals

The finite actual reconstruction in VHP6 and VHB9 admits a stronger
local estimate than their termwise triangle bound. Reuse exactly
VHP3's $S,K,w,X$, VHB2's self-adjoint metric defect, VHB5's
minimizer regularity and VHB8's finite-height tail. The ingredients
are classical Cauchy--Schwarz and disjoint input intervals; W268 in
[the actual-source account](suzuki2026screw.md#retain-all-disjoint-dilation-intervals-and-their-exact-harmonic-weights)
already uses disjoint dilation intervals and harmonic weights for a
different source contract. The additional application here concerns
the joint metrics of the actual even heat branches. It introduces no
new general localization theorem or literature-priority claim and
remains a paper derivation without Lean/kernel certification.

### Separate only the finite reconstruction before cutting frequencies

For $0<r\le1$, $R\ge1$ and an integer $N\ge1$ with $2rN<1$, put

$$
 I=[-r,r],\qquad
 \mathcal T_\beta(R)=\int_{|\xi|\ge R}|\widehat\beta(\xi)|^2d\xi,
 \qquad S_N=\sum_{n\le N}\mu(n)n^{-3}T_{2\log n}.
$$

The same source satisfies

$$
 \boxed{\quad
 \|\mathbf1_I X\|_2^2
 \le C\left[(1+\log N)\mathcal T_\beta(R)
       +M(F)(rRN+N^{-4}+r)\right].
 \quad}
 \tag{VHB11}
$$

Indeed, on $I$, the exact weight is

$$
 S_Nw(t)=e^{qt}\sum_{n\le N}\mu(n)n^{-1/2}
                         \beta(t+2\log n),\qquad q=5/4.
$$

Split $\beta=\beta_{<R}+\beta_{\ge R}$ by its full-line Fourier
transform, only in this FINITE sum. The factor $e^{qt}$ is uniformly
bounded on $I$. Fourier Cauchy--Schwarz gives
$\|\beta_{<R}\|_\infty^2\le CR\|\beta\|_2^2\le CRM(F)$.
Since $\sum_{n\le N}n^{-1/2}\le C\sqrt N$, its local squared
contribution is at most $CM(F)rRN$.

For the high-frequency contribution, use the SAME global function
in all input intervals:

$$
 \begin{aligned}
 &\int_I\left|\sum_{n\le N}\mu(n)n^{-1/2}
                       \beta_{\ge R}(t+2\log n)\right|^2dt\\
 &\quad\le
 \left(\sum_{n\le N}\frac{\mu(n)^2}{n}\right)
 \sum_{n\le N}\int_{I+2\log n}|\beta_{\ge R}(u)|^2du\\
 &\quad\le C(1+\log N)\mathcal T_\beta(R).
 \end{aligned}
 \tag{VHB12}
$$

For $n<N$, adjacent centers have distance
$2\log(1+1/n)\ge2/(n+1)\ge2/N$; the intervals of length $2r$
are disjoint under the stated condition. Thus the last sum pays
at most one full Fourier-tail mass, rather than $N$ copies.
No exponential weight is asserted for either Fourier projection,
and the infinite operator is not applied to these projected inputs.

For the remaining terms use the ORIGINAL $w$ and $Sw$.
The absolute operator tail obeys
$\|S-S_N\|\le\sum_{n>N}n^{-3}\le CN^{-2}$.
VHP3 bounds $\|w\|_2^2+\|Sw\|_2^2\le CM(F)$, while
$J_1:L^2\to L^\infty$ is bounded. Their local squared payments
are respectively $CM(F)N^{-4}$ and $CM(F)r$. Since
$X=S_Nw+(S-S_N)w+\tfrac32J_1Sw$, these estimates prove VHB11.

### Retain the full logarithmic order in the joint metric estimate

For every fixed $k\ge1$, on the SAME class
$M(F)+\mathcal L_k(g_F)\le D$, the actual branches satisfy, for
sufficiently small $\epsilon$ depending on $k,c$,

$$
 |\Delta_M|+|\Delta_H|
 \le C_kD L^{-k}\log(2+L),\qquad L=\log(1/\epsilon).
 \tag{VHB13}
$$

To see the scale exactly,
$\widehat\beta(\xi)=2\widehat g_F(2\xi)$, so
$\mathcal T_\beta(R)\le C_kD[\log(2+R)]^{-k}$.
In VHB11 take

$$
 r=\epsilon^{1/4},\qquad R=\epsilon^{-1/8},\qquad
 N=\lceil L^{k/4}\rceil.
$$

The separation condition holds for sufficiently small $\epsilon$.
The tail and operator-tail terms have orders
$DL^{-k}\log(2+L)$ and $DL^{-k}$; $rRN$ and $r$ are
exponentially small in $L$. VHB2 then pays the actual quadratic
metric defect, with cross-cut error $CM(F)\sqrt\epsilon/r$.
The Lipschitz-weight and exponential-conjugation errors from VHP4
are also exponentially small in $L$. This proves VHB13.

On actual unit negative cap-four minimizers, VHB5 consequently gives
$|\Delta_M|+|\Delta_H|\le C_sL^{-s}$ for every fixed $0<s<5$:
choose $\max(1,s)<k<5$ and absorb the logarithm. This improves
the joint metrics, not VHB3's original-source inverse estimate.
No strong fifth logarithmic moment follows.

### Use finite-height RH for the fifth-power boundary rate

Let $F\in\mathcal V$ have $\mathfrak E(F)\le0$, assume
$\mathsf{RH}(T)$, and take $T$ sufficiently large depending on the
fixed $c$. At the TARGET scale $\epsilon=1/T$, write $L=\log T$.
Then

$$
 \boxed{\quad
 |\Delta_M|+|\Delta_H|
 \le CM(F)L^{-5}\log(2+L).
 \quad}
 \tag{VHB14}
$$

Use VHB8 at the coarser $\sigma=T^{-1/4}$. With
$R=T^{1/8}$, the symbol $b_\sigma(2\xi)^2$ is bounded below
by a fixed positive constant on $|\xi|\ge R$. The exact Fourier
scaling above therefore gives

$$
 \mathcal T_\beta(R)
 \le C s_\sigma
 \le CM(F)\left[L^{-5}+T^{-1/8}+\eta_T/L\right]
 \le CM(F)L^{-5}.
$$

Take $r=T^{-1/4}$ and $N=\lceil L^{5/4}\rceil$ in VHB11.
Then $N^{-4}\le CL^{-5}$ and
$1+\log N\le C\log(2+L)$, while $rRN=T^{-1/8}N$
and all the other metric errors are smaller. This proves VHB14
on the original nonpositive-energy class; no nonpositive-energy
premise is imposed on the high-pass branch.

For the SAME hypothetical unit negative cap-four minimizer with
$e_4=-\delta$, VHP1, VHP7 and VHP9 now give

$$
 \begin{gathered}
 0\le Q_\lambda(F_h),Q_\lambda(F_v)
          \le C\delta L^{-5}\log(2+L),\\
 \lambda\ge
 [1/3-CL^{-5}\log(2+L)]\delta-C\eta_T.
 \end{gathered}
 \tag{VHB15}
$$

Here $M(F)\le4$, $|\mu|+\lambda\le C\delta$ and
$\mathcal H(F_h)\ge1/2$ are the existing minimizer bounds.
The supporting comparison still uses
$(\delta-3\lambda)\mathcal H(F_h)$, keeping its original direction.
The height premise and sufficiently large $T$ are essential to
VHB14--VHB15; they are not uniform fifth-order tails at arbitrarily
large frequency for a fixed verified height.

VHB11--VHB15 do not change VHB3's inverse/interpolation cost.
In particular a small $Q_\lambda(F_v)$ does not itself bound
$\lambda M(F_v)$ without paying the complete debit and the
original-source error. The final general negative allowance remains
VHR1's $CL^{-4}$. Full RH and strict Robin for every integer
$n>5040$ remain unproved.


## Retain each error's own moment at a positive supporting multiplier

Let $F$ be a hypothetical unit negative cap-four minimizer and retain
VHP7's GLOBAL supporting form. Assume its supporting multiplier
$\lambda>0$. The following application strengthens the logarithmic
regularity on this branch, with explicit multiplier dependence. It
reuses VHB3's actual inverse maps, W317's complete debit bound,
W338 and VHB13; no generic eigenfunction-regularity theorem or
additional physical moment is assumed. The estimates remain paper
derivations without Lean/kernel certification or a priority claim.

### Absorb the actual error moment before discarding it

Fix $0<\eta<2$, and write

$$
 \theta=\frac{4-2\eta}{5},\qquad
 \kappa=\frac{1-\theta}{\theta}>\frac14,\qquad
 \Lambda=1+\lambda^{-\kappa}.
$$

For an ACTUAL error source $G$, put $s_G=\|g_G\|_2^2$ and
$m_G=M(G)$. The same weighted interpolation and inverse maps as
VHB3, before replacing the error moment by the original budget, give

$$
 \mathcal N(G)^2\le C_\eta s_G^\theta m_G^{1-\theta}.
 \tag{VHB16}
$$

Indeed the unweighted squared profile norm is $2s_G$ after the
$t=2r$ scaling, its squared weight-$q$ norm is bounded by $Cm_G$, and
interpolation to $a_\eta=1/4+\eta/2$ has exponent
$1-a_\eta/q=\theta$. The actual inverses and the original
$\mathcal N$ weight are bounded at that strictly supercritical
weight, exactly as in VHB3. This is not an unweighted endpoint
inverse or an estimate on an independently chosen profile.

On these supporting forms $|\mu|\le C$ by VHP7 and the existing
complete-energy floor. W317, $\mathcal H(G)\le C\mathcal N(G)^2$
and Young absorption therefore give

$$
 \mathcal P(G)+\frac\lambda2 M(G)
 \le Q_\lambda(G)+C_\eta\lambda^{-\kappa}s_G.
 \tag{VHB17}
$$

Apply this only to the SAME $d=F-F_h$ and $F_v$. If
$M(F)+\mathcal L_k(g_F)\le D$, $k\ge1$, then VHB13,
$Q_\lambda(d)=Q_\lambda(F_h)$ and the existing profile-frequency
split imply

$$
 \begin{aligned}
 s_d+s_{F_v}&\le C_kD L^{-k},\\
 \mathcal P(d)+\mathcal P(F_v)
 +\frac\lambda2[M(d)+M(F_v)]
 &\le C_{k,\eta}D
       [\delta\log(2+L)+\lambda^{-\kappa}]L^{-k},
 \qquad L=\log(1/\epsilon).
 \end{aligned}
 \tag{VHB18}
$$

The complete debit and both pole terms are retained in this
application; the moment term is absorbed on the error source itself.

### Raise the logarithmic order and consume it in the branch estimates

Interpolating those SAME errors again in VHB16 avoids paying an
additional bare inverse multiplier. In particular

$$
 \begin{aligned}
 \mathcal N(d)^2+\mathcal N(F_v)^2
 \le C_{k,\eta}D L^{-k}\bigl[
 &(\delta/\lambda)^{1-\theta}
                         \log(2+L)^{1-\theta}
 +\lambda^{-\kappa}\bigr].
 \end{aligned}
 \tag{VHB19}
$$

Here $(\kappa+1)(1-\theta)=\kappa$. Since $\delta$ and
$\lambda$ have fixed uniform upper bounds, VHB18--VHB19 and W338
bound $\mathcal L_1(g_d)$ by
$C_{k,\eta}D\Lambda L^{-k}\log(2+L)$.
On $|\tau|\ge\epsilon^{-1/2}$, the multiplier $1-a_\epsilon$
is bounded below. Layer integration of this weighted Fourier tail
then gives the STRICT gain

$$
 M(F)+\mathcal L_{k'}(g_F)
 \le C_{k,k',\eta}\Lambda D
 \qquad(1\le k'<k+1).
 \tag{VHB20}
$$

Starting with any fixed uniform order $1\le k_0<5$ from VHB5,
a finite number of such gains reaches every finite target order.
More precisely, choose $0<h_i<1$ and
$k_j=k_0+j-\sum_{i=1}^j h_i$. The resulting bound is
$M(F)+\mathcal L_{k_j}(g_F)\le C_{j,k_0,\eta,h_i}\Lambda^j$.
All constants refer to the original actual minimizing sources.

This regularity has an existing consumer: for EVERY fixed $s>0$,
VHB13 and VHB18--VHB19 now give, on the positive-multiplier branch,

$$
 \begin{gathered}
 |\Delta_M|+|\Delta_H|
 +\mathcal N(d)^2+\mathcal N(F_v)^2
 +\mathcal P(d)+\mathcal P(F_v)\\
 \hspace{2em}+\lambda[M(d)+M(F_v)]
 \le C_{s,\lambda}L^{-s}.
 \end{gathered}
 \tag{VHB21}
$$

Choose $k_j>s$ and absorb the fixed logarithmic factors. The
constants in VHB21 are uniform in the minimizing vector after fixing
its positive supporting multiplier; no uniformity as
$\lambda\downarrow0$ is asserted. No additional physical moment or
physical-dilation derivative follows from these logarithmic estimates.

### Keep the multiplier cost when returning to finite-height negativity

VHB21 does not improve the uniform fourth-power negative allowance.
Under the same finite-height premise and outside VHP9's exponentially
small height tail, $\lambda\ge c\delta$. Each strict gain above
costs $\Lambda$, and using VHB19 for the complete error debit costs
one further $\lambda^{-\kappa}$. To return to the ORIGINAL complete
energy, use VHP1, the heat-branch lower bound and W317 directly:

$$
 \delta\le C\eta_T+|\mathfrak J(F_v)|
 \le C\eta_T+C\mathcal N(F_v)^2
 \le C\eta_T+C_j\delta^{-(j+1)\kappa}
                        L^{-k_j}\log(2+L).
$$

Starting from a uniform $k_0<5$, the resulting fixed-parameter
allowance has nominal logarithmic exponent

$$
 p_j=\frac{k_0+j-\sum_{i=1}^j h_i}{1+(j+1)\kappa}<4,
 \qquad
 4[1+(j+1)\kappa]-k_j
 =(5-k_0)+\sum_{i=1}^j h_i+(j+1)(4\kappa-1)>0.
 \tag{VHB22}
$$

Fixed logarithmic factors may further weaken that bound. VHB8's
finite-height weak fifth-order tail is not a global strong fifth
moment with which to restart the iteration. No limit in $j$ or
$\eta\downarrow0$ with controlled constants is supplied. Thus the
positive-multiplier regularity and branch rates in VHB20--VHB21
remain distinct from a uniform improvement of VHR1. Full RH and
strict Robin for every integer $n>5040$ remain unproved.

## Obtain positive Sobolev order from the same global null equation

Retain the hypothetical unit negative cap-four minimizer $F$ and
VHP7's GLOBAL supporting form, with $\lambda>0$. An analytic even
regularizer commutes with the COMPLETE arithmetic form. Its only
variational errors are consequently the two ORIGINAL physical
metrics in VHP3. A uniform Schur estimate pays their hard cuts and
allows a positive Sobolev order to be absorbed in VHB17.

This is a `repo-derived` application of W359, VHP1--VHP3, VHB16--VHB17
and classical Fourier multiplier and Schur estimates. Those suppliers
are reused; no general regularity theorem, priority claim or Lean/kernel
certification is supplied. The exponential multiplier cost below is
part of the estimate.

### Use a bounded regularizer before taking a Sobolev limit

Fix $c>q=5/4$ and $0<s_0<1/2$. In the $t$ coordinate of VHP3 set

$$
 j_{s,N}(\xi)=
 \left(\frac{c^2+\xi^2}{c^2+\xi^2/N^2}\right)^{s/2},
 \qquad J=j_{s,N}(D),\qquad N\ge2,\quad 0<s\le s_0.
 \tag{VHS1}
$$

Choose the branch positive on the real axis. It is even and
Schwarz-real on $|\Im z|<c$. For fixed $N$, $J-N^sI$ and
$J^2-N^{2s}I$ have symbols of order $-2$ on each smaller closed
strip. Their convolution terms have weighted $H^1$ regularity.
Applying VHP1's SAME Volterra/Möbius reconstruction to those terms
therefore gives actual $F_J,F_{J^2}\in\mathcal V$, with

$$
 \beta_J=J\beta,\quad \beta_{J^2}=J^2\beta,
 \qquad \beta(t)=g_F(t/2).
$$

Specifically, the smoothed terms give a half-line $H^1$ Gamma
profile whose zero extension has at most one jump, exactly as in
VHP1. Add $N^sF$ or $N^{2s}F$ to recover the full regularized
source. This range argument is for each finite $N$; it does not
assume a converse to W338 or positive regularity of $F$.

The Gamma multiplier and each full prime-power translation commute
with $J$. Both pole frequencies in the $\beta$ coordinate are
$\pm i/4$, where $j_{s,N}$ has the SAME real value. Thus W359,
including BOTH pole squares, gives exactly

$$
 \mathfrak E(F_J)=\Re\mathfrak E(F,F_{J^2}).
 \tag{VHS2}
$$

For each finite $N$ the strip bounds preserve the exponential
profile weight, so the complete prime sums and pole functionals
converge. The identity can equivalently be passed from VHP1's joint
core. No finite prime truncation or separate favorable sign is used.

### Keep the hard-cut metric commutators small in the Sobolev order

Write $X=KSw$ as in VHP3 and put

$$
 L=e^{qt}Je^{-qt},\qquad
 B_0=P_+,\qquad B_6=e^{-6t}P_+.
$$

The full-line multipliers $K,S,L$ commute, hence
$X_J=LX$ and $X_{J^2}=L^2X$. For $B=B_0,B_6$ define

$$
 D_B(X)=\langle LX,BLX\rangle
             -\Re\langle BX,L^2X\rangle.
$$

The GLOBAL mixed null equation and VHS2 give the exact account

$$
 0\le Q_\lambda(F_J)
 =\pi^{-7/2}\{\lambda D_{B_0}(X)-\mu D_{B_6}(X)\}.
 \tag{VHS3}
$$

Both original metrics remain in this formula. Their errors obey

$$
 \|[J,B]J^{-1}\|_{2\to2}\le Cs,
 \qquad \|LJ^{-1}-I\|_{2\to2}\le Cs,
 \qquad B=B_0,B_6,
 \tag{VHS4}
$$

uniformly in $N$. Here is the scalar estimate paying the cut.
The non-diagonal Fourier kernels of $B_0$ and $B_6$ are bounded by
$C/|\xi-\eta|$; the diagonal term of $B_0$ cancels in the
commutator. Put $a_\xi=(c^2+\xi^2)^{1/2}$. Direct differentiation
gives

$$
 0\le\frac{d\log j_{s,N}}{d\log a}\le s.
$$

Consequently the absolute commutator kernel is bounded by
$C|j_{s,N}(\xi)/j_{s,N}(\eta)-1|/|\xi-\eta|$.
Apply Schur with weight $a_\xi^{-1/2}$. On comparable scales the
derivative bound removes the diagonal singularity. On either far
scale the weighted row and column integrals are at most a constant
times

$$
 s\int_2^\infty\log v\,v^{s-3/2}dv\le C_{s_0}s.
$$

This proves the first estimate, including both signs of the real
frequency. For the second, the symbol is
$j_{s,N}(\xi+iq)/j_{s,N}(\xi)-1$. Integrate the logarithmic
derivative along that vertical segment. The segment stays inside
the fixed zero-free strip and the bound is $Cs$, independently of
$N$.

Set $Y=JX$ and write $L=(I+R)J$, $\|R\|\le Cs$.
In the second term of $D_B$, move the self-adjoint $J$ to the first
slot. The operator there is $JBJ^{-1}=B+[J,B]J^{-1}$.
Expansion and VHS4 therefore give $|D_B(X)|\le Cs\|Y\|_2^2$.
After reducing the fixed upper bound for $s$, the inverse of $I+R$
is uniformly bounded. VHP3 applied to the SAME actual $F_J$ then
gives

$$
 |D_{B_0}(X)|+|D_{B_6}(X)|
 \le Cs\|JX\|_2^2\le CsM(F_J).
 \tag{VHS5}
$$

The last step uses VHP3's full-line reconstruction bound for actual
even profiles, rather than a comparison of arbitrary full-line and
positive-half-line norms.

### Absorb the metric cost and retain the multiplier dependence

Fix $\eta$ as in VHB16 and retain
$\kappa=(1-\theta)/\theta>1/4$ and
$\Lambda=1+\lambda^{-\kappa}$. There are fixed $s_*,a_*>0$ such that
for

$$
 0<s\le\min\left(s_*,a_*\frac{\lambda}{\lambda+|\mu|}\right),
 \tag{VHS6}
$$

VHS3--VHS5 and VHB17 imply

$$
 \mathcal P(F_J)+\frac\lambda4M(F_J)
 \le C_\eta\Lambda\|g_{F_J}\|_2^2.
 \tag{VHS7}
$$

Indeed choose $s$ so that the upper bound for $Q_\lambda(F_J)$ is
at most $\lambda M(F_J)/4$. In W338,
$S(F_J)=\|u_{F_J}\|_2^2\le\mathcal P(F_J)$ since $p\ge1$.
The full logarithmic form comparison thus yields

$$
 \mathcal L_1(g_{F_J})+c_1\lambda M(F_J)
 \le C_\eta\Lambda\|g_{F_J}\|_2^2.
 \tag{VHS8}
$$

Choose $\log R=C_\eta\Lambda$ with a sufficiently large fixed
coefficient. The contribution of $|\tau|>R$ on the right of VHS8
is absorbed by its logarithmic left side. The remaining low
frequencies satisfy $j_{s,N}(\tau/2)^2\le C\exp(Cs\Lambda)$.
The original unit cap-four class has $\|g_F\|_2^2\le C$. Hence

$$
 \begin{aligned}
 \|g_{F_J}\|_2^2&\le C_\eta\exp(C_\eta s\Lambda),\\
 \mathcal L_1(g_{F_J})+\lambda M(F_J)
 &\le C_\eta\Lambda\exp(C_\eta s\Lambda).
 \end{aligned}
 \tag{VHS9}
$$

These bounds are uniform in $N$. Monotone convergence of
$j_{s,N}(\tau/2)^2$ proves the positive-order estimate

$$
 \boxed{\quad
 \|g_F\|_{H^s(\mathbb R)}^2
 \le C_\eta\exp[C_\eta s(1+\lambda^{-\kappa})].
 \quad}
 \tag{VHS10}
$$

The limiting weight is $(1+\tau^2/(4c^2))^s$, equivalent to the
usual $H^s$ norm with uniform constants for $s\le s_*$. This is a
positive Sobolev order of the original arithmetic profile, rather
than another finite logarithmic moment. Its range remains below
$1/2$; it supplies neither a continuous trace nor a physical
dilation derivative.

Under the finite-height premise, outside VHP10's exponentially
small allowance, VHP7 and VHP9 give $\lambda\asymp\delta$ and
$|\mu|\le C\delta$. A fixed $s>0$ is then allowed, but VHS10 costs
$\exp(C\delta^{-\kappa})$. For example, W367--W370's complete heat
comparison with $a=5/6$, $b=5/2$ and $\epsilon=1/T$ gives only

$$
 \delta\le C\eta_T+
 C\exp(C\delta^{-\kappa})T^{-s/3},
 \qquad \eta_T=\sqrt T\log(2+T)e^{-T}.
 \tag{VHS11}
$$

Its resulting exponent $1/\kappa<4$ does not improve VHR1's
existing $(\log T)^{-4}$ allowance. The positive-order estimate
and the uniform signed allowance are different conclusions. Full
RH and strict Robin for every integer $n>5040$ remain unproved.

## Control the complete finite physical dilation on that same minimizer

VHS10 has a consumer in the ORIGINAL source variation: it gives a
Hölder bound for the complete physical dilation, including its
Gamma term, every prime power, both poles and both original
metrics. The [existing physical-dilation formulas](hernandezsantamaria2025optimal.md#smooth-boundary-data-do-not-control-arithmetic-dilation-difference-quotients),
PD1--PD2, and VHB11's separated reconstruction are reused. This is
a paper application, without a derivative, a favorable energy sign,
an improved uniform Robin allowance or Lean/kernel certification.

Fix an order $s$ allowed by VHS6, and write

$$
 A_s=1+\|g_F\|_{H^s}^2
 \le C_\eta\exp(C_\eta s\Lambda),\qquad
 \nu_s=\frac{4s}{5s+2}.
$$

For $0<a\le1$ let

$$
 D_aF(x)=e^{7a/2}F(e^ax),\qquad G_a=D_aF-F.
$$

The parameter $a$ is the physical dilation size, not a Fourier
weight. These sources are not renormalized after variation.

### Pay the original metric variation at the arithmetic boundary

Put $h(t)=\sqrt\pi e^{7t/2}F(\pi e^t)$. The exact moment-coordinate
identity $h_{D_aF}(t)=h(t+a)$ gives

$$
 \begin{aligned}
 M(D_aF)&=M(F)-\int_0^a|h(t)|^2dt,\\
 \mathcal H(D_aF)&=e^{6a}
 \left[\mathcal H(F)-\int_0^a e^{-6t}|h(t)|^2dt\right].
 \end{aligned}
 \tag{VHD1}
$$

In particular $M(D_aF)\le M(F)\le4$. Domain membership also
persists. Its actual Gamma profile is
$u_{D_aF}=e^{5a/4}P_+u_F(\cdot+a)$. Translation preserves the
full logarithmic form, and the cross-half-line Carleman bound used
in W338 makes $P_+$ bounded in that form: its two diagonal
energies sum to the full energy up to a bounded $L^2$ cross term.
Thus $D_aF,G_a\in\mathcal V$. No scalar exterior-boundary
eigenfunction theorem is being applied.

VHS10 gives $\mathcal T_\beta(R)\le C_sA_sR^{-2s}$. Apply VHB11
with its interval radius $r=a$ and

$$
 N\asymp a^{-\nu_s/4},\qquad
 R\asymp a^{-\nu_s/(2s)}.
$$

For sufficiently small $a$, $2aN<1$. The three powers
$R^{-2s}$, $aRN$ and $N^{-4}$ are all of order $a^{\nu_s}$.
Since $h=\pi^{-7/4}X$ on the positive half-line, VHB11 and VHD1
therefore imply

$$
 \begin{aligned}
 \int_0^a|h(t)|^2dt&\le C_s A_s a^{\nu_s}\log(2/a),\\
 |M(D_aF)-M(F)|+
 |\mathcal H(D_aF)-\mathcal H(F)|
 &\le C_s A_s a^{\nu_s}\log(2/a).
 \end{aligned}
 \tag{VHD2}
$$

Enlarge $C_s$ for the remaining bounded range of $a$. This pays
the cut in the ACTUAL sixth moment, rather than replacing the
reconstructed source by its unweighted arithmetic profile.

### Retain the moving reflection and the complete arithmetic pairing

Let $g=g_F$ and $g_a=g_{D_aF}$. PD1 gives the folded translation

$$
 g_a(r)=e^{5a/4}g(|r|+a/2).
$$

Because $g$ is even, its difference from the unvaried profile is
the sum of a positive-half-line translate and a negative-half-line
translate. The classical boundedness of these two cuts on $H^u$,
$0\le u<1/2$, and the ordinary Fourier translation estimate give

$$
 \|g_a-g\|_{H^u}
 \le C_{s,u}a^{s-u}A_s^{1/2}\quad(0\le u<s),
 \qquad \|g_a\|_{H^s}\le C_s A_s^{1/2}.
 \tag{VHD3}
$$

This uses the true folded action; its reflection center has not
been fixed as $a$ changes.

For $b=5/2$, the exponential weight obeys
$\|g_a\|_b\le\|g\|_b\le C$: the factor $e^{5a/4}$ exactly
cancels the weighted translation factor, while the deleted
interval only lowers the squared norm. Interpolate VHD3 at $u=0$
with this SAME weight. For any $1/2<d<b$,

$$
 \|g_a-g\|_d
 \le C_{s,d}a^{s(1-d/b)}A_s^{(1-d/b)/2}.
 \tag{VHD4}
$$

As in W367--W368, the complete prime-power pairing has bilinear
bound $C_d\|v\|_d\|w\|_d$, since
$\sum_{n\ge2}\Lambda(n)n^{-d-1/2}<\infty$. Both pole
functionals are bounded in this same norm. The signed Gamma
pairing is bounded on $H^u\times H^u$ for every $u>0$, because
its multiplier grows logarithmically. Given

$$
 0<\rho<\frac45s,
$$

choose $d>1/2$ with $\rho<s(1-d/b)$ and $u>0$ with
$\rho<s-u$. VHD3--VHD4 and W359 then give an absolute bound for
the ENTIRE energy difference:

$$
 |\mathfrak E(D_aF)-\mathfrak E(F)|
 \le C_{s,\rho}A_s a^\rho.
 \tag{VHD5}
$$

The infinite prime sum and both poles belong to the same actual
$D_aF$. None is separately optimized, truncated or assigned a
favorable sign.

### Return the bound to the original source error

For $s<1/2$ one has $\nu_s>4s/5$. Hence the two metric errors in
VHD2 are also bounded by $C_{s,\rho}A_sa^\rho$.
VHP7's multipliers are uniformly bounded on these minimizers, so
VHD5 and the GLOBAL null property yield

$$
 0\le Q_\lambda(D_aF)=Q_\lambda(G_a)
 \le C_{s,\rho}A_s a^\rho.
 \tag{VHD6}
$$

Finally use VHB17 on this SAME actual $G_a$. VHD3 bounds its
squared unweighted profile error by $C_s A_sa^{2s}$. Since
$2s>\rho$, the complete Gamma and original source-moment errors
satisfy

$$
 \boxed{\quad
 \mathcal P(G_a)+\frac\lambda2M(G_a)
 \le C_{s,\rho,\eta}\Lambda A_sa^\rho.
 \quad}
 \tag{VHD7}
$$

Thus finite physical dilation is controlled in the actual
supporting-form, Gamma and sixth-moment norms at every fixed
positive multiplier. VHD7's exponent $\rho$ belongs to the squared
norm; the corresponding norm has Hölder exponent $\rho/2$.
The original moment error costs an additional
$\lambda^{-1}$ in VHD7. The exponent remains below one, so this
does not justify differentiating the physical dilation or asserting
$Q_\lambda(D_aF)=o(a)$. The exponential cost in VHS10 persists;
full RH and strict Robin for every integer $n>5040$ remain unproved.

## Recover the physical moment coordinate before estimating the source error

The positive-order regularizer also controls the ORIGINAL full-line
moment coordinate $X$. Consuming that information directly on
$G_a=D_aF-F$ improves the finite-dilation squared-error exponent
from VHD7's $\rho<4s/5$ to every $\rho<2s$. The bound pays a larger
explicit inverse-multiplier cost. This is a `repo-derived`
application of VHS5, VHS9, VHP3, VHD1 and W317; ordinary Sobolev
translation, embedding and half-line multiplication are reused.
It supplies no general regularity theorem, first-order dilation,
uniform allowance improvement, literature priority or Lean/kernel
certification.

Keep the SAME hypothetical unit negative cap-four minimizer,
positive supporting multiplier and order $s$ allowed by VHS6.
In particular $0<s<1/2$. Put

$$
 B_s=\left(1+\frac{\Lambda}{\lambda}\right)
                    \exp(C_\eta s\Lambda),
 \qquad \Lambda=1+\lambda^{-\kappa}.
$$

The larger constant $B_s$ must not be replaced by VHS10's smaller
unweighted-profile cost.

### Transfer the bounded regularizer to the original sixth-moment coordinate

For each finite $N$, VHS4 gives a uniformly bounded inverse of
$LJ^{-1}$ after the SAME reduction of $s$ already made in VHS5.
VHP3 applies to the actual regularized source, so

$$
 \|JX\|_2^2\le C\|LX\|_2^2
 =C\|X_J\|_2^2\le CM(F_J).
$$

VHS9 bounds the last expression by
$C_\eta\lambda^{-1}\Lambda\exp(C_\eta s\Lambda)$.
Monotone convergence of the regularizer weights, exactly as in
VHS10, consequently gives

$$
 \boxed{\quad \|X\|_{H^s(\mathbb R)}^2\le C_\eta B_s.\quad}
 \tag{VHM1}
$$

This is the physical reconstruction $X=KSw$, including all
Möbius shifts, rather than an independent arithmetic profile.
Its restriction gives $h=\pi^{-7/4}X$ on $t\ge0$.

To retain the original Gamma coordinate as well, let

$$
 A=S^{-1}=\sum_{n\ge1}n^{-3}T_{2\log n},
 \qquad \widetilde u(t)=e^{-q\max(t,0)}AX(t),
 \qquad q=5/4.
$$

The existing Dirichlet-convolution inverse is bounded on
full-line $H^s$: every translation is an isometry and the
coefficients are summable. Since $A,K,S$ commute,
$AX=Kw$. On the positive half-line, $e^{-qt}Kw$ is exactly the
original $u_F$. The bounded Lipschitz multiplier used in
$\widetilde u$ preserves $H^s$, so

$$
 \widetilde u|_{[0,\infty)}=u_F,
 \qquad \|\widetilde u\|_{H^s}^2\le C_s B_s.
 \tag{VHM2}
$$

Only an extension of this already actual coordinate is used;
no converse from a freely chosen Sobolev profile to source range
is assumed.

### Estimate the same source difference in both original norms

For $0<a\le1$ the exact physical action and VHD1 give

$$
 \begin{aligned}
 M(G_a)&=\pi^{-7/2}\int_0^\infty
                      |X(t+a)-X(t)|^2dt,\\
 u_{G_a}&=P_+\bigl[e^{qa}\widetilde u(\cdot+a)-\widetilde u\bigr].
 \end{aligned}
 \tag{VHM3}
$$

The second formula samples only $t,t+a\ge0$, where VHM2 is the
original Gamma coordinate. Fourier translation gives the first
bound below. For $0<v<s$, apply the ordinary
$H^s\to H^v$ translation bound and the boundedness of $P_+$ on
$H^v$, valid because $v<1/2$, to obtain

$$
 \begin{aligned}
 M(G_a)&\le C_s B_s a^{2s},\\
 \|u_{G_a}\|_{H^v}^2&\le C_{s,v}B_s a^{2(s-v)}.
 \end{aligned}
 \tag{VHM4}
$$

The amplitude error is $O(a)$ in norm and is absorbed since
$s-v<1$. The original positive Gamma multiplier satisfies
$p(\xi)\le C_v(1+\xi^2)^v$ for every $v>0$.
Choosing $v>0$ with $\rho<2(s-v)$ therefore proves

$$
 \boxed{\quad
 \mathcal P(G_a)+M(G_a)
 \le C_{s,\rho,\eta}B_s a^\rho
 \qquad(0<\rho<2s).
 \quad}
 \tag{VHM5}
$$

Thus both norms belong to the SAME original source error.
This also checks its Gamma form-domain membership directly.

### Use quadratic null cancellation before bounding the full energy variation

The one-dimensional Sobolev embedding
$H^s\hookrightarrow L^{2/(1-2s)}$, followed by Hölder on
$[0,a]$, gives
$\int_0^a|X(t)|^2dt\le C_sa^{2s}\|X\|_{H^s}^2$.
The exact VHD1 identities consequently imply

$$
 |M(D_aF)-M(F)|+
 |\mathcal H(D_aF)-\mathcal H(F)|
 \le C_s B_s a^{2s}.
 \tag{VHM6}
$$

Here $e^{6a}-1=O(a)$ is smaller than $Ca^{2s}$. No value or
trace of $X$ at zero is needed.

W317 bounds the ENTIRE debit of $G_a$ by
$|\mathfrak J(G_a,G_a)|\le C\mathcal N(G_a)^2\le CM(G_a)$.
This retains every prime power, both poles and both folded
channels. Together with VHP7's bounded multipliers and
$\mathcal H(G_a)\le CM(G_a)$, VHM5 gives

$$
 0\le Q_\lambda(D_aF)=Q_\lambda(G_a)
 \le\mathcal P(G_a)+CM(G_a)
 \le C_{s,\rho,\eta}B_s a^\rho.
 \tag{VHM7}
$$

Finally the exact identity
$\mathfrak E(D_aF)-\mathfrak E(F)
=Q_\lambda(G_a)-\lambda[M(D_aF)-M(F)]
+\mu[\mathcal H(D_aF)-\mathcal H(F)]$
and VHM6 imply

$$
 \boxed{\quad
 |\mathfrak E(D_aF)-\mathfrak E(F)|
 +Q_\lambda(D_aF)+\mathcal P(G_a)+M(G_a)
 \le C_{s,\rho,\eta}B_s a^\rho
 \qquad(0<\rho<2s).
 \quad}
 \tag{VHM8}
$$

The larger exponent uses the quadratic error AFTER the global
mixed null cancellation, rather than a separate estimate of the
mixed prime variation. As in VHD7, $\rho$ is the squared-norm
exponent; the corresponding norm exponent is $\rho/2$. The inverse-multiplier cost in $B_s$
remains; neither estimate uniformly dominates the other as
$\lambda\downarrow0$ and $a\downarrow0$ jointly.
Since $2s<1$, VHM8 still supplies neither $o(a)$ nor a physical
dilation derivative or favorable sign. It does not improve VHR1's
uniform $(\log T)^{-4}$ allowance. Full RH and strict Robin for
every integer $n>5040$ remain unproved.

## A critical signed quadratic defect on a fixed actual source

The subcritical estimate VHS5 cannot be extended as a universal
critical signed quadratic absorption estimate on actual sources.
The construction below keeps the ORIGINAL source inverse, every
Möbius shift, both metrics and the exponential tilt. It gives a
fixed actual source whose full-line reconstruction has every
subcritical Sobolev order and whose critical defect grows quadratically in the logarithm of the
regularizer cap, while its regularized moment grows only linearly
in that logarithm. This supplies the signed quadratic test on the
actual source range.

The actual inverse VHP1, full-line reconstruction VHP3 and the
finite-cap range argument of VHS1 are reused. Compact logarithm
and jump Fourier asymptotics and logarithmic frequency coordinates
are classical tools. The additional `repo-derived` application is
the signed critical asymptotic on this SAME actual source, without
a literature-priority claim or Lean/kernel certification. The
source is **not asserted to satisfy the GLOBAL supporting-form
null equation, the unit negative cap-four constraints, or even
nonpositive energy**. A cancellation forced by those hypotheses
remains a separate question.

### Critical regularizer and signed quadratic conclusion

Use the unitary Fourier transform

$$
 \widehat f(\xi)=(2\pi)^{-1/2}\int_{\mathbb R}f(t)e^{-i\xi t}\,dt,
 \qquad \langle f,g\rangle=\int\overline f g.
$$

Fix $q=5/4$, $c>q$, and set

$$
 j_N(\xi)=\left(\frac{c^2+\xi^2}{c^2+\xi^2/N^2}\right)^{1/4},
 \quad J_N=j_N(D),\quad L_N=e^{qt}J_Ne^{-qt},\quad N\ge2.
$$

These are VHS1's bounded regularizers at the critical order $s=1/2$. For a bounded real multiplication operator $B$, define

$$
 D_B^L(X)=\langle L_NX,BL_NX\rangle-
             \Re\langle BX,L_N^2X\rangle,
$$

and use $D_B^J$ for the same expression with $J_N$ in place of $L_N$. In particular, $B$ need not be positive.

For arbitrary real $A,C$, the construction below gives a fixed real actual source $F\in\mathcal V$, with its original full-line reconstruction $X=KSw$, such that

$$
 \boxed{D_{P_+}^{L}(X)=\frac{AC}{2\pi c}(\log N)^2+O(\log N).}
 \tag{VHC1}
$$

More generally, for fixed real $\lambda,\mu$,

$$
 \boxed{
 D_{\lambda P_+-\mu e^{-6t}P_+}^{L}(X)
 =\frac{(\lambda-\mu)AC}{2\pi c}(\log N)^2
   +O_{\lambda,\mu}(\log N).}
 \tag{VHC2}
$$

At the same time,

$$
 \|J_NX\|_2^2+\|L_NX\|_2^2=O(\log N),\qquad
 M(F_{J_N})=O(\log N).
 \tag{VHC3}
$$

For fixed $\lambda>0$ and $\lambda\ne\mu$, choose the sign of $AC$ to make the leading coefficient positive. The signed defect then cannot be absorbed into any fixed multiple of $\lambda M(F_{J_N})$, uniformly in $N$. All constants below may depend on the fixed cutoff, $A,C,c$, and the owned reconstruction operators, but not on $N$.

### An explicit even profile and its actual inverse

Let

$$
 t_0=2\log2,\quad a_n=2\log n,
 \quad 0<\varepsilon<\tfrac1{10}\min(t_0,a_3-t_0).
$$

Choose a real even $\chi\in C_c^\infty((-\varepsilon,\varepsilon))$ with $\chi=1$ on $[-\varepsilon/2,\varepsilon/2]$. Let $H=\mathbf1_{(0,\infty)}$, put $D=-\sqrt2 C$, and define, up to irrelevant values at isolated points,

$$
 \begin{split}
 \beta(t)={}&A\chi(t)\log|t|\\
 &+D\bigl[\chi(t-t_0)H(t-t_0)
              +\chi(t+t_0)H(-t-t_0)\bigr].
 \end{split}
 \tag{VHC4}
$$

This is real, even, compactly supported, and belongs to every $H^r(\mathbb R)$, $r<1/2$. Its only singularities are the logarithm at zero and the jumps at $\pm t_0$. No pointwise value is assigned at the logarithmic singularity.

For $t\ge0$, perform the same owned inverse as VHP1:

$$
 Y(t)=\int_0^\infty e^{v/4}\beta(t+v)\,dv,
 \qquad u(t)=\beta(t)+\tfrac32Y(t),
 \tag{VHC5}
$$

$$
 U(x)=x^{-9/4}u(\log(x/\pi)),\qquad
 F(x)=\sum_{n\ge1}\mu(n)n^4U(n^2x),\quad x\ge\pi.
 \tag{VHC6}
$$

These formulas really produce an actual member of $\mathcal V$, rather than invoking a converse to W338:

1. On the positive half-line $\beta$ is supported in $[0,t_0+\varepsilon]$. Hence $Y,u$ have this same upper support bound. Also $Y'=-\beta-Y/4$, so $Y\in H^1(0,\infty)$.
2. The sum in VHC6 is finite for $x\ge\pi$; with the chosen support it has only $n=1,2$. The finite divisor identity gives $\mathscr TF=U$. The original sixth moment is finite, since $U$ has bounded physical support and belongs to the weighted $L^2$ space there.
3. The zero extension of $u$ consists of a one-sided compact logarithm, a compact jump, and the zero extension of a compact half-line $H^1$ function. Its Fourier transform is $O((1+\log|\xi|)/|\xi|)$. Thus its actual $p$-weighted Fourier integral is finite, since $p(\xi)=O(1+\log(2+|\xi|))$. This proves $F\in\mathcal V$.
4. With $(I_{5/4}v)(t)=\int_0^\infty e^{-5a/4}v(t+a)da$, the Volterra identity $(I-\tfrac32 I_{5/4})u=\beta$ holds on $t\ge0$. Consequently the actual even arithmetic profile of $F$ is $g_F(r)=\beta(2r)$. The prescribed even profile and the reconstructed source agree.

Set, on the whole line exactly as in VHP3,

$$
 w=e^{qt}\beta,\quad
 S=\sum_{n\ge1}\mu(n)n^{-3}T_{a_n},\quad
 K=I+\tfrac32I_1,\quad X=KSw.
 \tag{VHC7}
$$

Here $I_1f(t)=\int_0^\infty e^{-v}f(t+v)\,dv$. All these are the owned actual reconstruction operators. On the positive half-line $X=\pi^{7/4}h_F$.

Near zero only the $n=1$ and $n=2$ terms of $Sw$ are nonzero. They give

$$
 Sw(t)=Ae^{qt}\log|t|+Ce^{qt}H(t)
 \quad (0<|t|<\varepsilon/2).
 \tag{VHC8}
$$

Indeed, the second coefficient is
$\mu(2)2^{-3}e^{qt_0}D=-D/\sqrt2=C$.
Since $K-I:L^2(\mathbb R)\to H^1(\mathbb R)$, VHC8 implies

$$
 X(t)=A\log|t|+CH(t)+R(t),\qquad R\in H^1_{\mathrm{loc}}\text{ near }0.
 \tag{VHC9}
$$

There is **no claim that the global remainder in VHC9 belongs to $H^1$**. The other shifted singularities are retained explicitly next.

### Keep every shifted singularity in the Fourier expansion

Put

$$
 d_+=De^{qt_0},\qquad d_-=-De^{-qt_0}.
$$

For $\xi\to+\infty$, the standard compact-logarithm and compact-jump expansions give

$$
 \widehat w(\xi)=\frac1{\sqrt{2\pi}\xi}
 \bigl[-\pi A-i d_+e^{-it_0\xi}-i d_-e^{it_0\xi}\bigr]
 +O(\xi^{-2}).
 \tag{VHC10}
$$

For completeness, the logarithm coefficient follows by differentiating $\chi\log|t|$: its principal singular derivative is $\operatorname{pv}(1/t)$, with nonunitary transform $-i\pi\operatorname{sgn}\xi$. The remaining derivative has transform $O(\xi^{-1})$. Multiplication of the logarithm by a smooth factor vanishing at zero adds $t b(t)\log|t|$; its second derivative is a compact $L^1$ function plus a compact principal-value $b(t)/t$, whose transform is bounded. It therefore adds $O(\xi^{-2})$. A compact step of jump $d$ contributes $d e^{-it_*\xi}/(i\sqrt{2\pi}\xi)+O(\xi^{-2})$, by integration by parts. These observations establish VHC10 with a genuine pointwise remainder.

The full-line Fourier multipliers of $S,K$ are

$$
 \sigma(\xi)=\sum_{n\ge1}\mu(n)n^{-3}e^{ia_n\xi},
 \qquad k(\xi)=1+\frac{3/2}{1-i\xi}.
$$

Both are bounded and $k-1=O(\xi^{-1})$. Multiplying VHC10 gives

$$
 \begin{split}
 \xi\widehat X(\xi)=\frac1{\sqrt{2\pi}}\sum_{n\ge1}\mu(n)n^{-3}
 \bigl[&-\pi A e^{ia_n\xi}\\
       &-i d_+e^{-i(t_0-a_n)\xi}
        -i d_-e^{-i(-t_0-a_n)\xi}\bigr]
       +O(\xi^{-1}).
 \end{split}
 \tag{VHC11}
$$

The error is uniform in $\xi\ge1$; the series of coefficients is absolutely summable. Exactly two terms in VHC11 have phase zero: the logarithm term with $n=1$, and the $d_+$ jump term with $n=2$. Their combined coefficient is

$$
 \frac{-\pi A-iC}{\sqrt{2\pi}}.
 \tag{VHC12}
$$

Every remaining phase $t_*$ has a fixed positive distance from zero:

$$
 |t_*|\ge d_*:=\min(t_0,a_3-t_0)>0.
 \tag{VHC13}
$$

This includes all shifted logarithms at $-a_n$, $n\ge2$, all shifted positive jumps at $t_0-a_n$, $n\ne2$, and all shifted negative jumps at $-t_0-a_n$. Coincident nonzero phases may be combined; their absolute coefficients are still summable.

In particular, $X\in H^r(\mathbb R)$ for every $0\le r<1/2$, $X\in L^1\cap L^2$, $\widehat X$ is bounded near zero, and $\widehat X(\xi)=O(1/|\xi|)$ at infinity. The $L^1$ assertion follows directly from VHC7, since $w\in L^1$ and the translations, the absolutely summable $S$, and $I_1$ are bounded on $L^1$.

Write $\ell=\log N$ and define for $x\ge0$

$$
 f(x)=c^{-1/2}e^x\widehat X(e^x)=a+e(x),
 \qquad a=\frac{-\pi A-iC}{\sqrt{2\pi c}}.
 \tag{VHC14}
$$

Then $e$ is bounded and has a uniformly bounded primitive:

$$
 \sup_{L\ge0}\left|\int_0^L e(x)\,dx\right|<\infty.
 \tag{VHC15}
$$

Indeed the remainder in VHC11 is $O(e^{-x})$, hence integrable in $x$. Each nonzero phase satisfies

$$
 \int_0^L e^{-it_*e^x}\,dx
 =\int_1^{e^L}\frac{e^{-it_*v}}v\,dv,
 \qquad\left|\int_1^R\frac{e^{-it_*v}}v\,dv\right|
 \le\frac3{|t_*|}\le\frac3{d_*},
 \tag{VHC16}
$$

by one integration by parts. Absolute summability of all coefficients proves VHC15. This is the estimate that pays every remote singularity; none is silently moved into an $H^1$ remainder.

### The exact four Fourier blocks of the quadratic defect

Set $Y_N=J_NX$. The Fourier convolution kernel of $P_+$ is

$$
 \tfrac12\delta(\xi-\eta)+\frac1{2\pi i}\operatorname{pv}\frac1{\xi-\eta}.
$$

The delta cancels in the double defect. Consequently its kernel in the $Y_N$ coordinate is

$$
 M_N(\xi,\eta)
 =\frac{i}{4\pi(\xi-\eta)}
 \left[\frac{j_N(\xi)}{j_N(\eta)}+
       \frac{j_N(\eta)}{j_N(\xi)}-2\right].
 \tag{VHC17}
$$

The numerator removes the diagonal singularity. Split each frequency into $\xi=\sigma e^x$, $\eta=\tau e^y$, $\sigma,\tau\in\{+,-\}$, and use the unitary coordinates

$$
 V_N^\sigma(x)=e^{x/2}\widehat Y_N(\sigma e^x).
$$

The exact logarithmic kernel is

$$
 \mathcal K_N^{\sigma\tau}(x,y)
 =\frac{i}{4\pi}
 \left[r_N(x,y)+r_N(x,y)^{-1}-2\right]
 \frac{e^{(x+y)/2}}{\sigma e^x-\tau e^y},
 \quad r_N=\frac{j_N(e^x)}{j_N(e^y)}.
 \tag{VHC18}
$$

The defect is the sum of the four integrals
$\iint\overline{V_N^\sigma(x)}\mathcal K_N^{\sigma\tau}(x,y)V_N^\tau(y)\,dx\,dy$.
At each fixed $N$, first restrict $X$ to the symmetric Fourier
band $\epsilon\le|\xi|\le R$, then send $\epsilon\downarrow0$ and
$R\to\infty$. Boundedness of $J_N$ and $P_+$ on $L^2$ passes the
quadratic form to the limit. The kernel bound below and VHC23's
$L^1$ bounds supply integrable domination for these four integrals.

For all real $x,y$, all $N$, and all blocks,

$$
 |\mathcal K_N^{\sigma\tau}(x,y)|\le C;
$$

for same-sign blocks it also obeys $C\min(|x-y|,1)$. To see this, note that
$0\le d\log j_N(e^x)/dx\le1/2$. For $x\ge y$, therefore $1\le r_N\le e^{(x-y)/2}$; substituting the largest possible numerator in VHC18 gives respectively the bounds by $\tanh(|x-y|/4)$ and $1-\operatorname{sech}((x-y)/2)$.

### Pay the cap and every exterior frequency

On $0\le x\le\ell$, write

$$
 j_N(e^x)=c^{-1/2}e^{x/2}e^{b_N(x)},
 \quad b_N(x)=\tfrac14\log(1+c^2e^{-2x})
              -\tfrac14\log(1+c^{-2}e^{2(x-\ell)}).
$$

For $\omega_N(x)=e^{-2x}+e^{-2(\ell-x)}$,

$$
 |b_N(x)|+|b_N'(x)|\le C_c\omega_N(x),\qquad
 \int_0^\ell\omega_N(x)\,dx\le C.
 \tag{VHC19}
$$

It follows that $V_N^+(x)=e^{b_N(x)}f(x)$, so it is bounded, and

$$
 \|V_N^+-f\|_{L^1(0,\ell)}\le C.
 \tag{VHC20}
$$

Because $X$ is real, $V_N^-=\overline{V_N^+}$.

Replace $r_N(x,y)$ in VHC18 by $e^{(x-y)/2}$. The resulting four kernels are exactly

$$
 \begin{array}{ll}
 \mathcal K_\infty^{++}=\dfrac{i}{4\pi}\tanh\dfrac{x-y}{4},
 &\mathcal K_\infty^{--}=-\mathcal K_\infty^{++},\\[2mm]
 \mathcal K_\infty^{+-}=\dfrac{i}{4\pi}
       \left(1-\operatorname{sech}\dfrac{x-y}{2}\right),
 &\mathcal K_\infty^{-+}=-\mathcal K_\infty^{+-}.
 \end{array}
 \tag{VHC21}
$$

On the middle square $[0,\ell]^2$,

$$
 |\mathcal K_N^{\sigma\tau}-\mathcal K_\infty^{\sigma\tau}|
 \le C[\omega_N(x)+\omega_N(y)].
 \tag{VHC22}
$$

For $|x-y|\ge1$, this follows directly from VHC19 and the exponential denominators in VHC18. For $|x-y|<1$, use
$|b_N(x)-b_N(y)|\le C|x-y|[\omega_N(x)+\omega_N(y)]$; differentiating the cosh numerator supplies the other factor of $|x-y|$, which cancels the sinh denominator. Thus VHC22 has no diagonal singularity.

The contribution of VHC22 to each bounded-amplitude quadratic integral is $O(\ell)$, by VHC19. Replacing $V_N^+$ by $f$, and $V_N^-$ by $\bar f$, also costs $O(\ell)$, using VHC20 and the uniform kernel bound.

The exterior logarithmic intervals are equally explicit. Since $\widehat X$ is bounded at zero and $O(1/|\xi|)$ at infinity,

$$
 |V_N^\sigma(x)|\le
 \begin{cases}
 Ce^{x/2},&x<0,\\
 C,&0\le x\le\ell,\\
 Ce^{-(x-\ell)/2},&x>\ell.
 \end{cases}
 \tag{VHC23}
$$

Hence the exterior $L^1$ norm is uniformly bounded and the total $L^1$ norm is $O(1+\ell)$. The uniform bound on VHC18 shows that every integral involving at least one exterior frequency is $O(\ell)$. This pays both the low-frequency regularization and the entire $N$-cap tail; no sharp-cut substitute for $j_N$ is assumed.

### Evaluate the four homogeneous blocks

We have reduced the defect, with error $O(\ell)$, to VHC21 on $[0,\ell]^2$, with inputs $f=a+e$ and $\bar f$, where $e$ is bounded and has bounded primitive.

For the same-sign blocks, decompose

$$
 \tanh(z/4)=\operatorname{sgn}(z)+r(z),\qquad r\in L^1(\mathbb R).
$$

The $r$-part is $O(\ell)$ by Young's inequality and $\|f\|_{L^2(0,\ell)}^2=O(\ell)$. The constant-constant sign integral vanishes. For an error factor, its primitive is bounded; explicitly,

$$
 \int_0^\ell\operatorname{sgn}(x-y)e(y)dy
 =2\int_0^x e(y)dy-\int_0^\ell e(y)dy=O(1).
$$

This controls the error-error term by $O(\ell)$. The constant-error terms are $O(\ell)$ as well: after interchanging the integrals they involve $\int_0^\ell(\ell-2y)e(y)dy$, bounded by $C\ell$ after one integration by parts with the bounded primitive. Therefore **both same-sign blocks are $O(\ell)$**.

For the cross blocks, the sech part is $O(\ell)$ by Young's inequality. Their constant parts, including both conjugate blocks and the unitary normalization, sum to

$$
 2\Re\left[\frac{i}{4\pi}
          \left(\int_0^\ell\overline{f(x)}dx\right)^2\right]
 =2\Re\left[\frac{i\bar a^2}{4\pi}\right]\ell^2+O(\ell).
$$

Since $a=(-\pi A-iC)/\sqrt{2\pi c}$,

$$
 2\Re\left[\frac{i\bar a^2}{4\pi}\right]
 =\frac{AC}{2\pi c}.
$$

Together with the cap and exterior-frequency bounds this proves

$$
 D_{P_+}^{J}(X)=\frac{AC}{2\pi c}\ell^2+O(\ell).
 \tag{VHC24}
$$

VHC15--VHC16 explicitly show why all remote shifted logarithms and jumps contribute only $O(\ell)$, including their cross terms with the singularity at zero and with each other. No real-symmetry restriction is dropped: the negative-frequency input is exactly the conjugate of the positive-frequency input throughout.

### The continuous joint-metric part has no quadratic logarithm

Let $C_6=(1-e^{-6t})P_+$. Its non-diagonal Fourier kernel equals that of $P_+$ multiplied by

$$
 \frac6{6+i(\xi-\eta)}.
$$

Thus its double-defect logarithmic kernel is VHC18 times this factor. Outside the middle square VHC23 again gives $O(\ell)$. On the middle square its absolute integral is uniformly bounded:

* For opposite signs, $|\xi-\eta|=e^x+e^y$, so the extra factor is bounded by $Ce^{-\max(x,y)}$, integrable on the quadrant.
* For the same signs, assume $x=y+z$, $z\ge0$. For $z\le1$, the product is bounded by $C\min(z,e^{-y})$; for $z\ge1$, it is bounded by $Ce^{-y-z}$. Both are integrable in $y,z\ge0$.

The bounded amplitudes therefore give $D_{C_6}^{J}(X)=O(\ell)$. Since

$$
 \lambda P_+-\mu e^{-6t}P_+
 =(\lambda-\mu)P_++\mu C_6,
$$

VHC24 proves VHC2 for the self-adjoint $J_N$.

### Retain the actual exponential tilt

In the adopted convention $L_N$ has symbol $j_N(\xi+iq)$. On $|\Im z|\le q<c$, the factors $|c^2+z^2|$ and $|c^2+z^2/N^2|$ are uniformly comparable to $c^2+\xi^2$ and $c^2+\xi^2/N^2$. Differentiating

$$
 m_N(z)=j_N(z)^2=
 \left(\frac{c^2+z^2}{c^2+z^2/N^2}\right)^{1/2}
$$

gives

$$
 m_N'(z)=m_N(z)\,
 \frac{zc^2(1-N^{-2})}
 {(c^2+z^2)(c^2+z^2/N^2)}.
$$

This is uniformly bounded on the strip, as is $j_N'=m_N'/(2j_N)$. Vertical integration yields

$$
 \|L_N-J_N\|_{2\to2}+\|L_N^2-J_N^2\|_{2\to2}\le C_{c,q}.
 \tag{VHC25}
$$

VHC10--VHC11 give $\|J_NX\|_2^2=O(\ell)$: the middle frequencies contribute $\int_1^N d\xi/\xi$; the $|\xi|>N$ contribution is $O(1)$, since $j_N^2\le N$. Expanding the first term of the defect and using VHC25 then shows

$$
 |D_B^L(X)-D_B^J(X)|
 \le C_B\|X\|_2(\|J_NX\|_2+\|X\|_2)
 =O(\sqrt\ell)+O(1).
 \tag{VHC26}
$$

This proves VHC1--VHC2 with the actual nonself-adjoint $L_N$. The tilt has not been discarded.

### Actual regularized sources and the precise method boundary

For each finite $N$, $j_N-N^{1/2}$ and $j_N^2-N$ have order $-2$ on smaller closed strips. The VHS1/VHP1 construction therefore supplies actual $F_{J_N},F_{J_N^2}\in\mathcal V$, including the nondegenerate case $AC\ne0$, in which $X\notin H^{1/2}$. Their actual reconstructions satisfy $X_{J_N}=L_NX$, and

$$
 M(F_{J_N})=\pi^{-7/2}\|P_+L_NX\|_2^2=O(\log N).
$$

The complete energy commutation identity continues to hold for every finite $N$. The initial profile is compactly supported; the regularized profiles have the required exponential weight from the zero-free strip $c>q$. Thus the complete prime-power sums, both pole functionals, and Gamma terms are the same actual objects used in VHS2. No arithmetic term or original metric is changed to create the example.

For fixed $\lambda>0$ and $\lambda\ne\mu$, choosing $(\lambda-\mu)AC>0$ yields

$$
 D_{\lambda P_+-\mu e^{-6t}P_+}^{L}(X)
 \sim \frac{(\lambda-\mu)AC}{2\pi c}(\log N)^2,
 \qquad M(F_{J_N})=O(\log N).
$$

Consequently a universal critical signed replacement of VHS5 by a fixed multiple of $M(F_{J_N})$ is false, even on actual sources with every subcritical Sobolev order. A fixed positive $\lambda$ does not supply an $N$-independent absorption constant for this example.

This leaves a narrower, genuinely null-specific question. A GLOBAL null minimizer could satisfy a relation that excludes, cancels, or signs the logarithm/jump cross coefficient. No such relation is proved here, and the example is not asserted to satisfy the GLOBAL null equation or the unit negative cap-four minimization constraints. When $\lambda=\mu$, the quadratic logarithmic term cancels; this proof does not settle the remaining critical absorption problem in that case. The result gives no dilation derivative, no $o(a)$ conclusion, and no RH/Robin improvement.

### The original source can satisfy every nontrivial fixed moment cap

Fix any $K_*>1$, $\lambda>0$ and $\mu\ne\lambda$. The source in
VHC2--VHC3 may be chosen so that

$$
 \|F\|_H=1,\qquad M(F)<K_*.
 \tag{VHC27}
$$

This cap is on the ORIGINAL unregularized source $F$; no cap on
$F_{J_N}$ is asserted. Keep VHC4's cutoff restriction and choose
$\varepsilon<(\log K_*)/6$ as well. Set $A=1$ and first $C=0$.
The Volterra inverse then has support in $[0,\varepsilon]$.
Consequently $U$ is supported in $[\pi,\pi e^\varepsilon]$;
since $\varepsilon<\log4$, no $n\ge2$ term of VHC6's actual
Möbius inverse contributes on $x\ge\pi$. Thus $F_0=U\ne0$,
where nonvanishing follows from the forward Volterra identity, and

$$
 M(F_0)\le e^{6\varepsilon}\|F_0\|_H^2
                   <K_*\|F_0\|_H^2.
$$

Now vary the jump coefficient $C$. The actual inverse is affine,
$F_C=F_0+CF_1$, in $H_6$. Both sides of the strict cap inequality
are continuous quadratic functions of $C$. It therefore persists
for all sufficiently small $|C|$, with $F_C\ne0$. Fix such a
nonzero $C$ with $(\lambda-\mu)C>0$ and normalize by
$\|F_C\|_H$. This rescales $A,C$ by the same positive constant,
preserving the nonzero signed leading coefficient. Only AFTER
fixing this source take $N\to\infty$ in VHC2--VHC3. This proves
VHC27 and the failure of uniform critical signed absorption even
within that unit original-source moment cap. The asymptotic
constants and starting $N$ may depend on $K_*$ and the fixed $C$.

A unit norm and a fixed original moment budget alone therefore do
not repair the generic endpoint estimate. No negative-energy,
GLOBAL null or minimizing property has been obtained for this
source. At cap one the unit feasible set is already empty by the
existing W321 result; no endpoint feasible vector is inferred.

The generic endpoint substitution is therefore unavailable. A
critical absorption argument for the hypothetical negative minimizer
requires additional information specific to that restricted class;
its SAME global null equation is one possible source.
This method boundary leaves VHR1's uniform $(\log T)^{-4}$
allowance unchanged. Full RH and strict Robin for every integer
$n>5040$ remain unproved.

The [fixed-source Gamma-payment obstruction](hernandezsantamaria2025optimal.md#a-fixed-actual-source-excludes-a-universal-gamma-only-critical-payment)
strengthens this generic method boundary: its signed defect is quadratic
in $\log\log\log N$, while its regularized moment and actual
Gamma payment, including a fixed spatial weight, remain uniformly bounded. That source is likewise not GLOBAL null.

## Weighted null estimates in the actual theta coordinate

Reuse W317's COMPLETE bilinear debit, W324's actual inverse, VHB3's
inverse on $H_{4+\eta}$, and VHP7's GLOBAL supporting form. The published
[exponential convolution-kernel supplier](../Fourier/mantoiupurice2007hardy.md),
Lemma 3.1, supplies the weighted Gamma step; its hypotheses are checked
below. Exponentially weighted energy identities and the digamma
recurrence are classical tools, not new general results.
The additional repo-derived interface keeps every theta dilation and
both original metrics while weighting the SAME null source. The
consumer below is direct physical compactification. This is paper
mathematics without Lean/kernel certification or a priority claim.

Suppose $F\in\mathcal V$, $\lambda\ge0$, $\mu\in\mathbb R$, and
$$
 Q_\lambda(G)=\mathfrak E(G)+\lambda M(G)-\mu\mathcal H(G)\ge0
 \quad(G\in\mathcal V),\qquad Q_\lambda(F)=0.
 \tag{VHN1}
$$
Polarization gives $Q_\lambda(F,G)=0$ for every ACTUAL $G\in\mathcal V$.
Keep $U=\mathscr TF$, its zero-extended Gamma coordinate
$u(t)=(\pi e^t)^{9/4}U(\pi e^t)$, $q=5/4$, and
$\mathcal G(f)=\int p(\xi)|\widehat f(\xi)|^2d\xi$ with W317's
fixed $p\ge1$. For every fixed $0<r<1/2$,
$$
 \mathcal G(e^{rt}u)\le C_r(1+|\mu|)M(F)
 \qquad(\lambda\ge0).
 \tag{VHN2}
$$
For $\lambda>0$ there is additionally an ACTUAL $F^{(r)}\in\mathcal V$
with $\mathscr TF^{(r)}=(x/\pi)^rU$ and
$$
 \lambda M_{6+2r}(F)+\mathcal P(F^{(r)})
 \le C_r(1+|\mu|)M(F),\qquad
 M_k(F)=\int_\pi^\infty(x/\pi)^k|F(x)|^2dx.
 \tag{VHN3}
$$
At $\lambda=0$, VHN2 asserts a coordinate property only; it does not
assert $F^{(r)}\in H_6$ or an additional original moment. The constants
are independent of $F,\lambda,\mu$ but may diverge at $r=1/2$.

### Construct the bounded actual tests before using nullity

For $R\ge1$ set $w(t)=\exp(r\min\{t_+,R\})$ on the WHOLE line and
$$
 U_{w^j}(x)=w(\log(x/\pi))^jU(x),\qquad
 F_{w^j}=\mathscr S U_{w^j},\qquad j=1,2.
 \tag{VHN4}
$$
For each finite $R$, W324 gives $F_{w^j}\in H_6$ and
$u_{F_{w^j}}=w^ju$. Bounded Lipschitz multiplication preserves the
logarithmic Gamma form: in its difference representation use
$\|wf-T_s(wf)\|_2\le\|w\|_\infty\|f-T_sf\|_2+
\min(\operatorname{Lip}(w)|s|,2\|w\|_\infty)\|f\|_2$.
The logarithmic kernel is $O(1/s)$ at zero and exponentially decaying
at infinity; a bounded rational remainder does not change membership.
This also applies to $w^2$, so BOTH tests belong to $\mathcal V$.
Membership constants may depend on $R$; the bounds below do not.

### Pay the full Gamma defect after shifting its first pole

Put $a=1/4$, $\alpha=2/\sqrt\pi$, and
$d_c(\xi)=\Re\operatorname{digamma}(c+i\xi)-\log\pi$. The exact
owned multiplier, including its rational factor, satisfies
$$
 \begin{aligned}
 p(\xi)&=\alpha\frac{\xi^2+a^2}{\xi^2+q^2}d_a(\xi)+c_\Gamma
        =\alpha d_q(\xi)-\alpha b(\xi)+c_\Gamma,\\
 b(\xi)&=\frac{(3/2)d_q(\xi)+a}{\xi^2+q^2}.
 \end{aligned}
 \tag{VHN5}
$$
Indeed $\operatorname{digamma}(a+1+z)=\operatorname{digamma}(a+z)
+(a+z)^{-1}$ and $q=a+1$. The analytic continuation uses
$[\operatorname{digamma}(q+iz)+\operatorname{digamma}(q-iz)]/2$,
not a complex-variable real-part operation. VHN5 makes $p$ analytic
on $|\Im z|<q$. On every smaller closed strip,
$p(z)=O(\log(2+|\Re z|))$ and
$p^{(j)}(z)=O_j(\langle\Re z\rangle^{-j})$ for $j\ge1$.
Thus $p$ belongs to the supplier's $\mathcal O_0^s(\mathbb C_q)$ for
any $0<s<1$. Apply its Lemma 3.1 with $m=1$: for
$k=(p')^\vee$ and every $0<\gamma<q$,
$\int e^{\gamma|h|}|k(h)|dh<\infty$.

Off the diagonal, the distribution kernel of $p(D)$ is a fixed
Fourier-normalization multiple of $k(h)/h$; any diagonal delta term
cancels in the commutator. The difference factor
in the commutator cancels that denominator, since
$$
 \frac{|w(t+h)/w(t)-1|}{|h|}\le r e^{r|h|}.
$$
Young's convolution inequality, choosing $r<\gamma<q$, gives
$\|[p(D),w]w^{-1}\|_{2\to2}\le C_r$, uniformly in $R$.
The same reasoning for $w^2$ uses $2r<q$; it preserves the operator
domain, and interpolation with $L^2$ preserves the positive form
domain. Lipschitz weights follow by smoothing with the same kernel
bound. These statements also verify the actual test membership in
VHN4 without invoking a new general weighted-domain theorem.

For $D_\Gamma=\mathcal P(F_w)-\Re\mathcal P(F,F_{w^2})$,
self-adjointness gives the form identity
$$
 \begin{aligned}
 D_\Gamma&=\Re\langle wu,[p(D),w]u\rangle,\\
 |D_\Gamma|&\le C_r\|wu\|_2^2\le C_rM(F).
 \end{aligned}
 \tag{VHN6}
$$
The identities extend from the operator domain by the just established
form-domain invariance. The last inequality uses $w\le e^{rt}$ on
the support of $u$, $r<q$, and W324's
$\|e^{qt}u\|_2^2\le CM(F)$. The zero extension is retained.
No boundary trace, pole deletion or smooth debit is assumed.

### Keep the mixed original moment instead of absorbing its defect

On $L^2(0,\infty)$ put $v=e^{qt}u$, $T_hv(t)=v(t+h)$ and
$S=\sum_{n\ge1}\mu(n)n^{-3}T_{2\log n}$. W324 gives exactly
$$
 M(F)=\pi^{-7/2}\|Sv\|_2^2,\qquad
 M(F,F_{w^2})=\pi^{-7/2}\langle Sv,S(w^2v)\rangle.
$$
There is no Volterra factor here: the weighted coordinate is $u$.
For $z=wv$, $A=wSw^{-1}$ and $B=w^{-1}Sw$, the mixed pairing is
$\pi^{-7/2}\langle Az,Bz\rangle$. Monotonicity and log-Lipschitz
continuity of $w$ give
$$
 \|A-I\|\le\zeta(3)-1<21/100,\qquad
 \|B-I\|\le\zeta(3-2r)-1\le\zeta(2)-1<13/20.
$$
Every positive-half-line translation is a contraction, so these bounds
pay ALL Möbius shifts. The first numerical inequality follows by
summing through $n=4$ and bounding the remaining $n^{-3}$ sum by
$\int_4^\infty x^{-3}dx$; the second follows from
$\zeta(2)=\pi^2/6$ and $\pi<22/7$. Expansion around the identity yields
$$
 \Re M(F,F_{w^2})\ge\frac7{2000}\pi^{-7/2}\|wv\|_2^2,
 \quad 1-\frac{21}{100}-\frac{13}{20}
              -\frac{21}{100}\frac{13}{20}=\frac7{2000}>0.
 \tag{VHN7}
$$

### Pay the complete mixed debit in the weaker inverse space

Choose $\eta=1-2r>0$ and $a_\eta=1/4+\eta/2=3/4-r$.
The actual inverse on $H_{4+\eta}$ has norm at most
$\zeta(1+\eta)$, since its single-dilation norm is $n^{-1-\eta}$.
Also $\mathcal N(G)^2+\mathcal H(G)\le C_\eta\|G\|_{H_{4+\eta}}^2$.
Using $\|V\|_{H_k}^2=\pi^{-7/2}\int e^{(k-7/2)t}
|(\pi e^t)^{9/4}V(\pi e^t)|^2dt$ and
$a_\eta+2r=3/4+r<q$ gives
$$
 \begin{aligned}
 \mathcal N(F_{w^2})^2+\mathcal H(F_{w^2})
 &\le C_r\|e^{a_\eta t}w^2u\|_2^2\le C_rM(F),\\
 |\mathfrak J(F,F_{w^2})|+|\mu|\,|\mathcal H(F,F_{w^2})|
 &\le C_r(1+|\mu|)M(F).
 \end{aligned}
 \tag{VHN8}
$$
W317 pays its ENTIRE mixed debit, including every prime power, both
folded channels, the cutoff and fixed Gamma shift. No diagonal
$\mathfrak J(F_w,F_w)$ or replacement metric is substituted.

Test VHN1 with the ACTUAL $F_{w^2}$. The exact account is
$$
 \mathcal P(F_w)+\lambda\Re M(F,F_{w^2})
 =D_\Gamma+\Re\mathfrak J(F,F_{w^2})
                +\mu\Re\mathcal H(F,F_{w^2}).
$$
VHN6--VHN8 imply
$$
 \mathcal P(F_w)+\frac7{2000}\lambda\pi^{-7/2}\|wv\|_2^2
 \le C_r(1+|\mu|)M(F).
 \tag{VHN9}
$$
Since $r<q$, the original moment already gives
$wu\to e^{rt}u$ in $L^2$. Closedness of the positive Gamma form
proves VHN2 for ALL $\lambda\ge0$. If $\lambda>0$, monotone
convergence also bounds $\|e^{(q+r)t}u\|_2^2$ by
$C_r(1+|\mu|)M(F)/\lambda$. The actual inverse on $H_{6+2r}$ has
norm at most $\zeta(3+2r)$ and agrees with W324's inverse on the
intersection, proving the additional original moment in VHN3.
It also makes $F^{(r)}=\mathscr S[(x/\pi)^rU]\in H_6$ well-defined;
VHN2 supplies its Gamma membership. This proves VHN3 without testing
with an unbounded-weight source before establishing its domain.

In particular, for $\lambda>0$ and $R_0\ge1$, the SAME original source
satisfies
$$
 M(F\mathbf1_{x\ge\pi R_0})
 \le C_r(1+|\mu|)\lambda^{-1}R_0^{-2r}M(F).
$$
This is a moment-tail statement only; a sharp cutoff is not asserted
to preserve the Gamma domain. No exponent-seven endpoint is proved.

## Direct physical compactification with the original cap

Apply VHN2--VHN3 to the SAME hypothetical unit negative cap-four
minimizer of VHP7, allowing $\lambda=0$. For every fixed
$0<\sigma<1/4$, there is a smooth nonincreasing cutoff $\chi_L(t)$,
one for $t\le L$ and zero for $t\ge L+1$, such that
$$
 \begin{gathered}
 F_L(x)=\chi_L(\log(x/\pi))F(x),\qquad
 \widehat F_L=F_L/\sqrt{\mathcal H(F_L)},\\
 \operatorname{supp}\widehat F_L\subset[\pi,\pi e^{L+1}],
 \quad M(\widehat F_L)\le M(F)\le4,\\
 0\le\mathfrak E(\widehat F_L)-\mathfrak E(F)
 \le C_\sigma(1+|\mu|)^2 M(F)e^{-2\sigma L}.
 \end{gathered}
 \tag{VHCp1}
$$
For sufficiently large $L$, the cutoff has nonzero norm. On VHP7's
bounded-multiplier cap-four branch, its coefficient and the lower
threshold for $L$ are independent of $\lambda$. This is a quantitative
SAME-source physical cutoff, unlike W330--W337's general-source
recovery through a preliminary smoothing and theta reconstruction.
The completed core need not be a finite Gaussian source. No new
qualitative density or general cutoff theorem is being asserted.

### Transfer a strictly weighted Gamma norm to the physical source

Choose $1/4<r_1<r_2<1/2$ with $\sigma=r_2-r_1$ and set
$f(t)=(\pi e^t)^{9/4}F(\pi e^t)$ for $t\ge0$, zero otherwise.
The ACTUAL theta relation and inverse give, on the positive half-line,
$$
 u(t)=\sum_{n\ge1}n^{-1/2}f(t+2\log n),\qquad
 f(t)=\sum_{n\ge1}\mu(n)n^{-1/2}u(t+2\log n).
$$
For $r>1/4$, put $f_r=e^{rt}f$, $u_r=e^{rt}u$. Their zero extensions
obey $u_r=P_+A_rf_r$, $f_r=P_+S_ru_r$, with
$$
 A_r=\sum_{n\ge1}n^{-1/2-2r}T_{2\log n},\qquad
 S_r=\sum_{n\ge1}\mu(n)n^{-1/2-2r}T_{2\log n}.
$$
Both coefficient sums converge absolutely. Translations are isometries
of the full logarithmic Gamma form. $P_+$ is bounded there by the
cross-half-line Carleman argument already used in W338 and VHD1.
Consequently the SAME actual profiles satisfy
$$
 \mathcal G(f_r)\le C_r\mathcal G(u_r),\qquad
 \mathcal G(u_r)\le C_r\mathcal G(f_r).
 \tag{VHCp2}
$$
Moreover $\|f_r\|_2^2=\pi^{7/2}\|F\|_{H_{7/2+2r}}^2$.
Since $7/2+2r=4+\eta$ with $\eta>0$, this pays $\mathcal N(F)^2$.
No endpoint $r=1/4$ or unweighted inverse is used.

Put $G_L=F-F_L$ and $a_L(t)=e^{-\sigma t}(1-\chi_L(t))$.
Then $\|a_L\|_\infty+\|a_L'\|_\infty\le C_\sigma e^{-\sigma L}$.
Bounded Lipschitz multiplication in the logarithmic form gives
$\mathcal G(a_Lh)\le C_\sigma e^{-2\sigma L}\mathcal G(h)$.
Indeed use its equivalent difference norm with kernel $e^{-s}/s$,
expand the product difference, and bound the multiplier difference by
$\min(2\|a_L\|_\infty,s\|a_L'\|_\infty)$.
Since $f_{G_L,r_1}=a_Lf_{r_2}$, VHCp2 and multiplication by
$e^{-r_1t_+}$ give the complete SAME-tail estimate
$$
 \mathcal P(G_L)+\mathcal N(G_L)^2+\mathcal H(G_L)
 \le C_{r_1,r_2}e^{-2\sigma L}\mathcal G(u_{r_2}).
 \tag{VHCp3}
$$
The original sixth moments of $G_L,F_L$ are finite by bounded physical
multiplication; VHCp3 establishes their Gamma membership as well.

For $\lambda>0$, VHN3 additionally pays
$$
 \lambda\left[M(G_L)+
 \int_\pi^\infty(1-\chi_L^2)(x/\pi)^6|F|^2dx\right]
 \le C_{r_2}(1+|\mu|)M(F)e^{-2r_2L}.
 \tag{VHCp4}
$$
At $\lambda=0$, both bracketed quantities are finite from the original
$M(F)$, and their contributions are exactly zero; no additional
moment is used. W317, VHN2 and VHCp3--VHCp4 therefore give
$$
 0\le Q_\lambda(G_L)
 \le C_{r_1,r_2}(1+|\mu|)^2M(F)e^{-2\sigma L}.
 \tag{VHCp5}
$$
The positive-multiplier moment cost $\lambda^{-1}$ is canceled by
$\lambda$ here; the complete debit is paid in its actual weaker norm.

### Normalize the same core without spending its cap

For the measure $|F(x)|^2dx$, the function $\chi_L^2$ decreases and
$(x/\pi)^6$ increases. The classical covariance inequality gives
$M(F_L)/\mathcal H(F_L)\le M(F)\le4$. Also VHCp2 and VHN2 imply
$$
 1-\mathcal H(F_L)\le C\mathcal G(u_{r_2})
                e^{-(7/2+2r_2)L}.
$$
Thus $\mathcal H(F_L)\ge1/2$ beyond a uniform threshold on the bounded
branch. Mixed nullity gives $Q_\lambda(F_L)=Q_\lambda(G_L)$ exactly,
and $\mathfrak E(F)=\mu-\lambda M(F)$. Hence
$$
 \mathfrak E(\widehat F_L)-\mathfrak E(F)
 =\frac{Q_\lambda(G_L)}{\mathcal H(F_L)}
 +\lambda\left[M(F)-\frac{M(F_L)}{\mathcal H(F_L)}\right].
 \tag{VHCp6}
$$
Both terms are nonnegative. Once $\mathcal H(F_L)\ge1/2$, the bracket
is at most twice the moment loss in VHCp4. At $\lambda=0$ the bracket
is finite and its contribution is zero. VHCp5--VHCp6 prove VHCp1.
In particular, if $\mathfrak E(F)=-\delta<0$, choosing
$L\ge(2\sigma)^{-1}\log(C_\sigma/\delta)$ and the fixed threshold
retains $\mathfrak E(\widehat F_L)\le-\delta/2$. Its support radius is
$O_p(\delta^{-p})$ as $\delta\downarrow0$ for any fixed $p>2$,
using $\sigma=1/(2p)$.
This gives no finite Gaussian atom-count or coefficient-size bound.

These weighted estimates and compactification do not control the
critical local log/jump charge. The fixed VHC source has compact
physical support and already has all finite physical moments; merely
proving moment finiteness cannot remove that example. Quantitative
null relations could impose additional cancellation, but none is
proved here. No dilation derivative, critical signed absorption,
improved VHR1 allowance or sign of the completed minimum is obtained.
The existing uniform $(\log T)^{-4}$ allowance is unchanged. Full RH
and strict Robin for every integer $n>5040$ remain unproved.
