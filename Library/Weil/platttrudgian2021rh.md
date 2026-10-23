---
bibkey: platttrudgian2021rh
authors: Dave Platt and Tim Trudgian
year: 2021
title: The Riemann hypothesis is true up to 3·10^12
doi: 10.1112/blms.12460
url: https://arxiv.org/abs/2004.09765v1
claim: Published verification supplies the finite-height RH premise. Exact heat-loss factorization and the complete arithmetic block bound give a whole-source negative allowance of order (log T)^(-4) in the original sixth moment; fixed height still leaves a negative allowance. A support-independent Gamma-only lower bound for the prime Hankel form fails on all compact half-line tests. An even actual-source partition controls the joint metric defect and bounds supporting multipliers of negative cap-four minima from below, up to the finite-height signed zero tail. Its null supporting vector bootstraps every fixed logarithmic order below five and recovers individual branch moments with an explicit inverse-multiplier cost; separation of the finite reconstruction intervals replaces its N-fold Fourier-tail payment by a harmonic factor, giving every fixed joint-metric exponent below five on actual negative minima and a fifth-power rate with a log-log factor on nonpositive-energy sources under RH(T), without improving the general exponent-four negative allowance. For hypothetical unit negative cap-four minimizers with a positive supporting multiplier, retaining the errors' own moments also gives every finite logarithmic order and arbitrary fixed logarithmic-power branch rates, with constants that deteriorate as the multiplier tends to zero.
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
