# Critical zeros obstruct a blanket exact source factorization

The [zero-reserve sharp-high check](vanishing-exterior-reserve.md)
concerns a simple multiplier allowance. The existing
[unprojected dual-source choice](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
avoids that particular projection error. A further question is whether
every discarded low source can be put exactly in $Q(sL^2+\mathbb Cv_0)$.
The full prime action gives an obstruction to that stronger requirement.

This is a conditional paper application of the original theta/operator
suppliers, classical analytic uniqueness, and the
[published critical-zero and Dirichlet-series facts](../../../Library/Weil/nist2026criticalzeros.md).
It supplies no numerical experiment, new generic factorization theorem,
priority claim, Lean certificate or sign of the actual form.

## Keep the entire discarded low family

Use the original even $H=L^2(dx)$ realization, $s>0$ and
$v_0=\sqrt\rho=2s\cosh(x/2)$. For any fixed finite $N>0$, put
$P=\mathbf1_{|\mathsf D|<N}$ and $Q=I-P$. Let $\mathcal E\subset PH$
be any finite-dimensional complex subspace containing $Pv_0$.
Retain the actual full operator

$$
T_c=\widetilde A-cI+c|v_0\rangle\langle v_0|,
\qquad 0\le c<1/2,\qquad \alpha=1/2-c.
$$

The [complete operator-domain interface](sharp-center.md#operator-domain-and-complete-block)
puts $PH$ in the unchanged minimal operator domain. The argument below
requires no high coercivity estimate at this fixed band.

There is a nonzero $p\in PH\cap\mathcal E^\perp$ such that

$$
QT_cp\ne Q(sf+a v_0)
\quad\text{for every }f\in H,\ a\in\mathbb C. \tag{CR1}
$$

This statement concerns some discarded low input for every finite
retained space. It does not decide the factorization of the saved
corrected finite residual or of an arbitrary particular column.

## Select a surviving critical-zero evaluation

For the infinitely many distinct positive critical ordinates $\gamma$,
define $\phi_\gamma=P(s\cos(\gamma x))$. These vectors, together with
$Pv_0$, are linearly independent. A finite relation after $P$ would
give a zero Fourier transform on $(-N,N)$ for
$s[\sum b_\gamma\cos(\gamma x)+2a\cosh(x/2)]$. The original
superexponential theta envelope makes its Fourier-Laplace transform
entire. Analytic uniqueness and Fourier injectivity make the bracket
zero everywhere. Its bounded cosine part forces $a=0$, and distinct
cosines are linearly independent.

Choose $\gamma$ with $\phi_\gamma\notin\mathcal E$, and set
$p=(I-\Pi_{\mathcal E})\phi_\gamma$, $h=sp$. The finite-band input
$p$ and its derivatives are bounded by the Fourier Cauchy--Schwarz
estimate, so $h$ has all exponential moments. Its bilateral transform

$$
G(z)=\int_{\mathbb R}h(x)e^{-zx}dx
$$

is entire. Evenness and the exact ground centering give

$$
G(1/2)=\tfrac12\langle p,v_0\rangle=0,\qquad
G(i\gamma)=\langle p,\phi_\gamma\rangle=\|p\|_2^2>0.
\tag{CR2}
$$

These use the repository's first-slot-linear convention. No constraint
at every critical-zero evaluation has been imposed on $p$.

## Divide the complete arithmetic action only with its full tail

The original prime block is $Bp=s\mathcal P h$, where

$$
\mathcal P h(x)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 [h(x-\log n)+h(x+\log n)]. \tag{CR3}
$$

This retains both directions and every prime power. With $t_n=\log n$,
the source Dirichlet series gives, for $\Re z>1/2$,

$$
\int_0^\infty\mathcal P h(x)e^{-zx}dx
=-G(z)\frac{\zeta'(z+1/2)}{\zeta(z+1/2)}+E_h(z),
\tag{CR4}
$$

where the actual half-line corrections are

$$
E_h(z)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\left[-e^{-zt_n}\int_{-\infty}^{-t_n}h(y)e^{-zy}dy
 +e^{zt_n}\int_{t_n}^{\infty}h(y)e^{-zy}dy\right].
\tag{CR5}
$$

To justify this formula, integrate each translated summand, complete
its bilateral integral in the negative shift, and retain the reflected
positive shift. For real $\sigma>1/2$, the complete bilateral term is
absolutely summable because
$\sum\Lambda(n)n^{-\sigma-1/2}<\infty$ and
$\int|h(y)|e^{-\sigma y}dy<\infty$. The omitted negative-half-line
and reflected terms have tails $|y|\ge\log n$. The theta envelope
there gives summable bounds $C_Bn^{2B}e^{-b'n^2}$ on every compact
$z$ set, also for derivatives, with $b'>0$ fixed. Consequently $E_h$
is entire; no unestimated boundary correction is dropped.

At the chosen critical zero of multiplicity $m_\gamma\ge1$, the
meromorphic right side has the nonzero principal part

$$
-\frac{m_\gamma G(i\gamma)}{z-i\gamma}. \tag{CR6}
$$

Subtracting $2a\cosh(x/2)$ changes its half-line transform only by
$a[(z-1/2)^{-1}+(z+1/2)^{-1}]$, with no pole at $i\gamma$.
If $\mathcal P h-2a\cosh(x/2)$ were in $L^2(0,\infty)$, its
Laplace transform would instead satisfy

$$
\left|\int_0^\infty
 [\mathcal P h(x)-2a\cosh(x/2)]e^{-(\sigma+i\gamma)x}dx\right|
\le\frac{\|\mathcal P h-2a\cosh(x/2)\|_2}{\sqrt{2\sigma}}.
\tag{CR7}
$$

That transform is holomorphic on $\Re z>0$. The meromorphic identity
from (CR4) continues throughout that half-plane; any interior poles
would have to be removable under the assumed $L^2$ representation.
At its boundary, (CR6) grows as a nonzero constant times $1/\sigma$,
contradicting (CR7). This uses a known critical-line zero and does
not assume that all zeros lie on that line. Hence

$$
\mathcal P h-2a\cosh(x/2)\notin L^2(0,\infty)
\qquad(a\in\mathbb C). \tag{CR8}
$$

## An arbitrary low lift cannot restore exact factorization

For the centered input, the existing full action formula gives

$$
F:=(T_c-\alpha I)p
=s[m(\mathsf D)h+c_\Gamma h-\mathcal P h]. \tag{CR9}
$$

Bounded $s,s'$ and the finite band put $h$ in $H^1$; the existing
logarithmic symbol estimate puts $m(\mathsf D)h$ in $L^2$.
Formula (CR8) therefore excludes $F=sf+a v_0$ with $f\in H$.

Suppose equality were possible after $Q$. Since $Q\alpha p=0$,
the difference $\ell=F-sf-a v_0$ would belong to $PH$. Every term
also has all exponentially weighted $L^2$ norms. This is immediate
for $sf$, $v_0$ and the two $L^2$ terms multiplied by $s$.
For the complete prime term, boundedness of $p$ gives
$|h|\le C s$. Split its series at $n=e^{2|x|+2}$, use
$\Lambda(n)/\sqrt n\le1$ below it and the theta envelope above it.
The resulting bound $|\mathcal P h(x)|\le C'(1+e^{2|x|})$
suffices after multiplication by $s$; no PNT error bound is needed.

The analytic uniqueness argument of (VR3) now applies to $\ell$:
all exponential $L^2$ norms give all exponential $L^1$ moments,
while its compact Fourier support makes the entire transform zero
on an outside interval. Thus $\ell=0$, contradicting (CR8)--(CR9).
This proves the paper implication (CR1) under the stated source premises.

## Keep the regulated cofinal question

An exact $sL^2$ factorization for every complementary-low source is
therefore a stronger condition than the required cofinal form comparison.
Removing finitely many directions cannot make that condition universal.
The obstruction already uses critical-line zeros; assuming RH would
not remove it. It gives no negative direction of the original form,
divergence of its inverse cost, or verdict on a selected finite trial.

Retained finite prime actions can still admit divided-source estimates,
with their complete omitted action paid at positive $\delta$ through the
existing (SC22) and tail suppliers. Their constants depend on the actual
head, bandwidth, derivatives and shared coefficient map. These estimates
and the low/complementary-low signs must be obtained on one common
subcritical sequence. No such scale-uniform signed supplier, original
all-input half-bound, RH or full Robin conclusion is supplied here.

The [regulated complete-prime source budget](regulated-prime-source-budget.md)
uses the existing complete count at a positive exterior reserve.
At each stage, its schedule uses that stage's prescribed source family
and one common parameter/band choice. Band-dependent source norms and
the actual low/complementary-low signs remain separate obligations.
