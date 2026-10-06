# Explicit whole-line high trials and derivative supplier

The [common matrix screen](common-matrix-screen.md) selects trial
coefficients, while the [forward-action supplier](forward-action.md)
only bounds low-band inputs. This note supplies separate weighted
derivative bounds for explicit high trials. The inverse-residual and
Schur comparisons remain the existing methods cited in
[the sharp-center interface](sharp-center.md); no new general method or
originality is claimed.

## Fix the trials before certifying their actions

Let $E:\mathbb C^{95}\to PL^2_{\rm even}$ have the exact orthonormal
columns

$$
p_j(x)=\frac1{\sqrt\pi}\int_0^{64}\cos(\eta x)
       \sqrt{\frac{2j+1}{64}}\,P_j(\eta/32-1)\,d\eta,
\qquad 0\le j\le94,
$$

where $P_j$ is the ordinary Legendre polynomial. Define
$H_{J,L}=T_{J,L}-\alpha I$ using the whole-line operator in
[forward-action.md](forward-action.md), including its exact multiplication
and mean terms. The [saved trial data](common-trials.json) fixes a real
dyadic matrix $B$ of size $95\times4$ and a real dyadic matrix $A$ of
size $4\times95$. Set

$$
Z=QH_{1024,64}EB,\qquad g=Qv_0. \tag{HT1}
$$

These definitions specify actual high vectors on the original real line.
They contain no periodic boundary condition, spatial cutoff or numerical
projection. The screen that chose $B,A$ used a full digamma multiplier
and periodic FFT; its vectors differ from (HT1). Its positive comparison
sign is not transported to these trials. The dyadic coefficients are
trial choices, not enclosures of an unknown operator eigenbasis.

## Exact ground lift

Write $p_0=Pv_0\ne0$, $\Pi_0=|p_0\rangle\langle p_0|/\|p_0\|^2$,
and let $F_{94}$ project onto $\operatorname{ran}E+\mathbb Cp_0$. The
fixed correction map on the full center is

$$
Y=-\frac{|g\rangle\langle p_0|}{\|p_0\|^2}
       +ZA E^*(I-\Pi_0). \tag{HT2}
$$

It satisfies $Yp_0=-g$ and $Y=YF_{94}$. The second equality follows
because both $p_0$ and every column of $E$ belong to $\operatorname{ran}F_{94}$.
The exact known $Tv_0=0$ gives $Cg=-Kp_0$, so the residual
$(K-CY)p_0$ vanishes exactly. Neither floating-point deflation nor a
small numerical ground residual supplies these equalities.

## Derivatives of the specified retained forward map

Reuse the full-line supremum upper bounds $S_0,S_1,S_2$ from the
low-band supplier. For $r=0,1,2$ put

$$
A_r=\sum_{j=0}^r\binom rj S_jN^{r-j},\qquad
D_r=\sum_{j=0}^r\binom rj S_jA_{r-j},\qquad N=64.
$$

Leibniz and Plancherel imply $\|(sp)^{(r)}\|_2\le A_r\|p\|_2$
for every $p\in PL^2$. The finite Gamma multiplier has norm at most

$$
M_J=2\sum_{k=0}^{J-1}a_k^{-1},\qquad a_k=2k+1/2.
$$

It commutes with derivatives. Thus
$\|(s\,m_J(\mathsf D)(sp))^{(r)}\|_2\le M_JD_r\|p\|_2$.
The multiplication contribution costs at most $8D_r\|p\|_2$.
For $W_L=\sum_{2\le n\le L}\Lambda(n)/\sqrt n$, each translated
product obeys the same $D_r$ bound; both directions cost
$2W_LD_r\|p\|_2$. This retained prime sum includes every prime power
through $L$, with its own $\log p$ weight.

The exact mean satisfies $|\langle v_0,p\rangle|\le\|p\|_2$.
To pay its derivatives, use the existing (WC2) envelopes
$|s^{(j)}(x)|\le K_je^{-b e^{2|x|}}$, $b=3/8$. Since
$v_0=2\cosh(x/2)s$, set

$$
V_0=1,\qquad
V_r=2\left(\frac\pi{2b}\right)^{1/4}
       \sum_{j=0}^r\binom rj 2^{-(r-j)}K_j,
\quad r=1,2.
$$

Then $\|v_0^{(r)}\|_2\le V_r$. Indeed derivatives of
$2\cosh(x/2)$ have absolute value at most $2^{1-r}e^{|x|/2}$;
substitution $u=e^{2|x|}$ bounds the squared envelope integral by
$\Gamma(1/2)/(2b)^{1/2}$. These are conservative global bounds, not
numerical derivative measurements of $v_0$.

Consequently, at $J=1024,L=64$,

$$
R_r=(M_{1024}+8+2W_{64})D_r+cV_r,
\qquad\|(H_{1024,64}p)^{(r)}\|_2\le R_r\|p\|_2. \tag{HT3}
$$

In particular these images belong to $H^2$. Sharp $Q$ commutes with
derivatives and contracts each derivative norm. Thus every column of
$Z$, and $g$, belongs to $H^2_{\rm even}$ and hence to the actual high
operator domain. This does not identify the maximal domain or imply
that an arbitrary residual belongs to it.

## Complete action tails on one common high family

Use the exact dyadics to enclose
$F_B=(\sum_{j,a}|B_{ja}|^2)^{1/2}\ge\|B\|$. Define

$$
\begin{aligned}
U_Z&=F_B(S_2R_0+2S_1R_1+S_0R_2),\\
U_g&=S_2+2S_1V_1+S_0V_2,\\
U&=(U_g^2+U_Z^2)^{1/2},\qquad
R=(1+F_B^2R_0^2)^{1/2}.
\end{aligned}
$$

For $\mathcal Z=(g,Z):\mathbb C^5\to QL^2$, Cauchy–Schwarz on the
same coefficients gives
$\|(s\mathcal Za)''\|_2\le U\|a\|$ and
$\|\mathcal Za\|_2\le R\|a\|$. The complete omitted-action bound is

$$
\|(T-T_{J',64})\mathcal Z\|
\le S_0\sigma_{J'}U+E_{p,64}R,\qquad
\sigma_{J'}=\frac1{2(2J'-3/2)^2}. \tag{HT4}
$$

The [directed coefficient program](high_trial_bounds.py) chooses a
sufficient power-of-two $J'$ for a target below $1/1000$. It evaluates
this tail coefficient without summing $J'$ retained actions. The result
therefore certifies a conservative paper-model tail allowance, not the
cost, accuracy or feasibility of evaluating its retained convolutions.
The construction of $Z$ remains fixed at $J=1024$ as $J'$ changes.

For the saved four-trial dyadics, the directed supplier gives
$F_B<1704.280684139688$, $R<49046.28874647354$ and
$U<313165777.4653100$. Its chosen sufficient count is $J'=262144$,
with complete action-tail bound below $0.000448454143055800<1/1000$.
This count is not asserted minimal or practical.

The [coherent-root Fourier supplier](strip-root.md) bounds the full
Gamma action omitted beyond a finite frequency band on this same
five-generator family. It retains $Z=QH_{1024,64}EB$ even when a later
action uses the full digamma symbol. Its directed band-$512$ allowance
is below $5.80\cdot10^{-18}$; it does not evaluate retained integrals
or certify a residual Gram.

This bound is uniform on the five explicit high generators. Applying it
to $Y$ requires their actual common coefficient map and the ground
normalization, rather than substituting a unit trial bound separately
for every low input. Exact $Cg=-Kp_0$ can also be used directly for the
ground contribution. Retained whole-line integrals, Gram and residual
enclosures, a Loewner lower matrix sign, and the $e_{94}$ remainder all
remain to be combined. No full positivity, Lean, Robin or RH certificate
is supplied.

## Reproduce

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/high_trial_bounds.py
```

The program reads the saved coefficient data and dyadic trials. It loads
only the original derivative program's coefficient setup, stopping at
its grid boundary, and records that program's hash. No original
integration grid is repeated. Outputs include exact upper dyadics,
trial and source hashes, the selected sufficient $J'$ and the unpaid
matrix obligations. The program is project-authored; directed arithmetic
and dependency licensing come from python-flint/FLINT.


The [stable projected-ground application](stable-ground.md) gives a
nonzero $e=E^*Pv_0$ directly from the existing one-sided operator tail
and exact ground relation. On $u\perp e$, the lift (HT2) becomes
$YEu=ZAu$. Its classical second Schur allowance is less than
$0.004660867160108$; the actual direction and restricted matrix remain
uncomputed.

The [continuous sinc projection supplier](continuous-projection.md)
applies to the localized forward map $H_{1024,64}EB$ before sharp-$Q$,
which can create spatial tails. It pays the infinite physical-lattice
quadrature and omitted input samples for the true cutoff64. Actual
forward sample errors, off-lattice high prime evaluations, common Grams
and the restricted matrix sign are separate obligations.

The [local high sample producer](local-high.md) now retains the actual
core $H,PH$ enclosures for these four columns. The
[localized whole-line Gram replay](local-z-gram.md) uses them to bound
$\|Z\|<1.0090$ and $\|(g,Z)\|<1.00904$. These actual real norms can
replace the conservative real $R$ allowance above; they do not replace
$U$ or the strip norms required for unbounded actions.

The [full-Gamma periodization supplier](full-gamma-periodic.md) gives
a local analytic replacement allowance on this same high family,
without changing the finite-$J$ definition of $Z$. This allowance alone
does not evaluate actions or other Gram blocks and does not settle the
exact-ground restricted sign.

The [off-grid/full-action interface](off-grid-action.md) and
[four-column high action](high-full-action.md) supply the actual
full-Gamma $Z$ actions and whole-line $Z^*CZ,(CZ)^*(CZ)$ blocks with
complete prime-tail transport. They retain the original trial
definition and give $\|CZ\|<1.051588$. The95 low actions, mixed blocks,
common residual Gram and restricted sign remain separate obligations.
