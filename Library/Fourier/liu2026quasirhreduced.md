---
bibkey: liu2026quasirhreduced
authors: Baiying Liu
year: 2026
title: Reduced-frequency applications to the actual C68 columns
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Repo-derived source-conditional applications to actual bare-J4 C68 columns give the original-W0 endpoint for all nonunit reduced frequencies and strict bounds on physical reduced frequencies with a small valuation-one good-prime product, retaining all sixth-power repetitions and one original coupled envelope. The powerful sector retains its U^(27/13+epsilon) raw bound; the parameterized extension has raw exponent E((1+eta)/2) for each fixed 0<=eta<(13-5sqrt6)/3. The sharper dominant-annulus dependence and the small sector up to U^(1/5) for both original and exact redesigned cutoffs remain valid. An explicit mixed planar/log Fourier producer supplies the common envelope for fixed original local profiles; any preceding signed component/height aggregate still requires its own bound. Full C68, other branches, J40, signed Robin restoration and RH remain unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Reduced-frequency applications to the actual C68 columns

This `repo-derived` companion uses the notation and source conventions
of the [Liu source card](../Analytic/liu2026quasirh.md), the
[complete-dual application](liu2026quasirhdual.md), and the
[joint mixed-Mobius and residue companion](liu2026quasirhresidue.md).
C1–C50 remain in the source card, C51–C76 in the complete-dual owner,
and R1–R46 in the residue companion. C77–C119 belong only to this note.
The deductions are conditional paper mathematics, without a source-proof
audit or Lean certification.
The [actual mixed-sixth companion](liu2026quasirhmixedsixth.md) gives the
complete-coefficient reductions and the quantified conditional
neighborhood-moment interface to C93–C97.

## A small reduced-frequency sector of the actual C68 columns

This is a conditional application of existing suppliers to the bare
(J4)/(C57) columns in (C68). Retain the corefree/common-$e=1$ branch,
$C=1$, source coprime-projector $\mathfrak b=1$, $q=L=U$ and
$D_{\rm src}=1$. Thus $g=f_i=1$, $N_i=X=U$ and
$K_{\rm row}\asymp RU$. Fix precisely [R43's genuine ideal-ray quotient](liu2026quasirhresidue.md#the-finite-ray-residual-of-the-documented-bare-j4-diagonal)
$H$, its original total class, $\zeta_i=1$, and no additional angular
multiplier. The original $\xi$, signs, squarefree/collision masks,
profiles and norm heights remain. This does not allow the arbitrary
coefficient vectors admitted by a generic large sieve.

The analytic premises are the pinned
[primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
`thm:main` and `lem:logarithmic-control`, in their full uniform
finite-order form. In particular, for every fixed $\delta,\eta>0$,
primitive nonprincipal $\rho$ of conductor norm $Q$ satisfies

$$
 |L(s,\rho)|+|L(s,\rho)^{-1}|
 \ll_{\delta,\eta}\{2Q(3+|\Im s|)^2\}^{\eta},
 \qquad \Re s\ge7/8+\delta.
 \tag{C77}
$$

Both directions of this bound, including its conductor uniformity, are
assumed; fixed-conductor polynomial bounds alone are not substituted.
Principal functions have the source's different regularization and
pole convention. They will not occur in the two slots below. These
are source premises, not an audit of the primary's proofs.

**The actual coefficients and their primitive characters.** Treat the
original $W_0$ and the exact redesigned $W_U$ separately. Write
$b^{(0)}=b_A$ and $b^{(U)}=b_U$, respectively, on the original inverse
annulus, with $A=U^{1/12}$. Their identities are C33–C38 and R34–R37:

$$
 b^{(\circ)}(d)=\mu(d)+K_{A;\circ}(d),\qquad
 K_{A;\circ}(d)=\sum_{e\mid d}\mu(e)2^{\omega(e)}
                         W_\circ(q_e/A),\qquad \circ\in\{0,U\}.
 \tag{C78}
$$

For $W_U$ the law, clamp and coefficient are fixed at this same $U$;
no law is reselected at a cofactor scale, and no comparison of the two
signed realizations is asserted. R35/R41's fixed real and logarithmic
moments pay the dilation integrals. There is no maximum-support power
of the clamp length.

Every nonzero element frequency has the unique factorization

$$
 k=\epsilon e_S(\mathbf j)r a^6,\quad
 \epsilon\in\mathcal O^\times,\quad 0\le j_p\le5\ (p\in S),\quad
 r\text{ good sixth-power-free},\quad a\text{ an integral ideal}.
 \tag{C79}
$$

Use the same fixed generators as C58. The ideal $a$ includes all its
$S$ factors and may overlap $r$; there is no $(a,r)=1$ restriction.
The sector here is $1<q_r\le U^t$, with fixed $t>0$. Sixth powers give
exactly $\chi_n(a^6)=\mathbf1_{(n,a)=1}$, including collisions; their
conductor triviality does not remove this mask. Units and $S$ labels
remain separate from the ideal-ray quotient.

Let $B_{i,\circ}(k;\Pi_i)$ be the literal unnormalized inner column
in (C68) on this frozen branch, with the actual compressed coefficient
from (C57) and its original external profile. Opening that coefficient
expresses it, for each original component, as

$$
 \sum_{\substack{d_1d_2\ {\rm sf}\\
             (d_1d_2,S\Pi_i r a)=1}}
 b^{(\circ)}(d_1)b^{(\circ)}(d_2)
 \vartheta_{i,r,\epsilon,\mathbf j}(d_1d_2)
 \mathbf1_{[d_1d_2]=\sigma_i}
 F_i(q_{d_1}/D,q_{d_2}/D).
 \tag{C80}
$$

Here $F_i$ is the given annular two-factor profile, including the
original external product profile and separated norm heights.
$\vartheta$ is the original orientation of $\chi_\bullet(r)$ times
its fixed finite-ray twists, including $\xi$, the C56 change-of-form
factor and the unit/$S$ label. This is the raw-column orientation of
(C68); C56 already accounts for the original Gauss multiplier. No
additional inverse Gauss factor is inserted. $\Pi_i$ denotes any of
the original polynomial-size deletion masks. The argument is uniform
in these masks, even when they depend on frozen row data; it does not
choose them anew or differentiate their coefficients.

Expand only the actual total-class selector:
$\mathbf1_{[n]=\sigma_i}=h^{-1}\sum_{\chi\in\widehat H}
\overline{\chi(\sigma_i)}\chi(n)$. Its absolute coefficient mass is
$1$. Each resulting presentation $\rho=\vartheta\chi$ has a primitive
inducer $\rho^*$ with $Q_\rho\ll_{H,S}q_r$. Indeed, at any good prime
with $v_p(r)=j\in\{1,\ldots,5\}$ the local sextic character has order
$6/\gcd(6,j)>1$; every fixed ray twist is unramified there. Since
$r\ne1$, none of these inducers is principal. This uses the primary's
physical-row ramification and defining-modulus convention, not equality
of conductor norms or a new lower bound on $Q_\rho$. It applies equally
to the conjugate orientation. The complete original defining-modulus
zeros, including redundant deletions, remain attached.

**Two slots of the literal joint product.** Reuse R3–R8 and R44 with
two slots. For each of the four actual $\mu/K$ choices, let
$M\subseteq\{1,2\}$, $T=\{1,2\}\setminus M$ and
$P=\operatorname{rad}(\Pi_i r a)|_{p\notin S}$.
Put $x_j=\rho^*(p)q_p^{-s_j}$ and $y_j=q_p^{-z_j}$. The joint series is

$$
 \begin{aligned}
 F_{M,P,\rho}(\mathbf s,\mathbf z)
 &=\prod_{p\nmid SP}\left(1-\sum_{j\in M}x_j
                          +\sum_{j\in T}x_j(1-2y_j)\right)\\
 &=H_{M,P,\rho}(\mathbf s,\mathbf z)
   \prod_{j\in M}L(s_j,\rho^*)^{-1}
   \prod_{j\in T}L(s_j,\rho^*)L(s_j+z_j,\rho^*)^{-2}.
 \end{aligned}
 \tag{C81}
$$

At an unexcluded prime, $H_p$ is the parenthesis times
$\prod_{j\in M}(1-x_j)^{-1}
 \prod_{j\in T}(1-x_j)(1-x_jy_j)^{-2}$.
At $p\mid SP$ replace only the parenthesis by $1$, retaining primitive
local values, including zeros at ramified primes. Thus the full
squarefree product and every deletion are encoded once. No local
numerator is inverted. R4–R5 give normal convergence after cancellation
of all linear terms whenever $\Re s_j>1/2$ and
$\Re(s_j+z_j)>1/2$, and $H\ll_\eta q_P^\eta$ on closed substrips,
uniformly in the character phases and heights.

Start the two $s$ lines at $2$ and all present $z$ lines at a fixed
small $\delta>0$. Move both $s$ lines to $7/8+\delta$, leaving those
$z$ lines at $\delta$. All numerator $L$ functions are nonprincipal
and entire, so there are no $s=1$ residues; no cutoff pole is crossed.
All reciprocal arguments remain in C77's strip, and the whole joint
correction stays in R5's domain. C77 bounds the numerator as well as
the reciprocal factors with arbitrarily small conductor/height powers.
The scale cost, before allocating losses, is
$D^{7/4+2\delta}A^{|T|\delta}$, at most
$U^{7/8+7\delta/6}$. This avoids paying the polynomial
$Q^{3/5}$ numerator bound below the uniform right strip.

Use the same finite Mellin/seminorm argument as R6–R8, with at most
four variables. For $1\le R\le U$, $q_k\ll RU$, $q_r\le U^t$ and
$q_{\Pi_i}\le U^{C_\Pi}$, both $Q_\rho$ and $q_P$ are polynomial in
$U$ (in particular $q_a\ll U^{1/3}$). Choose the internal
$\delta,\eta$ small enough for this fixed polynomial range and the
final $\varepsilon$. For $W_U$, Mellin inversion first uses
$W_0(t/x)$ under the actual fixed-$U$ product law. Each present
$K$ slot costs $x^\delta$, and R35's fixed real/log moments pay the
same integrations and horizontal joins. Consequently both actual
coefficient realizations satisfy

$$
 |B_{i,\circ}(k;\Pi_i)|
 \ll_{H,S,t,C_\Pi,\varepsilon}
       \mathcal H_{i,J}\,U^{7/8+\varepsilon},
 \qquad 1\le R\le U,\quad 1<q_r\le U^t.
 \tag{C82}
$$

Here $\mathcal H_{i,J}$ is its original side seminorm, with R41's
single moment enlargement for $W_U$. The finite Fourier sum is paid
by Minkowski with its actual coefficient mass. Choose one finite $J$
for all four choices, masks, units/$S$ labels and shells. Original
norm-height costs remain polynomial and are integrated against the
original sufficiently rapid fixed log-Fourier decay. For the actual
coupled component/height measure $dc$, require
$\int|dc|\,\mathcal H_{1,J}\mathcal H_{2,J}
 \le\mathcal N_{{\rm base},J}$, fixed or polylogarithmic in $U$,
with the original Fourier shell seminorms included. This is the common
base-envelope contract of R43–R46. An envelope supplied only for its
$\eta=h^{-2}$ component costs the fixed factor $h^2$ to recover this
base envelope. No allowance restarts per $r,a$, mask or component;
no derivative acts on $b^{(\circ)}$. For the fixed original-$W_0$ local
inputs specified in C114–C119 below, that construction supplies this
envelope; it does not supply an unspecified preceding signed aggregate.

**Counting every repetition and restoring the original scale.** Ordinary
ideal counting, with all six units and the original finite $S$ labels,
gives for the ball $0<q_k\ll RU$

$$
 \begin{aligned}
 \#\{k:1<q_r\le U^t\}
 &\ll 6\sum_{\mathbf j}q_{e_S(\mathbf j)}^{-1/6}
          (RU)^{1/6}
          \sum_{\substack{r\text{ as in C79}\\
                           1<q_r\le U^t}}q_r^{-1/6}\\
 &\ll_{K,S}R^{1/6}U^{1/6+5t/6}.
 \end{aligned}
 \tag{C83}
$$

This counts each full frequency once, including every admissible
sixth-power repetition, overlaps with $r$, and the $S$ factors of $a$.
It does not count each primitive inducer once and discard its repetitions.
Squaring C82 with an internally smaller loss therefore yields the
following restriction of the literal left side of C68:

$$
 \begin{aligned}
 M_{i,\circ}^{\le t}(R)
 &:=\sum_{\substack{0<q_k\ll RU\\k\text{ as in C79},\ 1<q_r\le U^t}}
                    |B_{i,\circ}(k;\Pi_i)|^2\\
 &\ll\mathcal H_{i,J}^{\,2}
            R^{1/6}U^{23/12+5t/6+\varepsilon}
 \le\mathcal H_{i,J}^{\,2}R U^{2+\lambda_t+\varepsilon},
 \qquad \lambda_t=-1/12+5t/6.
 \end{aligned}
 \tag{C84}
$$

Every character in this sum satisfies C68's $\psi_k^*\ne1$ test.
This is a sector estimate, not $W(\lambda_t)$ for its full row.
At $t=1/5$ it has exponent $25/12$ and restricted $\lambda=1/12$.

Apply Cauchy to the two original columns on this same frequency set,
then integrate their costs against the same $dc$. There are only the
original fixed labels in this $C=\mathfrak b=g=1$ branch, and C68's
source relation bounds its frozen scalar. The source multiplier is
exactly $q/L^3=U^{-2}$. Restoring the original unnormalized Gauss
pairing contributes exactly $U^2$ as in C57–C59; these cancel once.
Thus its shell/ball contribution costs
$\mathcal N_{{\rm base},J}R^{1/6}U^{23/12+5t/6+\varepsilon}$,
before the original $D^{-2}$ restoration. No second $U^2$ is present.
C56 fixes the self-dual planar measure; ideals are counted once, with
no extra area factor or division by six.

The complete original Fourier-weighted shell sum is also paid. On a
shell $q_k/U\asymp R\ge1$, the same separated profile envelope has
arbitrary fixed decay $R^{-B}$, including all needed derivatives.
For $R\le U$, sum C84 against this decay. For $R>U$ use the original
divisor bound $|b^{(\circ)}(d)|\ll\tau_3(d)$ instead of a nonuniform
puncture estimate: an unnormalized two-factor column has absolute
size $O(U^{1+\varepsilon})$. C83 and the same decay bound its full
energy tail by

$$
 \mathcal N_{{\rm base},J}U^{13/6+5t/6+\varepsilon}
         \sum_{R>U\ {\rm dyadic}}R^{1/6-B}
 \ll\mathcal N_{{\rm base},J}U^{7/3+5t/6-B+\varepsilon}.
 \tag{C85}
$$

A single fixed $B\ge4$ makes this negligible in the stated range;
the ball $q_k/U\le1$ uses $R=1$. Choose the derivative order once to
pay $B$, the Mellin integrals and all original height costs. There is
no unweighted infinite mean-square claim and no discarded large-$a$
mask.

Writing $\mathcal E_\circ^{\le t}$ for precisely this local signed
Poisson contribution with its original Fourier profiles, the result is

$$
 \begin{aligned}
 |\mathcal E_\circ^{\le t}|&\ll\mathcal N_{{\rm base},J}
                               U^{23/12+5t/6+\varepsilon},\\
 0<t&<\frac{51-20\sqrt6}{10},\\
 (1+B_*)-\left(\frac{23}{12}+\frac{5t}{6}\right)
       &=\frac{51-20\sqrt6-10t}{12}>0,\\
 t=1/5:\qquad
 |\mathcal E_\circ^{\le1/5}|&\ll\mathcal N_{{\rm base},J}
                                      U^{25/12+\varepsilon},\\
 D^{-2}|\mathcal E_\circ^{\le1/5}|&\ll\mathcal N_{{\rm base},J}
                                      U^{13/12+\varepsilon},\qquad
 (1+B_*)-25/12=\frac{49-20\sqrt6}{12}>0.
 \end{aligned}
 \tag{C86}
$$

For the last strict inequality, $49^2-6\cdot20^2=1$. Take the final
loss and absorption of the stipulated polylogarithms smaller than this
reserve. The cutoff $q_r\le U^{1/5}$ is unbounded as $U$ grows; it is
not a finite-conductor application. The conclusion holds separately
for $b_A$ with $W_0$ and for the exact $b_U$ with $W_U$.

**Scope beyond the small sector.** C84 alone supplies no full C68
$W(1/12)$. For original $W_0$, C93–C97 below give a bare endpoint
on every nonunit reduced-frequency annulus, including $q_r>U^{1/5}$;
the exact redesigned $W_U$ application here remains restricted to
this small sector. The $r=1$ frequencies are C58's
exceptional sector: R46 already pays their specified redesigned
bare-J4 realization, whereas the original-$W_0$ principal scalar
retains its stated obstruction. This application neither duplicates
that exceptional bound nor supplies a signed cutoff-change estimate.
The $k=0$ term, other source $\mathfrak b/C$, common-$e$, cores/gcds,
bad duals, generalized additional finite/angular factors and their
full measure, physical-row restoration, and same-common-beta signed
detector/$\rho$ recombination remain unpaid in their original places.
A selected Poisson contribution has no positivity or monotonicity
under physical-row selection. Full C68, J40, signed Robin restoration
and RH remain open. This is a `repo-derived` paper application of
C56–C68, C33–C38, R3–R9/R34–R46 and the explicit source premises;
no new generic theorem, Lean certification, source-proof audit or
literature-priority claim is made.

## A source-conditional dominant endpoint for original W0

Retain exactly C80 with the original $W_0$: write $B_i=B_{i,0}$ and
$b_A=\mu+K_{A;0}$, with $D=U^{1/2}$ and $A=U^{1/12}$. Keep the bare
corefree/common-$e=1$, $C=\mathfrak b=D_{\rm src}=1$, $q=L=U$ branch,
R43's original genuine fixed ideal-ray quotient and total-class
selector, $\zeta_i=1$, and no additional angular multiplier. Fix
$0<c<C_1$. In C79 retain **every** frequency with
$cU\le q_r\le C_1U$, including $a=1$, all six units, the original
$S$ labels, every sixth-power repetition $a$, its $S$ factors and its
overlaps with $r$. All actual $\mu/K$ terms, signs, twists,
squarefree/collision zeros and original deletion masks remain.

For sufficiently large $U$, conditional on the local source premises
specified below, for every final $\varepsilon>0$ one finite original
side-seminorm order $J$ gives

$$
\begin{aligned}
 M_i^{\rm dom}(R)
 &:=\sum_{\substack{0<q_k\ll RU\\
          k\text{ as in C79},\ cU\le q_r\le C_1U}}
             |B_i(k;\Pi_i)|^2\\
 &\ll_{c,C_1,H,S,C_\Pi,\varepsilon}
       \mathcal H_{i,J}(R)^2 R^{1/6}U^{\kappa+\varepsilon},
       \qquad 1\le R\le U,\\
 \kappa&=\frac{37-10\sqrt6}{6}=1+B_*.
\end{aligned}
\tag{C87}
$$

Here $\mathcal H_{i,J}(R)$ is C82's seminorm of the original side
profile on that Fourier shell (the ball uses $R=1$). Its required
weighted shell seminorm and the original component/height measure
are part of the **one** base-envelope premise below. This is an
application to the prescribed coefficient, rather than the prime
coefficient of [Xu–Sang v2, Theorem 1.2](https://arxiv.org/html/2610.17675v2#S1.Thmtheorem2),
which already has the same numerical exponent. C93–C97 below cover
the other original-W0 nonunit annuli at the bare endpoint; C87 retains
the sharper $R^{1/6}$ dependence on this dominant annulus. Neither
application supplies strict/full C68.

**Source correspondence and common bins.** Reuse C80–C81 and R4–R5/R44
for the literal two-slot series, including the complete defining-modulus
zeros. The additional local input is the pinned primary's
[`lem:logarithmic-control`, lines 1531–1551](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L1531).
For $\alpha\in[1/2,1]$ and small $e>0$, absence of zeros in the open
disk centered at $2+it$ of radius $2-\alpha-2e$ supplies
$|L|+|1/L|\ll\{2Q_\rho(3+|t|)^2\}^{\eta}$ on the closed concentric
disk of radius $2-\alpha-6e$, for every prescribed $\eta>0$.
This explicitly supplies each numerator **and** reciprocal below
$7/8$ on its local disk. Neither $L'/L$ control nor C77's global
right-strip bound substitutes for it. This lemma and `thm:main` remain
unaudited source premises; no validity of their major proofs is certified.

Use [Xu–Sang v2, §6.1, (6.1), Lemma 6.2 and Proposition 6.3](https://arxiv.org/html/2610.17675v2#S6)
on the original good sixth-power-free **physical rows** $r$, including
inducing orders properly dividing six. Cover $[cU,C_1U]$ by finitely
many source dyads $Q\asymp U$; $Q$ in that source is this row scale,
not the primitive conductor $Q_\rho$. Put all the original fixed ray,
unit/$S$, $\xi$ and C56 orientation twists of both sides and their
conjugates into the single fixed finite group $\Theta$, supported
on $S$, before assigning bins. Then every C80 presentation is in the
source family
$\mathcal X_r=\{\nu(n)\chi_n(r)^{\pm1}:\nu\in\Theta\}$.
The original total-class selector has absolute Fourier mass $1$,
as in C80. C80's good-prime ramification proves every primitive
inducer nonprincipal and $Q_\rho\ll_{H,S}q_r\ll U$; no conductor
lower bound or principal regularizer is needed.

On each source dyad choose $H_1=Q^\tau\asymp U^\tau$ in the order
required by Lemma 6.2: fix the final losses, $e$, and finite internal
moment/parameter-Sobolev orders, then a sufficiently small positive
$\tau\le1/100$, and only then the external Mellin-tail orders.
There are $O_e(1)$ common bins $(\ell,\alpha)$ with
$\alpha\le M_\ell(r)<\alpha+e$ and
$M_{\ell+1}(r)<\alpha+2e$. The count exponent is exactly
$\mathcal R(\alpha)$ of [§459, (459.7)](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计);
the floor $\alpha_0=51/100$ has $O(U)$ rows. The primary's
[`lem:buffered-bins`, lines 4281–4353](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L4281)
places all needed zero-free disks inside the common height rectangle
$|t|\le(3\ell+2)H_1$, giving both local $L$ directions for
$\Re s\ge\alpha+6e$. The extra $\Pi_i$ and $a$ deletions enter
C81's correction, not $\Theta$ or the zeros defining these bins.
In particular the count is never applied to a newly row-masked
witness polynomial or to the actual bilinear coefficient as a witness.

**The finite joint contour of the actual coefficient.** For each
$M\subseteq\{1,2\}$ and $T=\{1,2\}\setminus M$, the exact C81
inversion, with $P=\operatorname{rad}(\Pi_i r a)|_{p\notin S}$,
has integrand

$$
\widetilde F_i(s_1,s_2)D^{s_1+s_2}
 \prod_{j\in T}[\widehat W_0(z_j)A^{z_j}]
 H_{M,P,\rho}(\mathbf s,\mathbf z)
 \prod_{j\in M}L(s_j,\rho^*)^{-1}
 \prod_{j\in T}L(s_j,\rho^*)L(s_j+z_j,\rho^*)^{-2},
\qquad \frac{d\mathbf s\,d\mathbf z}{(2\pi i)^{2+|T|}}.
\tag{C88}
$$

Thus the four choices have respectively two reciprocal factors,
one reciprocal and one numerator with its squared reciprocal, or
two numerators with their two squared reciprocals. At most six
$L$ or reciprocal factors occur, counted with multiplicity.
This is C81's exclusive-prime identity, with $\mu$ in $M$ and
$K_{A;0}$ in $T$, not independently coprime slot sums. In particular
neither a sign nor a cross-slot collision zero has been replaced.

Start on $\Re s_1=\Re s_2=2$ and $\Re z_j=e>0$. Before moving any
line truncate **each** imaginary coordinate at
$T_0=H_1/16$, common to the four choices, both original sides and
all repetitions on this source dyad. Move the two finite $s$
segments successively to $\alpha+8e$, keeping every $z$ line at $e$.
Throughout the rectangles, $|\Im s_j|\le T_0$ and
$|\Im(s_j+z_j)|\le2T_0$. Every numerator argument has real part
at least $\alpha+8e$, and every $K$ reciprocal argument at least
$\alpha+9e$. These arguments and all horizontal faces lie in the
same buffer. Centering the local disk at each argument's height
places its part with real part at most $2$ in the controlled smaller
disk; the part farther right uses absolute Euler convergence.
Each factor in C88 is therefore $U^\eta$ for arbitrarily small
internal loss. The numerator is entire because its inducer is
nonprincipal. No $s=1$ pole, reciprocal zero, or $z=0$ cutoff pole
is crossed. R5 applies throughout since both $\Re s_j$ and
$\Re(s_j+z_j)$ exceed $1/2$; no local numerator of $H$ is inverted.

The original separated norm twists are kept in $F_i$ before this
inversion. Their actual polynomial derivative costs belong to
$\mathcal H_{i,J}(R)$, as in C82; this introduces neither a new
character nor an unbudgeted infinity type. For $q_k\ll RU$ on the
current annulus, $q_a\ll R^{1/6}$. With the original
$q_{\Pi_i}\le U^{C_\Pi}$ and $1\le R\le U$, even if $a$ overlaps
$r$ or contains $S$ factors,
$q_P\ll U^{C_\Pi+1}R^{1/6}\ll U^{C_\Pi+7/6}$.
R4–R5 and the primary's
[`lem:deleted-euler-factors`, lines 1602–1620](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L1602)
absorb $q_P^{\eta_P}$ by an internally small $\eta_P$, uniformly
in every original frozen polynomial-size mask. On the moved lines,
$D^{2\alpha+16e}A^{|T|e}\le U^{\alpha+49e/6}$.
Allocating $e$, the at most six $L$ losses and the deletion loss
inside the final $\varepsilon$ gives, on the same bin,

$$
 |B_i(k;\Pi_i)|
 \ll\mathcal H_{i,J}(R)U^{\alpha+\varepsilon},
 \qquad cU\le q_r\le C_1U,\quad q_k\ll RU,\quad 1\le R\le U.
\tag{C89}
$$

Summing the four actual terms and the original selector uses only
fixed constants and its actual mass $1$.

For completeness the joins use the primary's
[`lem:smooth-calculus`, lines 1123–1177](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L1123),
not an infinite local-contour assertion. On the original absolute
lines the entire joint series is absolutely bounded, uniformly in
its masks. The joint annular $\widetilde F_i$ and each
$\widehat W_0(e+it)$ have arbitrarily rapid Mellin decay. Hence the
omitted tails are
$O(\mathcal H_{i,J}(R)U^{C_0}T_0^{-N})$, with a fixed $C_0$
independent of $N$. On an $s_j$ horizontal face, $|\Im s_j|=T_0$;
pointwise logarithmic integration by parts in that coordinate of
$F_i$ gives the same bound after integrating the other coordinates.
All $L$ arguments on that face stay inside the buffer and R5 still
bounds $H$. Intersections of faces have the same estimates. The
$z$ tails remain on absolute lines and no $z$ contour is shifted.
After $\tau$ is fixed choose one finite external order with
$N\tau>C_0+10$, enlarging $J$ once to make every tail and join
$O(\mathcal H_{i,J}(R)U^{-10})$. This does not change the previously
fixed internal height order. The moved vertical segments are never
extended beyond the buffer, and no derivative acts on $b_A$.

**Bin energy and all original repetitions.** For each fixed original
unit/$S$ label and each $a$, apply Proposition 6.3 to the same
physical $r$ family. The restriction $q_k\ll RU$ can only decrease
this positive bin energy. Uniformity of C89 in its original masks
therefore gives

$$
 \sum_{\substack{r\in\mathcal B_{\ell,\alpha}\\
          cU\le q_r\le C_1U,\ q_k\ll RU}}|B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2
          U^{\mathcal R(\alpha)+2\alpha+\varepsilon}.
\tag{C90}
$$

Reuse the evaluated maximum (459.12), with
$\delta=2\alpha-1$:
$\max(\mathcal R(\alpha)+2\alpha)=1+B_*=\kappa$,
at $\alpha_*=(21-5\sqrt6)/12$. The second branch gives $2$ and
the floor gives $1+2\alpha_0=101/50<\kappa$.
This is the existing count and maximization, also used for the
different prime coefficient in Xu–Sang v2, Theorem 1.2; neither is a
new supplier here. There are only $O_e(1)$ bins and finitely many
source dyads. Ordinary ideal counting gives $O(R^{1/6})$ choices
of $a$ for this annulus, rather than $O(U^{1/6})$ at $R=1$.
Summing these choices with all six units and the finite $S$ labels
proves C87. No $(a,r)=1$ restriction, squarefree restriction on $a$,
or omission of its $S$ factors is made.

For $R>U$ use the original absolute divisor bound
$|B_i|\ll\mathcal H_{i,J}(R)U^{1+\varepsilon}$, rather than
extrapolating the polynomial-puncture range. The number of frequencies
on this same dominant $r$ annulus is $O(U R^{1/6})$.
The original pair-profile shell decay $R^{-B}$, with one fixed
$B\ge4$, consequently pays its entire large-$a$ tail:

$$
 \mathcal N_{{\rm base},J}U^{3+\varepsilon}
       \sum_{R>U\ {\rm dyadic}}R^{1/6-B}
 \ll\mathcal N_{{\rm base},J}U^{19/6-B+\varepsilon}.
\tag{C91}
$$

For $1\le R\le U$, sum C87 with the same decay; the ball uses $R=1$.
Thus every repetition of this $r$ annulus is restored in the original
Fourier-weighted sum, without an unweighted infinite-energy claim.

**One original measure and one normalization.** Choose $J$ once for
all four terms, bins, masks, classes, units/$S$ labels, repetitions,
components and shells. Use exactly C82 and R43–R46's original
coupled component/height measure $dc$. Including the single chosen
weighted shell seminorm in that same envelope means
$\int|dc|\,\mathcal H_{1,J}(R)\mathcal H_{2,J}(R)
\ll\mathcal N_{{\rm base},J}(1+R)^{-B}$, with
$\mathcal N_{{\rm base},J}$ fixed or polylogarithmic in $U$.
All original polynomial norm-height derivative costs are included
there. If only the $\eta=h^{-2}$ component envelope is supplied,
recovering the base envelope costs the same fixed $h^2$ as R43–R46.
No allowance restarts per mask, $r$, $a$, bin, class, component,
cofactor or height. This is a retained applicability premise, not
certification of an unspecified larger growing-height allowance or
of the full J40 component table.

Apply Cauchy to the two original columns on the **same** $k$ set,
then integrate against that same $dc$. In the bare branch,
$N_i=U$, $K_{\rm row}\asymp RU$ and $D_{\rm src}=1$; C87 has the
restricted C68 scaling $\lambda=\kappa-2=B_*-1$, using
$R^{1/6}\le R$. Restore C68's $q/L^3=U^{-2}$ and C57–C59's raw
Gauss-pairing factor $U^2$ exactly once; they cancel. C91 and the
small shells then give for precisely this signed local contribution
$\mathcal E_0^{\rm dom}$

$$
 |\mathcal E_0^{\rm dom}|
 \ll\mathcal N_{{\rm base},J}U^{\kappa+\varepsilon},
 \qquad
 D^{-2}|\mathcal E_0^{\rm dom}|
 \ll\mathcal N_{{\rm base},J}U^{B_*+\varepsilon}.
\tag{C92}
$$

The last factor is the original $D^{-1}$ on each side,
$D^{-2}=U^{-1}$. C56 fixes the self-dual planar measure; there is
no extra area, inverse Gauss, division by six or second $U^2$.

**Scope and remaining bound.** The added deduction is this finite
buffered-contour application to literal original-W0 C80, with its
same-annulus repetitions and common costs. It is not a source theorem
for these coefficients or a new general $L$-function estimate. Under
its stated premises it improves the generic raw $U^{13/6+\varepsilon}$
certificate to $U^{\kappa+\varepsilon}$ on this annulus. Accordingly,
with the same fixed/polylog envelope an actual-coefficient lower bound
$U^{13/6-o(1)}$ here would contradict C87, since
$13/6-\kappa=(5\sqrt6-12)/3>0$. Generic metaplectic operator
sharpness by itself does not identify these prescribed columns with
an operator witness. No realizable coherent lower-bound example is
asserted; coherent raw energy of size $U^{\kappa-o(1)}$ remains
compatible with C87.

The coefficient correspondence is checked by the four C81 identities
for literal C80 and the displayed finite rectangles, with $\Pi_i,r,a$
left symbolic. It fails if an actual numerator or reciprocal leaves
the common buffer, a primitive presentation escapes fixed $\Theta$,
a horizontal face needs an unavailable original seminorm, or the
actual $dc$ fails the stated common-envelope premise. No generic
operator witness or norm-only lower bound repairs any of these gaps.

There is **zero strict reserve**: local C68 sufficiency asks for
$\lambda<B_*-1$, whereas C87 gives equality. A coefficient-sensitive
positive-power improvement at the critical $\alpha_*$ bins, or
cancellation in the original common-beta signed aggregate, is still
missing. The all-annulus original-W0 endpoint C93–C97 below closes
the nonunit annular coverage gap at this same endpoint power. The
original-W0 exceptional principal scalar, $k=0$, other cores/common-$e$
and common-column branches,
other source $C/\mathfrak b$, generalized finite/angular factors and
their actual measure, bad duals, physical-row restoration and the
original signed common-beta Mobius detector/$\rho$ aggregation remain
unresolved. R46's redesigned exceptional payment is not transferred
to W0. Full C68, J40, Robin and RH remain open. All conclusions here
are source-conditional paper deductions, without source-proof audit,
Lean certification or originality certification.

## A source-conditional all-annulus endpoint for original W0

Retain the literal $B_i=B_{i,0}$ of C80 and exactly C87's bare branch,
original $W_0$, $b_A=\mu+K_{A;0}$, $D=U^{1/2}$ and $A=U^{1/12}$.
All four $\mu/K$ terms, product squarefreeness, original signs and
phases, class selectors and defining-modulus/collision zeros remain.
For sufficiently large $U$, under C77–C92's source premises and the
same original coupled-envelope premise, every final $\varepsilon>0$
admits one finite original seminorm order $J$ such that

$$
\begin{aligned}
 M_i^{>1}(R)
 &:=\sum_{\substack{0<q_k\ll RU\\
                 k\text{ as in C79},\ q_r>1}}
                 |B_i(k;\Pi_i)|^2\\
 &\ll_{H,S,C_\Pi,\varepsilon}
       \mathcal H_{i,J}(R)^2 R U^{\kappa+\varepsilon},
       \qquad 1\le R\le U,\qquad
       \kappa=1+B_*=\frac{37-10\sqrt6}{6}.
\end{aligned}
\tag{C93}
$$

There is no restriction $q_r\asymp U$, $a=1$, $(a,r)=1$, or
squarefreeness of $a$. Each frequency includes its six-unit label,
original $S$ label and complete ideal sixth power, with $S$ factors
and overlaps retained. C87 remains the sharper $R^{1/6}$ estimate
when $q_r\asymp U$. C93 is an application of the existing density
count and maximization to these actual columns, not a new density
theorem or a use of Xu–Sang's prime-coefficient estimate.

**Independent row and column scales.** Set $\theta=1/5$. C84 with
$t=\theta$ already pays $1<q_r\le U^\theta$, for original $W_0$,
by $\mathcal H_{i,J}(R)^2R^{1/6}U^{25/12+\varepsilon}$.
This is within C93 since $25/12<\kappa$. For the remaining rows use
disjoint physical dyads $q_r\asymp Q$, with
$U^\theta\ll Q\ll RU\ll U^2$. The source row parameter is $Q$;
the column scales stay $D=U^{1/2}$ and $A=U^{1/12}$. Neither is
reset to a power of $Q$, nor is $Q$ identified with $Q_\rho$.

Use precisely C87–C90's common fixed $\Theta$ and
$\mathcal X_r=\{\nu(n)\chi_n(r)^{\pm1}:\nu\in\Theta\}$ for both
original sides, all fixed ray/orientation twists and their conjugates.
The rows are the original good sixth-power-free nonunits, including
inducing orders properly dividing six. Good-prime ramification still
makes every primitive inducer nonprincipal. Xu–Sang §6.1 (6.1) gives
$Q_\rho\ll_{H,S}Q$ and the original row-deletion radical of norm
$O_{H,S}(Q)$; its zero extension is retained. The extra $\Pi_i,a$
deletions enter C81's $H$, not a growing $\Theta$, a new detector
polynomial or a different family of zeros.

Apply the same Lemma 6.2 and Proposition 6.3 on each $Q$ dyad, with
$\alpha_0=51/100$, fixed $0<e<10^{-3}$ sufficiently small and
$I=\lceil1/e\rceil+2$. The common bins have $1\le\ell<I$,
$\alpha\in(\alpha_0+e\mathbb Z_{\ge0})\cap[\alpha_0,1]$,
$\alpha\le M_\ell(r)<\alpha+e$ and
$M_{\ell+1}(r)<\alpha+2e$, where $M_j$ is the common primitive-zero
maximum through height $3jH_1$, floored at $\alpha_0$.
Use $H_1=Q^\tau$, $0<\tau\le1/100$. Fix the final losses, small
$e$ and finite internal moment/detector/parameter-Sobolev orders
first; then choose $\tau$ for those height costs and detector
hypotheses, and only then choose the external Mellin-tail orders.
All these choices are uniform over $U^\theta\ll Q\ll U^2$.
Floor bins have $O(Q)$ rows and above-floor bins have
$O(Q^{\mathcal R(\alpha)+\eta})$ rows, with exactly (459.7)'s
$\mathcal R$ and arbitrarily small prescribed $\eta>0$.
This reuses the source's permitted witness lengths, finite smooth
parameter dependence and polynomial height costs; no moment estimate
for the actual bilinear coefficient is substituted for that count.

**Uniform finite contours when $Q\ne U$.** Use C88's exact joint
integrand separately for all four actual choices. Truncate every
imaginary coordinate at $T_0=Q^\tau/16$ before shifting either $s$
segment from $2$ to $\alpha+8e$, with each $z$ line fixed at $e$.
The numerator and reciprocal arguments, including every $s_j+z_j$,
stay in C89's common buffered disks: their heights are at most
$2T_0$ and their real parts are at least $\alpha+8e$ or
$\alpha+9e$. The local logarithmic-control premise supplies both
$L$ directions; C77 alone is not used below its right strip.
Nonprincipality and positive $z$ lines exclude principal or cutoff
residues, and R5 controls the joint correction throughout. All
horizontal faces and intersections use that same finite buffer.

On these dyads $q_a\ll(RU/Q)^{1/6}$, and the actual puncture satisfies

$$
 q_P\ll U^{C_\Pi}Q(RU/Q)^{1/6}\ll U^{C_\Pi+2}.
$$

Thus deletion costs and the at most six numerator/reciprocal losses
fit inside a prescribed $U^\varepsilon$, uniformly in $Q,r,a$ and
the original masks. C89's scale cost is still
$D^{2\alpha+16e}A^{|T|e}\le U^{\alpha+49e/6}$.
The original absolute-line tails and all horizontal joins have
C89's bound $O(\mathcal H_{i,J}(R)U^{C_0}T_0^{-N})$, with one fixed
$C_0$ independent of the external order $N$. Since $Q\gg U^{1/5}$,
choose one finite $N$ with $N\tau/5>C_0+10$ and enlarge $J$ once.
Every tail and join is then $O(\mathcal H_{i,J}(R)U^{-10})$,
uniformly even at the smallest retained $Q$. This does not increase
the already fixed internal source height order. No moved vertical
segment is extended to infinity, and no derivative acts on $b_A$.

Also retain C81–C82's global right-strip contour in this fixed
polynomial range $q_r\ll U^2$, $q_a\ll U^{1/3}$. C77 supplies its
uniform $U^{7/8+\varepsilon}$ bound, with the same masks and one
common enlarged $J$. Taking the better of these two bounds gives

$$
 |B_i(k;\Pi_i)|
 \ll\mathcal H_{i,J}(R)
             U^{\min\{\alpha,7/8\}+\varepsilon},
 \qquad r\in\mathcal B_{\ell,\alpha}(Q),\quad q_k\ll RU.
\tag{C94}
$$

**Density with every repetition.** Put $d_{\alpha_0}=1$ for floor
bins and $d_\alpha=\mathcal R(\alpha)$ otherwise. For each fixed
unit/$S$ label and ideal $a$, the source count applies to the same
physical $r$ family; imposing the original frequency and collision
restrictions only decreases its positive energy. Sum over every
$a$ with $q_a\ll(RU/Q)^{1/6}$ by ordinary ideal counting.
C94 and the existing bin count therefore give

$$
 \sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
                    r\in\mathcal B_{\ell,\alpha}(Q)}}
              |B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2
       (RU)^{1/6}Q^{d_\alpha-1/6}
       U^{2\min\{\alpha,7/8\}+\varepsilon}.
\tag{C95}
$$

The six units and finite $S$ labels cost only their original fixed
sum, including $q_{e_S}^{-1/6}$. No primitive-inducer multiplicity
is discarded. The bound is uniform in the $a$-dependent deletion
mask, while the bins themselves are independent of that mask.

For $d_\alpha\ge1/6$, use $Q\ll RU$ and $d_\alpha\le1$ to bound
C95 by
$\mathcal H_{i,J}(R)^2R^{d_\alpha}
 U^{d_\alpha+2\min\{\alpha,7/8\}+\varepsilon}$.
Reuse C90 and (459.12): above the floor,
$\mathcal R(\alpha)+2\alpha\le\kappa$, with equality at
$\alpha_*=(21-5\sqrt6)/12<7/8$; the floor gives
$1+2\alpha_0=101/50<\kappa$. Hence this part is at most
$\mathcal H_{i,J}(R)^2R U^{\kappa+\varepsilon}$.
For $d_\alpha<1/6$, the negative $Q$ exponent in C95 and C77's cap
give instead
$\mathcal H_{i,J}(R)^2R^{1/6}U^{1/6+7/4+\varepsilon}
 =\mathcal H_{i,J}(R)^2R^{1/6}U^{23/12+\varepsilon}$.
In particular the high branch $\alpha>11/12$ does not create an
unpaid repetition cost. Sum the $O_e(1)$ bins and $O(\log U)$
physical dyads, absorbing their losses internally. Together with
the small-$Q$ C84 estimate this proves C93 without redoing the
density or its optimization.

**Original weighted tail and coupled restoration.** For $R>U$,
apply no bin estimate or polynomial-puncture extrapolation. The
original divisor bound gives
$|B_i|\ll\mathcal H_{i,J}(R)U^{1+\varepsilon}$, uniformly in
every deletion. There are $O(RU)$ full element frequencies in the
ball, so all nonunit reduced parts and all their repetitions have
energy $O(\mathcal H_{i,J}(R)^2RU^{3+\varepsilon})$.
Use exactly C91–C92's original coupled measure $dc$ and shell
seminorms, with one fixed $B\ge4$ and one finite $J$ large enough
for all the preceding bounds:

$$
\begin{aligned}
 \int|dc|\,\mathcal H_{1,J}(R)\mathcal H_{2,J}(R)
 &\ll\mathcal N_{{\rm base},J}(1+R)^{-B},\\
 \mathcal N_{{\rm base},J}U^{3+\varepsilon}
       \sum_{R>U\ {\rm dyadic}}R^{1-B}
 &\ll\mathcal N_{{\rm base},J}U^{4-B+\varepsilon}.
\end{aligned}
\tag{C96}
$$

The same fixed or polylogarithmic $\mathcal N_{{\rm base},J}$ pays
all original components and norm heights, masks, classes, units/$S$
labels, bins, dyads and repetitions. An eta-only envelope still
costs R43–R46's fixed $h^2$ to recover this base envelope. No
allowance is restarted at $Q$, $r$, $a$, or a component. Its actual
finite-order availability remains an applicability premise.

For $1\le R\le U$, Cauchy uses the two actual columns on the same
full nonunit $k$ set, followed by integration against this same
$dc$. C93 costs $R U^{\kappa+\varepsilon}$ before the shell decay;
the ball uses $R=1$. Sum with C96's decay and include its $R>U$
tail. In this bare branch $N_i=U$, $K_{\rm row}\asymp RU$ and
$D_{\rm src}=1$, so C93 has C68's endpoint scaling
$\lambda=\kappa-2=B_*-1$. Restore $q/L^3=U^{-2}$ and C57–C59's
raw Gauss-pairing $U^2$ exactly once; they cancel. For precisely the
original signed local nonunit contribution $\mathcal E_0^{>1}$,

$$
 |\mathcal E_0^{>1}|
 \ll\mathcal N_{{\rm base},J}U^{\kappa+\varepsilon},
 \qquad
 D^{-2}|\mathcal E_0^{>1}|
 \ll\mathcal N_{{\rm base},J}U^{B_*+\varepsilon}.
\tag{C97}
$$

Here $D^{-2}=U^{-1}$ restores the original $D^{-1}$ on each side.
C56's self-dual planar measure, the six units and ideals counted
once introduce no extra area, inverse Gauss, unit division or second
$U^2$. There is no unweighted infinite-energy assertion.

**Exact scope.** C93–C97 close the original-W0 bare nonunit annular
coverage gap, with **zero strict reserve**: local sufficiency still
requires $\lambda<B_*-1$, while this application gives equality.
The critical $\alpha_*$ bin is below C77's cap, so that cap supplies
no strict saving there. A coefficient-sensitive improvement or
cancellation in the same original signed aggregate remains needed.
The exact redesigned $W_U$ remains covered here only by C77–C86's
small nonunit sector and R46's specified exceptional realization;
no all-annulus $W_U$ bound or signed cutoff-change estimate is added.

The original-W0 $r=1$ principal scalar, $k=0$, other cores/common-$e$
and common-column branches, other source $C/\mathfrak b$, generalized
finite/angular factors and their actual measure, bad duals, full
physical-row restoration and the original common-beta signed Mobius
detector/$\rho$ aggregation remain unresolved. No positivity under
physical-row selection is assumed. All deductions retain the
unaudited source main, local logarithmic-control and density inputs,
and the actual one-envelope condition. There is no source-proof,
Lean or originality certification, unconditional or strict-C68
claim, or completion of full C68, J40, signed Robin restoration or RH.

## A source-conditional strict sector for powerful physical frequencies

Keep the literal original-$W_0$ columns $B_i=B_{i,0}$ of C80, on
C87's bare corefree/common-$e=1$, $C=\mathfrak b=D_{\rm src}=1$,
$q=L=U$ branch, with $D=U^{1/2}$ and $A=U^{1/12}$. Define
$\mathscr P$ to be the nonunit good sixth-power-free reduced parts
$r$ of C79 for which every nonzero good-prime valuation belongs to
$\{2,3,4,5\}$. Thus $(r)$ is powerful, and $q_r>1$. This restricts
the actual physical reduced frequency, with no restriction
$q_r\asymp U$ and no identification with a primitive conductor.
For each original component retain its original frequency-independent
$\Pi_i$, with $q_{\Pi_i}\le U^{C_\Pi}$, fixed before the frequency
sum. The additional radical $P=\operatorname{rad}(\Pi_i r a)|_{p\notin S}$
in C81 still varies with the actual $r,a$.

All four terms of $b_A(d_1)b_A(d_2)=(\mu+K_{A;0})(d_1)
(\mu+K_{A;0})(d_2)$, product squarefreeness, signs, fixed twists,
total-class selection and defining-modulus/collision zeros are
unchanged. Retain every C79 presentation
$k=\epsilon e_S(\mathbf j)r a^6$ with $r\in\mathscr P$: all six
units, all original $S$ labels, every ideal $a$, its $S$ factors and
its overlaps with $r$. In particular $\chi_n(a^6)$ remains the
collision mask $\mathbf1_{(n,a)=1}$.

Conditional on C77–C96's source main, local logarithmic-control and
physical-row density premises, and on the same original finite
coupled profile/height/shell envelope at the order used below, for
every final $\varepsilon>0$ one finite $J$ gives, for sufficiently
large $U$,

$$
\begin{aligned}
 M_i^{\mathscr P}(R)
 &:=\sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
                    r\in\mathscr P}}|B_i(k;\Pi_i)|^2\\
 &\ll_{H,S,C_\Pi,\varepsilon}
       \mathcal H_{i,J}(R)^2 R^{1/2}U^{27/13+\varepsilon},
       \qquad 1\le R\le U.
\end{aligned}
\tag{C98}
$$

Here $R$ is the original Fourier ball/shell scale and $U$ is the
column scale. The source's physical-row dyad $Q\asymp q_r$ is a
third parameter; neither $D$ nor $A$ is reset to a power of $Q$.
The seminorm and measure are exactly those of C94–C96, with one
common finite enlargement described below.

**Intersect the existing physical-row counts.** The fixed
[primary, powerful-ideal count, lines 5272–5282](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L5272)
already supplies
$\#\{r\in\mathscr P:q_r\le Y\}\ll_{K,S}Y^{1/2}$ for $Y\ge1$.
Reuse that classical count; no new counting or multiplicative-sieve
theorem is asserted. C94–C95 use the common physical-row bins from
[Xu–Sang v2, §6.1, Lemma 6.2 and Proposition 6.3](https://arxiv.org/html/2610.17675v2#S6)
with the owned exponent
[(459.7)](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计).
Set $d_{\alpha_0}=1$ at the floor $\alpha_0=51/100$, and above
the floor set

$$
 d_\alpha=\mathcal R(\alpha)=
 \begin{cases}
 (31-32\alpha)/(21-12\alpha),&\alpha\le11/12,\\
 2(1-\alpha),&\alpha\ge11/12.
 \end{cases}
$$

For every one of those same bins and every prescribed small
$\eta>0$, the two upper counts give

$$
 \#\bigl(\mathcal B_{\ell,\alpha}(Q)\cap\mathscr P\bigr)
 \ll Q^{m_\alpha+\eta},\qquad
 m_\alpha=\min\{d_\alpha,1/2\},\qquad
 m_{\alpha_0}=1/2.
\tag{C99}
$$

The restriction is imposed after forming the original bins. The
fixed common $\Theta$ still contains both sides' original ray,
unit/$S$, $\xi$, orientation twists and conjugates; the presentations
remain $\nu(n)\chi_n(r)^{\pm1}$. Good-prime ramification in C80
makes every primitive inducer nonprincipal even for valuations
$2,3,4,5$, including inducing orders properly dividing six.
The primitive conductor satisfies only the existing
$Q_\rho\ll_{H,S}Q$. Neither $a$ nor $\Pi_i$ changes the family
of zeros used to define a bin. In particular C99 does not assert
a new density theorem for a masked witness or for the actual
bilinear coefficient.

**The small physical dyads.** Set $\theta=1/5$ as in C93–C95.
Partial summation of the supplied powerful count gives
$\sum_{r\in\mathscr P,\ q_r\le Y}q_r^{-1/6}\ll Y^{1/3}$.
Counting all ideal sixth powers exactly as in C83, with the
original finite sum of $6q_{e_S(\mathbf j)}^{-1/6}$, consequently
bounds the number of frequencies with $q_r\le U^\theta$ by
$(RU)^{1/6}U^{\theta/3}$. C82, with the same original masks,
therefore gives

$$
 \sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
              r\in\mathscr P,\ q_r\le U^{1/5}}}
       |B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2 R^{1/6}
             U^{119/60+\varepsilon},\qquad
 \frac{119}{60}<\frac{27}{13}.
\tag{C100}
$$

This directly pays every small-$Q$ row at the stronger target
power. C84's $25/12$ bound for its larger row family remains valid;
it is not the small-$Q$ input for C98.

**Every remaining dyad, bin and repetition.** On disjoint physical
dyads $U^{1/5}\ll Q\ll RU\ll U^2$, use C88's exact joint series
and C94's pointwise estimate. Its finite contours have
$T_0=Q^\tau/16$, both $s$ lines moved to $\alpha+8e$, and all
present $z$ lines kept at $e>0$. Every actual numerator and
reciprocal, including $L(s_j+z_j,\rho^*)^{-2}$, remains in the
same source buffer. C81's joint correction retains the product
squarefree condition and all deletions, with
$q_P\ll U^{C_\Pi+2}$. The global right-strip contour supplies
the simultaneous cap at $7/8$. Thus C94 applies without a change
to either $\mu/K$ slot or to the original profiles.

Keep the same choice order: final losses, $e$ and internal source
orders, then sufficiently small $\tau>0$, then a finite external
Mellin-tail order with $N\tau/5>C_0+10$. C94's tails and joins
are uniformly $O(\mathcal H_{i,J}(R)U^{-10})$ on these dyads;
no moved segment is extended beyond its finite buffer and no
derivative acts on $b_A$.

For each $r$ there are $O((RU/Q)^{1/6})$ ideal choices of $a$.
C99 and C94, or equivalently C95 with its count intersected
before summing, now give

$$
 \sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
          r\in\mathcal B_{\ell,\alpha}(Q)\cap\mathscr P}}
       |B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2 (RU)^{1/6}
       Q^{m_\alpha-1/6}
       U^{2\min\{\alpha,7/8\}+\varepsilon}.
\tag{C101}
$$

The positive count includes every admissible $a$, without
$(a,r)=1$ or squarefreeness of $a$. Original collision restrictions
can only reduce that count. Uniformity in the actual $a$-dependent
radical pays its full energy; no primitive-inducer multiplicity
or sixth-power repetition is discarded.

If $m_\alpha\ge1/6$, use $Q\ll RU$ in C101 to obtain
$\mathcal H_{i,J}(R)^2R^{m_\alpha}
 U^{m_\alpha+2\min\{\alpha,7/8\}+\varepsilon}$.
Here $R^{m_\alpha}\le R^{1/2}$. If $m_\alpha<1/6$, use $Q\ge1$
and the cap instead, giving
$\mathcal H_{i,J}(R)^2R^{1/6}U^{23/12+\varepsilon}$.
This handles in particular every high-branch bin above $11/12$.

For the remaining bins, the continuous upper bound over the source
range has the exact maximum

$$
 \max_{\substack{\alpha\in[\alpha_0,1]\\
                  m_\alpha\ge1/6}}
 \bigl(m_\alpha+2\min\{\alpha,7/8\}\bigr)
 =\frac{27}{13},\qquad
 \alpha_c=\frac{41}{52},\quad
 \mathcal R(\alpha_c)=\frac12.
\tag{C102}
$$

Indeed, up to $\alpha_c$ the intersected exponent is
$1/2+2\alpha$, increasing to $27/13$; the floor contributes
$1/2+2\alpha_0=38/25$. From $\alpha_c$ to $7/8$ the derivative
of $\mathcal R(\alpha)+2\alpha$ is
$2-300/(21-12\alpha)^2\le-19/75<0$. From $7/8$ to $11/12$,
$\mathcal R(\alpha)+7/4$ decreases from $57/28<27/13$.
At $11/12$ the count exponent is $1/6$, and above it the
$23/12$ bound already applies. Thus neither the floor nor the
second density branch is omitted. The $O_e(1)$ bins and
$O(\log U)$ dyads, together with C100, prove C98 after allocating
all internal losses inside the final $\varepsilon$.

**One original envelope and the complete weighted tail.** Choose
one finite $J$ for all four terms, bins, dyads, masks, repetitions,
units/$S$ labels, components, norm heights and shells. Require
exactly C96's original coupled measure and shell contract
$\int|dc|\,\mathcal H_{1,J}(R)\mathcal H_{2,J}(R)
 \ll\mathcal N_{{\rm base},J}(1+R)^{-B}$, with one fixed
$B\ge4$ and fixed or polylogarithmic $\mathcal N_{{\rm base},J}$.
Its availability at this finite order is a premise. All polynomial
norm-height derivative costs belong to it. An eta-only envelope
costs the same fixed $h^2$ to recover the base envelope. No
allowance restarts at a dyad, bin, mask, $r$, $a$ or component.

For $R>U$, restrict C96's positive energy tail to this same
powerful sector. The original absolute divisor bound and
$O(RU)$ full-frequency count give the unchanged sufficient bound
$\mathcal N_{{\rm base},J}U^{3+\varepsilon}
 \sum_{R>U\ {\rm dyadic}}R^{1-B}
 \ll\mathcal N_{{\rm base},J}U^{4-B+\varepsilon}$.
This includes all large-$a$ masks and repetitions, without applying
a bin or polynomial-puncture estimate beyond $R=U$.

For $1\le R\le U$ apply Cauchy on the same powerful $k$ set
to the two actual columns, then integrate against that same $dc$.
Sum C98 against the stipulated decay; the ball uses $R=1$.
Restore the original $q/L^3=U^{-2}$ and the raw Gauss-pairing
$U^2$ exactly once, as in C97. For precisely this original signed
local sector contribution $\mathcal E_0^{\mathscr P}$ this yields

$$
 |\mathcal E_0^{\mathscr P}|
 \ll\mathcal N_{{\rm base},J}U^{27/13+\varepsilon},\qquad
 D^{-2}|\mathcal E_0^{\mathscr P}|
 \ll\mathcal N_{{\rm base},J}U^{14/13+\varepsilon}.
\tag{C103}
$$

Here $D^{-2}=U^{-1}$ restores the original factor on each side.
C56's self-dual measure introduces no extra area, inverse Gauss,
unit division or second $U^2$. Since $R^{1/2}\le R$, C98 has
restricted C68 scaling

$$
 \lambda_{\mathscr P}=\frac1{13}<B_*-1,\qquad
 \kappa-\frac{27}{13}
 =\frac{319-130\sqrt6}{78}>0,
 \qquad 319^2-6\cdot130^2=361.
\tag{C104}
$$

Take the final loss and absorption of the stipulated polylogarithms
smaller than this reserve. The unrestricted nonunit endpoint
C93–C97, the sharper dominant-annulus $R^{1/6}$ dependence of C87,
and C77–C86 for both original and exact redesigned cutoffs retain
their stated strengths and scopes.

**Exact scope and remaining critical family.** C98–C104 are a
`repo-derived` strict application to C79's powerful physical
reduced frequencies in the actual original-$W_0$ bare columns.
Their suppliers are the cited classical count, existing density
and C94's actual-coefficient contour; none is asserted as a new
count, large sieve, conductor-compression or multiplicity theorem.
C9–C10 in the source card concern column squareparts, and
PR1–PR10 in the [reflection companion](../Analytic/openai2026quasirh.md)
concern reflection choices; those distinct applications are not
being counted as this physical-row result.

Within the bare nonunit complement of $\mathscr P$, at least one
good prime necessarily has $v_p(r)=1$. This is a necessary
condition for a remaining critical row in that complement, not
a sufficient condition to be critical. No strict estimate for
all such rows follows here. The original-$W_0$ $r=1$ principal
scalar, $k=0$, other cores/common-$e$ and common-column branches,
other source $C/\mathfrak b$, generalized angular/finite families
and their actual measure, bad duals, full physical-row restoration
and the original common-beta signed Mobius detector/$\rho$
aggregation remain unresolved. No positivity or monotonicity under
physical-row selection, signed cutoff-change estimate, or
all-annulus redesigned-$W_U$ extension is asserted. The unaudited
source main/logarithmic-control/density inputs and the actual
one-envelope premise remain conditions throughout. There is no
source-proof audit, Lean or originality certification, or completion
of full C68, J40, signed Robin restoration or RH.

## A source-conditional strict sector with a small valuation-one product

Retain C98's literal original-$W_0$ C80 columns and bare branch:
$C=\mathfrak b=D_{\rm src}=1$, corefree/common-$e=1$, $q=L=U$,
$D=U^{1/2}$ and $A=U^{1/12}$. For a nonunit good sixth-power-free
physical reduced part $r$ of C79, define the ideals

$$
 \mathfrak s_1(r)=\prod_{\substack{p\notin S\\v_p(r)=1}}p,
 \qquad
 \mathfrak t(r)=\prod_{\substack{p\notin S\\2\le v_p(r)\le5}}
                       p^{v_p(r)},
 \qquad (r)=\mathfrak t(r)\mathfrak s_1(r).
\tag{C105}
$$

Thus $\mathfrak s_1$ is exactly the product of valuation-one good
primes, not the radical of $r$; it is squarefree and coprime to the
powerful ideal $\mathfrak t$. Fix, independently of $U$,

$$
 0\le\eta<\eta_\star:=\frac{13-5\sqrt6}{3},\qquad
 \theta=\frac{1+\eta}{2},\qquad
 \mathscr P_\eta=\{r\text{ as in C79}:q_r>1,
                     N(\mathfrak s_1(r))\le q_r^\eta\}.
$$

This selects $r$, not the full frequency
$k=\epsilon e_S(\mathbf j)r a^6$. If $a$ overlaps a prime of
$\mathfrak s_1(r)$, that prime has valuation $1+6v_p(a)$ in $k$,
so the valuation-one product of the full $k$ need not equal
$\mathfrak s_1(r)$. All ideals $a$, including overlaps and $S$
factors, remain in the frequency sum, together with every original
unit and $S$ label.

Each component's original $\Pi_i$ is frequency-independent, fixed
before that sum, and satisfies $q_{\Pi_i}\le U^{C_\Pi}$. Retain
literally $b_A=\mu+K_{A;0}$, all four $\mu/K$ terms in C80, the
product-squarefree condition, original signs and phases, total-class
selector, fixed twists and every defining-modulus/collision zero.
In particular the original $\chi_n(a^6)=\mathbf1_{(n,a)=1}$ stays
in C81's joint correction with
$P=\operatorname{rad}(\Pi_i r a)|_{p\notin S}$. Neither the
coefficient law nor the original column scales are reset at a
physical dyad $Q\asymp q_r$.

**Source correspondence and the intersected count.** The pinned
[primary, physical ideal split and stratum count, lines 5238–5294](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L5238)
already contains this split and its $Q V^{-1/2}$ upper count.
In that source's notation, take $u=r$, its supported factor
$\mathfrak s=1$ because $r$ is good, its powerful factor
$\mathfrak w=\mathfrak t(r)$ and its residual ideal
$\mathfrak k=\mathfrak s_1(r)$; the source scale $U$ there is
the present physical scale $Q$, not the column scale $U$ here.
Its residual $k$ is also distinct from C79's full frequency $k$.
Use the original fixed generators/unit convention, leaving C79's
external six-unit and finite $S$ labels in their original sums.

For $q_r\asymp Q$ and $N(\mathfrak t(r))\asymp V$, the actual
residual annulus is $N(\mathfrak s_1(r))\asymp Q/V$. The sector
condition forces $V\gg Q^{1-\eta}$. Sum the source's existing
$Q V^{-1/2}$ bound over these dyadic $V\ll Q$, including bounded
unit ranges. This geometric sum, with all physical restrictions
retained or enlarged only for a positive upper count, gives

$$
 \#\{r\in\mathscr P_\eta:q_r\asymp Q\}
 \ll_{K,S,\eta}Q^\theta,
 \qquad
 \#(\mathcal B_{\ell,\alpha}(Q)\cap\mathscr P_\eta)
 \ll Q^{m_\alpha+\delta},\qquad
 m_\alpha=\min\{d_\alpha,\theta\}.
\tag{C106}
$$

Here $\delta>0$ is an arbitrarily small internal count loss,
$d_{\alpha_0}=1$ at $\alpha_0=51/100$, and $d_\alpha$ above
the floor is exactly C99's existing piecewise $\mathcal R(\alpha)$.
In particular $m_{\alpha_0}=\theta$. The density half of the
intersection is precisely C94–C99's
[Xu–Sang v2, §6.1, Lemma 6.2 and Proposition 6.3](https://arxiv.org/html/2610.17675v2#S6)
with [(459.7)](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计).
The primary's powerful count and stratum count are suppliers, not
new results of this application. C106 is an intersection of two
upper counts on the same physical rows; no independence or new
sieve is assumed.

Form those bins first with C94–C99's one fixed $\Theta$ containing
both original sides' ray, unit/$S$, $\xi$, orientation twists and
conjugates. The family remains
$\mathcal X_r=\{\nu(n)\chi_n(r)^{\pm1}:\nu\in\Theta\}$,
including inducing orders properly dividing six. C80's good-prime
ramification makes every primitive inducer nonprincipal and gives
only $Q_\rho\ll_{H,S}Q$. Intersect afterwards with
$\mathscr P_\eta$. Neither $\mathfrak t$ nor $\mathfrak s_1$
is substituted for $r$ in the characters, primitive conductors,
zeros or density family. Additional $\Pi_i,a$ deletions stay in
C81's correction. The density is not applied to a new masked
witness or to the actual bilinear coefficient as a witness.

**The small physical scales and all repetitions.** Summing the
first count in C106 over dyads and partially summing gives
$\sum_{r\in\mathscr P_\eta,\ q_r\le Y}q_r^{-1/6}
\ll Y^{\theta-1/6}$. C83's complete sixth-power count therefore
pays every $1<q_r\le U^{1/5}$. With C82's original-$W_0$ bound,

$$
 \sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
       r\in\mathscr P_\eta,\ q_r\le U^{1/5}}}
       |B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2R^{1/6}
       U^{113/60+\theta/5+\varepsilon},\qquad 1\le R\le U.
\tag{C107}
$$

The multiplier being counted is the full original finite sum of
$6q_{e_S(\mathbf j)}^{-1/6}$ and all integral ideals $a$, not one
representative per primitive inducer. Since
$1/2\le\theta<\theta_\star:=(16-5\sqrt6)/6<2/3$, the small-scale
exponent is at most $121/60<27/13$. At $\eta=0$, C107 is exactly
C100's $119/60$ exponent. No application of a finite buffered
contour at bounded $Q$ is required.

**Exact optimization of the remaining $Q,R$ majorant.** For
$U^{1/5}\ll Q\ll RU\ll U^2$, reuse C94's simultaneous local
contour and global $7/8$ cap, with its tails and choice order.
For each $r$ there are $O((RU/Q)^{1/6})$ ideal choices of $a$;
this allows every overlap and $S$ factor. C106 and C94 give

$$
 \sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
           r\in\mathcal B_{\ell,\alpha}(Q)\cap\mathscr P_\eta}}
       |B_i(k;\Pi_i)|^2
 \ll\mathcal H_{i,J}(R)^2(RU)^{1/6}
       Q^{m_\alpha-1/6}
       U^{2\min\{\alpha,7/8\}+\varepsilon}.
\tag{C108}
$$

All original masks are paid uniformly through C94; collision
restrictions can only decrease this positive energy. Put
$\rho=\log_U R\in[0,1]$ and $x=\log_U Q$. Up to the fixed
dyadic endpoint constants, the exponent to maximize is
$ (1+\rho)/6+(m_\alpha-1/6)x+2\min\{\alpha,7/8\}$,
with $1/5\le x\le1+\rho$. Its continuous upper majorant has
the exact maximum, for every such $\rho$,

$$
\begin{aligned}
 \max_{\substack{\alpha_0\le\alpha\le1\\1/5\le x\le1+\rho}}
 \left\{\frac{1+\rho}{6}+
      (m_\alpha-\tfrac16)x+2\min\{\alpha,7/8\}\right\}
 &=\rho\theta+E(\theta),\\
 \alpha_\theta&=\frac{31-21\theta}{32-12\theta},\qquad
 E(\theta)=\theta+\frac{2(31-21\theta)}{32-12\theta}.
\end{aligned}
\tag{C109}
$$

To see all endpoints, when $m_\alpha\ge1/6$ the maximizing
$x$ is $1+\rho$, giving
$(1+\rho)m_\alpha+2\min\{\alpha,7/8\}$. Above the floor,
$\mathcal R(\alpha_\theta)=\theta$ and
$\alpha_*<\alpha_\theta\le41/52<7/8$, where
$\alpha_*=(21-5\sqrt6)/12$. Up to $\alpha_\theta$ the expression
is $(1+\rho)\theta+2\alpha$, increasing. Between
$\alpha_\theta$ and $7/8$, its derivative is
$2-300(1+\rho)/(21-12\alpha)^2<0$. Thus its maximum is the
displayed $\rho\theta+E(\theta)$. The floor contributes only
$(1+\rho)\theta+2\alpha_0$, strictly less.

On $7/8\le\alpha\le11/12$, the capped expression decreases
from $57/28+2\rho/7$, below
$E(\theta)+\rho\theta$ since $57/28<27/13\le E(\theta)$
and $2/7<\theta$. At $11/12$, $m_\alpha=1/6$.
For $\alpha>11/12$ the negative $Q$ exponent is maximized
instead at $x=1/5$, giving
$113/60+\rho/6+m_\alpha/5\le23/12+\rho/6$.
This too is below $E(\theta)+\rho\theta$. These statements
include the high density branch, the cap junction, and both
physical-dyad endpoints for every $R$. Equality in the continuous
majorant occurs at $x=1+\rho$, $\alpha=\alpha_\theta$; this
does not assert an occupied bin, simultaneous saturation of the
two counts, or attained sharpness for actual columns.

C107, C108–C109 and the original bin/dyad sums yield, for every
fixed $\eta$ in the stated range and every final $\varepsilon>0$,
under C77–C96's source main/logarithmic-control/density premises,

$$
\begin{aligned}
 M_i^\eta(R)
 &:=\sum_{\substack{0<q_k\ll RU,\ k\text{ as in C79}\\
                      r\in\mathscr P_\eta}}
                 |B_i(k;\Pi_i)|^2\\
 &\ll_{H,S,C_\Pi,\eta,\varepsilon}
       \mathcal H_{i,J}(R)^2 R^\theta
       U^{E(\theta)+\varepsilon},\qquad 1\le R\le U.
\end{aligned}
\tag{C110}
$$

One finite $J$ suffices for these bounds, conditional on the
original finite envelope at that order for their restoration.
At $\eta=0$ this recovers C98's $R^{1/2}U^{27/13+\varepsilon}$,
rather than replacing that sharper bound with a positive-$\eta$
specialization.

**One actual envelope, loss budget and original restoration.**
Use exactly C96's coupled measure $dc$ and shell contract, with
one fixed $B\ge4$ and one common finite $J$:
$\int|dc|\,\mathcal H_{1,J}(R)\mathcal H_{2,J}(R)
\ll\mathcal N_{{\rm base},J}(1+R)^{-B}$, where
$\mathcal N_{{\rm base},J}$ is fixed or polylogarithmic in $U$.
This is an applicability premise for the actual profiles and
norm heights at the required order. An unspecified polynomial
envelope does not qualify. All component, class, mask, unit/$S$,
dyad and repetition costs belong to this one envelope, including
the original height derivative costs. An envelope supplied only
for R43–R46's $h^{-2}$ component costs the same fixed $h^2$.
No allowance restarts at $Q,r,a$, a bin or a component.

For $R>U$ use the complete C96 weighted tail, restricted only
in its positive energy to $\mathscr P_\eta$:
$\mathcal N_{{\rm base},J}U^{3+\varepsilon}
\sum_{R>U\ {\rm dyadic}}R^{1-B}
\ll\mathcal N_{{\rm base},J}U^{4-B+\varepsilon}$.
It includes every large-$a$ repetition and collision mask; no
polynomial-puncture or bin estimate is extended past $R=U$.
For $R\le U$, Cauchy uses both original columns on the same
full $k$ sector and the same $dc$. Sum C110 with its stipulated
shell decay, using $R=1$ for the ball. Restore $q/L^3=U^{-2}$
and the original raw Gauss-pairing $U^2$ once, as in C97/C103,
and then $D^{-2}=U^{-1}$ once. For precisely this original signed
local contribution $\mathcal E_0^\eta$ the result is

$$
 |\mathcal E_0^\eta|
 \ll\mathcal N_{{\rm base},J}U^{E(\theta)+\varepsilon},\qquad
 D^{-2}|\mathcal E_0^\eta|
 \ll\mathcal N_{{\rm base},J}U^{E(\theta)-1+\varepsilon},\qquad
 \lambda_\eta=E(\theta)-2.
\tag{C111}
$$

The restricted C68 scaling uses $R^\theta\le R$. The self-dual
measure, unit count and fixed ideal generators introduce no extra
area, inverse Gauss, unit division or second normalization.

The strict reserve is

$$
\begin{aligned}
 \Delta(\eta)&=\kappa-E(\theta)>0,
       &0\le\eta<\eta_\star,\\
 E'(\theta)&=1-\frac{600}{(32-12\theta)^2}>0,
       &\tfrac12\le\theta<\theta_\star,\\
 E(\tfrac12)&=27/13,\qquad
 \lim_{\theta\uparrow\theta_\star}E(\theta)=\kappa,
       &\theta_\star=\frac{16-5\sqrt6}{6}.
\end{aligned}
\tag{C112}
$$

For a concrete strict allocation fix $\eta$ first and choose
$0<b<\min\{\varepsilon,\Delta(\eta)\}/16$. Budget at most
$b$ each for the following seven total energy/restoration losses:
the buffered contour displacement; the numerator/reciprocal
factors; the deleted joint Euler correction; the density loss
and its internal height/parameter costs; the bin/dyad sums; the
alternative right-strip/small-$Q$/absolute-tail estimates; and
absorption of the stipulated fixed or polylogarithmic envelope.
For example take $49e/3<b$, bound each of the at most twelve
$L$ or reciprocal factors after squaring by $U^{b/12}$, and take
the correction's internal exponent smaller than
$b/[2(C_\Pi+2)]$, using $q_P\ll U^{C_\Pi+2}$.
The density exponent loss can be taken smaller than $b/2$
since $Q\ll U^2$, with a further reduction to fit its internal
height costs in that same allowance. The original count has
only $O_e(1)$ bins and $O(\log U)$ dyads. All seven losses
together are at most $7b<\min\{\varepsilon,\Delta(\eta)\}$;
fixed Fourier masses, units and $S$ labels add constants only.

Preserve C94's source choice order: after fixing this loss budget,
fix sufficiently small $e$ and finite internal source
moment/detector/parameter-Sobolev orders, then sufficiently small
$0<\tau\le1/100$, and only then an external Mellin-tail order
$N$ with $N\tau/5>C_0+10$. Enlarge one common finite $J$ to
pay those tails, all joins and the chosen shell decay. The actual
envelope must be available at this $J$. Its existence is not
inferred from a lower-order envelope or an arbitrary smoothness
assertion. Thus C111 has strict restricted scaling after losses,
$\lambda_\eta+7b<B_*-1$. No generic $\varepsilon$ larger than
the reserve can be used for that conclusion. As
$\eta\uparrow\eta_\star$, $\Delta(\eta)\downarrow0$; the method
supplies neither strictness at the endpoint nor a uniform finite
$J$ up to it.

For the fixed nonzero choice $\eta=1/4<\eta_\star$, the exact
parameters and reserves are

$$
\begin{aligned}
 \theta&=5/8,\qquad \alpha_\theta=143/196,\qquad
 E(\theta)=817/392,\\
 E(\theta)-1&=425/392,\qquad
 \lambda_{1/4}=33/392,\\
 \Delta(1/4)&=\frac{4801-1960\sqrt6}{1176}
   =\frac{1}{1176(4801+1960\sqrt6)}
   \simeq8.86\mathbin{\cdot}10^{-8}>0,\\
 4801^2-6\cdot1960^2&=1.
\end{aligned}
\tag{C113}
$$

The contour, density, tail, dyadic and envelope losses just listed
must all fit inside this very small reserve for this example.
The displayed exponents are limiting upper majorants with a
chosen smaller positive loss, not zero-loss asymptotics.

**Domain gain and bounded nonduplication.** At $\eta=0$,
$N(\mathfrak s_1)=1$ is precisely the powerful sector
$\mathscr P$. Every fixed $\eta>0$ admits nonpowerful physical
rows beyond the small-$Q$ region. For example fix a good prime
ideal $\mathfrak p$ and let a different good prime ideal
$\mathfrak q$ grow. The fixed-generator row with
$(r)=\mathfrak p\mathfrak q^2$ has
$\mathfrak s_1(r)=\mathfrak p$ and eventually
$N(\mathfrak p)\le q_r^\eta$. With $U=q_r$, $a=1$ and the
unit $S$ label it lies on $Q\asymp U$, beyond $U^{1/5}$ and
in the original $R=1$ frequency ball. This demonstrates a larger
permitted domain; it gives no lower bound on its energy and
does not assert that a particular C80 column is nonzero.

The primary already owns the physical split, powerful count and
$QV^{-1/2}$ stratum estimate. C9–C10 in the
[source card](../Analytic/liu2026quasirh.md#removing-the-repeated-factor-cutoff-from-the-low-conductor-estimate)
and [§462](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#462-原卷积的大重复部分与完整交叉项)
concern repeated factors of the inverse-square columns and their
interference; PR1–PR10 in the
[reflection companion](../Analytic/openai2026quasirh.md#joint-control-of-all-powerful-prime-reflection-choices)
sum reflection choices on original numerators. Neither is the
C80 physical-$r$ sector defined in C105. Within these bounded
source correspondences, the retained application is their
existing row count intersected with C94's density bins and
optimized on the actual C80 columns, with all repetitions and
one original envelope. It claims no new supplier theorem or
literature priority. C77–C104 retain all their stated strengths,
including C87's sharper dominant-annulus dependence.

For each fixed $\eta$, the bare nonunit complement now has
$N(\mathfrak s_1(r))>q_r^\eta$; this necessary condition does
not make a row critical or bound that complement strictly.
The original-$W_0$ principal $r=1$ scalar, $k=0$, other
cores/common-$e$ and common-column branches, other source
$C/\mathfrak b$, generalized finite/angular families and their
actual measure, bad duals, full physical-row restoration and
the original common-beta signed Mobius detector/$\rho$
aggregation remain unpaid. There is no positivity or monotonicity
under signed physical-row selection, all-annulus redesigned-$W_U$
extension or signed cutoff-change bound. C105–C113 remain
source-conditional application exposition, with source main,
logarithmic-control, physical density and the actual finite
coupled envelope as premises; they certify neither those source
proofs nor Lean, originality, full C68, J40, signed Robin
restoration or RH.


## The common measure produced by the original fixed local kernel

This is an explicit application of the existing Fourier calculus to
C57–C59, supplying the profile-envelope premise of the identical bare
C80–C113 consumers. Retain their corefree/common-$e=1$,
$C=\mathfrak b=D_{\rm src}=1$, $q=L=U$ branch, the genuine fixed
ideal-ray quotient and total class of R43, $\zeta_i=1$, and no extra
angular multiplier. Use the original fixed smooth radial $w$ and four
fixed smooth annular profiles $V_i$, with $D=\sqrt U$ and
$A=U^{1/12}$. The arithmetic coefficient is the literal C57
$b_A=\mu+K_A$ with its original $W_0$ divisor cutoff. Both factor
annuli, every squarefree/gcd/deletion mask, collision zero, orientation,
$\xi$, C56 multiplier, unit and $S$ label remain. This application
constructs no preceding signed component/height family.

The reused tools are the pinned primary's `lem:kernel-seminorms`,
`lem:smooth-calculus` and `eq:inverse-log-fourier`–
`eq:inverse-fourier-moment`, together with C56's planar normalization
and R43's full finite Fourier mass. No new Fourier continuity theorem
or arithmetic estimate is asserted. In particular, the initial
marked-inverse polynomial in `eq:initial-residual-polynomial` is not
identified with C57's two-factor convolution.

**Include the row in the same transform.** Choose a fixed smooth
$\theta:[0,\infty)\to[0,1]$, equal to one on $[0,1]$ and zero on
$[2,\infty)$. Put $R_j=2^j$ and

$$
\begin{aligned}
 \kappa_0(y)&=\theta(|y|^2),\\
 \kappa_j(y)&=\theta(|y|^2)-\theta(2|y|^2)\quad(j\ge1),\\
 \sum_{j\ge0}\kappa_j(k/\sqrt{R_jU})&=1.
\end{aligned}
\tag{C114}
$$

The last identity telescopes for every $k$, including zero. The
arithmetic sum here still excludes $k=0$. Before any inversion retain
the fixed row restrictions
$\mathcal K_0=\{k:0<q_k\le2U\}$ and
$\mathcal K_j=\{k:R_jU/2\le q_k\le2R_jU\}$ for $j\ge1$,
intersected with their original physical-row restrictions and labels.
They contain the respective supports of $\kappa_j$ and remain outside
the separation. Individual separated integrands do not acquire shell
support merely because their integral has it.

Write $x_i=q_{d_i}/D$, $\ell_i=\log x_i$, and $p=\prod_i x_i$.
On $\mathbb C\times\mathbb R^4$ define the single ambient profile

$$
\begin{aligned}
 G_j(y,\boldsymbol\ell)
  ={}&\kappa_j(y)V_1(e^{\ell_1})V_2(e^{\ell_2})
       \overline{V_3(e^{\ell_3})V_4(e^{\ell_4})}
       e^{-\sum_i\ell_i/2}\\
    &\quad\times\widehat w\!\left(
          \sqrt{R_j}e^{-\sum_i\ell_i/2}y\right),\\
 \widehat G_j(\eta,\boldsymbol\xi)
  ={}&\int_{\mathbb C\times\mathbb R^4}
       G_j(v,\boldsymbol u)e_K(-v\eta)
       e^{-i\boldsymbol\xi\cdot\boldsymbol u}
       \,d\mu(v)\,d\boldsymbol u.
\end{aligned}
\tag{C115}
$$

There are six real transform coordinates. With $y=k/\sqrt{R_jU}$,
$|\sqrt{R_j}p^{-1/2}y|^2=q_k/(Up)$, so this is exactly C59's
kernel, including its inverse-root power, rather than a new rowwise
test. Let $\chi_i$ be fixed real annular cutoffs equal to one on
$\operatorname{supp}V_i$. Mixed inversion gives, for all $x_i>0$,

$$
\begin{aligned}
 &\kappa_j(y)\Psi_{q_k/U}(\boldsymbol x)\\
 &\quad=(2\pi)^{-4}
   \int_{\mathbb C\times\mathbb R^4}
       \widehat G_j(\eta,\boldsymbol\xi)e_K(y\eta)
       \prod_{i=1}^4[\chi_i(x_i)x_i^{i\xi_i}]
       \,d\mu(\eta)\,d\boldsymbol\xi.
\end{aligned}
\tag{C116}
$$

The planar pairing in real coordinates has matrix
$(2/\sqrt3)\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$
in the convention $\exp(2\pi i\langle v,\eta\rangle)$.
Its determinant has absolute value $4/3$; the factors
$d\mu=(2/\sqrt3)d\operatorname{Leb}$ in both variables therefore
make planar inversion self-dual. Only the four log coordinates
contribute $(2\pi)^{-4}$. The first side receives
$\chi_1x_1^{i\xi_1},\chi_2x_2^{i\xi_2}$; the conjugated side
receives $\chi_3x_3^{-i\xi_3},\chi_4x_4^{-i\xi_4}$.
This changes only the smooth profile presentation, with the original
$V_i$ retained exactly in the common density; it does not replace
$b_A$, choose independent kernels, or differentiate arithmetic weights.

C116 holds pointwise on the unchanged arithmetic tuple set. It does
not factor a cross-column gcd indicator. Retain every such detector
in its existing arithmetic reduction. At each already reduced C68
bilinear contraction, keep $e_K(k\eta/\sqrt{R_jU})$ outside the
columns and use its modulus one in Cauchy on the same restricted
$k$ set $\mathcal K_j$. The resulting column seminorms have only
fixed polynomial $\boldsymbol\xi$ costs. Taking the transform
separately at each actual $k$ would not provide this common density.

**One finite order pays all shells.** For fixed annular boxes set
$P_N(V)=\max_{0\le r\le N}\sup_{x>0}|(x\partial_x)^rV(x)|$,
and use the primary's Schwartz seminorm $s_m(w)$ in two real
coordinates. For prescribed $H,B\ge0$, take
$N=2\lceil(H+7)/2\rceil>H+6$ and
$m=2N+2\lceil B\rceil+2$. The existing finite Fourier estimate in
six dimensions and its fixed-pairing version give

$$
 \int |\widehat G_j(\eta,\boldsymbol\xi)|
       (1+|\eta|+|\boldsymbol\xi|)^H
       \,d\mu(\eta)\,d\boldsymbol\xi
 \ll_{H,B,\theta,\mathrm{boxes}}
       s_m(w)\prod_{i=1}^4P_N(V_i)(1+R_j)^{-B}.
\tag{C117}
$$

Indeed, on $j\ge1$ the fixed planar support has
$1/2\le|y|^2\le2$ and the log box is fixed. Derivatives through
order $N$ consume at most $N$ powers of $\sqrt{R_j}$, absorbed
by the Schwartz decay of $\widehat w$. The primary's finite-seminorm
bound transfers that control to the displayed $s_m(w)$.
The $j=0$ ball is smooth in its two planar coordinates at zero;
no logarithmic row coordinate or half-line extension is used.

For the actual fixed finite label table write its coefficients as
$a_{\lambda,\chi,\psi}$, with
$M_{\rm fin}=\sum_{\lambda,\chi,\psi}|a_{\lambda,\chi,\psi}|$.
The label $\lambda$ contains only original unit/$S$ labels when
these are split externally; they may instead remain in the row sets.
For each copy of R43's bare table,
$a_{\chi,\psi}=h^{-2}\overline{\chi(\sigma)\psi(\sigma)}$ and
$\sum_{\chi,\psi}|a_{\chi,\psi}|=1$.
Its trivial coefficient $h^{-2}$ is not the full mass.
On the disjoint union of shells and finite labels take counting
measure and define

$$
\begin{aligned}
 dc&=(2\pi)^{-4}a_{\lambda,\chi,\psi}
       \widehat G_j(\eta,\boldsymbol\xi)
       \,d\mu(\eta)\,d\boldsymbol\xi,\\
 \int(1+R_j)^b(1+|\eta|+|\boldsymbol\xi|)^H\,|dc|
 &\ll_{H,b,\theta,\mathrm{boxes}}
       M_{\rm fin}s_m(w)\prod_iP_N(V_i),\qquad b\ge0.
\end{aligned}
\tag{C118}
$$

For C118 choose C117 once with $B=b+2$ and its corresponding
orders; $\sum_{j\ge0}(1+2^j)^{-2}\le4/3$.
Choose $H$ at least the combined polynomial cost of both child
seminorms and all analytic consumers being used, and choose their
finite order $J$ once. Then this same measure satisfies
$\int|dc_j|\mathcal H_{1,J}\mathcal H_{2,J}
 \ll\mathcal N_{{\rm base},J}(1+R_j)^{-b}$,
with one $U$-independent $\mathcal N_{{\rm base},J}$ for fixed
inputs. A family is admitted if this displayed finite input-seminorm
product has an actually supplied polylogarithmic bound.
Kernel decay is paid once in the expanded bilinear form. No budget
restarts at a row, reduced part, sixth-power repetition, mask, mode,
component or shell. The exceptional $r=1$ rows are restored in this
identity, without asserting any new bound for their arithmetic sum.

**Which premise is supplied.** For precisely these fixed original
local inputs, C118 supplies the base-envelope contract of C82,
C91–C92 and C96–C97, and hence that premise for C98–C113 on the
identical branch. R43–R45 may use the same base profile measure for
the same original-$W_0$ local kernel. None of their other source,
contour, density or sector hypotheses is discharged. R46 uses the
different redesigned arithmetic cutoff $W_U$; this construction
neither substitutes it for $W_0$ nor transfers R46's strict bound
to the original realization.

For a preceding signed component/height measure $d\Lambda_U(t)$,
the required extra input is an actual producer and a bound of the form

$$
 \int |d\Lambda_U(t)|\,M_{\rm fin}(t)
       s_m(w_t)\prod_iP_N(V_{i,t})\ll(\log(2U))^C,
\tag{C119}
$$

with the specified common finite orders, including all original
polynomial height costs. Fixed per-profile control alone does not
imply C119. For generalized angular tables their actual weighted
Fourier variation is also required, and R43 is not a substitute.
Thus the fixed-input local envelope is explicitly supplied, while
an unspecified larger signed family retains its original premise.
There is no improved arithmetic exponent, saving for H or the complete
M46 remainder, full C68/J40 restoration, signed Robin estimate or RH
proof. These are conditional application formulas, without a source
major-proof audit, Lean certification or literature-priority claim.
