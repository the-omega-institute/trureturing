---
bibkey: liu2026quasirhreduced
authors: Baiying Liu
year: 2026
title: Reduced-frequency applications to the actual C68 columns
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Repo-derived source-conditional applications to actual bare-J4 C68 columns pay the nonunit reduced-frequency sector up to U^(1/5) for the original and exact redesigned cutoffs, and give the original-W0 dominant endpoint where the reduced-frequency norm is comparable to U, with all its sixth-power repetitions. Strict and full C68, other unpaid annuli and branches, J40 and signed Robin restoration remain unresolved.
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
and R1–R46 in the residue companion. C77–C92 belong only to this note.
The deductions are conditional paper mathematics, without a source-proof
audit or Lean certification.

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
no derivative acts on $b^{(\circ)}$.

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

**Unpaid complement.** Nonexceptional frequencies with $q_r>U^{1/5}$
retain the same actual coefficients and require a new estimate; C84
supplies no full C68 $W(1/12)$. The $r=1$ frequencies are C58's
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
which already has the same numerical exponent. The preceding unpaid
complement still requires a strict/full C68 estimate; C87 supplies
only an endpoint on this dominant annulus.

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
missing. Beyond C77–C86's paid small-$r$ sector, other reduced-frequency
annuli are not paid here. The original-W0 exceptional principal
scalar, $k=0$, other cores/common-$e$ and common-column branches,
other source $C/\mathfrak b$, generalized finite/angular factors and
their actual measure, bad duals, physical-row restoration and the
original signed common-beta Mobius detector/$\rho$ aggregation remain
unresolved. R46's redesigned exceptional payment is not transferred
to W0. Full C68, J40, Robin and RH remain open. All conclusions here
are source-conditional paper deductions, without source-proof audit,
Lean certification or originality certification.
