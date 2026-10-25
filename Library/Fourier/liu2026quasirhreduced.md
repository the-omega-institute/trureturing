---
bibkey: liu2026quasirhreduced
authors: Baiying Liu
year: 2026
title: Small reduced-frequency application to the actual C68 columns
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Repo-derived application of the pinned uniform finite-order source premises pays the actual bare-J4 C68 sector with nonunit reduced-frequency norm at most U^(1/5), separately for the original and exact redesigned cutoffs. The larger reduced-frequency complement, full C68, J40 and signed Robin restoration remain unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Small reduced-frequency application to the actual C68 columns

This `repo-derived` companion uses the notation and source conventions
of the [Liu source card](../Analytic/liu2026quasirh.md), the
[complete-dual application](liu2026quasirhdual.md), and the
[joint mixed-Mobius and residue companion](liu2026quasirhresidue.md).
C1–C50 remain in the source card, C51–C76 in the complete-dual owner,
and R1–R46 in the residue companion. C77–C86 belong only to this note.
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
