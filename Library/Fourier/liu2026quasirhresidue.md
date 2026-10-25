---
bibkey: liu2026quasirhresidue
authors: Baiying Liu
year: 2026
title: Joint mixed-Mobius estimates and the actual exceptional residue interface
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Repo-derived conditional joint Mellin bounds put the original fifteen constant-ray radial mixed-Mobius terms below the local comparison exponent; the actual all-K residue scalar and the full signed J40 contraction remain unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Joint mixed-Mobius estimates and the actual exceptional residue

This is a `repo-derived` companion to
[the four-factor source reduction](liu2026quasirhdual.md#four-inverse-factors-on-the-same-coprime-realization).
The deductions below are not attributed to Liu, Grafakos–Teschl or
Xu–Sang. They reuse C37, C48 and C51–C76, without certifying the
upstream main proof. In particular, $R_{7/8}$ is an explicit
source-conditional premise, not a newly proved zero-free strip.
The statements are paper mathematics, without Lean or CI certification.
Labels R1–R12 belong only to this companion; C1–C76 retain their scope.

Keep $K=\mathbb Q(\sqrt{-3})$, its original finite bad set $S$, ideals
counted once, $D=U^{1/2}$, $A=U^\alpha$, $0<\alpha<1/4$, and the
original real smooth cutoff $W$ of C37. On precisely the original
inverse annulus, $b_A=\mu+K_A$, where
$K_A(d)=\sum_{e\mid d}\mu(e)2^{\omega(e)}W(q_e/A)$.
The four-way squarefree product, every coprimality puncture, raw
sextic/cubic zero extension, profiles, signed coefficients and common
beta remain those of C59. Here $P$ is a squarefree puncture outside
$S$; in the frequency application it is $P_a$ of C58, not the
product-squarepart parameter of J40. No nonprincipal inverse-Hecke
hypothesis or new column coefficient is introduced.

## The joint estimate on each original nonempty subset

For $\varnothing\ne M\subseteq\{1,2,3,4\}$, put $m=|M|$,
$T=\{1,2,3,4\}\setminus M$ and $r=|T|$. Define

$$
Q_M(P;\Psi)=
\sum_{\substack{d_1d_2d_3d_4\ {\rm sf}\\
 (d_1d_2d_3d_4,SP)=1}}
 \prod_{i\in M}\mu(d_i)\prod_{k\in T}K_A(d_k)
 \Psi(q_{d_1}/D,\ldots,q_{d_4}/D).
\tag{R1}
$$

The profile is any smooth complex function supported on the same fixed
compact rectangle in $(0,\infty)^4$ as C52. Let $N_J(\Psi)$ bound its
partial derivatives up to order $J$ in each variable there. Assume
$1/2\le\beta<1$ and exactly $R_\beta$ of C48, including polynomial
vertical growth on each smaller closed strip. For every fixed $C$,
$q_P\le U^C$, and $\varepsilon>0$, one finite $J$ gives, uniformly in
all fifteen subsets,

$$
|Q_M(P;\Psi)|\ll_\varepsilon N_J(\Psi)(Uq_P)^\varepsilon
 D^{m\beta}
 \left[D A^{-(1-\beta)}
       +D^{1/2}A^{\beta-1/2}\right]^r.
\tag{R2}
$$

Constants depend on $K,S,W,\alpha,C$, the fixed rectangle, the strip
margins and the constants of $R_\beta$. For $r=0$ the bracket is $1$.
This is a joint estimate for the actual mixed coefficients, rather than
an estimate obtained by fixing three columns and taking their masses.

**Literal Euler product.** Expand only the $r$ actual divisor sums in
R1 and Mellin-invert their cutoffs. Write $x_i=q^{-s_i}$ and
$y_k=q^{-z_k}$. At $p\nmid SP$, squarefreeness of the full product
allows the prime in at most one $d_i$. A Mobius slot contributes
$-x_i$; a $K_A$ slot contributes $x_k(1-2y_k)$. Thus the joint series is

$$
\begin{aligned}
F_P(\mathbf s,\mathbf z)
 &=\prod_{p\nmid SP}
 \left(1-\sum_{i\in M}x_i+
                 \sum_{k\in T}x_k(1-2y_k)\right)\\
 &=H_P(\mathbf s,\mathbf z)
   \prod_{i\in M}\zeta_K(s_i)^{-1}
   \prod_{k\in T}\zeta_K(s_k)\zeta_K(s_k+z_k)^{-2}.
\end{aligned}
\tag{R3}
$$

The first product is literal for $\Re s_i>1$, $\Re z_k>0$.
It encodes the same forbidden cross-column prime collisions as C53;
there are no independent pairwise products. At an unexcluded prime,
with $L_p$ the parenthesis in R3,

$$
H_{P,p}=L_p\prod_{i\in M}(1-x_i)^{-1}
                \prod_{k\in T}(1-x_k)(1-x_ky_k)^{-2}.
\tag{R4}
$$

At $p\mid SP$, the factor is the same expression with $L_p=1$.
All linear monomials cancel at unexcluded primes. On every closed
substrip of

$$
\Re s_i>1/2\quad(1\le i\le4),\qquad
\Re(s_k+z_k)>1/2\quad(k\in T),
\tag{R5}
$$

let $a>1/2$ be a common lower bound for these real parts. Expansion
of the displayed denominators, whose moduli are bounded away from
zero, gives $H_{P,p}=1+O(q^{-2a})$, uniformly in all heights.
The constant uses only the closed real substrip. The unexcluded
product converges normally and is bounded there. No $L_p$ is inverted,
so its zeros create no polar divisor.

For an excluded prime the modulus is at most $\exp(C_aq^{-a})$ after
enlarging $C_a$ to cover finitely many small primes. For each $\eta>0$,
$C_aq^{-a}\le\eta\log q$ for all sufficiently large $q$.
The product over the remaining small primes is bounded independently
of $P$. Consequently $H_P\ll_\eta q_P^\eta$, uniformly in heights
on these substrips. This proves polynomial-puncture uniformity without
assuming $q_P\le A^2$ or dividing by a local numerator.

**Contour calculation.** Use
$\widetilde\Psi(\mathbf s)=\int\Psi(\mathbf x)
\prod_i x_i^{s_i-1}d\mathbf x$ and
$\widehat W(z)=\int_0^\infty W(t)t^{z-1}dt$ initially for $\Re z>0$.
The exact $4+r$ dimensional inversion has integrand

$$
\widetilde\Psi(\mathbf s)D^{\sum_i s_i}
 \prod_{k\in T}\big[\widehat W(z_k)A^{z_k}\big]
 F_P(\mathbf s,\mathbf z),
\qquad (2\pi i)^{-(4+r)}d\mathbf s\,d\mathbf z.
\tag{R6}
$$

Choose $0<\delta<(1-\beta)/10$, later small enough for the stated
loss, and start with every $\Re s_i=2$ and
$\Re z_k=c=\beta-1/2+2\delta>0$. Absolute convergence justifies this
inversion and all initial interchanges. First move the $m$ Mobius
lines to $\beta+\delta$. Next move each $K_A$ line to
$\Re s_k=1/2+\delta$, keeping its $z_k$ line at $c$, and take its
single $s_k=1$ residue. Throughout, $\Re(s_k+z_k)\ge\beta+3\delta$.
The only poles crossed are the simple poles of the ordinary
$\zeta_K(s_k)$. Inverse-zeta factors are holomorphic by $R_\beta$;
R5 holds during each move. Intersections of ordinary simple poles
are handled by these successive one-variable residues.

For a term with residue set $E\subseteq T$, now shift just its
$z_k$, $k\in E$, to $-h=\beta-1+\delta$. In those slots $s_k=1$,
so the reciprocal arguments have real part at least $\beta+\delta$.
All other slots retain $\Re s_k=1/2+\delta$, $\Re z_k=c$.
Hence R5 and $R_\beta$ still apply to the whole joint correction,
including all mixed prime monomials. The cutoff continuation is

$$
\widehat W(z)=-\frac1z\int_1^2W'(t)t^zdt.
\tag{R7}
$$

Its sole pole is simple at zero. In a residue slot the double zero
of $\zeta_K(1+z)^{-2}$ cancels that pole. Thus no cutoff residue is
crossed. The same cancellation is not claimed at zeros of $\zeta_K$;
all paths stay strictly to the right of those allowed by $R_\beta$.

A term with $\ell=r-|E|$ boundary slots has modulus bounded by a
constant times the common seminorm and

$$
q_P^\eta D^{m(\beta+\delta)}
 (D A^{\beta-1+\delta})^{r-\ell}
 (D^{1/2+\delta}A^{\beta-1/2+2\delta})^\ell.
\tag{R8}
$$

Each ordinary residue contributes the fixed field residue $\kappa$,
absorbed in the constant. Summing the $2^r$ choices and allocating
$\delta,\eta$ inside the final loss proves R2. In particular this
proof uses $A^{\beta-1/2}$ in each boundary slot. No stronger boundary
estimate is needed for the conclusion.

**One derivative and height envelope.** Here is explicit sufficient
control for the contour argument. Let $B$ be the reciprocal growth
degree from C48 for margin $\delta$, and let $L$ bound the ordinary
zeta growth on the fixed $s$ strips, off fixed small neighborhoods of
its pole. Such a finite $L$ is supplied by fixed-field continuation
and the functional equation. Smooth compact support and integration
by parts in each log-coordinate give
$|\widetilde\Psi(\mathbf s)|\ll_J N_J(\Psi)
\prod_i(1+|\Im s_i|)^{-J}$ uniformly on the real strips used.
R7 gives the analogous arbitrary decay of $\widehat W$ on each
vertical line. Near its crossed pole, use the holomorphic canceled
product instead. Every reciprocal factor in a $K_A$ slot has growth
at most $(1+|\Im s_k+\Im z_k|)^{2B}$, bounded by the product of the
two separate weights of degree $2B$. A Mobius slot has degree $B$.
Thus $J>L+4B+20$ suffices for absolute integration in all at most
seven variables and for the vanishing of horizontal faces.
Use truncated rectangles, detour the ordinary poles at bounded
height, apply the successive residue theorem, and let all heights
tend to infinity under these integrable bounds. This also justifies
interchanges in every residual integral, without a moving-height
reciprocal premise.

Enlarge this same finite $J$ once for the original derivatives and
profile separation; $W$ and its required derivatives are fixed.
For C59 use, for one fixed $B_0\ge4$, a common bound on
$(1+z)^{B_0}$ times all needed $x$-derivatives of $\Psi_z$, including
any originally required profile derivatives. Schwartz seminorms of
the original row Fourier transform and annular column seminorms
supply it. Their orders are enlarged once to pay $B_0$ and $J$.
For a component/height measure $dc$, the assumption is precisely
$\sum\int |dc|\,N_{J,B_0}(\Psi)\le\mathcal N_J$, with
$\mathcal N_J$ fixed or polylogarithmic in $U$. Include the original
$|\eta|$ and any external signed coefficient costs in this measure.
For the four norm heights, a polynomial seminorm cost of degree $g$
is integrable against log-Fourier decay of order greater than $g+5$;
choose that order once within the same envelope. Angular and other
original heights must satisfy their original absolute-measure
contract too. This is a retained hypothesis, not a claim that an
unspecified full-J40 table or height measure has been checked.
No derivative acts on $b_A$; no envelope is restarted per subset,
frequency, class, or component.

## Full-frequency consequence and positive reserve

Apply R2 to exactly $\Psi_z$ of C59 and $P=P_a$ of C58. Define
$\mathcal R_\mu$ by the original signed sum of all fifteen R1 terms,
including their individual $\eta$, component coefficients and height
integrals. The finite six-unit and $S$-exponent sums are unchanged.
There is no cancellation assumption between subsets.

Here are explicit full-frequency bounds. On the ball $z\le1$ there
are $O(U^{1/6})$ ideals $a$; on a dyadic shell $z\asymp R\ge1$ there
are $O((RU)^{1/6})$. On $1\le R\le U$, $q_{P_a}\le q_a\ll U^{1/3}$.
Use R2 with one fixed polynomial range, choosing its internal loss
small enough to pay this puncture factor and all $U$ losses. Its
seminorm is $O(\mathcal N_JR^{-B_0})$, and
$\sum_{R\ge1}R^{1/6-B_0}<\infty$ over dyadic shells.
For $R>U$ do not apply a nonuniform puncture estimate: use
$|K_A(d)|\ll_W3^{\omega(d)}$ on squarefree ideals, the original annulus,
and the fixed-field divisor bound. Each four-column absolute sum is
$O_\varepsilon(D^{4+\varepsilon})$. Consequently the entire tail is

$$
\ll\mathcal N_JU^{13/6+\varepsilon}
       \sum_{R>U}R^{1/6-B_0}
\ll\mathcal N_JU^{7/3-B_0+\varepsilon}.
\tag{R9}
$$

With $B_0\ge4$ this is negligible. All shell bounds are integrated
against the same absolute component measure. This proves summability
of the complete original frequency identity, without discarding large
punctures or altering its signed coefficients.

At $A=U^{1/12}$ and source-conditional $R_{7/8}$, a Mobius slot in R8
costs $U^{42/96}$, a residue slot $U^{47/96}$, and a boundary slot
$U^{27/96}$, apart from the allocated loss. After the frequency count,
a subset with $m$ Mobius slots and $\ell$ boundary slots costs
$U^{(204-5m-20\ell)/96+\varepsilon}$. Therefore

$$
|\mathcal R_\mu|\ll_\varepsilon
 \mathcal N_JU^{199/96+\varepsilon},\qquad
\rho=1+B_*-199/96=\frac{393-160\sqrt6}{96}>0,
\quad B_*=(31-10\sqrt6)/6.
\tag{R10}
$$

Indeed $393^2-6\cdot160^2=849>0$; numerically
$\rho=0.01126709536137\ldots$. Choose, for example, $\nu=\rho/4$
and $0<\varepsilon<\rho/4$, absorbing the stipulated polylogarithms
with a smaller internal loss. This pays this radial fifteen-term
obligation at $U^{1+B_*-\nu}$. It improves its C60 certificate by
$101/48-199/96=1/32$. The other fourteen terms and every boundary term
are covered by the same estimate, rather than assigned a fresh budget.

These are the unnormalized local Gauss powers of C59. Restore the
original $D^{-1}$ on each side of J4: their product is
$D^{-2}=U^{-1}$, giving $U^{103/96+\varepsilon}$ for this local
normalized remainder, below $U^{B_*-\nu}$. Keep every additional
physical-row, core, gcd, bad-dual and detector/rho prefactor in its
original place. The $U^2$ multiplying the all-$K_A$ residue in C60 is
already $D^4$; it is not an additional multiplier on R10. C56 fixes
the planar measure; there is no extra area factor or unit division.
This local calculation does not bound those other parameters or
identify the local Gauss object with the full J40 contraction.

## The actual profile moment and finite scalar

This section is a reuse application of the existing radial identities,
not a new Fourier theorem. Use
[Grafakos–Teschl, Section 2](grafakosteschl2013radial.md#radial-fourier-suppliers-and-the-actual-weighted-source)
for the two-dimensional Fourier–Bessel normalization, and the source
[Xu–Sang v2, Section 3.4](https://arxiv.org/html/2610.17675v2#S3.SS4)
for its radial Mellin identity. The standard Bessel Mellin value is
[DLMF 10.22.43](https://dlmf.nist.gov/10.22.E43).
Parameter correspondence: $c=2/\sqrt3$, $w(z)=W_{\rm row}(|z|^2)$,
Euclidean Fourier frequency radius $c\sqrt t$, with measure multiplier
$c$ from C56; Bessel order $0$ and power $2v-1$.
At $v=1/6$ that power is $-2/3$, satisfying
$\Re(\mu+0)>-1$ and $\Re\mu<1/2$ in the cited Bessel identity.
It is absolutely integrable even at infinity at this parameter.
Equivalently these are dimension $2$, Riesz potential order $5/3$,
and spatial kernel $|z|^{-1/3}$. No unrestricted inverse-$L^p$
assertion is used.

For the original smooth compact annular row and column profiles set

$$
\begin{aligned}
M_i&=\int_0^\infty V_i(x)x^{-1/3}dx
       =\mathcal M V_i(2/3),\\
C_w&=\int_0^\infty\widehat w_{\rm rad}(t)t^{-5/6}dt
 =\left(\frac{2\pi}{\sqrt3}\right)^{2/3}
    \frac{\Gamma(1/6)}{\Gamma(5/6)}
       \int_0^\infty W_{\rm row}(u)u^{-1/6}du,\\
\widehat I_4(1/6)&=C_wM_1M_2\overline{M_3M_4}.
\end{aligned}
\tag{R11}
$$

The row constant is the cited radial identity with the stated measure
and frequency scale; its gamma ratio is the standard Bessel Mellin
value, not a new source arithmetic constant. The last line follows directly by substituting
$t=z/(x_1x_2x_3x_4)$ in C59 and using Fubini; compact annular column
support, smoothness at zero and rapid Fourier decay ensure absolute
integrability. The resulting power of each $x_i$ is
$1/6-1/2=-1/3$. Thus these **factor** Mellin values are at $2/3$.
They must not be confused with either $\widehat I_4(1/6)$ or the
source **total-column** $1/6$ moment: the total column has already
absorbed the $t^{1/2}$ Gauss normalization in C57. The row profile
$W_{\rm row}$ is not the divisor cutoff $W$ of C37/C69.

For a nonnegative nonzero original row, $C_w>0$. A diagonal pairing
with $V_3=V_1$, $V_4=V_2$ has profile functional
$C_w|M_1M_2|^2$, positive if both Mellin values are nonzero. Nonnegative
nonzero column profiles have that property. This states positivity of
a profile functional, not of a selected Poisson component or of an
arithmetic residue. Complex actual profiles can have zero moments;
their values must be substituted, rather than inferred from smoothness.

For the documented J4 diagonal with no additional side multiplier,
J28 has $\zeta_i=1$. On a common ray refinement of order $h$, its
remaining finite table is
$\mathbf1_{g_1g_2=\sigma}\mathbf1_{g_3g_4=\sigma}$:
the $\xi$ and $\chi(-1)$ phases pair with their conjugates on the
same total class, and the exceptional numerator characters cancel
as in C58. Each relation admits $h$ pairs, so normalized counting
on four factors gives $\eta=h^2/h^4=h^{-2}$. Angular Haar measures
are normalized; this diagonal has no extra angular multiplier.
The six units and $S$ exponents then give
$(6/h^2)\prod_{p\in S}\sum_{j=0}^5q_p^{-j/6}>0$.
Four specified individual classes would instead give $h^{-4}$.
This finite Fourier calculation assumes no statistical independence
of the actual ideal classes or angles.

Additional original side multipliers must be averaged as their actual
finite/angular table. For a side multiplier $B$ the constant pair
coefficient is
$L_\sigma(B)=h^{-2}\sum_{g_1g_2=\sigma}\int B\,d\theta_1d\theta_2$;
a polarized table has coefficient
$L_\sigma(B)\overline{L_\sigma(B')}$, not an average of $|B|^2$.
The full J40 component and height aggregate is unspecified here;
the J4 diagonal value cannot substitute for that aggregate.

Writing $d_{\mathbf r}=q_{e_S(\mathbf r)}$, retain the exact interface

$$
\begin{aligned}
S_{\rm actual}
 &=\sum_{\epsilon,\mathbf r}\int
 \eta_{\epsilon,\mathbf r,c}d_{\mathbf r}^{-1/6}
 C_{w_c}M_{1,c}M_{2,c}\overline{M_{3,c}M_{4,c}}\,dc,\\
\mathcal E_{\rm rad}
 &=\frac{\bar C}{6}U^{13/6}\bar Q_A S_{\rm actual}
 +O_\varepsilon\!\left(\mathcal N_J
 [U^{199/96+\varepsilon}+U^{47/24+\varepsilon}
                         +U^{95/48+\varepsilon}]\right).
\end{aligned}
\tag{R12}
$$

Here $dc$ is the actual signed component/height measure; for a single
component omit the integral. The individual row constants stay inside
if rows differ. Absolute integrability follows from the same envelope,
and C74–C75 supply exactly $\bar C$, $\bar Q_A$ and the other two
errors. The common cutoff, field and $S$ are those of the local C59
branch; R12 does not combine branches with different constants by
silently identifying them. All original physical prefactors still
multiply their own components. This retains the source total-column
identity as an application and does not claim a new Fourier result.

## Unpaid mathematical interfaces

R10 pays only the original constant-ray radial fifteen-Mobius sum.
The all-$K_A$ principal bound remains $U^{17/8+\varepsilon}$ under
$R_{7/8}$. Neither $S_{\rm actual}=0$ nor $\bar Q_A=0$ is proved.
A nonzero finite/profile factor would not give a lower bound on
$\bar Q_A$, the principal term or the signed physical contraction.
C76, actual finite/profile cancellation, or another sufficient estimate
for this principal scalar remains necessary for this route.

A nonnegative nonzero row cannot annihilate R11's positive row
functional. Replacing it by a signed zero-moment kernel requires an
unproved transfer inequality for the same original positive row energy,
actual coefficient space and paid Type-I consumers. No such redesign
or automatic full-$b$ cancellation is used here. R10 does not turn
upper bounds into a same-realization cancellation identity.

The twisted residual $\mathcal R_{\rm tw}$, the nonexceptional C68
terms, other cores/gcds/bad duals, original common-e signed
detector/rho recombination at the same beta, physical-row restoration
and full J40 height/table aggregation remain unpaid. The original
Type-I coefficient and consumers are retained without new claims.
No selected-Poisson positivity, principal lower bound, stronger
zero-free strip, upstream main-proof certification, signed Robin
restoration or RH conclusion follows. The full research goal remains RH.


## Original-product zeros and finite rectangular residues

Retain exactly C73's $\bar Q_A,\bar H,\bar D_q$ and the original
$W,S$; the results here concern that local principal scalar. They
add finite polar information to R12, without evaluating
$S_{\rm actual}$ or changing R1–R12. Put $L=\log A$ and

$$
N_q(\mathbf z)=1-\frac{2\sum_{i=1}^4q^{-z_i}}{\bar D_q},\qquad
D_q(\mathbf z)=\prod_{i=1}^4(1-q^{-1-z_i})^{-2},\qquad
\bar D_q=q+5+\frac1{q-1}.
\tag{R13}
$$

Thus $\bar H_p=N_{q_p}D_{q_p}$ outside $S$, and
$\bar H_p=D_{q_p}$ inside $S$. These are C73's original factors,
with the four-way exclusive-prime rule; no product of independent
two-slot factors is substituted.

**The finite norm-7 factor.** The fixed arithmetic datum in the
[pinned primary manuscript, notation preceding its additive character](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex)
puts every prime above $6$ in $S$, together with the original fixed
modulus supports. In $K=\mathbb Q(\sqrt{-3})$, $3$ ramifies,
a rational prime $p\equiv1\pmod3$ splits into two primes of norm
$p$, and $p\equiv2\pmod3$ is inert with norm $p^2$.
For example these alternatives follow by factoring
$X^2+X+1$ modulo $p\ne3$: its roots are precisely the nontrivial
cube roots of unity. The primes over $2,3$ are excluded; the next
possible good norm is $7$, followed by $13$ (the inert prime $5$
has norm $25$). In particular no good norm lies below $13$ except
$7$. Define, using the unchanged $S$,

$$
n_7=\#\{p\notin S:q_p=7\}\in\{0,1,2\},\qquad
P_7(\mathbf z)=1-\frac{12}{73}\sum_{i=1}^4 7^{-z_i}.
\tag{R14}
$$

No norm-7 prime is newly excluded. Since $\bar D_7=73/6$, construct
$H_*$ directly as follows: at every unexcluded norm-7 prime use
$D_7$; at other unexcluded primes use $N_qD_q$; at primes in $S$
use $D_q$. This deletes only those finitely many numerators and
never divides by a numerator. Then

$$
\bar H=P_7^{\,n_7}H_*,\qquad
H_*\text{ is holomorphic and nowhere zero near every point of }
\{\Re z_i\ge-1/4\ (1\le i\le4)\}.
\tag{R15}
$$

Indeed for $q\ge13$ throughout that polytube,

$$
|1-N_q|\le\frac{8q^{1/4}}{\bar D_q}<1.
$$

The strict inequality follows from $q+5>8q^{1/4}$: it holds at
$13$, as $18^4>8^4\cdot13$, and the difference has derivative
$1-2q^{-3/4}>0$ thereafter. All denominators are nonzero since
$\Re(1+z_i)\ge3/4$. C73's normal convergence, unchanged by finitely
many factors, and the locally summable deviations from $1$ imply
nonvanishing of the product of these nonzero factors. The strict
bounds and C73's open domain $\Re z_i>-1/2$ also give the asserted
local neighborhoods. Thus R15 identifies the complete zero locus
of $\bar H$ in this polytube: it is empty when $n_7=0$, and is
exactly $P_7=0$ when $n_7>0$.

There are two useful consequences with different scopes. First,
$\bar H$ itself is nowhere zero on $\Re z_i\ge-1/5$: the only
additional check is $8\cdot7^{1/5}<73/6$, equivalently
$7\cdot48^5<73^5$. Second, on a conjugate-balanced tuple,

$$
H_*(a,a,\bar a,\bar a)>0\qquad(\Re a\ge-1/4).
\tag{R16}
$$

For each remaining good numerator its value is
$1-8q^{-\Re a}\cos(\Im a\log q)/\bar D_q>0$.
The denominator at every prime is $|1-q^{-1-a}|^{-8}>0$;
removed norm-7 numerators leave only this denominator. Normal
convergence makes the positive product strictly positive. This is a
statement about the Euler correction, not positivity of the physical
contraction or a selected Poisson component.

**A genuine one-coordinate polar slice.** Suppose $\varrho$ is a
zero of this same $\zeta_K$, of multiplicity $m\ge1$, with
$3/4\le\Re\varrho<1$, and set $a=\varrho-1$.
Fix arbitrary $z_2,z_3,z_4$ with $\Re z_j\ge1$. In this slice
$\bar H(a,z_2,z_3,z_4)\ne0$: at every good prime $q\ge7$,

$$
|1-N_q|\le\frac{2(q^{1/4}+3/q)}{\bar D_q}<1,
$$

because $2q^{1/4}<q$ and $6/q<5$. The same nonzero-product
argument applies, including norm $7$. The other three reciprocal
zeta factors are nonzero since their arguments have real part at
least $2$. Consequently C73's $\bar F$ has a pole of exact order
$2m$ in $z_1$ at $a$ on this slice. For its cutoff integrand below,
the order is $2m-v$ if $\widehat W$ has vanishing order $v<2m$
at $a$ and the other three cutoff values are nonzero; if $v\ge2m$
the singularity is removable. In particular the original cutoff's
nonvanishing at $a$ is an explicit sufficient hypothesis for a genuine
order-$2m$ pole. No such zero or cutoff nonvanishing is asserted to
exist. This rules out an automatic Euler-numerator cancellation of
all these zero divisors, without asserting noncancellation at every
four-zero intersection.

**All finite faces and residues.** Reuse the finite-contour principle
of [SV5 and its retained remainder](../ArithSums/srivastav2025sievevaughan.md#fixed-truncation-mellin-interface-and-remaining-source-coupling)
for the present original four-variable integrand

$$
G_A(\mathbf z)=\bar H(\mathbf z)
 \prod_{i=1}^4\left[\widehat W(z_i)A^{z_i}
                         \zeta_K(1+z_i)^{-2}\right],\qquad
\bar Q_A=\frac1{(2\pi i)^4}\int_{(c)^4}G_A(\mathbf z)\,d\mathbf z,
\quad c>0.
\tag{R17}
$$

The inversion is initially absolute, using C73. Fix $0<h<1/2$,
write $b=-h$, and take a finite $T>0$ for which the boundary of
$[b,c]+i[-T,T]$ meets no zero of $\zeta_K(1+z)$.
Let $\mathcal Z$ be its finite set of distinct interior zero
positions $a=\varrho-1$, recording each zero's multiplicity
separately. The only possible polar divisors of $G_A$ in this
rectangle product are these coordinate divisors. At $z_i=0$ the
simple pole of $\widehat W$ is canceled by the double zero of the
reciprocal zeta square, as in C74; there is no zero-position residue
at $0$ and no mixed polar divisor.

For a meromorphic function $f$, let the following operators act only
in coordinate $i$:

$$
\begin{aligned}
I_{b,i}f&=\frac1{2\pi i}\int_{b-iT}^{b+iT}f\,dz_i,
& Z_if&=\sum_{a\in\mathcal Z}\operatorname{Res}_{z_i=a}f,\\
H_{+,i}f&=\frac1{2\pi i}\int_{b+iT}^{c+iT}f\,dz_i,
& H_{-,i}f&=\frac1{2\pi i}\int_{b-iT}^{c-iT}f\,dz_i.
\end{aligned}
$$

Both horizontal integrals are oriented left to right. The full exact
finite-height identity is

$$
\begin{aligned}
\bar Q_A
 &=\sum_{E\sqcup B\sqcup C_+\sqcup C_-=[4]}
 (-1)^{|C_-|}
 \left(\prod_{i\in E}Z_i\right)
 \left(\prod_{i\in B}I_{b,i}\right)
 \left(\prod_{i\in C_+}H_{+,i}\right)
 \left(\prod_{i\in C_-}H_{-,i}\right)G_A+E_T,\\
E_T&=\frac1{(2\pi)^4}
 \int_{\mathbb R^4\setminus[-T,T]^4}
 G_A(c+it_1,\ldots,c+it_4)\,d\mathbf t,\\
|E_T|&\ll_{N,c,K,S,W} A^{4c}(1+T)^{-N}\qquad(A\ge1)
 \quad\text{for each fixed }N.
\end{aligned}
\tag{R18}
$$

The sum runs over all $4^4$ ordered partitions; empty products are
identities. Each $Z_i$ is itself the full finite sum over zero
positions. Thus a term with $k$ residues retains the factor
$(2\pi i)^{-(4-k)}$ from its remaining paths. This includes every
mixed residue/left-line/horizontal contribution, not just the full
corners. To prove it, truncate the original four right lines,
apply $I_{c,i}=I_{b,i}+Z_i+H_{+,i}-H_{-,i}$ successively, and
expand. The one-variable residue theorem gives that sign by the
positively oriented rectangle starting up its right edge. Compact
boundary paths, finitely many interior zeros and absence of mixed
polar divisors justify these finite interchanges and commuting
residues. The tail is only on the original right lines. There
$\bar H$ and the reciprocal zetas are bounded, and R7 gives arbitrary
Mellin decay of the fixed smooth cutoff, proving its displayed bound.
No estimate on a left-strip reciprocal, no infinite zero sum and no
disappearance of horizontal connectors is used. Substitution into R12
retains its exact multiplier $(\bar C/6)U^{13/6}S_{\rm actual}$
and all component-specific physical prefactors, with no new field
residue or unit factor.

**Multiplicity and the coupled derivative.** For a selected residue
coordinate $i$, let $\varrho_i$ have multiplicity $m_i$, put
$a_i=\varrho_i-1$ and define the holomorphic local function

$$
b_i(z)=\widehat W(z)
 \left(\frac{(z-a_i)^{m_i}}{\zeta_K(1+z)}\right)^2,
\qquad
b_i(a_i)=\widehat W(a_i)
 \left(\frac{m_i!}{\zeta_K^{(m_i)}(\varrho_i)}\right)^2.
\tag{R19}
$$

For any subset $E$ the residue at its chosen zero positions is exactly

$$
A^{\sum_{i\in E}a_i}
\left[
 \prod_{i\in E}\frac{(L+\partial_i)^{2m_i-1}}{(2m_i-1)!}
 \left\{\bar H(\mathbf z)\prod_{i\in E}b_i(z_i)\right\}
\right]_{z_i=a_i\ (i\in E)}
\prod_{j\notin E}\left[\widehat W(z_j)A^{z_j}
                              \zeta_K(1+z_j)^{-2}\right].
\tag{R20}
$$

This follows by extracting the coefficient of
$\prod_{i\in E}(z_i-a_i)^{2m_i-1}$ after factoring out the poles
and $A^{\sum a_i}$. Vanishing cutoffs or numerator factors are
already included; $2m_i$ is the possible order, not an assertion
that every intersection has that order.

For four simple zeros, R20 is
$A^{\sum_i a_i}[\prod_i(L+\partial_i)
 \{\bar H\prod_i b_i\}]_{\mathbf a}$.
If every original $\widehat W(a_i)\ne0$, an equivalent explicit
coupled formula is

$$
\begin{aligned}
\operatorname{Res}_{\mathbf z=\mathbf a}G_A
 &=A^{\sum_i a_i}\left(\prod_i B_i\right)
   \left[\prod_i(L+d_i+\partial_i)\bar H\right]_{\mathbf a},\\
B_i&=\frac{\widehat W(a_i)}{\zeta_K'(\varrho_i)^2},\qquad
 d_i=\frac{\widehat W'(a_i)}{\widehat W(a_i)}
                -\frac{\zeta_K''(\varrho_i)}{\zeta_K'(\varrho_i)}.
\end{aligned}
\tag{R21}
$$

Each $d_i$ in the operator is its fixed displayed value; derivatives
act on the full $\bar H$. In particular this is not a product of
four independent one-variable residue constants.

**Nonzero simple corners, including norm-7 resonance.** Suppose
$\varrho=\sigma+i\gamma$ is a simple nonreal zero of $\zeta_K$,
$3/4\le\sigma<1$, and the actual $\widehat W(a)\ne0$ at
$a=\varrho-1$. Such corners enter R18 when $1-h<\sigma$ and
$|\gamma|<T$; the boundary is still required to avoid all zeros.
Since $W$ is real, the conjugate values agree under conjugation. Set $u=7^{-a}=x+iy$, $k_7=12/73$,
$c_7=k_7\log7$, and $B_\varrho=\widehat W(a)/\zeta_K'(\varrho)^2$.
For the ordered balanced corner
$\mathbf a=(a,a,\bar a,\bar a)$ write
$P=P_7(\mathbf a)=1-4k_7x$ and
$V=H_*(\mathbf a)|B_\varrho|^4>0$.
Its residue is $A^{4(\sigma-1)}$ times a real polynomial in $L$.
Its degree and leading coefficient are

$$
\begin{array}{c|c|c}
\text{condition}&\text{degree}&\text{leading coefficient}\\ \hline
n_7=0\text{ or }P\ne0&4&P^{n_7}V\\
P=0,\ n_7=1&3&(\log7)V\\
P=0,\ n_7=2&2&4c_7^2(3x^2+y^2)V .
\end{array}
\tag{R22}
$$

In the first row $P^0=1$, even at $P=0$. All listed coefficients
are nonzero. To see the resonant rows directly, $\partial_iP_7=c_7u_i$
and $\partial_i\partial_jP_7=0$ for $i\ne j$. When $P=0$,
$\sum_i\partial_iP_7=\log7$. For $P_7^2$, the first nonzero
squarefree derivative sum is

$$
\sum_{i<j}\partial_i\partial_j(P_7^2)
 =2c_7^2\sum_{i<j}u_i u_j
 =4c_7^2(3x^2+y^2),\qquad
(u_1,u_2,u_3,u_4)=(u,u,\bar u,\bar u).
$$

Every smaller derivative of $P_7^{n_7}$ vanishes at resonance, so
the highest surviving power of $L$ places exactly $n_7$ derivatives
on that factor. Derivatives of $H_*$ and $b_i$ then affect only
lower powers. Resonance forces $x=73/48>0$, proving the last
coefficient is nonzero. Conjugation followed by slot permutation
fixes the balanced residue, proving reality. The six distinct
permutations have equal residues by symmetry of the original product
and cutoff, so their sum is six times this same polynomial.

For the repeated simple-zero corner $(a,a,a,a)$ the residue is
$A^{4a}$ times a complex polynomial. Put
$P=1-4k_7u$ and $V'=H_*(a,a,a,a)B_\varrho^4\ne0$.
Away from resonance (or when $n_7=0$), its degree is $4$ with
leading coefficient $P^{n_7}V'$. At $P=0$, $u=73/48$; its degree
and leading coefficient are $3,(\log7)V'$ for $n_7=1$, and
$2,\tfrac34(\log7)^2V'$ for $n_7=2$. The latter follows from
$2\sum_{i<j}c_7^2u^2=12c_7^2u^2=\tfrac34(\log7)^2$.
No extra factorial arises from repeating the zero in distinct
coordinates. Multiplicity of a zero of $\zeta_K$ itself is instead
handled by R19–R20. These corner statements are conditional on
simplicity and the original cutoff value; neither is inferred from
$R_{7/8}$. They do not show that the sum over other zeros, mixed
paths and all common-scale signed components is nonzero or large.

**Domain at the requested depth.** R15 covers a rectangle product
of depth $h=249/1000<1/4$. In C76's formal exponent arithmetic,
$12\Delta=20\sqrt6-48$, and, for the positive margin
$\nu=1/3000$,

$$
4h-12(\Delta+\nu)=\frac{6124}{125}-20\sqrt6
 =0.002205144336438\ldots>0,
\qquad 6124^2-6\cdot2500^2=3376>0.
\tag{R23}
$$

Thus the original-product factorization reaches a depth that would
be sufficient if the entire R18 expression admitted the corresponding
power bound. This is domain applicability only. The $\bar H$
nonvanishing tube of depth $1/5$ reaches only the formal all-line
exponent $4/5$; it gives no reciprocal-zeta strip or contour bound.
No left-line, mixed-residue or horizontal estimate at the deeper
rectangle is supplied. In particular no such bound is deduced from
$R_{7/8}$, and no limit $T\to\infty$ is taken here.

**Primary comparison and remaining consumer.** The following mappings
concern this zero-sensitive interface; they do not repeat R11's
settled Riesz normalization or replace the original profiles.

- Goldston–Pintz–Yildirim, [*Primes in Tuples I*, v1, Proposition 1,
  (2.14), (7.7)–(7.9)](https://arxiv.org/html/math/0508185v1),
  concerns integer tuple means with $M=k_1+k_2+\ell_1+\ell_2$,
  $R\ll N^{1/2}(\log N)^{-4M}$ and $h\le R^C$. Its main term is
  $N\binom{\ell_1+\ell_2}{\ell_1}(\log R)^{r+\ell_1+\ell_2}
  \mathfrak S/(r+\ell_1+\ell_2)!$, with $\mathfrak S$ replaced by
  $\mathfrak S+o_M(1)$. Setting $R=A,k_i=2$ matches an inverse-zeta
  square, but its shared-prime factor $p^{-1-s_1-s_2}$ is forbidden
  here; its logarithmic cutoff has Mellin pole order
  $k_i+\ell_i+1\ge3$, whereas the original $W$ has order $1$.
  Matching that order would require $\ell_i=-2$, outside its scope.
- Reuse [SV38's GKM supplier](../ArithSums/srivastav2025sievevaughan.md#a-published-moment-obstruction-applies-to-the-original-linear-factor).
  In Granville–Koukoulopoulos–Maynard, [v4, Theorems 1.3–1.4 and
  (8.5)–(8.6)](https://arxiv.org/html/1606.06781v4), the moment
  exponent at $2k=4$ is $\max\{2-4m,-1\}$ for integer smoothing
  index $m\ge0$. For a fixed real $C^m$ profile supported in
  $(-\infty,1]$, with bounded derivatives through $m>3/2$ and
  $f(0)\ne0$, Theorem 1.4(a) gives
  $c_{2,f}/\log R+O((\log R)^{-2+\varepsilon})$ when
  $x\ge R^4\log^2R$. Its local factor
  $1+p^{-1}\sum_{\varnothing\ne I\subseteq[4]}
  (-1)^{|I|}p^{-\sum_{i\in I}s_i}$ permits all divisor overlaps,
  unlike R13. Moreover $f_R(t)=W(R^t/A)$ with $R=2A$ has a
  transition width $\log2/\log R$, so its derivative bounds grow
  with $R$; it is not the theorem's fixed-profile family.
- Chen An, [*A Generalization of Graham's Estimate on the
  Barban–Vehov Problem*, v1, Theorem 1.1](https://arxiv.org/html/2206.10104v1),
  does allow $k=K$ and $1\le w<y\le x$, but its weights are
  $\mu_k(d)$ times the plateau/logarithmic ramp from $w$ to $y$.
  Its ideal mean square is $x/\log(y/w)+
  O_{[k:\mathbb Q],\mathrm{disc}(k)}(C_{\beta_0}x/\log^2(y/w))$,
  where $C_{\beta_0}=(1-\beta_0)^{-6}
  \min\{1,|\zeta_k'(\beta_0)|\}^{-2}$ if the specified Siegel
  zero exists, and $1$ otherwise. The square permits shared
  divisors and lacks both $2^{\omega}$ and the four-way mask;
  neither this cutoff nor its logarithmic saving supplies C76.
- Hu–Kaneko–Martin–Schildkraut, [*On a Mertens-type conjecture for
  number fields*, v2, Lemma 2.4, Proposition 2.12 and
  Theorem 1.4](https://arxiv.org/html/2109.06665v2), has the correct
  abelian field class. Its chosen heights and formula with residues
  $x^{\varrho}/(\varrho\zeta_K'(\varrho))$ assume RH for
  $\zeta_K$ and, for the formula, simple nontrivial zeros.
  The limiting-distribution theorem additionally assumes
  $\sum_{0\le\gamma\le T}|\zeta_K'(1/2+i\gamma)|^{-2}
  \ll_\alpha T^{1+\alpha}$ for $0\le\alpha<2-\sqrt3$.
  Those premises do not follow from $R_{7/8}$; a single reciprocal
  also does not provide estimates for the present four coupled
  reciprocal squares. None of these global conclusions is invoked
  in R18–R22.

The finite identity and its nonzero conditional corners specify what
a deeper contour argument must retain. A direct theta improvement
still needs estimates for their joint sum and all finite faces;
merely choosing a deeper line adds no saving. The alternative with
direct payoff is evaluation or cancellation of the actual R12 scalar.
The pinned definitions provide a functional, not that instantiated
full-J40 value. The missing operands are the complete actual
$a(d_1,d_2)$ and $\Omega_{\epsilon,\mathbf r}$ of C57–C59 and
R12's signed component/height measure. At their producer this must
retain J28's $\delta_i,\zeta_i,\rho(w),\chi_w(f_0r)$ and bad-dual
conjugates, the same beta and common $e$ with its Mobius sign,
both core/occupancy allocations, the original $\ell,r$ terms and
J40's selector $q_{r_2(m_{\rm good})}>U^{1/8}$. The actual row and
column Mellin values, all physical prefactors and the one common
absolute height envelope must accompany them. C59's
corefree/common-$e=1$ branch and R11's documented J4 diagonal do
not supply that full aggregate. No arbitrary profile, $h^{-2}$
diagonal substitution or redesigned cutoff evaluates it.

A smallest next mathematical consumer is a bound or actual signed
cancellation of R18's retained zero/face contributions at this depth,
or an instantiated cancellation of $S_{\rm actual}$. The first is
accepted only with its original cutoff, multiplicities and all
boundaries paid; the second only from the original full signed
operands and common envelope. An omitted face, an assumed cutoff
value or substitution of a different overlap law invalidates the
corresponding claim. Until one such estimate or cancellation is
proved, doing nothing and the present finite representation share
the same unresolved principal exponent; the representation adds
explicit polar data rather than a new bound. No principal lower
bound, global asymptotic, isolated-pair spectral corollary, full-$b$
cancellation, upstream-proof certification, signed Robin restoration
or RH conclusion is asserted. These are repo-derived paper deductions,
not Lean or CI evidence, and no priority claim is made.
