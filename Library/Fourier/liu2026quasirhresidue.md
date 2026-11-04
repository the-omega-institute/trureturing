---
bibkey: liu2026quasirhresidue
authors: Baiying Liu
year: 2026
title: Joint mixed-Mobius estimates and the actual exceptional residue interface
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Repo-derived conditional joint Mellin bounds pay the fifteen radial mixed-Mobius terms; fixed-cutoff polygonal localization pays the all-left and outer-face remainders of the original all-K scalar, retaining its fifteen coupled residue terms. A separately redesigned BPY Mellin cutoff and the actual bare-J4 finite-ray table pay the conditional local nonzero exceptional branch with one common budget; the original scalar, generalized angular factors and full signed J40 contraction remain unresolved.
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
Labels R1–R46 belong only to this companion; C1–C76 retain their scope.

Keep $K=\mathbb Q(\sqrt{-3})$, its original finite bad set $S$, ideals
counted once, $D=U^{1/2}$, $A=U^\alpha$, $0<\alpha<1/4$, and the
original real smooth cutoff $W$ of C37. On precisely the original
inverse annulus, $b_A=\mu+K_A$, where
$K_A(d)=\sum_{e\mid d}\mu(e)2^{\omega(e)}W(q_e/A)$.
The four-way squarefree product, every coprimality puncture, raw
sextic/cubic zero extension, profiles, signed coefficients and common
beta remain those of C59. Here $P$ is a squarefree puncture outside
$S$; in the frequency application it is $P_a$ of C58, not the
product-squarepart parameter of J40. R1–R42 introduce no nonprincipal
inverse-Hecke premise; R43–R46 separately state the fixed finite-order
suppliers for the bare-J4 residual. No new column coefficient is introduced.

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

Outside the bare-J4 finite-table application R43–R46, the twisted
residual $\mathcal R_{\rm tw}$ remains unpaid. The nonexceptional C68
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
power bound. R23 alone is domain applicability only. The $\bar H$
nonvanishing tube of depth $1/5$ reaches only the formal all-line
exponent $4/5$; it gives no reciprocal-zeta strip or contour bound.
The polygonal application below pays the regular boundaries while
retaining the complete finite residue aggregate. It does not deduce
a deeper zero-free strip from $R_{7/8}$ or take an infinite-height
residue limit.

## Fixed-cutoff polygonal localization of the original scalar

This is a source-specific `repo-derived` paper application of the
published Buck/Jensen supplier already recorded at
[LC168–LC182](../Analytic/romik2021orthogonal.md#exact-finite-jensen-error-and-the-published-exceptional-disc-floor):
Matthew Buck, *Integer points of meromorphic functions*,
[DOI 10.1017/S0013091513000436](https://doi.org/10.1017/S0013091513000436),
Lemma 2.4, equation (2.2), Remark 2.3, and the Jensen inequality
used there. No new exceptional-disc theorem is proposed. Keep every
coefficient and the ideal mask of C73, the same $K,S$, and **any
fixed original admissible smooth $W$**. Constants may use finitely
many of its seminorms for each requested error power. No Gevrey
condition, zero simplicity, zero spacing, derivative floor, RH or
ordinary-zeta reciprocal-height supplier is used.

**Dedekind normalization and the local supplier.** Write
$g(s)=(s-1)\zeta_K(s)$, an entire function, and for every integer $n$
put $\tau_n=n+1/2$, $Q_n=3+|\tau_n|$ and

$$
p_n(w)=\frac{g(2+i\tau_n+w)}{g(2+i\tau_n)},\qquad
p_n(0)=1,\qquad
\max_{|w|\le16}|p_n(w)|\le V_n=CQ_n^{B_0},\quad V_n\ge2.
\tag{R24}
$$

Here $C,B_0$ are fixed, independent of $n,A,W$. The upper-growth
input is precisely the unconditional fixed-field strip growth used
in R6–R8 and C74, now on $-14\le\Re s\le18$ for the regularized
$g$. For this degree-two field the completed function is
$(\sqrt3/(2\pi))^s\Gamma(s)\zeta_K(s)$ with functional equation
$s\leftrightarrow1-s$; its strip upper bounds and the absolutely
convergent right-half-plane Euler product supply a finite polynomial
degree on that fixed strip. The pole at $1$ has been removed before
taking the maximum, including the bounded-height windows. On the
normalizing line the same Dedekind Euler product gives
$\zeta_K(2)^{-1}\le|\zeta_K(2+i\tau_n)|\le\zeta_K(2)$,
so $|g(2+i\tau_n)|\asymp Q_n$. Thus this is a Dedekind-specific
normalization; it imports no lower bound inside the zero strip.

In Buck's notation take $u=1/p_n$, scale $s=2$, zero-count parameter
$m=0$, and $\epsilon=r/48$, where $r=10^{-6}$ is fixed. Jensen's
identity, with zero additive constant because $p_n(0)=1$, gives
$T(16,1/p_n)=T(16,p_n)\le\log V_n$. Lemma 2.4 consequently supplies
a finite union $U_n$ of open discs in the $w$ plane, of total radius
at most $48\epsilon=r$, such that

$$
|p_n(w)|\ge V_n^{-k},\qquad |w|\le4,\quad w\notin U_n,
\qquad k=6+\frac{\log(48/r)}{\log2}.
\tag{R25}
$$

The accompanying Jensen count is
$n(4,1/p_n)\le\log V_n/\log4$, with multiplicities; poles of
$1/p_n$ count zeros of $g$, not the removed zeta pole. In particular
every such zero in $|w|\le4$ belongs to $U_n$. Translate these discs
to the $z$ plane by $z=1+i\tau_n+w$, and call their union $E_n$.
Its real and imaginary projections each have total interval length
at most $2r$. For $-249/1000\le\Re z\le1$ and
$|\Im z-\tau_n|\le1$, the corresponding $|w|<2<4$. Outside $E_n$,
R24–R25 and
$\zeta_K(1+z)^{-1}=z/g(1+z)$ therefore give, for one fixed $B$,

$$
|\zeta_K(1+z)^{-1}|\le C Q_n^B
 \le C'(3+|\Im z|)^B.
\tag{R26}
$$

The formula at $z=0$ is interpreted by continuation and equals zero.
Indeed $|z|\ll Q_n$ and $|g(2+i\tau_n)|\gg Q_n$, so one may take
$B=B_0k$ after adjusting the fixed constant.
This polynomial bound holds on the chosen complement, including
low heights. It is not a polynomial bound on a complete zero-bearing
vertical line. The arbitrarily close zeros and their full
multiplicities remain inside the exceptional discs.

**An actual finite polygon, with bounded local length.** Set

$$
h_0=\frac{497}{2000},\qquad h_1=\frac{249}{1000},\qquad
I=(-h_1,-h_0),\qquad H=\lceil A\rceil+4\quad(A\ge2).
$$

Use the finite collection $E_n$, $-H-1\le n\le H$.
For each $-H\le n<H$ choose
$x_n\in I\setminus\pi_{\Re}(E_n)$; this is possible since
$|I|=1/2000>2r$. For $-H<n<H$ choose
$y_n\in(n-1/8,n+1/8)$ outside the imaginary projections of
$E_{n-1}\cup E_n$. Their total length is at most $4r<1/4$.
Choose a **single** $T\in(H-1/8,H+1/8)$ outside the imaginary
projections of $E_{H-1}\cup E_H$ and the negatives of the imaginary
projections of $E_{-H-1}\cup E_{-H}$. The excluded length is at
most $8r<1/4$. Put $y_{-H}=-T$, $y_H=T$. All choices can be made
outside the closed projection intervals as well, since their finite
total lengths have these strict margins.

Define $\Gamma_A$ upwards: in slab $n$ take the vertical segment
$[x_n+iy_n,x_n+iy_{n+1}]$; at each internal $y_n$ join
$x_{n-1}+iy_n$ to $x_n+iy_n$ horizontally. Each vertical segment
avoids $E_n$ by its real coordinate, and each join avoids both
adjacent unions by its height. All these segments have
$|\Im z-\tau_n|\le5/8$ in at least one of their stated windows.
R26 therefore holds on the entire path. The two outer horizontal
segments from its endpoints to $1\pm iT$ also avoid the relevant
unions, so R26 holds on them as well. The right side is
$[1-iT,1+iT]$, where the Euler-product reciprocal bound already
holds without disc deletion.

The heights $y_n$ strictly increase, by at least $3/4$. Distinct
vertical interiors occupy disjoint height intervals; horizontal
joins meet only their adjacent vertical endpoints. Removing a
zero-length join if necessary, $\Gamma_A$ is thus simple and meets
neither outer segment except at its own endpoint. Together with the
right side and outer segments it bounds a simple polygon
$\Omega_A$, oriented positively by going up the right side. There
are no holes or additional boundary components. Every boundary point
has $-h_1<\Re z\le1$; the entire closed polygon is in
$\Re z>-1/2$. In any height interval of length one there are at
most three vertical pieces, with total vertical length at most one,
and at most three joins, each of length less than $1/2000$.
In particular its local arclength is bounded by $2$, uniformly in
$A,H$, the discs and the choices. Its total length is $O(T+1)$,
and $T\asymp A$ is finite for every $A\ge2$.

Let $\mathcal Z_A$ be the distinct positions $a=\varrho-1$ with
$a\in\Omega_A$ and $\zeta_K(\varrho)=0$, retaining each
multiplicity $m_\varrho$. This is a finite set: $g$ is nonzero as
an entire function, the closed polygon is compact, and R26 excludes
boundary zeros. Membership is **in this polygon's actual interior**,
equivalently winding number one for its boundary, not the conditions
$\Re\varrho>1-h_0$ or $>1-h_1$ in a replacement rectangle.
Zeros in the narrow intervening band are selected by the actual
vertical segments and joins. All four coordinates use this same
polygon, zero set and top/bottom heights.

**Finite identity, with all fifteen terms.** For coordinate $i$ let
$J_i=(2\pi i)^{-1}\int_{\Gamma_A}dz_i$, let
$Z_i=\sum_{a\in\mathcal Z_A}\operatorname{Res}_{z_i=a}$, and let
$\ell_{\pm,A}$ be the segment from the corresponding endpoint of
$\Gamma_A$ to $1\pm iT$, left to right. Let $H_{\pm,i}$ integrate
over that segment with factor $(2\pi i)^{-1}$.
Let $I_{1,i}$ be the truncated upward right integral. The polygonal
residue theorem gives exactly
$I_{1,i}=J_i+Z_i+H_{+,i}-H_{-,i}$. Define

$$
\begin{aligned}
P_A&=\sum_{\varnothing\ne E\subseteq[4]}
       \left(\prod_{i\in E}Z_i\right)
       \left(\prod_{j\notin E}J_j\right)G_A,\\
L_A&=\left(\prod_{i=1}^4J_i\right)G_A,\\
C_A&=\sum_{\substack{E\sqcup B\sqcup C_+\sqcup C_-=[4]\\
                         C_+\cup C_-\ne\varnothing}}
 (-1)^{|C_-|}
 \left(\prod_{i\in E}Z_i\right)
 \left(\prod_{i\in B}J_i\right)
 \left(\prod_{i\in C_+}H_{+,i}\right)
 \left(\prod_{i\in C_-}H_{-,i}\right)G_A,\\
\bar Q_A&=P_A+L_A+C_A+E_T.
\end{aligned}
\tag{R27}
$$

Here $E_T$ is exactly R18's original right-line tail with $c=1$.
The fifteen $P_A$ terms have sizes $4,6,4,1$ for residue-subset
cardinalities $1,2,3,4$, all with positive operator sign. A term of
cardinality $k$ has exactly $(2\pi i)^{-(4-k)}$ on its remaining
paths. Each coordinate residue operator includes **every** zero
position in $\mathcal Z_A$. Formula R20 applies without alteration,
with arbitrary multiplicities and derivatives of the full coupled
$\bar H$. It allows vanishing cutoff values and Euler numerators;
no individual residue or inverse derivative is estimated here.

The cancelled product at $z_i=0$ remains holomorphic, as in R17–R18.
C73 puts $\bar H$ holomorphic on a neighborhood of the entire
closed polygon product, with no mixed polar divisors. Successive
one-coordinate Cauchy deformations on compact paths consequently
prove R27, and the finite residues commute. There is no omitted
cutoff residue, no change of mask, and no infinite zero sum.

**Payment of the all-left term and every outer face.** On
$\Gamma_A$, both outer segments and the right side put
$v_A(z)=|\widehat W(z)A^z\zeta_K(1+z)^{-2}|$.
R7 and R26, the local-length bound, and the fixed distance of the
left band from zero give

$$
\begin{aligned}
\int_{\Gamma_A}v_A(z)|dz|&\ll A^{-h_0},\\
\int_{[1-iT,1+iT]}v_A(z)|dz|&\ll A,\\
\int_{\ell_{\pm,A}}v_A(z)|dz|&\ll_M A(1+T)^{-M}
                       \quad\text{for every fixed }M>0.
\end{aligned}
\tag{R28}
$$

For example on the left choose a Mellin decay order larger than
$2B+2$ and sum the weights over unit-height intervals. On an outer
segment use the same uniform strip decay at height $T$ with order
larger than $2B+M$; its length is at most $1+h_1$ and $A^{\Re z}\le A$.
The original right side uses its Euler-product bound and R7. These
arguments use the fixed smooth cutoff's arbitrary polynomial decay,
without an exponential-decay or varying-cutoff assertion. C73 gives
a uniform bound for $\bar H$ throughout the fixed real polytube
$[-h_1,1]^4$, independently of all heights. It follows at once that
$|L_A|\ll A^{-4h_0}=A^{-497/500}$.

To pay a face containing residues, keep each $Z_i$ as its **whole**
finite operator and replace it by
$I_{1,i}-J_i-H_{+,i}+H_{-,i}$ on the closed boundary.
Its weighted contour mass is $O(A)$ by R28, uniformly in the
number, closeness and multiplicities of the enclosed zeros. After
this replacement in any term of $C_A$, at least one outer segment
remains and all other factors have weighted mass $O(A)$.
The uniform bound for the coupled $\bar H$ then proves

$$
|C_A|+|E_T|\ll_M A^4(1+T)^{-M},\qquad
\bar Q_A=P_A+O_{K,S,W}(A^{-497/500}),
\quad A\ge2.
\tag{R29}
$$

More precisely R27 retains $L_A$ exactly, and for every prescribed
$D>0$ the combined outer-face and original right-tail error is
$O_{D,K,S,W}(A^{-D})$: use $T\asymp A$ and $M>D+4$.
The contour and $P_A$ need not change with $D$; only the fixed
cutoff seminorms used in the estimate increase. This bounds the
complete finite faces, including those with several residue
coordinates, without summing absolute values of individual residues
or assuming a lower bound on any $\zeta_K^{(m)}(\varrho)$.

**The exact signed physical consumer.** R29 is unconditional for the
scalar C73 with fixed $K,S,W$. For R12 retain its source-conditional
$R_{7/8}$, original profiles, coefficient tables and common absolute
component/height envelope; those are premises of its existing
evaluation and other errors. With the same $A=U^{1/12}$, R27 gives
the exact substitution of $P_A+L_A+C_A+E_T$ for $\bar Q_A$ in R12.
In particular

$$
\begin{aligned}
\mathcal E_{\rm rad}
 &=\frac{\bar C}{6}U^{13/6}P_A S_{\rm actual}\\
 &\quad+O_{K,S,W}\!\left(
       \left|\frac{\bar C}{6}\right|
       U^{13/6}|S_{\rm actual}|A^{-497/500}\right)\\
 &\quad+O_\varepsilon\!\left(\mathcal N_J
 [U^{199/96+\varepsilon}+U^{47/24+\varepsilon}
                              +U^{95/48+\varepsilon}]\right).
\end{aligned}
\tag{R30}
$$

The multiplier is exactly R12's $(\bar C/6)U^{13/6}S_{\rm actual}$,
with the signed common-height aggregate still defined there, including
its individual $C_{w_c},M_{i,c},\eta_{\epsilon,\mathbf r,c}$ and
$d_{\mathbf r}^{-1/6}$. There is no extra field residue, unit factor,
absolute-mass replacement in the leading term or diagonal
substitution. An original additional physical prefactor multiplies
its own complete identity and errors; different local branches keep
their own constants and scalars. For a sharper outer-face account
the new error in R30 is the modulus of that exact multiplier times
$O(A^{-497/500})+O_D(A^{-D})$, with $L_A$ itself available in R27.

The absolute envelope already required by R12 bounds
$|S_{\rm actual}|\ll\mathcal N_J$ through R11's profile moments.
Under that same budget the new remainder has power
$U^{13/6-497/6000}=U^{12503/6000}$, times the original prefactors.
For the specific margin $\nu=1/3000$ of R23 it is below C76's local
target, since

$$
\frac{497}{500}-12(\Delta+\nu)
 =\frac{4899}{100}-20\sqrt6>0,
\qquad 4899^2-6\cdot2000^2=201>0.
\tag{R31}
$$

Any polylogarithmic envelope or stated $\varepsilon$ loss must be
allocated inside this positive margin, divided by $12$ on the
$U$ scale, and the existing R12 errors keep their stated losses.
This pays the regular remainder, not the principal scalar: there
is **no bound here on $P_A S_{\rm actual}$**, no evaluation of the
full signed aggregate, and no improvement of the principal exponent.
The finite polygon-dependent $P_A$ contains all fifteen coupled
zero/remaining-path terms, including every complete four-zero
corner. They cannot be discarded or replaced by an isolated balanced
corner. A sufficient next input is a bound for this full aggregate
at the C76 scale, with its actual signed physical multiplier, or a
proved cancellation of the original $S_{\rm actual}$. The paid
remainder does not imply either input, signed Robin restoration or RH.

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
a deeper contour argument must retain. R27–R29 pay its regular
all-left, outer-face and original right-tail contributions at the
stated polygonal depth. A direct theta improvement still needs an
estimate for the full retained $P_A$ or its actual signed physical
consumer. The alternative with direct payoff is evaluation or
cancellation of the actual R12 scalar.
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

A next mathematical consumer is a sufficient bound or actual signed
cancellation of the complete $P_A S_{\rm actual}$ in R30, or an
instantiated cancellation of $S_{\rm actual}$. The first retains the
original cutoff, polygon-dependent zero membership, multiplicities
and all fifteen terms; the second uses the original full signed
operands and common envelope. An omitted term, an assumed cutoff
value or substitution of a different overlap law invalidates the
corresponding claim. R29 pays a remainder without changing the
unresolved principal exponent. No principal lower
bound, global asymptotic, isolated-pair spectral corollary, full-$b$
cancellation, upstream-proof certification, signed Robin restoration
or RH conclusion is asserted. These are repo-derived paper deductions,
not Lean or CI evidence, and no priority claim is made.


## A source-Mellin dilation cutoff on the same polynomial

This application reuses the classical BPY laws and the analytic suppliers
of C25, C29, C37, C40, C54 and C59–C75. It changes the internal divisor
cutoff, not the physical row, inverse polynomial, frequency selectors or
component/height budget. Write $W_0$ for the original fixed $W$ throughout
R1–R31. Those statements, in particular the original-cutoff R27–R31 and
its retained fifteen-term residue aggregate, are unchanged. The result
below is a conditional paper application, with no new probability law,
residue computation, priority claim or Lean certification.

### Source correspondence and finite moment costs

Use Biane–Pitman–Yor, [§2.2, Proposition 1, and §6.1, (92)–(95)](https://arxiv.org/html/math/9912170v1#S6.SS1).
The §2.2 law is $\mathbb E Y^s=2\xi(s)$, with density
$y^{-1}H_{\rm BPY}(y)$ and $\mathbb E Y=1$; $H_{\rm BPY}$ is not the
Euler correction $\bar H$ or the dilation transform below. For the
special real odd character $\chi=\chi_{-3}$ put

$$
\begin{aligned}
\theta_\chi(t)&=\sum_{n\in\mathbb Z}n\chi(n)e^{-\pi n^2t},\qquad
\Lambda_\chi(s)=\pi^{-(s+1)/2}\Gamma((s+1)/2)L(s,\chi),\\
\Lambda_\chi(1)&=\frac1{3\sqrt3},\qquad
\int_0^\infty\theta_\chi(t)t^{(s+1)/2-1}dt=2\Lambda_\chi(s),\\
a&=\frac{\sqrt3}{2\pi},\qquad
F(s)=6s(s-1)a^s\Gamma(s)\zeta_K(s),\qquad F(0)=F(1)=1.
\end{aligned}
\tag{R32}
$$

Here the theta and $\Lambda_\chi$ conventions are exactly BPY (93) and
(95): their $\Lambda_\chi$ has no conductor power. The factor $3^{z/2}$
below supplies it. Also $\zeta_K=\zeta L(\cdot,\chi)$, and
$L(1,\chi)=\pi/(3\sqrt3)$, equivalently
$\sum_{n\ge0}[(3n+1)^{-1}-(3n+2)^{-1}]$.
The Bessel start in BPY §6.1 is $b=1/3$, distinct from $a$ in R32.
For $T_b=T_1^b(R_3)$ their displayed positive hitting-time density,
with this substitution, is

$$
f_{T_b}(t)=\frac{1}{\sqrt{2\pi}\,t^{3/2}}
 \theta_\chi\!\left(\frac{2}{9\pi t}\right).
$$

This gives the needed positivity of this special theta; it asserts no
positivity for general real characters. The normalization is fixed by
this density and (93)–(95), not by the unnumbered Mellin or Laplace
prefactors in §6.1. In particular the normalized theta density used here
is $\theta_\chi(t)/(2\Lambda_\chi(1))$.

For explicit correspondence with the reused laws, let $Y^*$ have the
size-biased §2.2 law $y\,d\mathbb P_Y(y)$ and let $V$ independently have
that normalized theta density. The existing product law
$C_0=Y^*\sqrt{3V}$ has
$\mathbb E C_0^z=2\xi(1+z)3^{z/2}\Lambda_\chi(1+z)/\Lambda_\chi(1)
=F(1+z)$, by gamma duplication. For two independent copies take
$C=C_0C'_0$ and denote its law by $\nu$. Thus the supplier used by this
application is

$$
H(z)=\mathbb E C^z=F(1+z)^2
 =36z^2(1+z)^2a^{2+2z}\Gamma(1+z)^2\zeta_K(1+z)^2.
\tag{R33}
$$

The apparent singularities are removable. The BPY density/theta tails
supply all real positive and negative moments; R33 is their entire
Mellin transform. This paragraph identifies the reused laws and their
scales; it does not replace their construction by an asserted arbitrary
Dirichlet-$L$ probability law.

Fix $\eta=1/100$, $L=U^\eta$, and, for $U\ge1$, set

$$
c_U=\min(L,\max(L^{-1},C)),\qquad
\nu_U=\operatorname{law}(c_U),\quad H_U(z)=\mathbb E c_U^z,\qquad
W_U(t)=\int W_0(t/x)\,d\nu_U(x),\quad A=U^{1/12}.
\tag{R34}
$$

Then $0\le W_U\le1$, $W_U=1$ on $[0,L^{-1}]$ and $W_U=0$ on
$[2L,\infty)$. It is smooth; each logarithmic derivative is bounded by
the corresponding fixed derivative of $W_0$. Its transform is
$\widehat W_U(z)=\widehat W_0(z)H_U(z)$ initially for $\Re z>0$.
The clamp moves toward $1$ and does **not** retain R33's exact zeros.
For any fixed integer $k\ge0$ and $|r|\le1$, a sufficient uniform bound is

$$
\int x^r(1+|\log x|)^k\,d\nu_U(x)
 \le C_k[H(2)+H(-2)],\qquad
C_k=\max\{1,e^{1-k}k^k\},\quad C_0=1.
\tag{R35}
$$

Indeed $(1+t)^ke^{-t}\le C_k$ for $t\ge0$, so the integrand is bounded
by $C_k(x^2+x^{-2})$; clamping decreases this last sum. More generally
$\int(x^P+x^{-P})d\nu_U\le H(P)+H(-P)$ for fixed $P>0$.
All four cutoff coordinates below use the product law $\nu_U^4$,
independent of the original actual signed component/height measure.
A common dilation would instead supply $H(\sum z_i)$ and would not
cancel the four separate inverse-zeta squares.

### The restricted split, support and fixed-$U$ recursion

Write $z_0=(bD)^{1/2}\asymp U^{1/4}$ for the original C25 threshold
($b$ here is its fixed annular endpoint, not the Bessel start). Keep
$D=U^{1/2}$, the original annulus, masks, raw characters and side profiles.
The two complementary coefficients before any collapse are exactly

$$
\begin{aligned}
\lambda_{\mathrm I,U}(d)
 &=-\mu^2(d)\sum_{\substack{rsc=d\\q_r\le z_0,\ q_s\le z_0}}
       \mu(r)\mu(s)W_U(q_{rs}/A),\\
\lambda_{\mathrm{II},U}(d)
 &=-\mu^2(d)\sum_{\substack{rsc=d\\q_r\le z_0,\ q_s\le z_0}}
       \mu(r)\mu(s)[1-W_U(q_{rs}/A)].
\end{aligned}
\tag{R36}
$$

In particular neither complementary sum loses the original separate
$r,s$ restrictions. Since $W_U(q_{rs}/A)\ne0$ implies
$q_{rs}<2AL<z_0$ eventually, the first sum legitimately collapses to
C25's coefficient $-\mu(q)\tau(q)$ on squarefree coprime $(q,c)$.
Thus on the same actual inverse polynomial,
$M_\psi=M_{\mathrm I,U}+M_{\mathrm{II},U}$, with the original $D^{-1/2}$
on each polynomial and the same $V(q_d/D)$.
The complementary coefficient remains squarefree-supported and bounded
in modulus by $\tau_3(d)$, since $0\le1-W_U\le1$.
Its guaranteed exclusion is now

$$
q_{d_{\le z_0}}\le AL^{-1}\ \Longrightarrow\
\lambda_{\mathrm{II},U}(d)=0,
\qquad
b_U(d):=\lambda_{\mathrm{II},U}(d)=\mu(d)+K_{A;U}(d)
\quad\hbox{on the original inverse annulus},
\tag{R37}
$$

where $K_{a';U}(m)=\sum_{e\mid m}\mu(e)2^{\omega(e)}W_U(q_e/a')$.
For the exclusion every allowed $rs$ divides $d_{\le z_0}$, hence its
cutoff is $1$. The annular identity is the same C37 divisor identity,
using $2AL<z_0$. The former guaranteed threshold $A$ is not retained.
These coefficients change outside the excluded set too.

For $p\nmid m$, C37 applied inside the same $\nu_U$ integral gives
$K_{a';U}(pm)=K_{a';U}(m)-2K_{a'/q_p;U}(m)$ and the identical recursion
for $\Lambda_{a';U}=\mu+K_{a';U}$. Keep $U$ and $\nu_U$ fixed on every
cofactor; do not reselect a law at a cofactor scale. As in C38 the
cofactor is only an algebraic extension off the original annulus.
C40's residual survives: for fixed squarefree good $b_0$, eventually
$q_{b_0}\le A/L$; distinct primes outside $b_0$ with $q_p,q_q>2AL$ give
$K_{A;U}(b_0pq)=\mu(b_0)$ and $b_U(b_0pq)=2\mu(b_0)$ on that annulus.
Balanced prime exponents remain $1/4+o(1)$, outside C39's fine-slot
capacities; no coarse-slot or conditional-cofactor estimate is supplied.

### Uniform Type-I transfer with the original Hecke suppliers

Retain **all** [C29 premises](../Analytic/liu2026quasirh.md#combining-two-bounds-on-the-same-buffered-type-i-bin): the buffered upper and reciprocal bounds
for the original Hecke family on the same bins, their original counts
$R(\delta)$, floor $a_0=51/100$, zero-prime-slot nonprincipal plain
fourth moment, polynomial-size complete original deletion masks,
bounded annular lengths, original zero extensions and finite ray
presentations. Principal inducing exceptions have precisely C25–C29's
bounded-support treatment; no general principal plain-moment theorem
is assumed. For a fixed finite twist, a principal inducing character on
the sixth-power-free physical rows has good-prime support inside that
twist support and bounded valuations, hence occurs only at bounded
scales. No new conductor lower bound is introduced. These are
conditional inputs of the pinned primary
manuscript (`lem:buffered-bins`, `lem:detector-dyads`, `lem:plain`,
`lem:logarithmic-control`, `lem:deleted-euler-factors`,
`lem:smooth-calculus`), not consequences of the principal $R_{7/8}$.

For fixed $x\in[L^{-1},L]$, use cutoff $W_0(t/x)$ and dyadic blocks
$Q\le2Ax$, with $C=D/Q$. Their joint logarithmic profiles have uniform
seminorms: on a nonzero block $Q/(Ax)\le2$. The two finite internal
Fourier/Mellin heights share the same fixed fraction of the original
buffer $T_1$ as in C29, with the two local lines at
$\Re s=\Re t=a_{\rm bin}+8e$; tails stay on absolute lines and are paid by its
fixed polynomial growth and chosen decay. The range
$Q\ll U^{1/12+\eta}$ remains a bounded annular polynomial range, with
$Q<D$. There is no larger row-twist allowance or infinite local contour.
Here $\delta=2a_{\rm bin}-1$, and the original counting exponent is
$R(\delta)=(15-16\delta)/(15-6\delta)$ for
$1/50<\delta\le5/6$, and $R(\delta)=1-\delta$ for
$5/6\le\delta\le1$. The local upper and reciprocal estimates
together give the first bound; the inverse-square estimate and the
original full nonprincipal plain fourth moment give the second, after
C26’s summable correction. On that same positive bin quantity this gives

$$
T_{Q,x}(\delta)\ll U^\varepsilon
 \min\{U^{R(\delta)+\delta},\ UQ^{2\delta}\}.
$$

For $\delta\le1/2$, its second branch is at most
$O(U^{13/12+\varepsilon}\max(1,x))$, since $x^{2\delta}\le\max(1,x)$.
For $\delta\ge1/2$, the unchanged first branch is at most
$U^{13/12+\varepsilon}$ by C29. The floor uses
$U(2Ax)^{1/25+O(e)}\ll U^{13/12+\varepsilon}\max(1,x)$.
Choose the bin width, internal losses and buffer exponent in C29's
original order and absorb only the stipulated dyadic/polylog costs.
Linearity followed by Minkowski on this **whole positive** $L^4$ norm
gives

$$
\|M_{\mathrm I,U}\|_4^4
 \ll_\varepsilon
 \left[\int\max(1,x)^{1/4}d\nu_U(x)\right]^4
 U^{13/12+\varepsilon}\ll_\varepsilon U^{13/12+\varepsilon}.
\tag{R38}
$$

The bracket is bounded by $[1+H(1/4)]^4$ independently of $U$.
No maximum-support cutoff $AL$ replaces this final bound. It concerns
the same polynomial and common positive norm; it is not a transfer
inequality for any selected signed radial mask.

### Ideal scalar cancellation and the paid clamp comparison

Let $W_\nu(t)=\int W_0(t/x)d\nu(x)$, a noncompact cutoff. All real
moments give its Mellin transform $\widehat W_0(z)H(z)$ on the starting
half-plane. In the **actual R17**, there is no factor
$1/(1+\sum_i z_i)$. Its one-coordinate inverse-zeta quotient is

$$
G(z):=H(z)\zeta_K(1+z)^{-2}
 =36z^2(1+z)^2a^{2+2z}\Gamma(1+z)^2.
$$

Consequently its fourfold integrand is
$\bar H(\mathbf z)\prod_i[\widehat W_0(z_i)G(z_i)A^{z_i}]$.
The simple cutoff pole at zero is canceled by $z_i^2$. Gamma's poles
are outside $\Re z_i>-1/2$; C73's $\bar H$ is holomorphic and bounded
on smaller closed real substrips there. Stirling supplies exponential
vertical decay, in addition to the fixed smooth cutoff's decay.
Thus absolute inversion and successive shifts of all four lines give

$$
|\bar Q_A[W_\nu]|\ll_h A^{-4h}\qquad(0<h<1/2\ \hbox{fixed}).
\tag{R39}
$$

This shift does not require a deeper reciprocal strip: R33 cancels its
zero divisors identically before shifting. It says nothing analogous
about $H_U$, $W_0$ or the clamped C74 integrand.

Pay the clamp in C73's absolute coefficient sum instead. Put

$$
B_1=\prod_{p\notin S}\left(1+\frac2{q_p\bar D_{q_p}}\right)<\infty,
\qquad p=\lceil100(D_0+1/3)\rceil,\quad D_0>0.
$$

For four fixed positive dilations $x_i$, dropping only coprimality
restrictions after absolute values gives

$$
\sum_{\substack{e_1e_2e_3e_4\ {\rm sf}\\(\prod e_i,S)=1}}
 \frac{\prod_i2^{\omega(e_i)}|W_0(q_{e_i}/(Ax_i))|}
      {\prod_{p\mid e_1e_2e_3e_4}\bar D_{q_p}}
 \le (2A)^4B_1^4\prod_i x_i.
$$

Indeed each coordinate sum is at most
$2Ax_i\sum_{e\ {\rm sf},(e,S)=1}2^{\omega(e)}/(q_e\prod_{p\mid e}\bar D_{q_p})
=2Ax_i B_1$. Couple $x=C$ and its clamp in each of the four independent
coordinates and telescope. On the upper tail,
$\mathbb E[(C+c_U)1_{C>L}]\le2L^{-p}H(p+1)$; on the lower tail it is
at most $2L^{-p}H(-p)$. Each other coordinate has first moment at most
$1+H(1)$. Hence

$$
\begin{aligned}
|\bar Q_A[W_U]-\bar Q_A[W_\nu]|
 &\le128B_1^4(1+H(1))^3[H(p+1)+H(-p)]A^4U^{-p/100}\\
 &\ll_{D_0}U^{-D_0}.
\end{aligned}
\tag{R40}
$$

Here $A^4=U^{1/3}$ is included in the choice of $p$. This compares
absolutely convergent coefficient sums, never divides a small tail by
inverse zeta near a zero, and proves a scalar estimate only for the
redesigned cutoff. It does not bound $\bar Q_A[W_0]$.

### All errors in the same component and height envelope

Take one finite $J$ at least the original C29/C59 profile order and
$J>L_\zeta+8B_\delta+20$, where $L_\zeta$ bounds ordinary zeta growth
and $B_\delta$ is the original $R_{7/8}$ reciprocal-growth exponent on
the smaller strip. Choose $0<\delta<1/80$ within the final epsilon
allocation. Use shell decay order $4$, log moments through
$k=8J+32$, and ordinary/inverse moments through
$P=\max(2,p+1)$. In particular $h=1/3,D_0=1$ in R39–R40 permits
$p=134$, $P=135$; these are fixed moments, not growing orders.

A sufficient common dilation enlargement of the original absolute
profile/component/height envelope is

$$
\widetilde{\mathcal N}_J
 \le C_{J,W_0}[C_k(2+H(P)+H(-P))]^4\mathcal N_J.
\tag{R41}
$$

To see the finite-order cost, put $t=xy$ in each cutoff integral.
Logarithmic differentiation preserves the fixed derivatives of
$W_0(y)$; differentiating a Mellin transform introduces only
$(\log x+\log y)^j$. On its fixed transition interval these are bounded
by R35, with the stated extra orders sufficient for the four transforms,
finite joins and integrations by parts. The ordinary/inverse moments
also cover R40. The same finite $J$ pays the five integrals of C74;
there is no fresh height budget per subset, frequency shell or dilation.
Integrate this one envelope against the absolute value of the original
signed measure before using Fubini or Minkowski. Dilation variables
are independent of that measure, not substitutes for its rows or signs.

More explicitly, the $K$ residue and boundary powers in R8 become,
respectively, $x^{-1/8+\delta}$ and $x^{3/8+2\delta}$.
R35 bounds their log-weighted integrals uniformly; the $\mu$ slots
are unchanged. The original frequency counts, polynomial puncture
range and R9 tail estimate still apply: $|K_{A;U}|\le3^{\omega}$
independently of the enlarged support. Thus the full fifteen-term R10
error remains $O_\varepsilon(\widetilde{\mathcal N}_JU^{199/96+\varepsilon})$.
For C54/C60, each shifted divisor coordinate costs
$(Ax)^{1/2+\delta}$ and each residue coordinate only a small fixed
moment. Averaging the products gives the same
$U^{23/12}A^{1/2}=U^{47/24}$ error; $AL<D$ keeps the $j=1$ term
dominant. For C74–C75 use **only**
$h_0=1/8-\delta$, $\sigma=1/8+\delta$ with $R_{7/8}$.
The clamped Mellin multiplier has modulus at most
$\int x^{\Re z}d\nu_U(x)$, and its required derivatives are paid by
R35. C72's $\sigma-h_0>0$ and the original reciprocal strip therefore
still give $U^{95/48+\varepsilon}$. The deeper $h=1/3$ shift belongs
solely to R39's separately paid ideal scalar.

Finally R12's leading term remains exactly
$(\bar C/6)U^{13/6}\bar Q_A[W_U]S_{\rm actual}$, with R11–R12's
actual individual row and column moments and signed measure. The
original shell envelope $|\Psi_t|\le\mathcal N_J(1+t)^{-4}$ on its
fixed rectangle gives, after its absolute component/height integral,
$|S_{\rm actual}|\le\operatorname{Vol}(\mathrm{rectangle})
\operatorname B(1/6,4-1/6)\mathcal N_J$. No diagonal value or positive
selected-row mass is substituted. R39 with $h=1/3$ and R40 with
$D_0=1$ now give the complete redesigned constant-ray **local** branch

$$
\begin{aligned}
|\mathcal E_{\rm rad,U}|
 &\ll_\varepsilon\widetilde{\mathcal N}_J
 [U^{37/18+\varepsilon}+U^{199/96+\varepsilon}
  +U^{47/24+\varepsilon}+U^{95/48+\varepsilon}+U^{7/6}]\\
 &\ll_\varepsilon\widetilde{\mathcal N}_JU^{199/96+\varepsilon},\\
1+B_*-199/96-1/3000
 &=\frac{393-160\sqrt6}{96}-\frac1{3000}
 =0.010933762028037\ldots>0.
\end{aligned}
\tag{R42}
$$

The constant is independent of $U$ and of admissible actual components
within the same original absolute envelope, but depends on the fixed
source hypotheses, strip margins, profiles and BPY moments specified
above. Choose the internal losses within this reserve to obtain the
registered local target $U^{1+B_*-1/3000+\varepsilon}$.
Every original physical prefactor stays attached to its own component:
the $U^2=D^4$ in C60 is already included, the two original $D^{-1}$
side factors give $D^{-2}=U^{-1}$ when restored, and row/core/gcd,
bad-dual, detector/rho and height factors are not erased or counted
twice. The field measure, six units, $S$ factors, $1/6$, $\bar C$ and
$d_{\mathbf r}^{-1/6}$ retain C56 and R12's normalization.

R38's whole-moment interference supplies only
$C_b=(3B_*+13/12)/4$, whose saving
$(B_*-13/12)/4=0.000212607173676\ldots<1/3000$.
It cannot be assigned to a selected signed radial mask. Accordingly
R42 supplies neither an original-$W_0$ scalar bound nor a signed
cutoff-change estimate. R43–R46 below treat only the bare-J4 finite-ray
residual. Generalized additional finite/angular factors, C68
nonexceptional terms, other cores/gcds/bad duals, original common-beta
signed detector/rho recombination, physical-row restoration and full
J40 component/height aggregation
remain unresolved. The BPY law and this application do not certify
its conditional Type-I or $R_{7/8}$ suppliers, the upstream main proof,
Robin or RH.

## The finite-ray residual of the documented bare J4 diagonal

This application concerns exactly R11's J4 diagonal, with $\zeta_i=1$,
fixed total class $\sigma$, and no additional angular multiplier. Keep
C58–C59's corefree/common-$e=1$, $C=1$, nonzero-exceptional realization,
all original signs, masks, six units, $S$ exponents, frequencies and
profiles. It uses finite character orthogonality and R3–R9's joint
contours, not a new character estimate. The analytical premises are the
pinned [primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
`thm:main`, `lem:hecke-strip-growth` and `lem:logarithmic-control`:
finite-order zero-freeness in $\Re s>\beta_H=7/8$, polynomial upper
bounds on the $s$ strips, and polynomial reciprocal bounds on every
smaller closed right strip. Both upper and reciprocal control are used.
They are retained source premises, without an audit of their proofs or
an assertion about nonzero infinity types. Principal upper bounds use
the source's regularization $(s-1)\zeta_K(s)/(s+1)$; their pole is retained.

**The actual finite table and its primitive inducers.** Let
$H$ be the original fixed ideal-ray quotient, refined as in C58 to
present R11's total-class selectors and fixed phases, and put $h=|H|$.
Precisely, its class map is the surjection
$I(\mathfrak m)/P_1(\mathfrak m)\twoheadrightarrow H$ for the original
fixed ray modulus/refinement $\mathfrak m$, whose support is included
in $S$. This is the ideal-ray convention of the primary's Introduction
(lines 50–57), fixed-datum contract (590–603), and fixed-ray normalizer
(7007); its fixed phase presentation is specified at 3327–3343.
No element/unit-label enlargement, new modulus, or change of selector is
being chosen. The units in C58 remain separate. A finite character
$\chi\in\widehat H$ pulls back along this surjection to its original
zero-extended finite-order Hecke presentation; write $\chi^*$ for its
primitive inducer. Distinct $H$ characters have distinct primitive
inducers: equal inducers give equal values on every ideal prime to
$\mathfrak m$, hence equal characters of the quotient. In particular
$\chi^*=1$ if and only if $\chi=1$. This uses the genuine ideal quotient,
not equality of conductor norms. The complete defining-modulus zero
extensions and the original $S$ deletions stay attached, including
redundant deletion primes as in primary lines 590–603 and 4243–4256.

Normalized finite orthogonality gives the concrete direct-character table

$$
\begin{aligned}
\Omega_{\rm diag}(\mathbf g)
 &=\mathbf1_{g_1g_2=\sigma}\mathbf1_{g_3g_4=\sigma}
   =\sum_{\chi,\psi\in\widehat H}
      a_{\chi,\psi}\chi(g_1)\chi(g_2)\psi(g_3)\psi(g_4),\\
a_{\chi,\psi}&=h^{-2}\overline{\chi(\sigma)\psi(\sigma)},
 \qquad\mathbf n=0,\qquad\eta=a_{1,1}=h^{-2},\\
\sum_{\chi,\psi}|a_{\chi,\psi}|&=1,\qquad
m_2=\frac{2(h-1)}{h^2},\qquad m_4=\frac{(h-1)^2}{h^2},
 \qquad m_2+m_4=1-\eta.
\end{aligned}
\tag{R43}
$$

Here $m_2$ is the absolute Fourier mass with exactly one of $\chi,\psi$
nontrivial, hence exactly two nonprincipal slots; $m_4$ has both
nontrivial, hence four. Only $(1,1)$ is removed in $\Omega_{\rm diag}-\eta$.
There is no angular support or statistical-independence assertion.
For $h=1$ the residual is identically zero. Every original external
component coefficient multiplies this table and retains its absolute
cost in the common measure below; it is not absorbed into a new weight.

**The literal joint product for all sixteen choices.** For any
$M\subseteq[4]$, including $M=\varnothing$, use $\mu$ in $M$ and the
actual $K_A$ in $T=[4]\setminus M$. For a mode of R43 put
$(\chi_1,\ldots,\chi_4)=(\chi,\chi,\psi,\psi)$,
$x_i=\chi_i^*(p)q_p^{-s_i}$ and $y_k=q_p^{-z_k}$. The same exclusive-prime
mask in R3 gives

$$
\begin{aligned}
F_{P,\boldsymbol\chi}(\mathbf s,\mathbf z)
 &=\prod_{p\nmid SP}
    \left(1-\sum_{i\in M}x_i+\sum_{k\in T}x_k(1-2y_k)\right)\\
 &=H_{P,\boldsymbol\chi}(\mathbf s,\mathbf z)
    \prod_{i\in M}L(s_i,\chi_i^*)^{-1}
    \prod_{k\in T}L(s_k,\chi_k^*)L(s_k+z_k,\chi_k^*)^{-2},\\
H_{P,\boldsymbol\chi,p}
 &=\left(1-\sum_{i\in M}x_i+\sum_{k\in T}x_k(1-2y_k)\right)
    \prod_{i\in M}(1-x_i)^{-1}
    \prod_{k\in T}(1-x_k)(1-x_ky_k)^{-2}
       \quad(p\nmid SP).
\end{aligned}
\tag{R44}
$$

At $p\mid SP$ replace only the displayed parenthesis by $1$, using
the primitive local values, including zeros at ramified primes.
Thus the full original deletions occur in $H$, not a second time in the
$L$ factors. R4–R5 apply with unit character phases: the linear terms
cancel, the good factors are $1+O(q_p^{-2a})$ for $a>1/2$, and the
excluded factors cost $C_{H,S,\delta,\varepsilon}q_P^\varepsilon$.
No local numerator is inverted, even when it vanishes. The conductor
norms $Q_\chi$ form one fixed finite list; their upper-growth costs
$Q_\chi^{3/5}$ and reciprocal constants are included once in $C_H$.
They are not variable conductor losses hidden in $U^\varepsilon$.

Apply exactly R6–R8's successive contours, with
$0<\delta<1/80$ allocated inside the final loss. A $\mu$ slot ends at
$\Re s_i=\beta_H+\delta$. A $K$ slot ends at $\Re s_i=1/2+\delta$,
with $\Re z_i=\beta_H-1/2+2\delta$. A nonprincipal numerator $L$ is
entire, so this move has no $s_i=1$ residue. A principal $K$ slot has
exactly the ordinary simple residue of $\zeta_K(s_i)$; retain the joint
$H$ and all other factors evaluated there, and move only that slot's
$z_i$ to $\beta_H-1+\delta$. Its reciprocal square has a double zero
at $z_i=0$, cancelling the sole cutoff pole as in R7. Nonprincipal
boundary slots keep positive $\Re z_i$, so cross no cutoff pole.
The reciprocal arguments remain strictly to the right of $7/8$;
all joint correction arguments remain in R5. There is no additional
angular reciprocal strip, mixed polar divisor, or principal residue
assigned to a nonprincipal character.

For each fixed tuple let $M$ have $m$ slots, let $r_0$ count its
principal $K$ slots, and let $r_1$ count its nonprincipal $K$ slots.
Apart from the common seminorm and the allocated losses, R8 therefore
bounds that entire mixed term by

$$
D^{m\beta_H}
 [DA^{-(1-\beta_H)}+D^{1/2}A^{\beta_H-1/2}]^{r_0}
 [D^{1/2}A^{\beta_H-1/2}]^{r_1}.
$$

This includes all sixteen $\mu/K$ choices and every principal
residue/boundary subset, with at most eight Mellin variables including
the all-$K$ case. At the unchanged $A=U^{1/12}$ the three slot
costs are $U^{42/96}$ for $\mu$, $U^{47/96}$ for a principal $K$
residue, and $U^{27/96}$ for a $K$ boundary. With $v$ nonprincipal
slots, the largest choice uses $\mu$ there and principal $K$ residues
elsewhere. R9's full frequency count then gives
$U^{(204-5v)/96+\varepsilon}$. The generic nontrivial tuple allows
$v=1$, yielding $199/96$; the actual paired support has $v=2$ or $4$.
Consequently, for the same signed C59 residual with only its bare J4
table and for either $W_0$ or the redesigned $W_U$,

$$
|\mathcal R_{\rm fin,U}|
 \ll_{H,\varepsilon}\widetilde{\mathcal N}_{{\rm base},J}
 \left[m_2U^{97/48+\varepsilon}+m_4U^{23/12+\varepsilon}\right].
\tag{R45}
$$

For $W_0$ omit the dilation enlargement on the envelope and the
subscript $U$ on the residual. The original signs are retained before
the triangle inequality; no cancellation between modes or subsets is
assumed. R9's polynomial puncture range and its absolute divisor tail
apply unchanged, since $|\chi_i(d_i)|\le1$ and
$|K_{A;U}(d)|\le3^{\omega(d)}$ on squarefree ideals.

**One measure and the same redesigned realization.** Here
$\mathcal N_{{\rm base},J}$ is the original absolute component/profile/
height envelope *before* the coefficients of R43, retaining the
original unit/$S$ sums, signed external coefficient costs and
$(1+z)^4$ shell seminorm. This is the common coefficient-measure premise
of C59 and primary lines 9511–9524, not an independently chosen budget.
Choose one finite $J$ at least R41's order and
$J>L_H+8B_{H,\delta}+20$, taking the maximum growth degrees over the
fixed primitive list. Original norm heights remain in the external
profiles, with their polynomial derivative costs integrated against the
original log-Fourier decay of sufficiently high fixed order. All
original separated heights must satisfy this same absolute-measure
contract. No derivative acts on $b_U$, and no allowance restarts for a
mode, subset, shell or component.

For $W_U$ use exactly R34–R42's fixed-$U$ coefficient $b_U$ and the
four independent draws of the existing product law $\nu_U^4$.
The $K$ residue and boundary powers of a dilation $x$ are
$x^{-1/8+\delta}$ and $x^{3/8+2\delta}$, respectively; R35's real/log
moments and the same R41 enlargement pay them uniformly. Thus take
$\widetilde{\mathcal N}_{{\rm base},J}$ to be R41's one fixed moment
factor times $\mathcal N_{{\rm base},J}$. There is no maximum-support
factor $L^c$, new law, mode-dependent dilation, or extra height budget.
The radial envelope is
$\widetilde{\mathcal N}_{\eta,J}=h^{-2}
\widetilde{\mathcal N}_{{\rm base},J}$ for this fixed table.
If only that eta-weighted original envelope is supplied, the full
Fourier envelope costs $h^2$ times it and the residual costs
$(h^2-1)$ times it; R45's two separate costs are
$2(h-1)$ and $(h-1)^2$ times it. These are fixed-source factors,
not a silent promotion from eta mass to full mass.

For precisely this $b_U$ on both parts of C59, the finite residual is
all of $\mathcal R_{\rm tw,U}$. Combine R45 with the existing radial
R42 on the same components and measure. The complete **local nonzero
exceptional** sum then satisfies

$$
\begin{aligned}
|\mathcal E_{\rm exc,U}|
 &=|\mathcal E_{\rm rad,U}+\mathcal R_{\rm fin,U}|\\
 &\ll_{H,\varepsilon}\widetilde{\mathcal N}_{{\rm base},J}
 [h^{-2}U^{199/96+\varepsilon}
       +m_2U^{97/48+\varepsilon}+m_4U^{23/12+\varepsilon}]\\
 &\ll_{H,\varepsilon}\widetilde{\mathcal N}_{{\rm base},J}
       U^{199/96+\varepsilon},\\
D^{-2}|\mathcal E_{\rm exc,U}|
 &\ll_{H,\varepsilon}\widetilde{\mathcal N}_{{\rm base},J}
       U^{103/96+\varepsilon}.
\end{aligned}
\tag{R46}
$$

The same fixed or polylogarithmic envelope assumption and internal-loss
allocation as R42 give its registered margin $1/3000$ below $1+B_*$
(and below $B_*$ after restoring just $D^{-2}$). The $U^2=D^4$ from
C60 is already counted. C56's planar measure, ideals counted once,
six units, $S$ factors, $\bar C/6$ and $d_{\mathbf r}^{-1/6}$ remain in
their original places; the finite Fourier coefficient creates no new
area factor or unit division.

R46 pays this conditional bare-J4 local branch only. The zero-frequency
$k=0$ term, nonexceptional C68, extra generalized $\zeta_i$/angular
factors and their component/height measure, other cores/common gcds,
bad duals, full physical-row and detector/rho restoration at the same
beta, and the full J40 contraction remain unpaid. R45 does not control
the original-$W_0$ principal scalar; R46 uses the redesigned cutoff and
supplies no signed cutoff-change estimate. No arbitrary replacement
profile, statistical law or joint weight, principal lower bound,
upstream-proof audit, originality claim, Lean certification, Robin
restoration or RH conclusion follows.
