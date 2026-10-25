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
