---
bibkey: liu2026quasirhdual
authors: Baiying Liu
year: 2026
title: Complete-dual applications to the quasi-Riemann inverse fourth moment
doi: null
url: https://arxiv.org/abs/2610.12234v2
claim: Source-conditional applications of the pinned Gauss, Poisson, cubic and sextic inputs pay specified complete-dual regions and reduce an original inverse-fourth improvement to a small-product-squarepart head estimate; that remaining estimate is not supplied.
strata_touched: []
license: citation-only
triage: anchor
---

# Complete-dual applications to the quasi-Riemann inverse fourth moment

This companion to the [Liu source card](../Analytic/liu2026quasirh.md) records
`repo-derived` applications, not additional theorems attributed to Liu.
It reuses that card's pinned primary manuscript, original coefficients,
physical rows, collision zeros and fixed or polylog profile/height
contract. The primary Gauss/Poisson formulas, Heath--Brown cubic sieve
and original sixth-order sieve remain the analytic suppliers.
No new sieve, literature-priority claim or Lean certification is made.

Here $D=\sqrt U$, $q_a$ denotes ideal norm, $t(a)$ the original fixed
multiplicative ray class, and $\mathcal K_{U,\Omega}$ the complete
physical-row kernel defined in the [actual-order-six correlation](../Analytic/liu2026quasirh.md#the-actual-order-six-correlation-for-the-inverse-fourth-moment).
The baseline exponent is $B_*=(31-10\sqrt6)/6$.
The intrinsic product-squarepart norm $P$ and coefficient-envelope
large-$P$ bound are [C16--C18](../Analytic/liu2026quasirh.md#localizing-the-remaining-contraction-by-the-product-squarepart).

## Reusing Möbius--Gauss cancellation in the complete dual

The [squarefree Gauss pairing](../Analytic/faveri2026fixedorder.md#known-estimates-for-the-squarefree-gauss-pairing)
and its [additive-character transport](../Analytic/faveri2026fixedorder.md#exact-additive-character-transport)
already supply the detector's `eq:signal`, pair-Gauss formula and shift to
the DDDS convention. They must be reused rather than reconstructed from a
rational conductor. In particular, on their stated equal-ray coprime
squarefree packet, cancelling the two original Möbius signs in the root
factor leaves angular and cubic Gauss coefficients. It does not remove
the character of each complete dual ideal.

**The joint matrix retains order six.** For a good primary squarefree
column $x$, let $\chi_x$ be the original raw sextic character, including
its zeros, and put $\kappa_x=\chi_x^2$, $\lambda_x=\chi_x^3$. In precisely
the cited additive conventions, the already supplied shift gives

$$
B_{m,x}:=\lambda_x(m)\overline{\widetilde g_3(-3m,x)}
=\overline{\gamma_2(x)}\,\overline{\chi_x(m)}.
$$

Indeed $\overline{\widetilde g_3(-3m,x)}
=\overline{\gamma_2(x)}\kappa_x(m)$ and
$\lambda_x\kappa_x=\overline{\chi_x}$. If $(m,x)>1$, both sides are
zero, by the primitive cubic Gauss identity at the colliding prime.
For any identical finite row and column sets, therefore,
$B=\overline C\operatorname{diag}(\overline{\gamma_2})$, where
$C_{m,x}=\chi_x(m)$. The diagonal is unitary. These two matrices have the
same singular values; the same nonnegative separate row and column weights
or real zero mask preserve the identity with the conjugated matrix.
A complex coupled weight must be transported too. Thus this identity
alone supplies no smaller cubic operator norm. It does not exclude extra
cancellation for the actual coefficient vector.

**Opening the actual coefficient repairs one applicability mismatch.**
The fixed-twist numerator average in (B2) of the
[growing-ray supplier](../Analytic/faveri2026fixedorder.md#a-tame-growing-ray-application-to-the-complete-classwise-pole)
cannot simply be evaluated on a diagonal where both its quadratic twist
and numerator are determined by $m$. There is, however, an admissible way
to use that supplier for each fixed $m$: open $A_D$ itself.

Consider only the $t_a=t_b=1$, common-column-gcd $h=1$,
$\ell=r=1$ term in the existing complete Poisson majorant, within a fixed
equal-ray packet and with fixed bad-prime data. Here $D=\sqrt U$,
$q_x,q_y\asymp U$, the primitive good conductor is $xy$, and the natural
dual range is $q_m\ll U$. This is a specified term of that majorant, not
a positive domination claim for a signed subset of the earlier $E_6$.
For a bounded selector $\omega_M$ on good dual ideals $q_m\asymp M$,
$1\le M\le U$, define this normalized piece explicitly by

$$
\begin{aligned}
\mathfrak E_1(M)=
\sum_{\substack{x,y\ {\rm good\ sf},\ (x,y)=1\\t(x)=t(y)=\tau}}
&g_D(x)\overline{g_D(y)}\epsilon_{x,y}
\frac{U}{\sqrt{q_xq_y}}\\
&\quad\times\sum_{m\ {\rm good}}\omega_M(m)
\overline{\chi_{x,y}(m)}
\mathscr W\!\left(\frac{q_mU}{q_xq_y}\right).
\end{aligned}
$$

Here $\epsilon_{x,y}$ and $\chi_{x,y}$ retain the source root convention
and original ratio zeros. Only this good-dual, equal-ray term is selected;
other original terms are not deleted from the full moment.

Detect $(x,y)=1$ by $\sum_{e\mid(x,y)}\mu(e)$. For each squarefree $e$,
allocate $e=e_1e_2$ in the exact convolution
$A_D(x,1)=\sum_{uv=x}V(q_u/D)V(q_v/D)$ and write $x=euv$ after
allocation. The two remaining lengths are

$$
D'=D/q_{e_1},\qquad N'=D/q_{e_2},\qquad D'N'=U/E,
\qquad E=q_e.
$$

Cubic Gauss CRT leaves a cubic symbol between $u$ and $v$. For fixed
$m$, its full sextic dual factor is an allowed finite inducing twist
on each variable, with extra good modulus $f_m=\operatorname{rad}(m)$ and
$F_m=q_{f_m}\le q_m$, including any primes used only for zero extension.
The theta numerator is the other convolution variable, with the existing
$e$-shift; its coprimality with $m$ is enforced by the original dual zeros.
This avoids the earlier numerator/conductor overlap. Keep every
squarefree and finite-class constraint; the original denominator exclusions
are retained in the application of (B2).

Apply (B2) directly by Mellin inversion and Cauchy with the actual outer
coefficient vector. There is no $\vartheta$ weight in this sum, so no
bounded-multiplier contraction or deletion of such a weight is used.
Both convolution factors have the angular conjugate-cubic Gauss form;
choose the smaller one as the outer length. For each allocation the
resulting scalar $S_{e,m}$ satisfies

$$
|S_{e,m}|^2\ll U^\varepsilon F_m E^{1/2}
D'N'\min(D',N')
\le U^\varepsilon F_m U^{3/2}/E.
$$

The allocation count is a divisor loss and $\sum_{q_e\ll U}q_e^{-1}
\ll\log U$, so their sum costs $U^\varepsilon$. Alternatively the
existing cubic large sieve gives the summed bound $U^{5/3+\varepsilon}$,
independent of $m$: sum
$D'N'(D'+N'+(D'N')^{2/3})$ over the same allocations. Its first two
terms cost $U^{3/2+\varepsilon}$ and the last costs
$U^{5/3+\varepsilon}$.

The Poisson prefactor and the two original $D^{-1}$ coefficients leave
$U^{-1}$ at $q_x,q_y\asymp U$. There are $O(M)$ dual ideals in the dyad
and $F_m\ll M$. Consequently this specified procedure supplies

$$
|\mathfrak E_1(M)|\ll U^\varepsilon
\min\{U^{1/2}M^2,\ U^{2/3}M\}.
$$

The coupled Poisson profile does not cost a power of $M$ here. Writing
$s=M/U\le1$, $\rho_x=q_x/U$, $\rho_y=q_y/U$ and
$\rho_m=q_m/M$, its scaled factor is
$(\rho_x\rho_y)^{-1/2}
\mathscr W(s\rho_m/(\rho_x\rho_y))$ on fixed compact annuli.
Smoothness of the original radial Fourier transform at zero bounds all
required logarithmic derivatives uniformly for $0<s\le1$; compact
Mellin separation pays the resulting polynomial heights with the same
fixed seminorm contract.

The two certificates cross at $M=U^{1/6}$. The angular application
improves the cubic certificate only below that point, where the cubic
certificate was already below $U$. At the full natural length $M\asymp U$,
the better of these certificates is merely $U^{5/3+\varepsilon}$.
In particular the angular application does not enlarge the range
$M<U^{B_*-2/3}$ already paid by this cubic certificate. This compares
bounds produced by specified procedures, not lower bounds for the actual
sum. The other common gcds, original row parameters, finite components
and full long-conductor contraction remain outside this restricted
calculation. The Gauss transport and analytic suppliers are reused;
no improved full inverse-fourth exponent, signed Robin conclusion,
literature-priority claim or Lean certification is supplied.

### A joint bound for the same good-dual term

For precisely the preceding $\mathfrak E_1(M)$, averaging the raw sextic
matrix jointly before taking absolute values improves the paid dual
range. This is a `repo-derived`, source-conditional application of the
existing pair-Gauss formula, the sixth-order sieve and the preceding
scalar cubic certificate. It retains the original $g_D$, equal-ray
packet, good-dual selector and $t_a=t_b=h=\ell=r=1$ restrictions.
For $U^{1/3}\le M\le U$, the resulting bound is

$$
\boxed{
|\mathfrak E_1(M)|\ll U^\varepsilon
\left(U^{17/18}M^{1/6}+U^{5/6}M^{1/3}\right).
}
\tag{J1}
$$

**The matrix and the common gcd.** Reuse the
[classwise pair-Gauss formula](../Analytic/faveri2026fixedorder.md#a-classwise-squarefree-column-pole-consumer-with-shared-gcds)
in its original additive convention:
$\epsilon_{x,y}=c_\tau\gamma_1(x)\overline{\gamma_1(y)}$,
$|\gamma_1|=1$. The class constant includes the original
$\chi_y(-1)$ sign. Together with
$\overline{\chi_{x,y}(m)}=\overline{\chi_x(m)}\chi_y(m)$,
this is a raw-character Gram kernel on the coprime locus. Extend this
product formula algebraically off that locus and impose $(x,y)=1$
by $\sum_{e\mid(x,y)}\mu(e)$. This does not extend the primitive
ratio formula to noncoprime conductors.

Use the already justified compact Mellin separation of the Poisson
profile. For each separated term, write $x=er,y=es$ and $q_e\asymp E$.
The column length is $B\asymp U/E$. The original bound
$|g_D(x)|\ll U^{-1/2+\varepsilon}$ implies that the product of the two
column-vector $\ell^2$ norms is $\ll U^\varepsilon/E$.
The $O(E)$ choices of $e$ in its dyad cancel this factor after a triangle
inequality; dyads cost $U^\varepsilon$. The original squarefree masks
$(r,e)=(s,e)=1$ remain column masks. The shared character factor leaves
the row mask $(m,e)=1$. A bounded complex selector or Mellin row factor
is controlled by Cauchy between the two positive squared norms; it is
not deleted from the signed sum by a contraction assertion.

**Separate small sixth-power-free cores.** Write uniquely
$m=nv^6$, where $n$ is sixth-power-free. No condition $(n,v)=1$ is
imposed. Fix $1\le L\le M$ and first select $q_n>L$.
For fixed $e,v$, the collision zeros retain the column masks
$(r,v)=(s,v)=1$ and the row mask $(n,e)=1$; terms with $(v,e)>1$
vanish. Restricting a positive squared norm preserves the existing
sixth-order sieve bound

$$
F_6(T,B)\ll (TB)^\varepsilon
\left(T+B+T^{5/6}B^{1/3}+T^{1/3}B^{5/6}\right),
\qquad T\asymp M/q_v^6,\quad B\asymp U/E.
$$

All column phases, including $\gamma_1(er)$ and the original coefficient,
stay in the actual vectors. This uses no growing inducing-character
supplier. Sum over $q_v\ll(M/L)^{1/6}$ and then over the common-gcd
dyads. Ideal counting gives

$$
|\mathfrak E_{1,\,q_n>L}(M)|\ll U^\varepsilon
\left[M+U(M/L)^{1/6}
 +M^{5/6}U^{1/3}+M^{1/3}U^{5/6}\right].
\tag{J2}
$$

For example the $T$, $T^{5/6}$ and $T^{1/3}$ terms sum respectively
$q_v^{-6}$, $q_v^{-5}$ and $q_v^{-2}$, all convergently; the $B$
term counts the allowed $v$. The remaining negative powers of $E$
cannot increase the bound.

For $q_n\le L$, count the dual ideals first:

$$
\#\{m:q_m\asymp M,\ q_n\le L\}
\ll M^{1/6}\sum_{q_n\le L}q_n^{-1/6}
\ll M^{1/6}L^{5/6}.
$$

The preceding per-$m$ cubic certificate is uniform in $m$ and is
$U^{2/3+\varepsilon}$ after the same coefficient normalization.
Consequently

$$
|\mathfrak E_{1,\,q_n\le L}(M)|
\ll U^{2/3+\varepsilon}M^{1/6}L^{5/6}.
\tag{J3}
$$

Taking $L=U^{1/3}$ balances (J3) against
$U(M/L)^{1/6}$. For $M\le U$, both $M$ and
$M^{5/6}U^{1/3}$ are at most $M^{1/3}U^{5/6}$, proving (J1).
For $M<U^{1/3}$ the preceding cubic certificate already costs at most
$U^{1+\varepsilon}$.

Thus this specified term costs $U^{13/12+\varepsilon}$ throughout
$M\le U^{3/4}$, and has exponent strictly below $B_*$ for
$M\le U^m$ with fixed $m<13-5\sqrt6=0.752551\ldots$.
The joint certificate improves the preceding cubic certificate once
$M>U^{1/3}$; at $M=U$ it still costs $U^{7/6+\varepsilon}$.
The proof of (J3) above uses the original Möbius convolution; the
coefficient interface below analyzes the new Type-II convolution
directly. In particular (C31), a whole moment comparison, does not
transport a selected dual sum. Other common
gcds, original components, the full small-$P$ contraction, signed Robin
restoration and RH remain outside (J1). This is an application of the
cited suppliers, with no new sieve, priority or Lean-certification claim.

### A coefficient interface for the cubic low-core estimate

The cubic certificate, unlike the angular (B2) certificate, accepts
arbitrary complex coefficient vectors. This permits a direct application
to the actual Type-II factor, without a selected-sum transport theorem.
The following `repo-derived` interface reuses the primary manuscript's
`lem:fixed-gauss-phase`, its Gauss CRT formula and
`eq:cubic-large-sieve` (Heath–Brown's cubic large sieve).

Let $b(d)$ be supported on good squarefree ideals, independent of the
physical row and dual ideal, with $|b(d)|\le C_b\tau_k(d)$ for fixed
$k$. Keep the original fixed multiplicative ray twist $\xi$, and define
the genuine self-convolution

$$
h_b(a)=D^{-1}\xi(a)\sum_{d_1d_2=a}
 b(d_1)b(d_2)V(q_{d_1}/D)V(q_{d_2}/D),\qquad D=\sqrt U.
\tag{J4}
$$

Define $\mathfrak E_{1,b}$ by substituting $h_b$ for $g_D$ in the same
specified good-dual, equal-ray term. To bound one fixed dual ideal,
detect $(x,y)=1$ as before, allocate $e=e_1e_2$ between the two factors
of $x=euv$, and put
$D'=D/q_{e_1}$, $N'=D/q_{e_2}$. The original squarefree column imposes
$u,v$ squarefree, $(uv,e)=1$ and $(u,v)=1$.

Write $\kappa_u(v)=\chi_u(v)^2$ and
$\theta_e(w)=\chi_e(w)\chi_w(e)$. The already supplied CRT and
reciprocity formulas give, on this coprime locus,

$$
\gamma_1(euv)=\gamma_1(e)\theta_e(u)\theta_e(v)
 \mathcal R(u,v)\kappa_u(v)\gamma_1(u)\gamma_1(v).
\tag{J5}
$$

The class factor $\mathcal R(u,v)$ is fixed after a finite partition of
$t(u),t(v)$, with their product class still prescribed by $t(x)$.
The two coefficient vectors retain $b(e_1u)$, $b(e_2v)$, the respective
$V$ factors, $\xi$, $\gamma_1$, $\theta_e$, norm phases and the original
$\overline{\chi_u(m)}$, $\overline{\chi_v(m)}$ zeros. The conditions
$(u,e)=(v,e)=1$ are separate coefficient masks. The only coupled mask
$(u,v)=1$ is exactly the zero extension of $\kappa_u(v)$.
If $(e,m)>1$, the whole scalar is zero. The negative-root side is
handled by conjugating its entire scalar. Thus these are legitimate
arbitrary coefficient vectors for the cubic sieve; no Möbius–Gauss
cancellation or removal of a bounded multiplier is required.

For the unnormalized scalar $H_{e,m}^{e_1,e_2}$ from this allocation,
the two squared vector norms are at most
$C_b^2U^\varepsilon D'$ and $C_b^2U^\varepsilon N'$. Cauchy and the
cubic sieve give

$$
|H_{e,m}^{e_1,e_2}|^2
\ll C_b^4U^\varepsilon D'N'
 \left[D'+N'+(D'N')^{2/3}\right],\qquad D'N'=U/q_e.
\tag{J6}
$$

The allocation count costs a divisor loss. The first two terms sum
$UD\sum_{e_1}q_{e_1}^{-2}\sum_{q_{e_2}\ll D}q_{e_2}^{-1}
\ll U^{3/2+\varepsilon}$ and its transpose. The last sums
$U^{5/3}\sum_e\tau(e)q_e^{-5/3}\ll U^{5/3}$.
Restore the two factors $D^{-1}$, and apply Cauchy between the two
scalars of each separated rectangular profile. The per-$m$ certificate
is therefore $C_b^4U^{2/3+\varepsilon}$.
The original compact Mellin separation pays all polynomial profile
heights. No derivatives of $b$ are taken and no new power of the
Type-I cutoff is introduced.

Consequently (J1)–(J3) hold for $\mathfrak E_{1,b}$, with the factor
$C_b^4$. In particular they hold for
$b=\lambda_{\mathrm{II},b}$ and $b=r_A\lambda_{\mathrm{II},b}$,
both bounded by $\tau_3$ on squarefree support. This directly pays their
specified $M\le U^{3/4}$ prefix at $U^{13/12+\varepsilon}$ in the
$P=1$ part of (C20). The angular branch $U^{1/2}M^2$ is not asserted
for these arbitrary coefficients: its inner special Gauss sequence is
a stronger hypothesis than the cubic sieve requires. Neither the
full natural dual range nor the other original terms follow from
this coefficient interface.

### A multiple-Dirichlet-series model of the raw phase

The Gauss numerator shift and (J5) identify a precise model for a
specified scalar, before applying a bound. On the squarefree coprime
support of (J5), its moving phase, with the fixed-$e$ factors left in
the actual coefficient vectors, is

$$
\gamma_1(uv)\overline{\chi_{uv}(m)}
=q_{uv}^{-1/2}\sum_{z\bmod uv}\chi_{uv}(z)e(mz/(uv)).
$$

This is the normalized **sextic** Gauss sum with numerator $m$.
Both sides vanish when $(m,uv)>1$. The original $b(e_1u)$,
$b(e_2v)$, profiles, fixed-core twists and masks remain present;
the identity does not turn them into standard Dirichlet-series
coefficients. It reuses the pinned Gauss shift, rather than lowering
the order of the original dual character.

An exact function-field model of this raw phase can be read from
[Sawin--Whitehead, *Functional equations of axiomatic multiple Dirichlet
series, Weyl groupoids, and quantum algebra*, arXiv:2507.08662v2,
Lemma 2.2 and Proposition 4.1](https://arxiv.org/html/2507.08662v2).
This is a `repo-derived` parameter match using their existing formulas,
not an analytic estimate attributed to that paper. Let $q\equiv1\pmod{12}$
be a prime power, let $\chi$ have order six on $\mathbb F_q^\times$,
and let $u,v,m$ be monic polynomials, with $uv$ squarefree. The variable
order is $(u,v,m)$. In their notation the required symmetric matrix is

$$
M=\begin{pmatrix}4&2&5\\2&4&5\\5&5&0\end{pmatrix}\pmod6.
$$

Indeed their quadratic character is $\xi=\chi^3$, so Lemma 2.2 uses
the derivative character $\xi\chi=\chi^4$. Splitting the derivative of
$uv$ gives diagonal exponents $4,4$ and cross exponent $4+4\equiv2$;
the numerator shift gives exponents $-1\equiv5$ against $m$.
Reciprocity has no sign for this choice of $q$. Proposition 4.1,
since $M_{33}=0$, permits arbitrary $m$, including nonsquarefree $m$.
With $a_M$ denoting their axiomatic coefficient and $g_\chi$ their
finite-field Gauss sum, the exact normalization is

$$
q^{-(\deg u+\deg v)/2}g_\chi(m,uv)
=\left(\frac{g_\chi}{\sqrt q}\right)^{\deg u+\deg v}a_M(u,v,m).
$$

For $(m,uv)=1$ this follows from Lemma 2.2 and (4.1); on a collision
both sides are zero. The remaining factor depends only on degrees
and has modulus one, so it is transported by a change of the first
two series variables.

**The finite-root-system continuation hypothesis fails for this model.**
In the bicharacter convention of their Section 5, let $\zeta$ be a
primitive sixth root of unity. The $u,v$ diagonal labels are
$-\zeta^4=\zeta$, and their mutual label is $\zeta^2$. The reflection
exponent in either direction is therefore

$$
m_{uv}=m_{vu}
=\min\{k\ge0:\zeta^{k+1}=1\text{ or }\zeta^{k+2}=1\}=4.
$$

Both directions satisfy Theorem 3.10's divisibility condition:
$\gcd(6,4+3)=1$ divides every incident entry. Lemma 5.16(2) preserves
the parameter matrix under each of these two reflections, so the
reflections can be composed repeatedly. On the invariant span of the
first two basis vectors their matrices and product are

$$
s_u=\begin{pmatrix}-1&4\\0&1\end{pmatrix},\qquad
s_v=\begin{pmatrix}1&0\\4&-1\end{pmatrix},\qquad
s_us_v=\begin{pmatrix}15&-4\\4&-1\end{pmatrix}.
$$

The product has eigenvalues $7\pm4\sqrt3$ and hence infinite order.
Thus the reflection groupoid has infinitely many morphisms, even
though these two reflections preserve its parameter matrix. This
model does not meet the finite arithmetic-root-system hypothesis of
Theorem 5.5. Finiteness of the set of parameter matrices alone would
not supply that hypothesis.

This calculation concerns the unweighted function-field model and
uses classical Gauss identities and the cited reflection formulas.
It supplies no number-field continuation or bound for the actual
$b$-weighted scalar. In particular it does not identify all prime-power
coefficients with the original source, transport its angular/ray data,
or pay the other original Poisson terms. Continuation on a smaller
domain, methods for infinite groupoids and other representations are
not excluded. Neither a stronger inverse-fourth estimate nor (J24),
signed Robin restoration or RH follows from this model identification.

#### The reflected star retains pairing and continuation obligations

Under the same $q\equiv1\pmod{12}$ and order-six $\chi$ hypotheses,
[Sawin--Whitehead, Theorem 4.7](https://arxiv.org/html/2507.08662v2#S4.Thmtheorem7)
and [matrix transform (1.11)](https://arxiv.org/html/2507.08662v2#S1.E11)
reflect the $m$-Dirichlet coordinate, in order $(u,v,m)$, to

$$
M_\star=\tau_m(M)=\begin{pmatrix}0&0&1\\0&0&1\\1&1&0\end{pmatrix}\pmod6.
$$

For $uv$ squarefree, Proposition 4.1 gives
$a_{M_\star}(u,v,m)=(u/m)_\chi(v/m)_\chi$ for every monic $m$,
including nonsquarefree $m$, with collision zeros retained. This is a
**same-sign** character pairing. By contrast, Example 5.12's (5.15)
uses a character and its conjugate for an absolute second moment.
Theorem 4.7 acts on degree-residue vectors with a scattering matrix;
a functional-equation conversion must retain its Gauss/root-number
factors and degree shifts and costs. The original $b$ weights have not
become canonical MDS coefficients. The separate central-moment route is
[already assessed](../Analytic/liu2026quasirh.md#mollified-central-moments-retain-a-shorter-inverse-length).

[Popa--Walsh, *A decomposition of Weyl group multiple Dirichlet series
for symmetrizable Kac-Moody root systems*, arXiv:2607.11834v2](https://arxiv.org/html/2607.11834v2)
provide genuine infinite-type continuation for a fixed symmetrizable
Cartan matrix and its Chinta--Gunnells action, with distinct hypotheses.
[Proposition 3.6](https://arxiv.org/html/2607.11834v2#S3.Thmdefinition6)
continues the corrected average $D_{\mathrm{re}}\Delta_{\mathrm{im}}Z_\xi$
holomorphically to the complexified Tits-cone interior, for a fixed
$\xi\in P^+$. [Theorem 4.12](https://arxiv.org/html/2607.11834v2#S4.Thmdefinition12)
requires Chinta--Gunnells invariance and Hypothesis $H(R)$ on $\Omega(R)$,
with $R\ge\log_q r$: $D_{\mathrm{re}}Z$ must be holomorphic there and
$Z$ must have the prescribed absolutely convergent Taylor expansion.
Its decomposition converges normally in the stated polydisk.
For their constructed global function-field WMDS, with $q\equiv1\pmod{2n}$,
[Theorem 5.4](https://arxiv.org/html/2607.11834v2#S5.Thmdefinition4)
gives normal convergence of $D_{\mathrm{re}}\mathcal Z$ on the explicit
Weyl-invariant $X(R_{q,r})_{\mathbb C}$, $R_{q,r}=\max(1,\log_q r)$.
This supplies meromorphic continuation on that subdomain, rather than
unrestricted full-cone continuation or estimates for arbitrary insertions.

In the displayed star basis, the bicharacter labels are $q_{ii}=-1$
and $q_{um}q_{mu}=q_{vm}q_{mv}=\zeta_6$, a primitive sixth root.
The ordinary diagonal Cartan-type relation
$q_{ij}q_{ji}=q_{ii}^{a_{ij}}$ cannot hold on either nontrivial edge:
no integer power of $-1$ equals $\zeta_6$. This excludes directly
importing that conventional Cartan-type realization in this basis;
it excludes neither alternative constructions nor other continuations.

This is a `repo-derived` applicability check using the cited formulas.
Identification of the actual coefficients, prime-power and angular/ray
data, and a uniform bound with the original $b$ weights over the full
natural dual length remain unproved bridges. No analytic saving,
natural-boundary theorem, originality claim or RH conclusion follows.

### A common-gcd region with all original row expansions

The same cubic interface and joint sextic estimate also pay an
additional part of the original small-$P$ region. The result here remains
an equal-ray, **total-squarefree-column** statement. For $h_b$ in (J4),
using the complete original physical row kernel, define

$$
\mathcal E_{\tau,H}^{\rm sf}(b)=
\sum_{\substack{a,c\ {\rm sf},\ q_a,q_c\asymp U\\
 t(a)=t(c)=\tau,\ q_{(a,c)}\asymp H}}
 h_b(a)\overline{h_b(c)}\mathcal K_{U,\Omega}(a,c).
\tag{J7}
$$

For $1\ll H\ll U^{1/4}$, the source-conditional bound is

$$
\boxed{
|\mathcal E_{\tau,H}^{\rm sf}(b)|
\ll C_b^4U^\varepsilon
\left[U+U^{7/6}H^{-1}+U^{10/9}H^{-5/18}
             +U^{7/6}H^{-1/2}\right].
}
\tag{J8}
$$

**Keep the common support and row indicators.** Write $a=hx,c=hy$.
The ideals $h,x,y$ are squarefree and pairwise coprime,
$q_x,q_y\asymp B=U/H$, and
$t(x)=t(y)=\tau/t(h)$. The primitive ratio conductor is $xy$,
and its zero-only radical is $\operatorname{rad}(hS)$.
Expand the sixth-power-free physical-row indicator with $\ell$, and
its zero-only primes with $r\mid\operatorname{rad}(hS)$, exactly as in
the source Poisson argument. Put $\kappa=q_\ell^6q_r$.
Omit empty original row sums with $\kappa>c_\Omega U$ before applying
Poisson; hence $q_\ell\ll U^{1/6}$. All original restrictions,
including $(\ell,hxyS)=1$, remain in force.

Poisson contributes $H/\kappa$ and natural full-dual length
$\kappa U/H^2$. Detect $(x,y)=1$ by a common divisor $e$.
At $q_e\asymp E$, the normalized column-vector norm product is
$\ll C_b^4U^\varepsilon/(HE)$; $O(E)$ choices of $e$ cancel the
$E^{-1}$. Summing $O(H)$ choices of $h$ leaves $H/\kappa$.
All $r$ and finite-class phases remain column factors or collision
masks accepted by the positive-norm estimates.

For the scalar low-core bound allocate $h=h_1h_2$, $e=e_1e_2$
between the two original factors. Their remaining lengths obey

$$
D'=\frac{D}{q_{h_1}q_{e_1}},\qquad
N'=\frac{D}{q_{h_2}q_{e_2}},\qquad
D'N'=\frac{U}{HE},\qquad D',N'\ll D.
$$

The argument of (J5)–(J6), with coefficients
$b(h_1e_1u)$ and $b(h_2e_2v)$, gives for each fixed $h$ and full dual
ideal, including the Poisson and coefficient normalization,

$$
\frac{C_b^4U^\varepsilon}{\kappa}
 \left(U^{1/2}+U^{2/3}H^{-2/3}\right)
\ll\frac{C_b^4U^{2/3+\varepsilon}H^{-2/3}}{\kappa}.
$$

The last comparison uses $H\ll U^{1/4}$; it is not assumed for larger
$H$. Arbitrary divisor-bounded $b$ preserves these separate vectors.

**Retain four high-core terms.** First take the dual ideal good and
write it as $nv^6$, with $n$ sixth-power-free and no coprimality condition
between $n,v$. For a good-dual dyad $M$ and $q_n>L$, the same
sixth-order sieve gives

$$
\frac{C_b^4H}{\kappa}U^\varepsilon
\left[M+B(M/L)^{1/6}+M^{5/6}B^{1/3}
                         +M^{1/3}B^{5/6}\right].
\tag{J9}
$$

The complementary low-core count costs
$C_b^4\kappa^{-1}U^{2/3+\varepsilon}H^{1/3}M^{1/6}L^{5/6}$.
For $M\ge B^{1/3}$, choose $L=B^{1/3}$ to balance it against
the second term in (J9). At $M\ll\kappa U/H^2$, the four costs are

$$
C_b^4U^\varepsilon\left[
\frac UH,
\ \kappa^{-5/6}U^{10/9}H^{-5/18},
\ \kappa^{-1/6}U^{7/6}H^{-1},
\ \kappa^{-2/3}U^{7/6}H^{-1/2}\right].
$$

Unlike the $\ell=r=1$ case, the enlarged dual range can exceed $B$;
none of these four terms is discarded. Summing $q_\ell\ll U^{1/6}$
costs respectively $U^{1/6}$, a constant, $\log U$, and a constant.
The sums over $r\mid\operatorname{rad}(hS)$ cost $U^\varepsilon$;
their powers are respectively $r^0,r^{-5/6},r^{-1/6},r^{-2/3}$.
For $M<B^{1/3}$, the scalar cubic certificate and $O(H)$ choices of
$h$ instead give $C_b^4U^{1+\varepsilon}/\kappa$, summably.

A general dual ideal is $sm_0$, with $s$ supported on the fixed bad
primes $S$ and $m_0$ good. Its natural good-dual length is
$M\ll\kappa U/(H^2q_s)$. The four endpoint costs gain
$q_s^{-1},q_s^{-1/6},q_s^{-5/6},q_s^{-1/3}$, respectively; all
four $S$-supported sums converge. For the small-$M$ certificate,
rapid-decay truncation leaves a polylogarithmic number of $s$.
The original radial transform and its logarithmic derivatives decay
arbitrarily fast beyond the natural length, paying all further dyads.
No bad-dual component or original auxiliary expansion is deleted.
These sums prove (J8).

In particular,

$$
\boxed{
U^{1/6}\le H\le U^{1/4}
\quad\Longrightarrow\quad
|\mathcal E_{\tau,H}^{\rm sf}(b)|
\ll C_b^4U^{13/12+\varepsilon}.
}
\tag{J10}
$$

For total-squarefree columns, $P=H$ and
$q_{\mathfrak f}\asymp U^2/H^2$. Thus (J10) pays the additional
same-class region $U^{1/6}\le P<U^{1/4}$, with conductor scales
between $U^{3/2}$ and $U^{5/3}$. It applies to the original Möbius
factor and directly to the actual Type-II and rough factors above.
It does not pay nonsquarefree columns, smaller $H$, or the original
signed cross-class contraction. A finite positive class partition is
not an identification with that signed contraction. The complete
inverse-fourth gain, signed Robin restoration and RH remain unproved.
All Gauss, Poisson and sieve inputs are reused; the new region is a
source-conditional application, without priority or Lean certification.

### Extending the paid region to cube-free low-repeat columns

Fix $T\ge1$ and write actual cube-free columns uniquely as
$a=t_a^2s_a$, $c=t_c^2s_c$, with squarefree, coprime factors within each
column. For $h_b$ from (J4), retain the complete original kernel and define

$$
\mathcal E_{\tau,\le T}(P_0;b)=
\sum_{\substack{q_a,q_c\asymp U,\ t(a)=t(c)=\tau\\
 r_2(a)\ne r_2(c),\ q_{t_a},q_{t_c}\le T\\
 P_0\le P(a,c)<U^{1/4}}}
 h_b(a)\overline{h_b(c)}\mathcal K_{U,\Omega}(a,c).
\tag{J11}
$$

Provided $P_0/T^2\gg1$, the fixed-core application below gives

$$
\boxed{
|\mathcal E_{\tau,\le T}(P_0;b)|
\ll C_b^4U^\varepsilon
\left[UT^2+U^{7/6}T^4P_0^{-1}
 +U^{10/9}T^{23/9}P_0^{-5/18}
 +U^{7/6}T^3P_0^{-1/2}\right].
}
\tag{J12}
$$

**Freeze the repeated support before applying the existing CRT.** Put
$J=t_at_c$, $C=(t_a,t_c)$, and record the single-occupancy primes from
the opposite repeated support by
$d_a\mid t_c/C$, $d_c\mid t_a/C$. Exactly,

$$
a=Agx,\qquad c=Bgy,\qquad
A=t_a^2d_a,\quad B=t_c^2d_c,
$$

where $g,x,y$ are squarefree, pairwise coprime and prime to $J$.
In particular,

$$
(s_a,s_c)=g,\qquad
P(a,c)=q_{t_a}q_{t_c}q_g,\qquad
(a,c)=(A,B)g.
$$

Thus the sharp $P$ cut is a scalar restriction after fixing these cores
and $g$; it does not mask the remaining bulk rectangle. At $q_g\asymp G$,
$G\gg P_0/T^2$ and $G<U^{1/4}$.
The fixed primitive conductor and full conductor are

$$
f_0=\operatorname{rad}\!\left(
 \frac{A}{(A,B)}\frac{B}{(A,B)}\right),\qquad
F_0=q_{f_0},\qquad \mathfrak f=f_0xy.
$$

The support of $f_0$ lies in the symmetric difference of $t_a,t_c$;
$F_0\le q_J$ and $F_0/(q_Aq_B)\le1$.
The zero-only radical is $R=\operatorname{rad}(gABS)/f_0$.
Reuse the [all-column finite CRT formula](../Analytic/faveri2026fixedorder.md#extending-the-classwise-pole-consumer-to-all-convolution-columns),
which already treats reduced valuations $1,2,-1,-2$.
It supplies $\Gamma(\rho)\gamma_1(x)\gamma_{-1}(y)$,
separate fixed-core twists in $x,y$ and a reciprocity phase fixed on
bulk classes. The primitive $\rho$ has conductor $f_0$.
The remaining $\overline{\rho(m)}$, including its zeros, is a bounded
row multiplier. For $m=nv^6$ it becomes $\overline{\rho(n)}$ with the
$v$-collision mask. These are accepted by the positive-norm estimates;
no moving-conductor contour estimate or uniformly fixed bad-prime
assumption is introduced.

Set $X=U/(q_AG)$, $Y=U/(q_BG)$ and $B_0=U/G$, so $X,Y\le B_0$.
For the original $\kappa=q_\ell^6q_r$ expansion, Poisson contributes
$U/(\kappa\sqrt{F_0XY})$ and natural dual length

$$
M\ll\frac{\kappa F_0XY}{U}
 =\frac{\kappa UF_0}{q_Aq_BG^2}
 \le\frac{\kappa U}{G^2}.
$$

After detecting $(x,y)=1$ by $e$, $q_e\asymp E$, the normalized
vector-norm product is at most
$C_b^4U^\varepsilon\sqrt{XY}/(UE)$.
Multiplying the Poisson factor gives at most
$C_b^4U^\varepsilon/(\kappa E)$.
The $O(E)$ choices of $e$ and $O(G)$ choices of $g$ therefore give
exactly the high-core envelope (J9), with $H=G$ and $B=B_0$.

For the scalar cubic bound, open the two actual factors with

$$
d_1=t_ad_{a,1}g_1e_1u,\qquad
d_2=t_ad_{a,2}g_2e_2v,
$$

where the subscripts allocate $d_a,g,e$ between them.
The separate vectors retain
$b(t_ad_{a,1}g_1e_1u)$ and $b(t_ad_{a,2}g_2e_2v)$;
no multiplicativity or Möbius cancellation is used.
Their remaining length product is $X/E$ and each length is at most $D$.
The calculation (J5)--(J6), summed over allocations and $e$, bounds the
unnormalized squared scalar by
$C_b^4U^\varepsilon(XD+X^{5/3})$, and likewise for $Y$.
Restoring both normalizations and Poisson gives at most

$$
\frac{C_b^4U^\varepsilon}{\kappa\sqrt{F_0}}
\sqrt{(D+X^{2/3})(D+Y^{2/3})}
\le\frac{C_b^4U^\varepsilon}{\kappa}
 \left(U^{1/2}+U^{2/3}G^{-2/3}\right).
$$

The second term suffices because $G<U^{1/4}$.
The same low/high-core split as in (J8)--(J9), retaining all four terms
and all original $\ell,r$ and bad-dual sums, now gives for each fixed
repeated-core/occupancy pattern

$$
C_b^4U^\varepsilon
\left[U+U^{7/6}G^{-1}+U^{10/9}G^{-5/18}
 +U^{7/6}G^{-1/2}\right].
$$

The enlarged $R$ costs only a divisor loss; its primes are never deleted
from the original zeros. There are $O(T^2U^\varepsilon)$ repeated-core
pairs and occupancy patterns. Substitute $G\gg P_0/T^2$ to obtain
(J12). Also $q_A,q_B\le T^3$, whence
$X,Y\gg U^{3/4}T^{-3}$. For the following parameter range, the bulk
cannot have $x=y=1$, and actual ratio order six is retained.

In particular, let

$$
T=U^\theta,\qquad P_0=U^{1/6}T^6,\qquad0<\theta<1/72.
$$

The four terms of (J12) become
$UT^2$, $UT^{-2}$, $U^{115/108}T^{8/9}$ and $U^{13/12}$.
All are at most $U^{13/12}$, so

$$
\boxed{
|\mathcal E_{\tau,\le T}(P_0;b)|
\ll C_b^4U^{13/12+\varepsilon},\qquad
U^{1/6+6\theta}\le P<U^{1/4}.
}
\tag{J13}
$$

This extends the total-squarefree result (J10) to all cube-free
low-repeat columns in the stated equal-ray region. It applies directly
to the original Möbius, actual Type-II and rough factors of (J4).
A strong whole large-repeat tail for the latter two factors is not
supplied by this argument.

### Truncate before the positive class partition

For the **original Möbius source**, the [existing whole-tail estimate](../Analytic/liu2026quasirh.md#small-shared-gcd-localization-using-the-existing-inverse-l-input)
can be combined with (J13) without estimating signed cross-class
correlations. First set $g=g_D=g_{\le T}+g_{>T}$, and only then put
$c_{\tau,T}=g_{\le T}\mathbf1_{t(a)=\tau}$.
For $J_0=|\mathcal T|$ and the original physical-row operator $\mathsf A$,
finite Cauchy and Hilbert-space triangle give

$$
\mathcal T(g_{\le T})\le J_0\sum_\tau\mathcal T(c_{\tau,T}),
\qquad
\sqrt{\mathcal T(g)}\le
\sqrt{\mathcal T(g_{\le T})}+\sqrt{\mathcal T(g_{>T})}.
\tag{J14}
$$

No class filter is applied to the old tail bound. The coefficients,
physical rows and zeros are unchanged. Apply the cubic-block supplier
and (C18) afresh to each $c_{\tau,T}$ through its coefficient envelope.
Together with (J13), they pay the entire $P\ge P_0$ part at
$U^{13/12+\varepsilon}$ and the cubic part at $U^{1+\varepsilon}$.
Thus the only additional sufficient input is the **aggregate real upper
bound**

$$
\boxed{
\mathcal R_T(P_0):=
\operatorname{Re}\sum_\tau E_{6,\,P<P_0}(c_{\tau,T})
\ll U^{B_*-\sigma+\varepsilon},\qquad\sigma>0.
}
\tag{J15}
$$

The sum is the original ordered unequal-parity contraction with both
coefficients replaced by $c_{\tau,T}$. Separate absolute bounds for
every class are stronger than this sufficient target.
Assuming (J15), the owned bound
$\mathcal T(g_{>T})\ll U^{B_*-\theta/25+\varepsilon}$ and (J14) yield

$$
\boxed{
\mathcal T(g_D)\ll
U^{\max\{B_*-\theta/25,\ 13/12,\ B_*-\sigma\}+\varepsilon}.
}
\tag{J16}
$$

Every fixed
$0<\nu<\min\{\theta/25,\ B_*-13/12,\sigma\}$ is consequently a
full original inverse-fourth saving, **if (J15) is supplied** uniformly
for the original finite presentations and required profile derivatives.
Restore those presentations using their fixed positive norm costs.
For example, $\theta=1/1000$ gives $P_0=U^{259/1500}$ and tail saving
$1/25000$; an additional (J15) with $\sigma=1/100000$ would suffice
for any fixed $\nu<1/100000$. No such residual estimate is supplied here.
The $\theta/50$ cost in the earlier moment-difference comparison (C15)
is unnecessary for this one-sided upper bound: (J14) combines the new
head estimate directly with the tail norm.

The positive partition is a sufficient upper-bound route, not an
identification with or estimate of the original signed cross-class
$E_6$. Nor is (J15) asserted necessary or equivalent to RH.
For a truncated Type-II factor, its packets no longer have the two
inverse-$L$ series used in the original Möbius tail proof.
The fixed-core sixth-order sieve followed by Minkowski gives

$$
\mathcal T(h_{\mathrm{II},>T})
\ll U^\varepsilon\left(U+U^{7/6}T^{-2/3}\right).
$$

Indeed, at fixed $t$ the squarefree column length is $U/q_t^2$,
the normalized squared coefficient norm is $\ll U^\varepsilon/q_t^2$,
and $\chi_t(u)^2$ is a bounded row multiplier. Apply the existing
sixth-order sieve and then Minkowski over $q_t>T$.
This particular certificate beats $B_*$ only for
$\theta>(5\sqrt6-12)/2=0.123724\ldots$, incompatible with
$\theta<1/72$. The [direct density bound](#a-direct-repeat-tail-and-a-smaller-sufficient-head)
below is stronger, but also cannot pay a cutoff this small. Neither
certificate replaces the Möbius tail in (J16).
The residual (J15), full inverse-fourth improvement, signed Robin
restoration and RH remain open. These are source-conditional
applications of existing suppliers, not Lean-certified results.

### Summing every repeated core with unequal bulk norms

Retaining the core weights and the two bulk lengths separately removes
the low-repeat restriction from a further paid region. For $h_b$ in
(J4), let $\mathcal E_{\tau,P}^{\rm all}(b)$ be the original equal-ray,
unequal-parity contraction with $P\le P(a,c)<2P$, truncated at
$P(a,c)<U^{1/4}$. Keep every cube-free column and all original rows.
The same suppliers give

$$
\boxed{
|\mathcal E_{\tau,P}^{\rm all}(b)|
\ll C_b^4U^{7/6+\varepsilon}P^{-5/12},
\qquad 1\le P<U^{1/4}.
}
\tag{J17}
$$

In particular, summing dyads pays $U^{1/5}\le P<U^{1/4}$ at
$C_b^4U^{13/12+\varepsilon}$, with no repeated-core cutoff.

**Keep the actual factor cap.** Reuse the fixed-core decomposition in
(J11)--(J12), writing $t_a=c_0r_0$, $t_c=c_0s_0$, with $c_0,r_0,s_0$
pairwise coprime and squarefree. Let $C,R,S,G$ be their norm dyads and
that of $g$. Then $P\asymp C^2RSG$. The occupancy choices satisfy
$d_a\mid s_0$, $d_c\mid r_0$, and exactly

$$
(A,B)=c_0^2d_ad_c,\qquad f_0=r_0s_0,\qquad F_0=q_{f_0}\asymp RS.
$$

The actual lengths remain $X=U/(q_AG)$, $Y=U/(q_BG)$, and the natural
dual length is $M\ll\kappa UF_0/(q_Aq_BG^2)$.
In the scalar allocation each original factor on the $a$ side contains
$t_a$, so its remaining length is at most $D/q_{t_a}$.
The calculation behind (J6), summing the allocations and the common
coprimality ideal $e$, therefore gives for one fixed dual ideal

$$
\sum_e|H_{a,e}(m)|^2
\ll C_b^4U^\varepsilon X\left(D/q_{t_a}+X^{2/3}\right)
\ll C_b^4U^\varepsilon X^{5/3}.
$$

Indeed $D/q_{t_a}\le X^{2/3}$ is equivalent, up to fixed annular
constants, to $q_{t_a}q_{d_a}^2G^2\le U^{1/2}$; its left side is at
most $P^2$. The other side is identical with $a,c$ interchanged.
No multiplicativity of $b$ is required.

**Bound complete positive side norms separately.** Apply Cauchy to the
full $(e,m)$ sum before choosing its internal core thresholds.
For the $X$ side, its sixth-power-free dual core above $L$ costs

$$
C_b^4U^\varepsilon X
\left[M+X(M/L)^{1/6}+M^{5/6}X^{1/3}+M^{1/3}X^{5/6}\right].
$$

Below $L$, the scalar certificate costs
$C_b^4U^\varepsilon X^{5/3}M^{1/6}L^{5/6}$.
At $L=X^{1/3}$ these give

$$
\begin{aligned}
\sum_{e,m\sim M}|H_{a,e}(m)|^2
&\ll C_b^4U^\varepsilon XQ(M,X),\\
Q(M,X)&=M+M^{1/6}X^{17/18}
       +M^{5/6}X^{1/3}+M^{1/3}X^{5/6}.
\end{aligned}
\tag{J18}
$$

If $M<X^{1/3}$, the all-row scalar bound $MX^{5/3}$ is already
bounded by the second term of $XQ(M,X)$.
The $Y$ norm chooses its own threshold $Y^{1/3}$. These choices need
not agree: Cauchy uses two complete positive norms, not a common
partition of the signed contraction. Common-$e$ and dual collision
masks stay in the norms; fixed-core twists and $\bar\rho(m)$ remain
bounded coefficient factors or row multipliers throughout.

Poisson and the two original $D^{-1}$ coefficients now leave
$\kappa^{-1}F_0^{-1/2}\sqrt{Q(M,X)Q(M,Y)}$ per fixed core and $g$.
Counting their ideals in the dyads gives the positive majorant

$$
\frac{C_b^4U^\varepsilon GC\sqrt{RS}}{\kappa}
\sqrt{Q(M,X_0)Q(M,Y_0)},\qquad
\begin{cases}
X_0=U/(C^2R^2G),\\
Y_0=U/(C^2S^2G),\\
M\ll\kappa U/(C^4RSG^2).
\end{cases}
\tag{J19}
$$

The occupancy ideals are omitted only from this increasing positive
majorant: they decrease $X,Y,M$, and their count costs divisors.
They have not been removed from the CRT identities or original zeros.
Also $q_AG,q_BG\ll P^2$, so the actual $X,Y\gg U/P^2\gg U^{1/2}$;
the bulk principal exception $x=y=1$ is absent.

**Sum the original auxiliary rows and all core dyads.** Write
$C=U^c,R=U^r,S=U^s,G=U^g$ and $p=2c+r+s+g$ for the norm scales.
Fixed annular factors and dyads are absorbed in $U^\varepsilon$.
In (J19) the length exponents, before the $\kappa$ factor, are

$$
x=1-2c-2r-g,\quad y=1-2c-2s-g,\quad
m=1-4c-r-s-2g.
$$

Expand the two square roots into sixteen positive terms.
The four $M$-powers in $Q$ are
$\alpha=(1,1/6,5/6,1/3)$. A term $i,j$ has $\kappa$-power
$(\alpha_i+\alpha_j)/2-1$; summing the original
$q_\ell\ll U^{1/6}$ adds at most
$\max(0,(\alpha_i+\alpha_j)/2-5/6)$ to its $U$ exponent.
The zero-only $r$-divisors cost $U^\varepsilon$.
For a dual part supported on the fixed bad primes, the decay power is
$(\alpha_i+\alpha_j)/2>0$, so every such sum converges.
The original transform's rapid decay pays dyads beyond the natural
length. No original auxiliary expansion or bad-dual term is omitted.

Each resulting exponent is affine in $c,r,s,g$.
At $p=0$ all sixteen exponents are at most $7/6$.
At $p=1/4$, the simplex vertices and maxima are

| Nonzero core exponent | Maximum over the sixteen terms |
|---|---|
| $c=1/8$ | $11/12$ |
| $r=1/4$ or $s=1/4$ | $17/16$ |
| $g=1/4$ | $25/24$ |

Thus every exponent on $0\le p\le1/4$ is at most
$(1-4p)7/6+4p(17/16)=7/6-5p/12$. This proves (J17).
This is an unequal-length and weighted-core application of the existing
suppliers; no new sieve or literature-priority claim is made.

### An untruncated sufficient target for the actual Type-II factor

Combine (J17) with the coefficient-envelope bound (C18) for
$P\ge U^{1/4}$. For any genuine $h_b$ in (J4), first take the positive
finite class partition $c_\tau=h_b\mathbf1_{t(a)=\tau}$.
The entire $P\ge U^{1/5}$ part is paid at
$C_b^4U^{13/12+\varepsilon}$, and its cubic block at
$C_b^4U^{1+\varepsilon}$. Consequently the additional sufficient input

$$
\operatorname{Re}\sum_\tau E_{6,\,P<U^{1/5}}(c_\tau)
\ll U^{B_*-\sigma+\varepsilon},\qquad\sigma>0,
\tag{J20}
$$

would imply $\mathcal T(h_b)\ll
U^{\max(13/12,B_*-\sigma)+\varepsilon}$ for fixed $C_b$.
The head here has no repeated-core truncation, so no Type-II tail
estimate is needed. This supplies a different route from the smaller,
truncated original-Möbius target (J15); neither residual is supplied.

For the actual Type-II factor $b=\lambda_{\mathrm{II},b}$, use its exact
polynomial identity with the paid Type-I part (C30) and apply the
$L^4$ triangle inequality directly. Assuming (J20) uniformly for its
original finite components and required profile derivatives, the
original Möbius fourth moment then has the same exponent
$\max(13/12,B_*-\sigma)$.
Every fixed $0<\nu<\min(B_*-13/12,\sigma)$ would be a saving.
The smaller $(B_*-13/12)/4$ transfer allowance in (C31)--(C32) belongs
to their moment-difference comparison; this one-sided consumer does
not compare those signed differences.
No bound for (J20), complete inverse-fourth improvement, signed Robin
restoration or RH is proved by the paid sector alone.

### A small parity core in the full natural good-dual range

A separate application pays an arithmetic part of the full natural dual
range in precisely $\mathfrak E_{1,b}(M)$ from (J1)--(J6).
Retain its good-dual selector, equal ray and
$t_a=t_c=h=\ell=r=1$ restrictions, and select $q_{r_2(m)}\le A_0$.
Then

$$
\boxed{
|\mathfrak E_{1,b,\,q_{r_2(m)}\le A_0}(M)|
\ll C_b^4U^\varepsilon U^{8/9}M^{1/6}A_0^{5/6},
\qquad1\le A_0\le M\le U.
}
\tag{J21}
$$

Write uniquely $m=ab^2v^6$, where $a=r_2(m)$ is squarefree,
$b$ is cubefree and $ab^2$ is sixth-power-free.
No coprimality between $a,b,v$ is imposed. For fixed $a,v$,

$$
\overline{\chi_x(m)}=
\overline{\chi_x(a)}\,\overline{\kappa_x(b)}
\mathbf1_{(x,v)=1},\qquad \kappa_x=\chi_x^2.
$$

Thus the $b$ family is genuinely cubic. Its fixed $a$ twist and all
$v$ and common-$e$ collisions remain in the separate coefficient
vectors or row masks. This is a support restriction, not a global
conversion of the sextic matrix to a cubic one.

At norm dyads $q_a\asymp A$, $q_v\asymp V$, the cubic row length is
$B\asymp(M/(AV^6))^{1/2}\le\sqrt U$.
Reuse the [cubefree-index cubic supplier](../Analytic/faveri2026fixedorder.md#separating-the-lower-order-character-blocks)
$\Theta_3(B,X)\ll(BX)^\varepsilon[B+X+(BX)^{2/3}]$.
Here $X\le U$, so it costs at most $U^{1+\varepsilon}$.
The J1 common-$e$ vector norms and $O(A V)$ choices of $a,v$ give
$C_b^4U^{1+\varepsilon}AV$.
Independently, J6 and ideal counting of these same duals give
$C_b^4U^{2/3+\varepsilon}M^{1/2}A^{1/2}V^{-2}$.
Their crossover is $V_0=U^{-1/9}M^{1/6}A^{-1/6}$.
Summing the minimum over $V$, then over $A\le A_0$, gives (J21).
When $V_0<1$, the scalar branch alone is smaller than that envelope.

In particular $A_0\le U^{1/30}$ pays this selected support at
$U^{13/12+\varepsilon}$ through $M\asymp U$, beyond J1's uniformly
paid prefix $M\le U^{3/4}$.
The remaining large parity cores, other original auxiliary expansions
and bad duals are outside (J21). This restricted result does not supply
(J15) or (J20). All results in this note remain source-conditional
applications, without analytic Lean certification or an RH proof.

### A direct repeat tail and a smaller sufficient head

The support-density argument already used in
[(C35)](../Analytic/liu2026quasirh.md#rough-support-of-the-actual-type-ii-remainder)
applies to a general repeat cutoff, without first fixing each repeated
core. Combining it with the joint core constraints in (J19) gives a
smaller sufficient head for every genuine $h_b$ in (J4), including the
actual Type-II factor. These are applications of the same sixth-order
and cubic suppliers, not new sieves or literature-priority claims.

**Apply the sieve to the whole tail.** Write each supported column
uniquely as $a=t_{\rm rep}(a)^2s$, with $t_{\rm rep}(a),s$ squarefree
and coprime.
For $1\le T\le\sqrt U$, put
$h_{b,>T}=h_b\mathbf1_{q_{t_{\rm rep}(a)}>T}$. The original divisor envelope and
ideal counting give

$$
\begin{aligned}
\|h_{b,>T}\|_2^2
&\ll C_b^4U^{-1+\varepsilon}
 \sum_{q_t>T}\#\{s:q_s\ll U/q_t^2\}\\
&\ll C_b^4U^\varepsilon\sum_{q_t>T}q_t^{-2}
 \ll C_b^4U^\varepsilon T^{-1}.
\end{aligned}
$$

Every such column is cube-free, hence sixth-power-free. Directly apply
the [owned sixth-order supplier](../Analytic/faveri2026fixedorder.md#the-large-sieve-statement)
at lengths $U,U$ to this one row-independent coefficient vector:

$$
\boxed{
\mathcal T(h_{b,>T})
\ll C_b^4U^{7/6+\varepsilon}T^{-1}.
}
\tag{J22}
$$

The fixed physical presentations, their twists and the original zeros
are transported exactly as in that supplier's existing family interface.
An enlargement is made only within the positive row norm. This is a
fresh sieve application to a supported vector, not a contraction of an
already estimated moment under a column mask. No inverse-$L$ identity
or factorization of the truncated coefficient is required.
The same estimate applies to the required finitely many profile
derivatives within the original fixed or polylogarithmic height contract.

Set $T=U^{1/12}$ and truncate before the positive ray partition:
$c_{\tau,T}=h_b\mathbf1_{q_{t_{\rm rep}(a)}\le T}\mathbf1_{t(a)=\tau}$,
where $t(a)=\tau$ denotes the existing ray label.
The whole discarded tail is now paid at $C_b^4U^{13/12+\varepsilon}$.

**Retain both repeat caps in the complete-dual estimate.** For each
dyad $U^{1/6}\le P<U^{1/4}$, use (J18)--(J19) on these coefficients,
retaining the complete original equal-ray, unequal-parity kernel.
The cutoff is constant after fixing its cores; it does not change
either actual convolution-factor vector. Then

$$
\boxed{
|E_{6,\,P\le P(a,c)<\min(2P,U^{1/4})}(c_{\tau,T})|
\ll C_b^4U^{13/12+\varepsilon},\qquad T=U^{1/12}.
}
\tag{J23}
$$

Here is the additional joint estimate needed beyond (J17).
In its notation put $C=U^c,R=U^r,S=U^s,G=U^g$. The two caps give
$c+r\le1/12$, $c+s\le1/12$, while
$p=2c+r+s+g\ge1/6$. Fixed annular constants enter $U^\varepsilon$.
For $\alpha=(1,1/6,5/6,1/3)$ and
$\beta=(0,17/18,1/3,5/6)$, each of the sixteen positive terms has
exponent

$$
\begin{aligned}
f_{ij}={}&g+c+(r+s)/2
 +\tfrac12(\alpha_i+\alpha_j)(1-4c-r-s-2g)\\
&+\tfrac12\beta_i(1-2c-2r-g)
 +\tfrac12\beta_j(1-2c-2s-g)\\
&+\max\{0,(\alpha_i+\alpha_j)/2-5/6\}.
\end{aligned}
$$

The last term already pays the original $\ell$ sum, exactly as in (J17).
Across the sixteen terms, the largest coefficients of $c,r,s,g$ are
respectively $-14/9,-1/12,-1/12,-5/18$. Thus each exponent decreases
in each coordinate. Scaling all four coordinates down by $1/(6p)$
preserves the two caps and can only increase the bound, so it suffices
to treat $p=1/6$.
On that face, $0\le r,s\le1/12-c$ and
$g=1/6-2c-r-s$. Its square sections contract to the apex, giving exactly
the following five vertices and maxima:

| $(c,r,s,g)$ | $\max_{i,j}f_{ij}$ |
|---|---|
| $(0,0,0,1/6)$ | $13/12$ |
| $(0,1/12,0,1/12)$ | $77/72$ |
| $(0,0,1/12,1/12)$ | $77/72$ |
| $(0,1/12,1/12,0)$ | $13/12$ |
| $(1/12,0,0,0)$ | $1$ |

Affine interpolation proves (J23). Occupancy ideals are omitted only
from the increasing positive majorant, as in (J19). All original
$\ell,r$, common-$e$ masks, fixed-core twists, collision zeros and
bad-dual sums remain covered by that calculation. In particular no
new principal bulk exception is introduced.

**The sufficient original-coefficient input.** Use (C18) for
$P\ge U^{1/4}$ and (J23) below it. Apply the existing cubic-block bound
to each $c_{\tau,T}$ afresh through its divisor envelope. The additional
sufficient estimate is now

$$
\boxed{
\operatorname{Re}\sum_\tau
E_{6,\,P<U^{1/6}}(c_{\tau,T})
\ll C_b^4U^{B_*-\sigma+\varepsilon},
\qquad T=U^{1/12},\quad\sigma>0.
}
\tag{J24}
$$

Assuming this uniformly for the original components and required
profile derivatives, finite positive partition and the whole-tail
norm triangle (J14), now with (J22), imply

$$
\boxed{
\mathcal T(h_b)
\ll C_b^4U^{\max\{13/12,B_*-\sigma\}+\varepsilon}.
}
\tag{J25}
$$

For actual $b=\lambda_{\mathrm{II},b}$, combine with (C30) by the direct
$L^4$ triangle as in (J20). Every fixed
$0<\nu<\min\{B_*-13/12,\sigma\}$ would then be an original Möbius
fourth-moment saving. This remains conditional on (J24). It bounds the
aggregate real head, without requiring separate absolute estimates
for each ray or subtracting a masked moment from a full one.
The small-cutoff original-Möbius route (J15) remains separate.

**Two rough prime-overlap shapes remain.** For the actual rough factor
$b=r_A\lambda_{\mathrm{II},b}$ in (C33), every prime exceeds
$2A=2U^{1/12}$. A nonunit repeated core therefore exceeds $T$ and is
already in the paid tail; the retained coefficient is precisely the
squarefree part $g_{\rm sf}$ of (C34)--(C35).
On two such columns $P=q_g$, where $g$ is their squarefree gcd.
If $q_g<U^{1/6}$, then $g$ is either $1$ or one prime of norm
$2U^{1/12}<q_g<U^{1/6}$, since a product of two supported primes
exceeds $4U^{1/6}$.
Thus in this rough specialization (J24) consists only of the coprime
squarefree-column contraction and the one-common-prime contraction,
with their actual coefficients, phases and zeros. Their combined real
upper bound is not supplied. The nonrough Type-II part remains outside
this specialization, so a saving for these rough shapes alone does not
prove the full (J24), signed Robin restoration or RH.
