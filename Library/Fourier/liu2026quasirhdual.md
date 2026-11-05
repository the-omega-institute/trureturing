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

### One-factor completion retains a joint coefficient array

This is a `repo-derived`, source-conditional applicability and cost check
for (J4)--(J6), reusing finite Fourier/Gauss identities. Fix an original
ray/unit component and its original representative of each ideal, extending
coefficients by zero to $\mathcal O=\mathbb Z[\omega]$. Put $\delta=\sqrt{-3}$,
$e_K(z)=\exp(2\pi i\operatorname{Tr}_{K/\mathbb Q}z)$; the codifferent is
$\delta^{-1}\mathcal O$, so $e_K(rx/(\delta f))$ pairs $\mathcal O/(f)$ perfectly.
After the finite reciprocity correction, extract from one actual $u$ factor
its primitive finite character $\chi_m$, of conductor $\mathfrak f=(f)$ and
$Q=N\mathfrak f$. At fixed $m,v$, write that factor as
$S_{m,v}=\sum_u a_v(u)\chi_m(u)$, $H_m=\sum_v c_m(v)S_{m,v}$,
with the original outer weights $c_m(v)$. Set, for $x,r\bmod f$,

$$
A_{m,v}(x)=\sum_{u\equiv x\ (f)}a_v(u),\qquad
B_{m,v}(r)=Q^{-1/2}\sum_{x\bmod f}A_{m,v}(x)e_K(-rx/(\delta f)).
$$

Fourier inversion and the primitive Gauss identity give exactly

$$
S_{m,v}=\gamma_m\sum_{r\bmod f}B_{m,v}(r)\overline{\chi_m(r)},\qquad
\gamma_m=Q^{-1/2}\sum_{x\bmod f}\chi_m(x)e_K(x/(\delta f)),\quad
|\gamma_m|=1,\qquad \sum_r|B_{m,v}(r)|^2=\sum_x|A_{m,v}(x)|^2.
$$

[Gao--Zhao v2, §2.2 (2.3) and Lemma 2.3](https://arxiv.org/html/2201.01885v2#S2.SS2)
give the squarefree Gauss magnitude, coprime shifts and local collision
zeros, with $\widetilde e(z)=e_K(z/\delta)$. The primitive identity vanishes
at nonunits of $\mathfrak f$. For imprimitive original constituents use
this primitive conductor and retain every extra zero mask in $a_v$;
unit Gauss normalization at the larger original modulus is not asserted.
Injective periodization of the support $q_u\ll N_u$ gives
$\|B_{m,v}\|_2=\|a_v\|_2$; $N_u=o(Q)$ suffices by the diameter bound below.
But $a_v$ retains $b(e_1u)$, $\gamma_1(u)$, $\theta_e(u)$, $\kappa_u(v)$,
the original profiles, angular/ray data and all zeros. Thus $B$ depends on
both $m$ and $v$; no common coefficient vector or short support follows.
For a nontrivial primitive ray character and the smooth compactly supported
radial majorant specified in [de Faveri v1, Lemma 3.1](https://arxiv.org/html/2610.04045v1#S3.Thmtheorem1),
the ideal sum has prefactor $N/\sqrt Q$ and rapidly decaying dual length
$Q/N$. That smooth-coefficient statement is not applied to this $a_v$.

For $e_1=e_2=1$, $N_u=N_v=D=\sqrt U$ and $Q\asymp U$, rowwise Cauchy
over all $Q$ transformed coordinates gives the specified certificate

$$
|H_m/D|^2\ll C_b^4U^\varepsilon QN_uN_v^2/D^2
\asymp C_b^4U^{3/2+\varepsilon}.
$$

Here $H_m=H_{1,m}^{1,1}$ is the unnormalized (J6) scalar. Its elementary
physical-coordinate certificate instead uses $N_u^2N_v^2/D^2$; completion
followed by this Cauchy costs $Q/N_u\asymp U^{1/2}$. The already owned (J6)
certificate is $C_b^4U^{2/3+\varepsilon}$. These are upper certificates
for the same normalized scalar, not lower bounds or full-(J24) exponents.

**Moving collision zeros test the short-dual premise.** At $N_u=N$,
$Q\asymp N^2$, take any fixed finite rational centers
$\Xi\subset K/\mathcal O$. Choose a fixed ideal $\mathfrak H$ with
$\xi\mathfrak H\subset\mathcal O$ for every $\xi\in\Xi$; this includes
packets from all original fixed bad moduli. Suppose $E=\|a_v\|_2^2>0$
and a good prime $\mathfrak p\mid v$ has $P=N\mathfrak p$ and
$(\mathfrak p,\mathfrak H)=1$. The actual $\kappa_u(v)$ makes $a_v(u)=0$
whenever $\mathfrak p\mid u$, including the zero extension outside support.
Choose $P$ representatives $h\in\mathfrak H$ modulo $\mathfrak p$ with
$Nh\ll_{\mathfrak H}P$, using a fundamental parallelogram of
$\mathfrak H\mathfrak p$. Require reduction modulo $f$ injective on the
support and all its translates by these $h$. For $q_u\ll N$, $P=o(N)$
and $Q\asymp N^2$, their squared diameter is $O_{\mathfrak H}(N+P)<Q$,
which verifies this requirement: a nonzero element of $(f)$ has norm at least $Q$.
For each supported $u$, some $h$ has $u+h\equiv0\pmod{\mathfrak p}$;
no alias can fill that zero. With $T_hA(x)=A(x+h)$, consequently
$\sum_h\|T_hA-A\|_2^2\ge E$.

Let $E_{\rm tail}(\Xi,L)$ be the $B$ energy outside the union of bands
$\operatorname{dist}(r/f,\xi+\mathcal O)^2\le L/N$; equivalently
$|r-f\xi|^2\le LQ/N$ modulo $f\mathcal O$, the ordinary dual norm scale.
On these bands $|e_K(rh/(\delta f))-1|^2\ll_{\mathfrak H}PL/N$,
since $\xi$ annihilates $\mathfrak H$; elsewhere it is at most $4$.
Parseval, summed over the $P$ translations, therefore gives

$$
E\le C_\Xi P^2(L/N)E+4P E_{\rm tail}(\Xi,L),\qquad
E_{\rm tail}(\Xi,L)\ge\frac{1-C_\Xi P^2L/N}{4P}E.
$$

**An actual nonzero instance.** Use $b=\lambda_{\mathrm{II},b}$,
$A_{\rm b}=N^{1/6}$, $U=N^2$, and a fixed original $V\ne0$. Use the (J5)
factor with its original two $V$ profiles and fixed Mellin heights.
In a compact interval where $|V|>0$, choose squarefree $v=\mathfrak p\mathfrak q\mathfrak r$
with $P\asymp\log N\le A_{\rm b}$ and $q_{\mathfrak q},q_{\mathfrak r}\asymp\sqrt{N/P}>2A_{\rm b}$.
The exact [C25/C37--C40 coefficient](../Analytic/liu2026quasirh.md#cofactor-recursion-and-the-actual-prime-slot-capacity)
has only $1,\mathfrak p$ in its $W$-weighted divisor sum, giving
$K_{A_{\rm b}}(v)=1-2=-1$ and $b(v)=\mu(v)+K_{A_{\rm b}}(v)=-2$.
Choose $u$ as a distinct rough semiprime of norm in the same nonzero
$V$ interval times $N$, with both primes $\asymp\sqrt N>4A_{\rm b}$;
(C33) gives $b(u)=2$. The [existing fixed-ray prime-pair counting input](../Analytic/liu2026quasirh.md#the-original-convolution-norm-before-sixth-power-compression)
supplies these choices: fix prime classes with the prescribed product
classes, use disjoint fixed relative norm intervals at the displayed scales,
and delete the finitely many collisions. Choose a good prime dual $m$
of norm $\asymp N^2$ in an allowed class; its primitive conductor has
$Q\asymp N^2$, and it meets neither $u$ nor $v$. Original unit representatives
and finite twists are retained, $\kappa_u(v)\ne0$, and all remaining (J5)
phases have unit modulus. The specified nonzero $V$ intervals and allowed
classes therefore give $a_v(u)\ne0$ and $E>0$ for this actual factor.
Taking $L=N^{1/2}$ (eventually $2\le L\le N/10$) gives
$E_{\rm tail}/E\ge1/(8P)\gg1/\log N$. This refutes uniform
$E_{\rm tail}\ll_A L^{-A}E$ for these actual Type-II factors, even after
any fixed finite rational packets. It is no lower bound for $H_m$, a row
moment or (J24): cross terms can cancel. Growing or $m$-dependent packets
and joint-array estimates remain possible. Completion leaves the weighted
$\sum_v c_m(v)B_{m,v}(r)$ contraction against $\overline{\chi_m(r)}$ joint
in $m,v,r$. The unpaid quantitative target remains exactly (J24), with each
eligible factor replaced by this array, at full natural lengths and with
every original component and required profile derivative.
No new harmonic-analysis theorem, analytic saving, originality, RH proof
or Lean certification is claimed.

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

### A simultaneous cubic average in the full weighted small-parity sector

The following `repo-derived` application uses [de Faveri,
*Optimal large sieve for fixed order characters*, arXiv:2610.04045v1,
§8, Proposition 8.1, (8.1)](https://arxiv.org/html/2610.04045v1#S8.Thmtheorem1)
on the original two convolution variables and the square part of the
complete dual ideal. The other inputs are the Gauss CRT and smooth calculus
of the [pinned primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
`lem:fixed-gauss-phase`, `eq:sextic-sieve-pair-gauss`,
`eq:sextic-sieve-pair-poisson`, `eq:sextic-sieve-transform-bounds` and
`lem:smooth-calculus`, with the already matched
[all-column CRT](../Analytic/faveri2026fixedorder.md#extending-the-classwise-pole-consumer-to-all-convolution-columns).
This is a paper/source-conditional estimate, with no new sieve,
literature-priority claim or Lean certification.

**The sector is defined after the original Poisson expansion.** Keep
$c_{\tau,T}$ in (J24), $T=U^{1/12}$, and the actual
$b=\lambda_{\mathrm{II},b}$ in (J4), with $|b|\le\tau_3$.
More generally the argument accepts the stated $C_b\tau_k$ envelope.
For $1\le P<U^{1/6}$ and $H\ge1$, let $\mathfrak D_{P,\le H}$ be the
sum of the actual complete-dual terms of
$\sum_\tau E_{6,\,P\le P(a,c)<\min(2P,U^{1/6})}(c_{\tau,T})$
whose good dual part satisfies $q_{r_2(m_{\rm good})}\le H$.
The selector is inserted in each pair's Poisson series before profile
separation and the common-$e$ expansion. This definition retains every
original finite ray/angular component, original $\ell,r$ term,
repeated core, occupancy choice, allocation, bad-prime dual part and
required derivative profile. All dual dyads are retained, with the
original Fourier decay. It defines neither a positive physical moment
nor a nonnegative subset of $E_6$. The source-conditional bound is

$$
\boxed{
|\mathfrak D_{P,\le H}|
\ll C_b^4U^{1+\varepsilon}
       \left(H^{1/2}+P^{1/3}H^{2/3}\right).
}
\tag{J26}
$$

Constants have the same fixed-data and profile-seminorm dependence as
(J18)--(J19); their original fixed or polylogarithmic aggregate costs
are required. In particular,

$$
\boxed{
H(P)=U^{1/8}P^{-1/2}
\quad\Longrightarrow\quad
|\mathfrak D_{P,\le H(P)}|
\ll C_b^4U^{13/12+\varepsilon}.
}
\tag{J27}
$$

Since $H(P)\ge U^{1/24}$ in this $P$ range, the same estimate, summed
over $P$, pays the entire original expanded sector with
$q_{r_2(m_{\rm good})}\le U^{1/24}$. No repeated-core cutoff beyond the
one already present in $c_{\tau,T}$ is added.

**Actual coefficients in a fixed core.** Use exactly the notation of
(J18)--(J19): $t_a=c_0r_0$, $t_c=c_0s_0$, with pairwise coprime
squarefree $c_0,r_0,s_0$; $d_a\mid s_0$, $d_c\mid r_0$; and

$$
a=Agx,\quad c=Bgy,\quad A=t_a^2d_a,\quad B=t_c^2d_c,
\quad f_0=r_0s_0,\quad F_0=q_{f_0},\quad
X=\frac{U}{q_AG},\quad Y=\frac{U}{q_BG}.
$$

The primitive fixed character $\rho$ on $f_0$ has local exponents
$2-\mathbf1_{p\mid d_c}$ at $p\mid r_0$, and
$-2+\mathbf1_{p\mid d_a}$ at $p\mid s_0$, in the original raw sextic
symbols. These exponents are $1,2,-1,-2$, respectively; its original
zeros are retained. The remaining zero-only radical is
$R_0=\operatorname{rad}(gABS)/f_0$.
Fix the original $r\mid R_0$, the allowed $\ell$ and
$\kappa=q_\ell^6q_r$. The row substitution supplies
$\rho(r)\chi_x(r)\overline{\chi_y(r)}$ and the original
$\ell$-coprimality masks. Its Möbius signs remain outside the two side
norms. The complete CRT root is the cited one, including
$\Gamma(\rho)$, the fixed bulk-class reciprocity factor and
$\gamma_{-1}(y)=\chi_y(-1)\overline{\gamma_1(y)}$.

After detecting $(x,y)=1$, fix the squarefree $e$ and allocate
$d_a=d_{a,1}d_{a,2}$, $g=g_1g_2$, $e=e_1e_2$. On the $a$ side put

$$
k_i=t_ad_{a,i}g_ie_i,\qquad
x=euv,\qquad d_1=k_1u,\quad d_2=k_2v,
\qquad q_u\asymp L_1,\quad q_v\asymp L_2.
$$

Thus $L_1L_2\asymp X/q_e$ and each $L_i\ll D/q_{t_a}\le D$.
Every original convolution coefficient remains $b(k_1u)b(k_2v)$;
in particular the three-slot definition of $\lambda_{\mathrm{II},b}$
is neither opened into new independent vectors nor replaced by an
optimizing vector. Its envelope is used only for squared vector norms.
Use $t_c,d_c$ on the other side. The original caps
$q_{t_a},q_{t_c}\le T$ are scalar restrictions on these fixed cores
and remain in the outer sum.

Here is an explicit separated presentation, with constants depending
only on the fixed data of this application left outside the scalar.
Let $\delta_i(w)$ retain squarefreeness, goodness,
$(w,\ell t_at_cge)=1$ and its chosen ray class; let $\zeta_i(w)$
be the chosen factor in the original multiplicative ray/angular
expansion, with its original coefficient outside the scalar. For the
(J4) component itself $\zeta_i=1$; factors already included in $\xi$
are not inserted again.
Partition the two variable classes far enough that $\mathcal R(u,v)$
in (J5) is constant. With
$\theta_e(w)=\chi_e(w)\chi_w(e)$, write

$$
\begin{aligned}
A_u&=b(k_1u)V(q_{k_1}q_u/D)\xi(u)\gamma_1(u)\theta_e(u)
       \eta_1(u)q_u^{it_1},\\
B_v&=b(k_2v)V(q_{k_2}q_v/D)\xi(v)\gamma_1(v)\theta_e(v)
       \eta_2(v)q_v^{it_2}.
\end{aligned}
\tag{J28}
$$

To specify $\eta_i$, fix a generator $\widetilde s$ of the bad-prime
part of $m$, together with any original unit component. On the $a$
side its factors are exactly

$$
\eta_i(w)=\delta_i(w)\zeta_i(w)\rho(w)\chi_w(f_0r)
                         \overline{\chi_w(\widetilde s)}.
$$

For the $c$ side conjugate its entire scalar: replace
$\rho(w)\chi_w(f_0r)$ in this formula by
$\overline{\rho(w)}\chi_w(-f_0r)$, retain its own original finite
factors and profiles, and conjugate the resulting side in the final
pairing. The $-1$ is precisely the retained $\gamma_{-1}$ sign.
Factors evaluated at $e$ or the allocated fixed cores stay outside;
any original collision there makes that term zero. All displayed
$\eta_i$ have modulus at most the original component bound. Fixed
core characters are coefficient factors, not added to the bad set of
the cited theorem. Norm normalizations on compact annuli are included
in the separated smooth profile; $t_1,t_2$ are its real Mellin heights.
This describes each original finite component separately, with its
original coefficient in the outer sum.

For this fixed component the unnormalized scalar is therefore

$$
H_{\beta z^2}
 =\sum_{u,v}A_uB_v\kappa_u(v)
       \overline{\chi_u(\beta z^2)\chi_v(\beta z^2)},
\qquad \kappa_u=\chi_u^2.
\tag{J29}
$$

The full dual ideal is $m=s\beta z^2$, where
$m_{\rm good}=\beta z^2$ uniquely, $\beta=r_2(m_{\rm good})$ is
squarefree, and $(\beta,z)>1$ is allowed. The bounded primitive-core
factor $\overline{\rho(m)}$ and the common-$e$ collision mask are
still outer row multipliers. Formula (J29) is an algebraic extension
of the original coprime bulk formula, used only inside its exact
Möbius detection. It asserts no primitive conductor formula for the
added noncoprime pairs.

**Match the fixed-vector theorem, including its zeros.** Multiplicativity
and the zero-preserving convention for powers give, for every $u,v,\beta,z$,

$$
\kappa_u(v)\overline{\chi_u(\beta z^2)}
 =\overline{\chi_u(\beta)}\kappa_u(vz^2).
\tag{J30}
$$

A prime common to $u$ and any of $v,\beta,z$ makes both sides zero.
The $v$-dual zeros remain in the other factor of (J29). For fixed
$\beta,\widetilde s,e$, allocations and separating heights, set
$\lambda_u=A_u\overline{\chi_u(\beta)}$. This vector is squarefree
in $u$ and independent of both $v$ and $z$.

The character correspondence is exact, rather than an identification
by order alone. The primary manuscript defines
$\kappa_u(w)=(w/u)_3$ on its generators congruent to $1\pmod3$.
[De Faveri's Example 2.2](https://arxiv.org/html/2610.04045v1#S2.SS4)
identifies its cubic family with $\chi^{\rm dF}_u(w)=(u/w)_3$ for
these same primary generators. The primary manuscript's precise cubic
reciprocity in `lem:fixed-gauss-phase` gives equality on coprime inputs;
both families are zero on collisions, by their respective definitions.
Apply that example with its fixed exclusion of the prime above $3$;
our original extra fixed bad primes are retained as support masks.
On added positive-norm rows use the source character family itself;
the equality with the raw kernel is needed only on the original good
rows. Thus no growing modulus or extra reciprocity weight is inserted in
Proposition 8.1. The sextic sign $\mathcal R$ has already been retained
in (J5), and is not an omitted cubic correction.

Cauchy in $v$ gives, before any row enlargement,

$$
|H_{\beta z^2}|^2
\le\left(\sum_v|B_v|^2|\chi_v(\beta z^2)|^2\right)
 \sum_{v\ {\rm original}}
 \left|\sum_u\lambda_u\kappa_u(vz^2)\right|^2.
$$

Bound the first factor by $C_b^2U^\varepsilon L_2$ and enlarge the
$v,z$ sets only in the remaining nonnegative squared norm. Proposition
8.1 applies with $(\mathfrak q,\mathfrak a,\mathfrak b)=(u,v,z)$,
$\|\lambda\|_2^2\ll C_b^2U^\varepsilon L_1$, and gives

$$
\begin{aligned}
\sum_{z\sim Z}|H_{\beta z^2}|^2
 &\ll C_b^4(UZ)^\varepsilon L_1L_2 F(L_2,Z;L_1),\\
F(A,B;Q)&=AB+\min(A,B)^{2/3}\max(A,B)^{1/3}Q
                  +\min(A,B)^{1/3}\max(A,B)^{2/3}Q^{2/3}.
\end{aligned}
\tag{J31}
$$

The outer ideals in the cited theorem are arbitrary, so $z$ need not
be squarefree or coprime to $\beta$. Its only squarefree requirement
is the one already met by $u$. Remark 8.2's unworked cube-free inner
extension is not used. In particular this argument never treats the
moving joint coefficient array $B_{m,v}$ as a common inner vector.
Common-$e$, fixed-core and $v$-dual row masks can be enlarged only at
the positive-norm step above; they have not been deleted from the
signed contraction.

**Sum allocations and parity cores before restoring normalization.**
For $L_1,L_2\ll D$ and every $Z\ge1$,

$$
F(L_2,Z;L_1)\ll DZ+D^{4/3}Z^{2/3}.
$$

For $Z\le D$ its two mixed terms are at most
$D^{4/3}Z^{2/3}$; for $Z\ge D$ they are bounded by
$D^{4/3}Z^{2/3}$ and $DZ$, respectively. Thus this comparison imposes
no upper cutoff on $Z$. In a good-dual dyad $q_{m_{\rm good}}\asymp M$,
$Z\asymp(M/q_\beta)^{1/2}$ and only $q_\beta\ll M$ occur. Ordinary
ideal counting yields

$$
\sum_{q_\beta\le H}Z\ll M^{1/2}H^{1/2},\qquad
\sum_{q_\beta\le H}Z^{2/3}\ll M^{1/3}H^{2/3},
$$

where empty $Z<1$ boxes are omitted; the bounds also hold when $H>M$.
Cauchy over the actual allocations costs only divisors. Since
$L_1L_2\asymp X/q_e$ and
$\sum_{q_e\ll X}\tau_k(e)/q_e\ll U^\varepsilon$, summing $e$ gives

$$
\boxed{
\sum_{\substack{e,\,m_{\rm good}\sim M\\ q_{r_2(m_{\rm good})}\le H}}
 |H_{a,e}(m)|^2
\ll C_b^4(UM)^\varepsilon X\,
 \left[DM^{1/2}H^{1/2}+D^{4/3}M^{1/3}H^{2/3}\right].
}
\tag{J32}
$$

The $(UM)^\varepsilon$ notation retains the source theorem's
length loss on the unrestricted dual dyads. The original nonempty-row
cutoff bounds $\ell,r$ and the core scales polynomially in $U$, so
$N_s\ll U^{O(1)}$ below. Rapid decay absorbs the remaining
$(1+M/N_s)^{\varepsilon}$ factor; the final loss is $U^\varepsilon$
after choosing the input epsilon smaller.

The $Y$ side has its own allocations and the identical bracket.
Apply Cauchy between these two complete $(e,m)$ side norms with all
original outer masks bounded there. Restore $D^{-2}=U^{-1}$ and the
Poisson factor $U/(\kappa\sqrt{F_0XY})$: per fixed core the bracket
in (J32) is multiplied by $1/(\kappa\sqrt{F_0})$.
Counting $c_0,r_0,s_0,g$ in their dyads gives precisely the (J19)
prefactor $GC\sqrt{RS}/\kappa$.

Occupancy ideals remain in every identity and coefficient. In this
positive majorant they only decrease $X,Y$ and the natural length;
their number is a divisor loss. With the same $X_0,Y_0$ as (J19),
write

$$
N_s=\frac{\kappa U}{C^4RSG^2q_s}.
$$

This is an upper bound for the actual natural good-dual length, not a
truncation. For $\alpha=1/2,1/3$ and fixed $A_1>1$,
$\sum_{M\ge1\ {\rm dyadic}}M^\alpha(1+M/N_s)^{-A_1}\ll N_s^\alpha$,
also when $N_s<1$. On every dual dyad, the original transform and each
required logarithmic derivative contribute arbitrary decay in
$M/N_s$ beyond this scale. Summing all dyads in (J32), including the
case $N_s<1$, replaces $M^{1/2},M^{1/3}$ by
$N_s^{1/2},N_s^{1/3}$ in the positive bound. The core envelope is
consequently

$$
C_b^4U^{1+\varepsilon}
\left[
 C^{-1}\kappa^{-1/2}q_s^{-1/2}H^{1/2}
 +G^{1/3}C^{-1/3}(RS)^{1/6}
       \kappa^{-2/3}q_s^{-1/3}H^{2/3}
\right].
\tag{J33}
$$

The $\ell$ sums are $\sum q_\ell^{-3}$ and $\sum q_\ell^{-4}$,
both convergent. The original zero-only $r$ sums have powers
$q_r^{-1/2}$ and $q_r^{-2/3}$ and cost $U^\varepsilon$ over divisors
of $R_0$. The two fixed-$S$ dual sums converge by the displayed
$q_s^{-1/2}$ and $q_s^{-1/3}$ factors. All core dyads and finite
partitions cost the original $U^\varepsilon$ allowance. No principal
bulk exception appears: $X,Y\gg U/P^2\gg U^{1/2}$, as in (J19).

For completeness, profile separation is made before applying (J31).
On fixed annuli its transform factor has argument a fixed monomial
in the normalized $u,v,z$ norms and the ratio $M/N_s$.
`lem:smooth-calculus` supplies a common coefficient measure for these
rows. Below the natural scale all required logarithmic derivatives
are uniformly bounded by smoothness at zero; above it they have
arbitrary rapid decay. Differentiating any of the originally required
profiles changes its finite seminorm and logarithmic factors, not
$b$, its squarefree support, or the independence of $\lambda_u$.
The arbitrary-vector bound (J31) is uniform in the separating norm
phases and bounded multiplicative angular factors. Minkowski therefore
restores every original finite component and required derivative with
its original fixed or polylogarithmic total cost. No polynomial
height budget is renewed for each component.

Finally $P\asymp C^2RSG$, so
$C^{-1}\le1$ and
$G^{1/3}C^{-1/3}(RS)^{1/6}\ll P^{1/3}$. Summing (J33) proves (J26).
At $H=H(P)$ its two terms are respectively
$U^{17/16+\varepsilon}P^{-1/4}$ and $U^{13/12+\varepsilon}$,
which proves (J27).

**The complementary target keeps the original signs.** In the restricted
$P=1$, good-dual, $h=\ell=r=1$ consumer, (J32) and the original
normalization give

$$
|\mathfrak E_{1,b,\,q_{r_2(m)}\le H}(M)|
\ll C_b^4U^\varepsilon
 \left[U^{1/2}M^{1/2}H^{1/2}
       +U^{2/3}M^{1/3}H^{2/3}\right].
$$

For $1\le M\le U$ and $H\ge1$, the first term is bounded by the
second. At $M=U$ this pays $H\le U^{1/8}$, beyond the $U^{1/30}$ range
already paid by (J21). The full-parameter assertion is (J27), not an
extrapolation from this restricted example.
Let $\mathfrak D_{>}$ denote the remaining actual expanded sum in
(J24), with $q_{r_2(m_{\rm good})}>H(P)$ in its $P$ dyad and with
all the same original parameters and weights. Exact Poisson expansion
and the complementary selectors give

$$
\operatorname{Re}\sum_\tau E_{6,\,P<U^{1/6}}(c_{\tau,T})
 =\operatorname{Re}\mathfrak D_{>}
   +\operatorname{Re}\sum_{P<U^{1/6}}\mathfrak D_{P,\le H(P)}.
$$

The second summand is now bounded by $C_b^4U^{13/12+\varepsilon}$.
A bound $\operatorname{Re}\mathfrak D_{>}
\ll C_b^4U^{B_*-\sigma+\varepsilon}$, for some $\sigma>0$ uniformly
under the same original component/derivative contract, would supply
(J24) with the resulting exponent
$\max\{13/12,B_*-\sigma\}<B_*$. Such a bound is not supplied.
The complement includes the natural $M\asymp U$ squarefree good duals;
its aggregate real part still requires joint cancellation. This
application proves no complete J24 estimate, inverse-fourth saving,
signed Robin restoration or RH conclusion.


### Retaining the shorter modulus and both actual side lengths

The same sector $\mathfrak D_{P,\le H}$ defined before (J26) admits
an estimate with no $P^{1/3}$ loss. Reuse de Faveri v1 Proposition 8.1,
(8.1), and Example 2.2 in exactly the character correspondence of
(J28)--(J31), together with the owned Gauss, Poisson and smooth-calculus
applications through (J33). For the original $c_{\tau,T}$ of (J24),
$T=U^{1/12}$, and its actual $b=\lambda_{\mathrm{II},b}$, or the stated
$C_b\tau_k$ envelope, the source-conditional strengthening is

$$
\boxed{
|\mathfrak D_{P,\le H}|
 \ll C_b^4U^{1+\varepsilon}(H^{1/2}+H^{2/3}),
 \qquad 1\le P<U^{1/6},\quad H\ge1.
}
\tag{J34}
$$

This is the identical complete weighted sector: the parity selector is
still inserted in each original Poisson series, before separation and
common-$e$ detection. In particular all repeated cores, occupancies,
common-$e$ signs, original $\ell,r$ expansions, bad duals, finite
components and derivative profiles in that definition remain present.
The constants and aggregate profile/height costs are those of
(J26)--(J33). Uniformly in the same $P$ range,

$$
\boxed{
H=U^{1/8}
 \quad\Longrightarrow\quad
|\mathfrak D_{P,\le U^{1/8}}|
 \ll C_b^4U^{13/12+\varepsilon}.
}
\tag{J35}
$$

This fixed cutoff also pays the sum over all the $P$ dyads with their
original signs. It enlarges the tapered paid sector of (J27), whose
cutoff is $U^{1/8}P^{-1/2}$; it does not change that earlier estimate.

**Orient each actual allocation before applying the supplier.** In
(J28)--(J29), fix the cores, the original finite component and heights,
$\widetilde s$, $e$ and its allocations, and the squarefree parity
ideal $\beta$. Let

$$
Q=\min(L_1,L_2),\qquad L=\max(L_1,L_2),\qquad
K=QL\asymp X/q_e,\qquad W_a=D/q_{t_a}.
$$

On nonempty annuli $Q,L\ge1$ up to fixed annular constants, which are
absorbed throughout, and $L\ll W_a$. Cubic reciprocity in the pinned
`lem:fixed-gauss-phase` gives $\kappa_u(v)=\kappa_v(u)$ on coprime
primary inputs. Both sides are zero on collisions, so this equality
also holds on the algebraically extended scalar in (J29). If $v$ is
the shorter variable, interchange the two entire vectors and their
separate masks and heights. The scalar and its fixed outside phases
are unchanged. In particular this operation does not replace sextic
reciprocity by a sign-free assertion: its original $\mathcal R$ factor
and the negative-root side's $-1$ factor remain exactly as in (J28).

The shorter variable is now the squarefree modulus $\mathfrak q$ in
Proposition 8.1. Its actual vector is the corresponding vector of
(J28) multiplied by $\overline{\chi_{\mathfrak q}(\beta)}$, as in
(J30), and is independent of the other original convolution variable
and $z$. The remaining convolution coefficient, including its dual
zeros, is removed only by the same Cauchy inequality used for (J31).
Thus (J31) applies with $(A,B;Q)=(L,Z;Q)$; it is not an application
to a moving vector or a new optimized vector. Example 2.2 and the
precise primary cubic reciprocity already checked there identify the
source character in either orientation. Its exclusion of the prime
above $3$ is fixed; the other original excluded primes and core
characters stay coefficient masks or factors, not growing bad data
for the supplier. The outer $z$ remains arbitrary, and $(\beta,z)>1$
is allowed. No cube-free inner extension from Remark 8.2 is needed.

For the function $F$ in (J31), retaining the actual product gives

$$
F(L,Z;Q)\ll LZ+K^{2/3}Z^{2/3},
 \qquad 1\le Q\le L,\quad Z\ge1.
\tag{J36}
$$

Indeed, if $Z\le L$, the two mixed terms are
$Z^{2/3}L^{1/3}Q$ and $Z^{1/3}L^{2/3}Q^{2/3}$.
Their ratios to $K^{2/3}Z^{2/3}$ are respectively
$(Q/L)^{1/3}$ and $Z^{-1/3}$, both at most one.
If $Z\ge L$, the ratios are $(Q/Z)^{1/3}$ and $L^{-1/3}$,
again at most one. This comparison has no upper restriction on $Z$.
It preserves $K$ in place of the earlier bound $D^2$ and uses the
shorter modulus in the first ratio.

Consequently a single allocation satisfies

$$
\sum_{z\sim Z}|H_{\beta z^2}|^2
 \ll C_b^4(UZ)^\varepsilon K
       [W_aZ+K^{2/3}Z^{2/3}].
$$

Both original coefficients $b(k_1u)b(k_2v)$ remain those in (J28).
Their separate squared norms supply the factor $C_b^4K$; their fixed
allocated divisor factors are absorbed by $U^\varepsilon$.
No multiplicativity, cancellation or differentiability of $b$ is used.
For $m_{\rm good}=\beta z^2\sim M$, use the same parity counts as in
(J32): the sums of $Z$ and $Z^{2/3}$ over $q_\beta\le H$ are at most
$M^{1/2}H^{1/2}$ and $M^{1/3}H^{2/3}$. Empty boxes are omitted, so
these statements hold also for $H>M$. Cauchy over the actual
allocations costs only divisors. Summing the common ideal $e$ uses
$\sum_{q_e\ll X}\tau_j(e)/q_e\ll U^\varepsilon$ for the first term
and the convergent $\sum_e\tau_j(e)/q_e^{5/3}$ for the second, with
fixed $j$. Thus the complete positive side norm obeys

$$
\boxed{
\sum_{\substack{e,\,m_{\rm good}\sim M\\
 q_{r_2(m_{\rm good})}\le H}}|H_{a,e}(m)|^2
 \ll C_b^4(UM)^\varepsilon X
 \left[W_aM^{1/2}H^{1/2}
           +X^{2/3}M^{1/3}H^{2/3}\right].
}
\tag{J37}
$$

The other side has its own shorter-variable choice, actual $Y$ and
$W_c=D/q_{t_c}$. The choices need not agree across the two sides or
across allocations: each bounds a complete positive side norm.
Cauchy then pairs the two norms on the same original $(e,m)$ set.
The common-$e$ Möbius coefficient, $\overline{\rho(m)}$ and all other
outer phases are retained in the signed pairing, with their absolute
values bounded at this step. No positivity of the selected physical
contraction is asserted.

**Restore all four unequal-side cross products.** Keep
$C,R,S,G,X_0,Y_0$ from (J19). The actual lengths satisfy
$X\le X_0=U/(C^2R^2G)$ and $Y\le Y_0=U/(C^2S^2G)$, while
$W_a\asymp D/(CR)$ and $W_c\asymp D/(CS)$. Restoring the two
original $D^{-1}$ coefficients and the original Poisson factor, then
counting the cores in their dyads, gives the positive majorant

$$
\frac{C_b^4(UM)^\varepsilon GC\sqrt{RS}}{\kappa}
 \sqrt{\mathcal B_a(M,H)\mathcal B_c(M,H)},
\quad
\begin{cases}
\mathcal B_a=W_aM^{1/2}H^{1/2}+X_0^{2/3}M^{1/3}H^{2/3},\\
\mathcal B_c=W_cM^{1/2}H^{1/2}+Y_0^{2/3}M^{1/3}H^{2/3}.
\end{cases}
\tag{J38}
$$

Occupancy ideals remain in the original coefficients, conductor and
zeros. They are omitted only from this increasing positive majorant:
they decrease $X,Y$ and the natural dual length and have only a divisor
number of choices. In particular they do not increase $W_a,W_c$.
The original caps $q_{t_a},q_{t_c}\le T$ are retained, although no
additional use of them is needed for the bound below.

For each fixed bad-prime dual part $s$, the natural good-dual scale is
bounded above by the same
$N_s=\kappa U/(C^4RSG^2q_s)$ as before (J33).
Expand the square root in (J38) into its four positive cross products
before summing dual dyads. Their $M$ powers are $1/2,5/12,5/12,1/3$.
The original transform and required logarithmic derivatives supply
arbitrary decay above $N_s$. The dyadic inequality used for (J33)
therefore replaces each $M^\alpha$ by $N_s^\alpha$, including when
$N_s<1$, without truncating the complete dual. With a smaller input
epsilon, the source length loss is absorbed exactly as for (J32).
The resulting four core costs, in the order first--first,
first--second, second--first, second--second, are bounded by

$$
\begin{aligned}
C_b^4U^{1+\varepsilon}\big[&
 C^{-2}(RS)^{-1/2}\kappa^{-1/2}q_s^{-1/2}H^{1/2}\\
&+C^{-11/6}G^{-1/6}R^{-5/12}S^{-7/12}
       \kappa^{-7/12}q_s^{-5/12}H^{7/12}\\
&+C^{-11/6}G^{-1/6}R^{-7/12}S^{-5/12}
       \kappa^{-7/12}q_s^{-5/12}H^{7/12}\\
&+C^{-5/3}G^{-1/3}(RS)^{-1/2}
       \kappa^{-2/3}q_s^{-1/3}H^{2/3}\big].
\end{aligned}
\tag{J39}
$$

All four products are needed for asymmetric $X,Y$; no equality of the
side lengths or allocations is assumed. Every displayed core power
is nonpositive, so there is no $P$ loss when summing their dyads.
Since $\kappa=q_\ell^6q_r$, the original $\ell$ sums are respectively
$\sum q_\ell^{-3}$, $\sum q_\ell^{-7/2}$ and
$\sum q_\ell^{-4}$, all convergent. The original $r\mid R_0$ sums
retain powers $q_r^{-1/2},q_r^{-7/12},q_r^{-2/3}$ and cost divisors.
The bad-prime dual sums have strictly positive decay powers
$1/2,5/12,1/3$ and converge. Core dyads and allocations cost the
original $U^\varepsilon$ allowance. The bulk lengths still satisfy
$X,Y\gg U/P^2\gg U^{1/2}$, so no principal $x=y=1$ exception is added.

Profile separation and restoration are precisely those already
justified for (J31)--(J33): separate the whole original coupled profile
on annuli before the fixed-vector application, use smoothness at zero
and rapid decay at infinity, and restore it by its common coefficient
measure. The shorter-variable choice depends only on the allocation's
lengths, not on a moving row. It only exchanges the two original
separating phases; the source norm bound is uniform in them.
Minkowski restores all original finite ray/angular presentations and
required derivatives with the same fixed or polylogarithmic aggregate
seminorm/height cost. No derivative falls on $b$ and no height budget
is renewed per component. Since $H^{7/12}\le H^{2/3}$ for $H\ge1$,
(J39) proves (J34). At $H=U^{1/8}$ the endpoint powers are
$U^{17/16+\varepsilon}$ and $U^{13/12+\varepsilon}$, proving (J35).

**The enlarged sector has its own exact signed complement.** Let
$\mathfrak D_{>}^{\rm unif}$ be the actual original expanded sum in
(J24) selected, in every $P<U^{1/6}$ dyad, by
$q_{r_2(m_{\rm good})}>U^{1/8}$. Keep every original coefficient,
parameter, phase, zero, bad dual and profile on this complementary
support. Exact complementary selectors give

$$
\operatorname{Re}\sum_\tau E_{6,\,P<U^{1/6}}(c_{\tau,T})
 =\operatorname{Re}\mathfrak D_{>}^{\rm unif}
   +\operatorname{Re}\sum_{P<U^{1/6}}
                      \mathfrak D_{P,\le U^{1/8}},
 \qquad T=U^{1/12}.
\tag{J40}
$$

This complement differs from the tapered $\mathfrak D_{>}$ after
(J33); the selector $U^{1/8}P^{-1/2}$ there has not been silently
changed. The second term in (J40) is paid at
$C_b^4U^{13/12+\varepsilon}$ by (J35). A uniform aggregate real bound
$\operatorname{Re}\mathfrak D_{>}^{\rm unif}
\ll C_b^4U^{B_*-\sigma+\varepsilon}$ for some $\sigma>0$, under the
same original component and derivative contract, would supply the
saving needed in (J24)--(J25), with exponent
$\max\{13/12,B_*-\sigma\}<B_*$. That complementary bound is not
supplied. In particular the natural $M\asymp U$ squarefree good duals
remain in it and still require joint cancellation. The refinement is
a source-conditional application of the cited suppliers, with no new
sieve, literature-priority or Lean-certification claim. It proves no
large-parity complement estimate, full (J24), inverse-fourth saving,
signed Robin restoration or RH conclusion.

### An every-split support obstruction for the actual Type-II convolution

The standard well-factorable import has a support obstruction for both
the actual $b=\lambda_{\mathrm{II},b}$ on its original inverse annulus
and the genuine joint coefficient $h_b$ in (J4). This is a
`repo-derived` applicability result, using the existing coefficient
identities and fixed-ray prime-ideal supply below. It supplies no
strict inverse-fourth improvement and does not settle (J24) or (J40).

**The source definition and its domain.** The existing owner is the
[Maynard well-factorable section](../Analytic/shortuniformity2026robininterfaces.md#well-factorable-distribution-preserves-the-total-prime-baseline).
In the pinned primary, [Definition 1](https://arxiv.org/html/2006.07088v1#Thmdfntn1)
requires, for **every real** $Q=Q_1Q_2$, $Q_i\ge1$, a convolution of
two 1-bounded sequences, the $i$th supported on $1\le n\le Q_i$.
[Definition 2](https://arxiv.org/html/2006.07088v1#Thmdfntn2)
requires the same for every real $Q=Q_1Q_2Q_3$, with three separately
prescribed supports. One convenient internal factorization or fixed
prime block is insufficient. Theorem A and Theorem 1.1 estimate the
integer prime-AP discrepancy
$\pi(x;q,a)-\pi(x)/\varphi(q)$, at levels respectively
$Q\le x^{4/7-\varepsilon}$ and $Q\le x^{3/5-\varepsilon}$, with fixed
$a$ and arbitrary fixed logarithmic saving. They supply no Hecke
ideal-coefficient or common-$\beta$ signed-contraction theorem here;
even satisfying their weight definition would leave that transport
unproved.

For the support calculation only, **define** the following ideal-norm
analogue, without importing an analytic theorem. For $j=2$ or $3$ and
$Q\ge1$, write $\mathsf S_j(a;Q)$ when every real factorization
$Q=\prod_{i=1}^jQ_i$, $Q_i\ge1$, permits

$$
a(\mathfrak n)=
\sum_{\mathfrak d_1\cdots\mathfrak d_j=\mathfrak n}
 \prod_{i=1}^j\gamma_i(\mathfrak d_i),
\qquad
\gamma_i(\mathfrak d)=0\quad\text{if }N\mathfrak d>Q_i.
\tag{J41}
$$

The convolution is over good integral ideals, each counted once, and
the complex $\gamma_i$ may depend on the split. There is **no amplitude
bound** in this definition. Thus failure of $\mathsf S_j$ also rules
out the literal ideal-norm version with 1-bounded or divisor-bounded
factors. This definition does not aggregate different ideals of equal
norm into an integer-modulus weight.

**A nonzero semiprime forces a larger level.** If
$a(\mathfrak n)\ne0$, $\mathfrak n=\mathfrak p\mathfrak q$ for
distinct prime ideals, and $p_0=\min(N\mathfrak p,N\mathfrak q)$, then

$$
\mathsf S_j(a;Q)\quad\Longrightarrow\quad
Q\ge N\mathfrak n\,p_0^{\,j-1},\qquad j=2,3.
\tag{J42}
$$

Indeed, any supported convolution first forces $Q\ge N\mathfrak n$.
For $1\le r<p_0$, prescribe $Q_1=\cdots=Q_{j-1}=r$ and
$Q_j=Q/r^{j-1}$. All prescribed lengths are at least one: for these
two values of $j$, $Q\ge N\mathfrak n\ge p_0^{j-1}$.
Every divisor of $\mathfrak n$ other than the unit has norm at least
$p_0$, so the first $j-1$ factors must all be units. The last must
be $\mathfrak n$, forcing $Q\ge N\mathfrak n\,r^{j-1}$.
Let $r\uparrow p_0$ to obtain (J42).

Apply this to $b$ restricted to the original annulus
$q_d\asymp D=\sqrt U$, with the original $A=A_{\rm b}=U^{1/12}$.
The balanced nonzero semiprimes in
[C33/C36](../Analytic/liu2026quasirh.md#the-new-remainder-also-excludes-a-norm-only-payment)
already have $b(\mathfrak p\mathfrak q)=2$ and
$N\mathfrak p,N\mathfrak q\asymp U^{1/4}$. Their identity is reused,
not rederived. The fixed-ray prime-ideal supply chooses their product
inside a fixed interval where the original $V$ is nonzero. Hence the
obstruction also holds with the actual $V(q_d/D)$ and unit-modulus
ray twist included. Formula (J42) requires levels at least
$U^{3/4+o(1)}$ for binary and $U^{1+o(1)}$ for triple factorability;
neither is available at the original $Q=U^{1/2+o(1)}$.
These are necessary levels, not existence results at larger levels.

This failure is a common zero of all convolution terms at an offending
split. Changing amplitude bounds cannot fill it. A finite signed sum
of convolutions with those same prescribed support bounds, or smaller
ones, also vanishes there, regardless of its coefficients. A fixed
block decomposition that does not admit the offending split is a
different hypothesis and is not ruled out by this observation.

**The joint $h_b$ has its own obstruction.** Fix the original nonzero
smooth **complex** annular $V$ of one (J4) component, and choose $t_0>0$
with $v_0=V(t_0)\ne0$. Fix $c>2$. Choose a sufficiently small fixed
$\delta>0$ such that $c(1-\delta)>2$ and

$$
|V(t)-v_0|\le |v_0|/10
\quad\text{for }t_0(1-\delta)^2\le t\le t_0(1+\delta)^2.
$$

Using the
[existing fixed-ray prime-pair supply](../Analytic/liu2026quasirh.md#the-original-convolution-norm-before-sixth-power-compression),
choose four distinct good prime ideals with

$$
N\mathfrak q_j\in cU^{1/12}[1-\delta,1+\delta],\qquad
N\mathfrak p_i\in(t_0/c)U^{5/12}[1-\delta,1+\delta],
\qquad i,j=1,2.
$$

The cited fixed-ray prime-ideal theorem applies in each of these
fixed relative intervals as its length tends to infinity. Delete $S$
and the finitely many coincidences. For the displayed (J4), the inner
ideal conditions are goodness and squarefree support, and $\xi$ has
modulus one there. If a further original ray selector is retained,
qualify the construction to an allowed component as follows: take
$t(\mathfrak q_1)=t(\mathfrak q_2)=r$ and
$t(\mathfrak p_1)=t(\mathfrak p_2)=s$, with $sr=\kappa$ an allowed
factor class on which the original multiplier is nonzero. A retained
column class must then allow $\tau=\kappa^2$. The same supply provides
these primes in the fixed classes. No assertion is made for an
incompatible selector, a zero component, or an arbitrary varying
profile. The fixed unit representatives and finite ray multipliers
are retained; four independent ray phases are not substituted for
the multiplicative $\xi$ of (J4).

The formula below is for (J4). A compatible further selector keeps
all four terms; any additional nonzero multiplier constant on these
fixed classes is retained as their common scalar.

Put $w=\mathfrak p_1\mathfrak p_2\mathfrak q_1\mathfrak q_2$ and
$t_{ij}=N(\mathfrak p_i\mathfrak q_j)/D$. All $t_{ij}$ lie in the
displayed nonzero neighborhood of $t_0$. Since both primes in each
mixed pair exceed $2A$, the existing
[C40 with $b_0=1$](../Analytic/liu2026quasirh.md#cofactor-recursion-and-the-actual-prime-slot-capacity)
gives $b(\mathfrak p_i\mathfrak q_j)=2$ on this original annulus.
The only divisors of $w$ in the $D$ annulus are the four mixed pairs:
single primes and $\mathfrak q_1\mathfrak q_2$ are below it,
$\mathfrak p_1\mathfrak p_2$ and every triple are above it.
Thus exactly four **ordered** factorizations contribute to (J4),
each with $b(d_1)b(d_2)=4$, and multiplicativity gives

$$
h_b(w)=8D^{-1}\xi(w)
 \left[V(t_{11})V(t_{22})+V(t_{12})V(t_{21})\right]\ne0.
\tag{J43}
$$

For completeness, each product in brackets differs from $v_0^2$ by
at most $(21/100)|v_0|^2$, so the bracket differs from $2v_0^2$ by
at most $(21/50)|v_0|^2<2|v_0|^2$. This continuity estimate is valid
for complex $V$ and retains interference between both pairings; it
uses neither positivity nor an absolute-value replacement of the sum.

Here $Nw\asymp U$. A divisor of $w$ without a $\mathfrak p_i$ has
norm $O(U^{1/6})$; one containing a $\mathfrak p_i$ has norm
$\gg U^{5/12}$. At the natural level $L=U^{1+o(1)}$, prescribe the
binary split $Q_1=U^{1/3}$, $Q_2=L/U^{1/3}=U^{2/3+o(1)}$.
Both lengths are at least one for large $U$. The first divisor can
contain no $\mathfrak p_i$, so its complement contains both and has
norm at least $N\mathfrak p_1N\mathfrak p_2\asymp U^{5/6}>Q_2$.
Every supported convolution is zero at $w$, contradicting (J43).
Thus genuine joint $h_b$, not merely $b$, fails binary factorability
at its natural level.

There are also the following stronger necessary levels for this
witness. Write $p_*=\min_iN\mathfrak p_i$. If
$\mathsf S_2(h_b;L)$ holds, nonvanishing first gives $L\ge Nw$.
Prescribe $Q_1=r$, $1\le r<p_*$, approaching $p_*$ from below, and
$Q_2=L/r$.
These lengths are at least one. Again the second divisor must contain
both large primes, so $L\ge rN\mathfrak p_1N\mathfrak p_2$.
For triple factorability the equal split requires that some factor
can contain each large prime. Consequently

$$
\begin{aligned}
\mathsf S_2(h_b;L)&\Longrightarrow
 L\ge p_*N\mathfrak p_1N\mathfrak p_2\gg_{V,c,\delta}U^{5/4},\\
\mathsf S_3(h_b;L)&\Longrightarrow
 L\ge\left(\max_iN\mathfrak p_i\right)^3
 \gg_{V,c,\delta}U^{5/4}.
\end{aligned}
\tag{J44}
$$

The equal triple split has all lengths $L^{1/3}\ge1$; below its stated
threshold no factor can carry the largest prime. These are necessary
bounds only, with no sufficiency or optimality assertion. The same
common-zero argument covers arbitrary amplitudes and finite signed
sums with the offending support bounds.

**Limit of the obstruction.** Opening $b$ into its actual prime or
cofactor blocks remains legitimate, but cannot certify standard
every-split well-factorability at these original levels. General
fixed-block multilinear estimates and signed cancellation are not
excluded. Nothing here is an energy lower bound, a lower bound or
obstruction for the signed (J40) complement, or a joint estimate reaching
the sufficient local exponent $1+B_*-\sigma$ for $\sigma>0$.
The exponent $13/6$ is the generic local energy baseline.
The original Hecke domain,
raw sextic collision zeros, common $\beta$, signs and common-$e$
detector, fixed/polylog profile seminorms, and all unit/ray/core/bad-dual
aggregation costs remain in the original contract. In particular,
(J40) and its unpaid aggregate real complementary bound are unchanged.
No new analytic estimate, literature-originality claim, Lean
certification, inverse-fourth saving, signed Robin restoration or RH
completion follows.

The two-factor predecessors C21–C50 and the explicit reciprocal premise
are in the [analytic note](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients).
The following C51–C76 concern the four-factor exceptional interface of
this Fourier note; they retain the original signed J40 scope.

## Four inverse factors on the same coprime realization

Retain $K=\mathbb Q(\sqrt{-3})$, $q_d=Nd$, the fixed $S$, and the
ideal-counting convention of [(C41)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients). Let $D=U^{1/2}$ and $A=U^\alpha$,
where $0<\alpha<1/4$ is fixed. On the original inverse annulus use exactly
$b_A=\mu+K_A$ of [(C37)](../Analytic/liu2026quasirh.md#cofactor-recursion-and-the-actual-prime-slot-capacity), with its original smooth $W$ and collision zeros.
The support condition $2A<z\asymp U^{1/4}$ then holds eventually in
[(C25)](../Analytic/liu2026quasirh.md#a-smooth-type-i-cutoff-using-the-existing-reciprocal-strip). All statements below are paper-level `repo-derived` deductions;
$R_\beta$ always means the explicit principal reciprocal hypothesis
[(C48)](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip), including polynomial vertical growth on smaller closed strips.
In particular $R_{7/8}$ is source-conditional on the
[pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
`thm:main` and `lem:logarithmic-control`, and is not certified here.

For a smooth complex $\Psi$ supported on a fixed compact rectangle in
$(0,\infty)^4$, and squarefree $P$ outside $S$, put

$$
\begin{aligned}
Q_4(P;\Psi)&=\sum_{\substack{d_1d_2d_3d_4\ {\rm sf}\\
 (d_1d_2d_3d_4,SP)=1}}
 \prod_{i=1}^4b_A(d_i)\,
 \Psi(q_{d_1}/D,\ldots,q_{d_4}/D),\qquad I_\Psi=\int\Psi(\mathbf x)\,d\mathbf x,\\
C_4(P)&=\kappa^4\prod_{p\in S}(1-q_p^{-1})^4
 \prod_{p\notin S}(1+4q_p^{-1})(1-q_p^{-1})^4
 \prod_{p\mid P}(1+4q_p^{-1})^{-1},\\
\Theta_{4,A}(P)&=\sum_{\substack{e_1e_2e_3e_4\ {\rm sf}\\
 (e_1e_2e_3e_4,SP)=1}}
 \frac{\prod_{i=1}^4\mu(e_i)2^{\omega(e_i)}W(q_{e_i}/A)}
 {\prod_{p\mid e_1e_2e_3e_4}(q_p+4)},
 \qquad \kappa=\mathop{\rm Res}_{s=1}\zeta_K(s).
\end{aligned}
\tag{C51}
$$

The squarefree product forces all four factors to be pairwise coprime.
This is the actual relation obtained from squarefree columns
$s=d_1d_2$, $t=d_3d_4$ and common-column gcd $(s,t)=1$.
Squaring [(C41)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients) would allow primes shared across the two columns; even
its unforced local factor would be $(1+2/q_p)^2$, instead of
$1+4/q_p$. Thus neither $\Theta_A(P)^2$ nor independent copies of the
two-variable mean describe this realization. The old two-variable
result remains applicable in its original scope.

**Four-factor absolute-error theorem.** Suppose $1/2\le\beta<1$ and
$R_\beta$. For every fixed polynomial range $q_P\le U^C$ and
$\varepsilon>0$, a finite derivative order $J$ gives

$$
\begin{aligned}
Q_4(P;\Psi)&=D^4C_4(P)I_\Psi\Theta_{4,A}(P)
 +O_\varepsilon\!\left(\mathcal N_J(Uq_P)^\varepsilon
 [D^{3+\beta}+D^{7/2}A^{1/2}]\right),\\
|\Theta_{4,A}(P)|&\ll_\varepsilon
 A^{-4(1-\beta)+\varepsilon}q_P^\varepsilon,
\qquad 0<C_4(P)\ll_{K,S}1.
\end{aligned}
\tag{C52}
$$

Here $\mathcal N_J$ is the maximum of the partial derivatives of
$\Psi$ up to order $J$ in each variable on that rectangle. Constants
depend on $C,\alpha,K,S,W$, supports, strip margins and the reciprocal
growth constants. The displayed $q_P^\varepsilon$ version is retained
when summing frequency shells; no condition $q_P\le A^2$ is imposed.

**Proof.** Reuse the divisor identity [(C37)](../Analytic/liu2026quasirh.md#cofactor-recursion-and-the-actual-prime-slot-capacity), the literal Euler-factor
method [(C44)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients), the deleted-factor estimate [(C45)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients) under [(C48)](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip), and the
normal-convergence argument [(C47)](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip). Expand first the $K_A^4$ term and
fix the four $e_i$. Its series is $\prod_i\zeta_K(s_i)G_{\mathbf e,P}(\mathbf s)$.
Writing $x_i=q_p^{-s_i}$, the local factors of $G$ are

$$
\begin{array}{c|c}
p\nmid SPe_1e_2e_3e_4&(1+x_1+x_2+x_3+x_4)\prod_i(1-x_i)\\
p\mid e_j&x_j\prod_i(1-x_i)\\
p\mid SP&\prod_i(1-x_i).
\end{array}
\tag{C53}
$$

The first factor has no linear term. The literal product therefore
converges normally whenever every $\Re s_i>1/2$; one never divides
by its potentially vanishing numerator. On smaller closed strips its
bound is $\ll_\eta(q_P\prod_iq_{e_i})^\eta
\prod_iq_{e_i}^{-\Re s_i}$. At $\mathbf s=\mathbf1$, forcing a prime
into any one variable gives $q_p^{-1}/(1+4q_p^{-1})=(q_p+4)^{-1}$.
Four smooth Mellin inversions and successive contour shifts to
$1/2+\delta$ give the residue in (C52). For a subset of $j\ge1$
shifted variables, summing the forced divisors costs

$$
\mathcal N_J(Uq_P)^\varepsilon D^{4-j/2}A^{j/2},
\qquad j=1,2,3,4.
\tag{C54}
$$

This follows from the same sums $\sum_{q_e\le2A}\tau(e)q_e^{-1/2-\delta}$
and $\sum_{q_e\le2A}\tau(e)/q_e$ as [(C44)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients). Since $A<D$, the $j=1$
term dominates. Choose $J$ once to pay four Mellin integrals, their
horizontal joins and the ordinary zeta growth.

There are fifteen other terms in $(\mu+K_A)^4$. In each choose one
$\mu$ variable, fix the other three, and use [(C45)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients)/[(C48)](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip) with
$r=\operatorname{rad}(SP\prod_{i\ne j}d_i)$, so $q_r\ll q_PD^3$.
That inner sum is $O(\mathcal N_JD^{\beta+\varepsilon}q_P^\varepsilon)$;
each remaining absolute mass is $O(D\log^2(2A))$, or $O(D)$ for a
$\mu$ factor, by [(C46)](../Analytic/liu2026quasirh.md#the-actual-radial-column-mean-with-both-type-ii-coefficients). This proves the $D^{3+\beta}$ error for their
entire sum. Only the principal reciprocal is used: there is no
application to nontrivial ray or angular Hecke inverses.

Finally the four-variable Mellin series of $\Theta_{4,A}$ is

$$
\prod_{p\notin SP}\left(1-\frac{2\sum_iq_p^{-z_i}}{q_p+4}\right)
 =\prod_i\zeta_K(1+z_i)^{-2}H_{4,P}(\mathbf z).
\tag{C55}
$$

After dividing by $\prod_i(1-q_p^{-1-z_i})^2$, the local correction
minus one has only terms $O(\sum_iq_p^{-2-\Re z_i}
+\sum_{i,j}q_p^{-2-\Re z_i-\Re z_j})$ on smaller strips. Thus $H_{4,P}$
is holomorphic for every $\Re z_i>-1/2$, normally convergent and
$\ll_\eta q_P^\eta$ uniformly in the heights there. Excluded primes
have factor $\prod_i(1-q_p^{-1-z_i})^{-2}$, costing $q_P^\eta$.
Move all four lines to $\beta-1+\delta$. The simple pole of each
$\widehat W$ at zero is canceled by its corresponding double
reciprocal-zeta zero. Rapid Mellin decay and [(C48)](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip) prove the second
line of (C52), with no residue or mixed polar divisor. This completes
the proof. Fixed polynomial ranges allow $\delta,\eta$ to be allocated
within any final $U^\varepsilon$ loss.

## The constant-ray exceptional component with actual columns

Use [Xu–Sang v2, §3.1 (3.3)–(3.4), §3.2 (3.8), and §3.3
(3.11)](https://arxiv.org/html/2610.17675v2#S3), only as finite Gauss,
Poisson and exceptional-frequency identities. Their field is this same
$K$; columns use the literal raw sextic symbol and its zero extension.
Fix the corefree branch, original common-$e=1$, and source common-column
gcd $C=1$. This $C$ is not a repeated-column core. The source moving
twist ideal is the unit ideal. No arbitrary-arithmetic-weight version
of its Proposition 3.1 or Lemma 5.1 is assumed.

**Normalization and the multiplier.** In the source conventions set

$$
\begin{aligned}
e_K(z)&=\exp(4\pi i\operatorname{Im}z/\sqrt3),\qquad
 d\mu(z)=(2/\sqrt3)\,d\operatorname{Re}z\,d\operatorname{Im}z,\\
\widehat w(y)&=\int_{\mathbb C}w(z)e_K(-zy)\,d\mu(z)
 =\widehat w_{\rm rad}(|y|^2),\\
G(s,k)&=q_s^{-1/2}\sum_{x\bmod s}\chi_s(x)e_K(kx/s)
 =\gamma_1(s)\overline{\chi_s(k)}\quad(s\ {\rm good\ sf}).
\end{aligned}
\tag{C56}
$$

The lattice is self-dual for this measure. The last equality includes
collision zeros, since the raw character is primitive at every prime
of a good squarefree $s$. It is the same Gauss convention as the
pinned manuscript's `eq:sextic-sieve-pair-gauss` and (J5).
Consequently an original side scalar $\gamma_1(s)\overline{\chi_s(m)}$
is $\chi_s(-1)G(s,-m)$. The true change-of-form multiplier is
$\chi_s(-1)$, together with the original $\xi(s)$ and finite
ray/angular factors; it is not an extra inverse Gauss sum and is not
a replacement of $b_A$ by $1$. The original (J5) CRT factors are
already inside $\gamma_1(s)$ and must not be inserted a second time.

Fix a common refined total ray $[s]=[t]=\sigma$ and include its
selectors in both original side weights. For one such component write
its arithmetic column as

$$
c_s=\mathbf1_{s\ {\rm good\ sf}}
 \sum_{d_1d_2=s}b_A(d_1)b_A(d_2)
 V_1(q_{d_1}/D)V_2(q_{d_2}/D)\,a(d_1,d_2),
\tag{C57}
$$

where $a$ retains the original factor-class selectors, $\xi(s)$,
$\chi_s(-1)$ and original angular factors in this orientation.
Separated norm heights belong to the $V_i$, with their actual
polynomial seminorm costs. Distinct side profiles are allowed by
polarization. Consider the unnormalized element-row Gauss pairing
$\mathcal E=\sum_m w(m/\sqrt U)
 (\sum_s c_sG(s,-m))\overline{(\sum_t c'_tG(t,-m))}$.
This specifies a local Gauss object with actual columns, not the full
physical-row moment or a selected positive part of J40. The source
normalization is $U^{-1}$ on each column; taking its column profile to
be $t^{1/2}c_s$ shows that $\mathcal E$ is $U^2$ times that normalized
pairing. This use is an identity before any smooth-column estimate.
Equivalently, direct opening gives Poisson multiplier
$U/\sqrt{q_sq_t}=(t_st_t)^{-1/2}$, $t_s=q_s/U$.
The original $D^{-1}$ side normalizations of (J4), and all physical
row/core prefactors, still have to be restored in their own contraction.

On the $C=1$ branch the finite correlation is exactly
$\chi_s(k)\overline{\chi_t(-k)}\mathfrak r(s,t)$.
The source's refined equal-total-ray condition gives
$\mathfrak r(s,t)\overline{\chi_t(-1)}=1$.
Its exceptional frequencies have the unique form

$$
k=\epsilon e_S(\mathbf r)a^6,\qquad
\epsilon\in\mathcal O^\times,\quad
0\le r_p\le5\ (p\in S),\quad
 e_S(\mathbf r)=\prod_{p\in S}\pi_p^{r_p},\qquad
P_a=\operatorname{rad}(a)\big|_{p\notin S}.
\tag{C58}
$$

Here $a$ ranges once over integral ideals, including its possible
$S$ factors, with fixed generators; all six units occur. $P_a$ is a
frequency puncture, not the original product-squarepart $P$ of J40.
The characters of $\epsilon e_S(\mathbf r)$ are constant on a refined
total ray fiber, so they cancel between its two columns. Sixth powers
leave precisely the original mask $\mathbf1_{(st,a)=1}$. There is no
coprimality replacement on a different row family.

After that cancellation, let $\Omega_{\epsilon,\mathbf r}(\mathbf d)$
be the remaining actual four-factor finite-ray/angular weight, including
both total-class selectors and the original component coefficient.
Expand only this given weight under its original presentation contract.
Let $\eta_{\epsilon,\mathbf r}$ be the coefficient with four trivial
ray characters and zero angular modes, with normalized counting measure
on each ray group and normalized Haar measure on each angular circle.
This defines a linear component even when it is zero. For four specified
factor classes in a ray group of order $h$, with no further multiplier,
the coefficient is $h^{-4}$; a total-class relation or any additional
weight must instead be averaged as its actual table. In particular,
one must not assign $h^{-4}$ to a general total-class selector.
All nontrivial characters and angular modes remain in
$\Omega-\eta$. This is a coefficient expansion, not independence of
the four actual ideal classes or angles.

Write $z=q_{e_S(\mathbf r)}q_a^6/U$ and

$$
\begin{aligned}
\Psi_z(\mathbf x)&=V_1(x_1)V_2(x_2)
 \overline{V_3(x_3)V_4(x_4)}
 (x_1x_2x_3x_4)^{-1/2}
 \widehat w_{\rm rad}\!\left(\frac z{x_1x_2x_3x_4}\right),\\
I_4(z)&=\int\Psi_z(\mathbf x)\,d\mathbf x,\\
\mathcal E_{\rm exc}&=\mathcal E_{\rm rad}+\mathcal R_{\rm tw},\qquad
\mathcal E_{\rm rad}=\sum_{\epsilon,\mathbf r}\eta_{\epsilon,\mathbf r}
 \sum_a Q_4(P_a;\Psi_{q_{e_S(\mathbf r)}q_a^6/U}).
\end{aligned}
\tag{C59}
$$

Precisely, $\mathcal R_{\rm tw}$ is the very same sum over
$\epsilon,\mathbf r,a,d_1,d_2,d_3,d_4$, with the squarefree product,
$(\prod d_i,SP_a)=1$, the same $\prod b_A(d_i)\Psi_z$, and weight
$\Omega_{\epsilon,\mathbf r}(\mathbf d)-\eta_{\epsilon,\mathbf r}$.
This is an exact signed residual. No absolute value, new beta row,
positivity of the selected frequencies, or monotonicity under selection
of physical rows is asserted. The $k=0$ diagonal is outside (C59).

The proof of (C59) is finite opening of the two Gauss sums, row Poisson
with (C56), the $C=1$ correlation above, and (C58). Squarefreeness of
each column and their gcd $1$ give exactly (C51)'s four-way mask.
The correlation phases cancel on each original total-class fiber before
taking the stated linear coefficient. Thus no unproved arithmetic
column-mean theorem is used to identify this component.

**Summing the proved component.** Assume $R_\beta$ and the same fixed
or polylogarithmic aggregate profile/height contract. Applying (C52)
to (C59) gives

$$
\begin{aligned}
\mathcal E_{\rm rad}
 &=U^2\sum_{\epsilon,\mathbf r}\eta_{\epsilon,\mathbf r}
   \sum_a C_4(P_a)\Theta_{4,A}(P_a)
       I_4(q_{e_S(\mathbf r)}q_a^6/U)
   +\mathcal R_{KK}+\mathcal R_\mu,\\
|\mathcal R_{KK}|&\ll_\varepsilon\mathcal N_J
 U^{23/12+\varepsilon}A^{1/2},\qquad
|\mathcal R_\mu|\ll_\varepsilon\mathcal N_J
 U^{(10+3\beta)/6+\varepsilon},\\
|\mathcal E_{\rm rad}|&\ll_\varepsilon\mathcal N_JU^\varepsilon
 [U^{13/6}A^{-4(1-\beta)}
   +U^{(10+3\beta)/6}+U^{23/12}A^{1/2}].
\end{aligned}
\tag{C60}
$$

Here $\mathcal R_\mu$ is exactly the aggregate of the fifteen
$\mu$-containing terms in (C59); $\mathcal R_{KK}$ is the remainder of
the all-$K_A$ term after its displayed residue. The finite sum over
units and $S$ exponents remains visible in the main term.
There is no additional planar area multiplier: $\kappa^4$ already
accounts for counting ideals once, and (C56) fixes the Fourier measure.

To justify the full frequency sum, on each shell $z\asymp R\ge1$
all the required derivatives of $\Psi_z$ are
$O_B(\mathcal N_{J,B}R^{-B})$. Ideal counting gives
$O((RU)^{1/6})$ possible $a$; the ball $z\le1$ has $O(U^{1/6})$.
First retain any fixed polynomial shell range. Its $q_{P_a}^\varepsilon$
factor in (C52) is paid by choosing its internal loss smaller; one
cannot discard frequencies merely because $q_{P_a}>A^2$.
For the remaining shells the original divisor envelope bounds the four
columns absolutely, and arbitrary Fourier decay makes their sum smaller
than any prescribed power by enlarging the fixed shell cutoff and $B$.
The same argument bounds the residue tail using the absolute divisor
mass of $\Theta_{4,A}$. It proves (C60) without truncating the actual
frequency identity. In (C59)–(C68), $\mathcal N_J$ denotes the original
aggregate of component seminorms against the absolute coefficient
measures, including the $|\eta_{\epsilon,\mathbf r}|$ costs; it is required
to be fixed or polylogarithmic. One derivative order is chosen for all shells,
finite components and separated heights. If their growth has degree $h$,
log-Fourier decay of order greater than $h+5$ is integrable in four
variables. Derivatives act only on the external profiles, never on
$b_A$, and no budget is restarted per $a$ or ray class.

## Joint cutoff certificate and the unpaid estimates

Put $B_*=(31-10\sqrt6)/6$ and
$\Delta=7/6-B_*=(5\sqrt6-12)/3=0.082482904638630\ldots$.
The unnormalized local energy comparison exponent is $1+B_*$;
restoring the original $D^{-2}=U^{-1}$ coefficient normalization gives
the exponent $B_*$ used in J40. This comparison does not identify the
entire Gauss object (C59) with J40 or pay its omitted parameters.
At the unchanged $A=U^{1/12}$, (C52) and (C60), conditionally on
$R_{7/8}$, give the following explicit certificate:

$$
\begin{aligned}
\Theta_{4,A}(P)&\ll_\varepsilon U^{-1/24+\varepsilon}q_P^\varepsilon,\\
|\mathcal E_{\rm rad}|&\ll_\varepsilon\mathcal N_JU^\varepsilon
 (U^{17/8}+U^{101/48}+U^{47/24}),\\
17/8-(1+B_*)&=0.040816237971963\ldots,\\
101/48-(1+B_*)&=0.019982904638630\ldots,\qquad
1+B_*=2.084183762028037\ldots.
\end{aligned}
\tag{C61}
$$

The $101/48$ term is the fifteen-$\mu$ aggregate, not the smaller
error that would result from squaring the two-factor mean. These are
upper-bound certificate gaps, not lower bounds for any actual term.
No full energy improvement follows, and no selected Poisson component
has been declared nonnegative.

**The same coefficient pays Type I.** For $A=U^\alpha$, keep the
actual split [(C25)](../Analytic/liu2026quasirh.md#a-smooth-type-i-cutoff-using-the-existing-reciprocal-strip), the original physical family, all finite ray
presentations, original zero extensions and the shared finite-height
allowance. Reuse [(C29)](../Analytic/liu2026quasirh.md#combining-two-bounds-on-the-same-buffered-type-i-bin), whose primary suppliers are the
[pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
`lem:buffered-bins`, `lem:detector-dyads`, and the zero-prime-slot
case of `lem:plain`. These require the original nonprincipal inducing
rows, polynomial-size original deletion masks, bounded annular length
ranges, and finite internal Mellin heights whose total lies within
the same buffer. There is no new conductor lower bound. The proof of
[(C29)](../Analytic/liu2026quasirh.md#combining-two-bounds-on-the-same-buffered-type-i-bin) is uniform in $Q\ll U^\alpha$, since only the smooth profile's
$Q/A$ ratio changes. It supplies, on the very same bin,

$$
\begin{aligned}
T_Q(\delta)&\ll U^\varepsilon
 \min\{U^{f(\delta)},U^{1+2\alpha\delta}\},\\
f(\delta)&=R(\delta)+\delta
 =\delta+\frac{15-16\delta}{15-6\delta}
 \quad(1/50<\delta\le5/6),\qquad
f(\delta)=1\quad(5/6\le\delta\le1).
\end{aligned}
\tag{C62}
$$

The floor separately costs $U^{1+\alpha/25+\varepsilon}$. Norm heights
and all internal Mellin variables share the original buffer; the
Fourier/Mellin tail orders are chosen once after the desired loss.
There is no infinite-local-contour extension or differentiation of
$b_A$. Dyadic and fixed/polylog aggregate costs are absorbed only
within the original common envelope.

Differentiation gives $f'(\delta)=1-150/(15-6\delta)^2$ and
$f''(\delta)=-1800/(15-6\delta)^3<0$. Hence the unique maximum is

$$
\delta_*=(15-5\sqrt6)/6=0.458758547680685\ldots,\qquad
f(\delta_*)=B_*,\qquad
\alpha_I=\frac{B_*-1}{2\delta_*}
 =\frac{3-\sqrt6}{6}=0.091751709536137\ldots.
\tag{C63}
$$

This bin is also inside the range $\delta\le3/4$ if that restriction
is imposed from the source's $7/8$ Hecke region. For the full bin range,
the envelope $\max_\delta\min\{f(\delta),1+2\alpha\delta\}$ has a
strict gap below $B_*$ exactly when $0<\alpha<\alpha_I$.
Indeed at $\delta_*$ its minimum is $B_*$ for $\alpha\ge\alpha_I$.
Below that threshold, the increasing line intersects the decreasing
side of $f$ at

$$
\delta_\alpha=\frac{15-10/(1-2\alpha)}6>\delta_*,\qquad
\tau(\alpha)=1+2\alpha\delta_\alpha<B_*.
\tag{C64}
$$

Before this crossing the minimum is at most the line's value there;
after it, $f$ decreases to $1$. The floor is smaller since
$2\delta_\alpha>1/25$. Thus $\tau$ is an admissible full-range Type-I
exponent, and $\tau(1/12)=13/12$, recovering [(C30)](../Analytic/liu2026quasirh.md#combining-two-bounds-on-the-same-buffered-type-i-bin).
This is a limit of these two UPPER BOUND inputs. It does not assert
that the critical bin is populated at its counting bound or that any
actual Type-I moment attains that exponent.

For $\alpha<\alpha_I$, the same positive $L^4$ Minkowski argument as
[(C31)](../Analytic/liu2026quasirh.md#combining-two-bounds-on-the-same-buffered-type-i-bin) gives $\mathcal T_{\rm II}\ll U^{B_*+\varepsilon}$ and

$$
|\mathcal T_\mu-\mathcal T_{\rm II}|
 \ll U^{(3B_*+\tau(\alpha))/4+\varepsilon}.
\tag{C65}
$$

The original cubic and large-product-squarepart payments add $13/12$,
so the full difference-transfer exponent is
$\max\{13/12,(3B_*+\tau(\alpha))/4\}$, with reserve
$\min\{B_*-13/12,(B_*-\tau(\alpha))/4\}$.
Here $B_*-13/12=0.000850428694703\ldots$.
At $\alpha_I$ the interference reserve vanishes. A one-sided triangle
transfer also needs a Type-I exponent below $B_*$ and does not repair
this envelope limit.

**The coupled-current-input incompatibility.** Making just the
four-factor residue upper bound in (C60) smaller than $U^{1+B_*}$
requires the sufficient-estimate inequality
$4\alpha(1-\beta)>\Delta$. At $\beta=7/8$ this becomes

$$
\alpha>\alpha_G=2\Delta
 =0.164965809277260\ldots,
\qquad\hbox{whereas the paid Type-I envelope requires }\alpha<\alpha_I.
\tag{C66}
$$

The windows are disjoint, though both endpoints satisfy the exact-split
support limit $\alpha<1/4$. As $\alpha\uparrow\alpha_I$ the residue
certificate approaches exponent $13/6-\alpha_I/2
=2.120790811898598\ldots>1+B_*$, while the Type-I reserve tends to
zero. Moreover the $R_{7/8}$ bound for $\mathcal R_\mu$ in (C60)
is $U^{101/48+\varepsilon}$ for every such cutoff, so merely changing
$A$ does not pay that error either. The $KK$ contour error alone is
below target throughout this Type-I window.

For general $\beta$, the main-term and Type-I inequalities can overlap
only if $\beta<2-\sqrt6/2=0.775255128608411\ldots$; at the fixed
$\alpha=1/12$ the main-term inequality is
$\beta<13-5\sqrt6=0.752551286084110\ldots$.
The separate errors still require
$(10+3\beta)/6<1+B_*$ and $23/12+\alpha/2<1+B_*$.
These are conditional algebraic thresholds for the displayed estimates,
not new zero-free regions, necessary RH conditions, actual lower bounds
or a global impossibility theorem. A hypothetical squared-two-factor
interface has the same formal residue exponent, but (C51) shows why it
cannot replace this four-factor theorem or its fifteen-term error.

**The next exceptional input has a fixed meaning.** Define

$$
\mathscr S_4(U)=U^{-1/6}\sum_{\epsilon,\mathbf r}\eta_{\epsilon,\mathbf r}
 \sum_a C_4(P_a)\Theta_{4,A}(P_a)
 I_4(q_{e_S(\mathbf r)}q_a^6/U).
\tag{C67}
$$

At the unchanged cutoff a sufficient new frequency-average estimate is
$|\mathscr S_4(U)|\ll\mathcal N_JU^{-\Delta-\sigma+\varepsilon}$
for some fixed $\sigma>0$. Currently (C52) supplies only
$U^{-1/24+\varepsilon}$. This target asks for cancellation on the
same coupled frequency realization. It must be accompanied by
$|\mathcal R_\mu|,|\mathcal R_{\rm tw}|
\ll\mathcal N_JU^{1+B_*-\sigma+\varepsilon}$, or a bound of this
strength for their same-object signed sum together with the residue.
The $KK$ remainder is already smaller. Principal $R_\beta$ supplies
neither the ray/angular residual estimate nor a nonprincipal inverse
Hecke estimate. All these targets are unproved.

**A sufficient local nonexceptional interface, also unproved.** The
precise gap in [Xu–Sang v2, (2.6), (3.6)–(3.7) and Lemma
3.2](https://arxiv.org/html/2610.17675v2#S3.SS2) concerns arithmetic
columns on the same Poisson row. Freeze its $C,\mathfrak b$,
$g=(\operatorname{rad}C,k)$, tensor branch and ray term. Put
$X=L^2/q$, $N=L/(q_Cq_{\mathfrak b})$, $N_i=N/q_{f_i}$,
$K_{\rm row}\asymp RX/q_C$ and $k=gk'$. Let $D_{\rm src}=N\mathfrak d$
be the source moving-twist radical norm, distinct from $D=\sqrt U$,
and let $R_{C,g}$ be its (3.7). The fixed $\Pi_i$ masks are independent
of $k'$. Let $d_i(n)$ be the actual compressed column coefficient at
$C\mathfrak b f_i n$, including its original side/core allocations;
for actual squarefree columns the admissible branch has $C$ squarefree
and $f_i=1$. A sufficient hypothesis $W(\lambda)$ is

$$
\sum_{\substack{0<q_{k'}\ll K_{\rm row}/q_g\\\psi^*_{k'}\ne1}}
\left|\sum_n d_i(n)\nu_i(n)\chi_n(k')
 \chi_n(gd_{\mathbf e}C^\flat)\mathbf1_{(n,\Pi_i)=1}
 V_i(q_n/N_i)\right|^2
\ll N_i(K_{\rm row}/q_g)D_{\rm src}R_{C,g}
 U^{\lambda+\varepsilon}.
\tag{C68}
$$

The symbols $\nu_i,d_{\mathbf e},C^\flat,\psi^*_{k'}$ are exactly those
of the frozen source branch (3.6). Quantification includes all its
original polynomial-size masks, collision zeros, fixed twists and
prescribed bounded profiles, with fixed polynomial height costs and
no new conductor lower bound. It is not a claim for optimized or plain
columns. Divisor-boundedness gives $\sum|d_i(n)|^2\ll N_iU^\varepsilon$;
that mass statement does not prove (C68).

To check local sufficiency, Cauchy on the same $k'$ row gives
$w_{C,g}\sqrt{M_1M_2}$, where $M_i$ is the left side of (C68).
The source relation $w_{C,g}R_{C,g}/q_g\le q_C$ bounds this by
$NRXD_{\rm src}U^{\lambda+\varepsilon}$. On dyads
$q_C\asymp C_0,q_{\mathfrak b}\asymp B_0$, restoring $q/L^3$ and the
$O(C_0B_0)$ frozen labels gives $RD_{\rm src}U^{\lambda+\varepsilon}$.
Shell decay pays $R$. In the corefree $q=L=U$, $D_{\rm src}=1$
normalization of (C59), restoration of $U^2$ therefore gives
$U^{2+\lambda+\varepsilon}$. Thus $\lambda<B_*-1$ would suffice
locally; $\lambda=1/12$ would leave the reserve
$B_*-13/12$ above. The original plain-coefficient (2.6) does not
supply (C68). Its proof would be a new actual-coefficient estimate.
External log-Fourier separation pays its fixed polynomial height
cost with sufficiently rapid decay; derivatives still avoid $b_A$.

Even these exceptional and nonexceptional local targets together do
not close J40. They must be placed back on its original common beta
rows, with all product-squareparts $P<U^{1/6}$, common-$e$ signed
Möbius detector, $\rho$, nontrivial cores, common-column gcds, unit/ray/
angular terms, bad duals and full natural dual dyads. Moving
$D_{\rm src}$ losses and every profile/height coefficient must then be
summed under the one original fixed/polylog aggregate budget; they
cannot enter an unspecified constant. A physical squarefree-row subset
may be restricted after a complete positive energy bound, not by
monotonicity of a signed nonexceptional or exceptional component.
The actual same-beta signed contraction, signed Robin restoration and
RH remain open. No Lean, source-major-proof or priority certification
is made.

## Exact frequency residue and the averaged coupled theta

This continuation evaluates only the displayed all-$K_A$ residue sum
in (C60). Retain (C51), (C58)–(C60), their original profiles and finite
coefficients, and set $A=U^{1/12}$. For each fixed
$d=q_{e_S(\mathbf r)}>0$, put $X=(U/d)^{1/6}$ and $C_0=C_4(1)$.
All sums below count integral ideals once, including the $S$ factors
of $a$. Define the signed or complex functional and Mellin transforms

$$
T_d(U)=\sum_a C_4(P_a)\Theta_{4,A}(P_a)I_4((q_a/X)^6),\quad
\widehat I(v)=\int_0^\infty I_4(t)t^{v-1}\,dt,\quad
\widehat W(z)=\int_0^\infty W(t)t^{z-1}\,dt.
\tag{C69}
$$

Here $I_4$ is smooth at zero and rapidly decreasing with the original
profile envelope; $\widehat I$ is holomorphic for $\Re v>0$.
The original cutoff is $1$ below $1$ and $0$ above $2$.
Omit its four factors temporarily and define

$$
\mathcal D(s,\mathbf z)=
\sum_{\substack{a;\ e_1e_2e_3e_4\ {\rm sf}\\
 (e_1e_2e_3e_4,S)=1,\ (a,e_1e_2e_3e_4)=1}}
\frac{C_4(P_a)q_a^{-s}\prod_i\mu(e_i)2^{\omega(e_i)}q_{e_i}^{-z_i}}
 {\prod_{p\mid e_1e_2e_3e_4}(q_p+4)}.
\tag{C70}
$$

In (C70), $a$ is unrestricted; only the product of the four $e_i$ is
squarefree. Absolute convergence holds for $\Re s>1$, $\Re z_i>0$.
For $q=q_p$, $Q=q^{-s}$, $Z=\sum_iq^{-z_i}$, the normalized local
factor of $\mathcal D/C_0$ is $(1-Q)^{-1}$ at $p\in S$, and otherwise

$$
1-\frac{2Z}{q+4}+\frac q{q+4}\frac Q{1-Q}
=\frac{1-[4Q+2(1-Q)Z]/(q+4)}{1-Q}.
\quad
\mathcal D=C_0\zeta_K(s)\prod_i\zeta_K(1+z_i)^{-2}H(s,\mathbf z).
\tag{C71}
$$

Indeed a prime dividing $a$ contributes $q/(q+4)$ to $C_4(P_a)/C_0$
and cannot divide any $e_i$; otherwise it may enter exactly one $e_i$.
Outside $S$, $H_p$ is the numerator in (C71) divided by
$\prod_i(1-q^{-1-z_i})^2$; inside $S$ it is just that inverse product.
No numerator is inverted. Write $\sigma=\Re s$, $\tau_i=\Re z_i$.
For large $q$, uniformly in all heights on fixed closed real substrips,

$$
H_p-1=O\left(q^{-1-\sigma}+\sum_iq^{-2-\tau_i}
 +\sum_iq^{-1-\sigma-\tau_i}
 +\sum_{i,j}q^{-2-\tau_i-\tau_j}\right),\qquad
\sigma>0,\quad\tau_i>-1/2,\quad\sigma+\tau_i>0.
\tag{C72}
$$

Every exponent then exceeds $1$, proving normal convergence and a
uniform bound for $H$. Its finite denominators do not vanish in this
domain. In particular $H$ introduces no mixed polar divisor.

**Exact residue.** Put $L_q=1-4/[q(q+4)]$ and
$\bar D_q=(q^2+4q-4)/(q-1)=q+5+1/(q-1)$. At $s=1$ the numerator
in (C71) is $L_q(1-2Z/\bar D_q)$. Consequently

$$
\begin{aligned}
\mathop{\rm Res}_{s=1}\mathcal D(s,\mathbf z)&=\bar C\bar F(\mathbf z),\\
\bar C&=\kappa C_0\prod_{p\notin S}L_{q_p}
 =\kappa^5\prod_{p\in S}(1-q_p^{-1})^4
 \prod_{p\notin S}(1+4/q_p-4/q_p^2)(1-q_p^{-1})^4,\\
\bar F(\mathbf z)&=\prod_{p\notin S}
 (1-2\textstyle\sum_iq_p^{-z_i}/\bar D_{q_p})
 =\prod_i\zeta_K(1+z_i)^{-2}\bar H(\mathbf z),\\
\bar Q_A&=\sum_{\substack{e_1e_2e_3e_4\ {\rm sf}\\(e_1e_2e_3e_4,S)=1}}
 \frac{\prod_i\mu(e_i)2^{\omega(e_i)}W(q_{e_i}/A)}
 {\prod_{p\mid e_1e_2e_3e_4}\bar D_{q_p}}.
\end{aligned}
\tag{C73}
$$

The Euler product for $\bar F$ is literal for $\Re z_i>0$; elsewhere
use its displayed factorization. Outside $S$, $\bar H_p$ is its
numerator divided by $\prod_i(1-q_p^{-1-z_i})^2$, and inside $S$ it
is the inverse denominator. Cancellation of linear terms proves normal
convergence for every $\Re z_i>-1/2$, with uniform bounds on fixed
closed real substrips, as in (C55). Thus the $a$ average changes the
prime denominator to $q+5+1/(q-1)$, while each of the four inverse-zeta
exponents stays $-2$. This is a coupled theta, not a square of a
two-variable theta.

**Conditional absolute-error evaluation.** Assume the explicit
[$R_\beta$](../Analytic/liu2026quasirh.md#the-coupled-euler-product-under-an-explicit-reciprocal-strip).
For fixed $0<h<\min\{1-\beta,1/2\}$ and $h<\sigma<1$,

$$
T_d(U)=\frac{\bar C}{6}X\widehat I(1/6)\bar Q_A
 +O_{K,S,W,h,\sigma,R_\beta}(\mathcal N_JX^\sigma A^{-4h}),
\qquad |\bar Q_A|\ll_{K,S,W,h,R_\beta}A^{-4h}.
\tag{C74}
$$

These are absolute bounds, uniform for the specified fixed finite $d$
family and profiles in one common envelope. The moment is signed or
complex; it is not a positive mass or a claimed nonzero number.

**Proof.** Fivefold Mellin inversion initially on $\Re s>1$,
$\Re z_i>0$ gives the integral of
$[\widehat I(s/6)/6]X^s\prod_i[\widehat W(z_i)A^{z_i}]
\mathcal D(s,\mathbf z)$, with measure $(2\pi i)^{-5}ds\,d\mathbf z$.
Move the four $z_i$ lines to $-h$, then the $s$ line to $\sigma$.
The condition $\sigma>h$ keeps all mixed terms inside (C72).
Only $s=1$ contributes a residue, exactly (C73) and its fourfold Mellin
integral $\bar Q_A$. The factor $1/6$ is from the sixth norm power.
Moreover
$\widehat W(z)=-z^{-1}\int_1^2W'(t)t^z\,dt$ has only a simple pole
at zero, with residue $1$. The corresponding double zero of
$\zeta_K(1+z_i)^{-2}$ cancels it throughout this deformation.
There are no $z_i=0$ residues. This cancellation says nothing about
poles at $z_i=\rho-1$ for zeros $\rho$ of $\zeta_K$.

For explicit height control set $\delta=1-\beta-h>0$. The premise
$R_\beta$ bounds each inverse-zeta square by
$O((1+|\Im z_i|)^{2B_\delta})$ on the shifted strips.
Fixed-field meromorphic continuation supplies polynomial zeta growth
of some finite degree $L$ on the $s$ strip away from $1$; bounded-height
joins detour that pole. Choose one finite
$J>L+8B_\delta+20$, enlarged for the original derivative contract.
A sufficient envelope bounds
$\sup_{t\ge0}(1+t)^{J+3}|I_4^{(j)}(t)|$ for $0\le j\le J$,
together with the required original-profile and cutoff seminorms.
Integration by parts gives rapid Mellin decay on the fixed positive
$s/6$ strips and on the $z_i$ lines. This pays all five vertical
integrals, horizontal joins and tails by absolute integrability, giving
the error in (C74). The fourfold argument for $\bar F$ proves its
second bound. No growing-height or new reciprocal allowance is used.
All component/height seminorms are aggregated against absolute
coefficient measures within the same fixed or polylogarithmic budget.

There is no extra $\prod_{p\in S}(1-1/q_p)$ from $a$: its ideals
include all $S$ factors, accounting for the fifth $\kappa$.
The factor $d^{-1/6}$ is already in $X$. The six units remain in the explicit finite sum with
$\eta_{\epsilon,\mathbf r}$, without an extra factor or division by six.
The original $U^2$, $D^{-1}$ side factors and physical-row/core
prefactors of (C59)–(C60) must all be restored in their original places.

**Scale and remaining obligation.** At source-conditional $R_{7/8}$,
choose $h$ just below $1/8$ and $\sigma$ just above $h$, allocating fixed
margins to $\varepsilon$. For every $\varepsilon>0$ this yields

$$
\begin{aligned}
\bar Q_A&\ll_\varepsilon U^{-1/24+\varepsilon},\\
T_d(U)&=\frac{\bar C}{6}d^{-1/6}U^{1/6}\widehat I(1/6)\bar Q_A
 +O_\varepsilon(\mathcal N_JU^{-1/48+\varepsilon}),\\
T_d(U)/X&=\frac{\bar C}{6}\widehat I(1/6)\bar Q_A
 +O_\varepsilon(\mathcal N_JU^{-3/16+\varepsilon}).
\end{aligned}
\tag{C75}
$$

Thus this isolated $U^2T_d$ has principal bound
$O(\mathcal N_JU^{17/8+\varepsilon})$ and evaluation error
$O(\mathcal N_JU^{95/48+\varepsilon})$, times its original prefactor
in modulus. Relative to $U^{13/6}$ the principal saving is still $1/24$;
the new error saves $3/16>\Delta$. Since
$\Delta-1/24=0.040816237971963\ldots$, the principal bound still misses
the sufficient local target $U^{1+B_*-\nu}$. The evaluation error is
below that target when $\varepsilon+\nu<3/16-\Delta$.

If the same $I_4$ is used throughout the finite sum, its leading scalar
is $\widehat I(1/6)\sum_{\epsilon,\mathbf r}
\eta_{\epsilon,\mathbf r}d_{\mathbf r}^{-1/6}$.
If profiles differ, retain their individual moments inside that sum.
An exact vanishing of this scalar would remove this residue, but must
be proved from the actual profiles and coefficient tables. Smoothness
alone neither forces nor excludes it; no such cancellation is proved
here. Without it, one sufficient new hypothesis, with the same uniform
cutoff/derivative contract, is

$$
|\bar Q_A|\ll_\varepsilon A^{-12(\Delta+\nu)+\varepsilon},\qquad
12\Delta=0.989794855663562\ldots,
\tag{C76}
$$

or a sufficient signed bound for the actual finite aggregate. The
provided contour gives exponent $1/2$, not this exponent. Further
joint deformation must control the residue itself: $R_{7/8}$ does not
exclude zeros at or left of $7/8$, bound crossed zero residues, or
force $\bar H$ to vanish there. No new zero-free input or inverse-zeta
pole cancellation is assumed. All old (C60) error estimates remain
unchanged. The target bounds for the other fifteen $\mu$ terms,
$\mathcal R_{\rm tw}$, (C68), other cores/gcds, bad duals and the
original same-$\beta$ signed J40 aggregation remain unpaid. A selected Poisson component has no
positivity or monotonicity under physical-row selection. This reduction
is paper-level only and does not strengthen the principal estimate,
prove a lower bound or impossibility theorem, certify the manuscript,
or close J40, signed Robin restoration or RH.

The [joint mixed-Mobius and residue companion](liu2026quasirhresidue.md)
proves a source-conditional improvement of the fifteen radial mixed terms,
with the original profiles and punctures, and records the actual finite
residue interface. Its scope and remaining J40 obligations are explicit.

## A small reduced-frequency sector of the actual C68 columns

The [reduced-frequency companion](liu2026quasirhreduced.md#a-small-reduced-frequency-sector-of-the-actual-c68-columns)
retains C77–C86 for the small nonunit sector of the actual bare-J4
columns, with the original and exact redesigned cutoffs. Its
[original-W0 dominant endpoint](liu2026quasirhreduced.md#a-source-conditional-dominant-endpoint-for-original-w0)
retains C87–C92's sharper $R^{1/6}$ bound on $q_r\asymp U$.
The [all-annulus original-W0 endpoint](liu2026quasirhreduced.md#a-source-conditional-all-annulus-endpoint-for-original-w0)
extends bare nonunit coverage in C93–C97 to every $r>1$, with all
sixth-power repetitions, independent physical-row and column scales,
one original coupled envelope and the weighted large-shell tail.
The source-conditional raw $U^\kappa$, $D^{-2}$-restored $U^{B_*}$
endpoint has zero strict C68 reserve; the exceptional original-W0
principal scalar, other branches and full C68/J40/RH remain open.
C51–C76 remain in this note.
