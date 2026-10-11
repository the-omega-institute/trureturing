---
bibkey: faveri2026fixedorder
authors: Alexandre de Faveri
year: 2026
title: Optimal large sieve for fixed order characters
doi: null
url: https://arxiv.org/abs/2610.04045v1
claim: Theorem 1.1 supplies a source-conditional mixed moment for the original common-character sextic detector; known cubic and quadratic suppliers pay its lower-order blocks, leaving an actual-order-six residual, while the generic count budget is dominated by existing legal detector settings and signed restoration remains open.
strata_touched: []
license: citation-only
triage: anchor
---

# Optimal large sieve for fixed order characters

The source is [arXiv:2610.04045v1](https://arxiv.org/pdf/2610.04045v1), submitted 2 October 2026. This card records Theorem 1.1, a conditional application to the original common-character detector, a reduction of its remaining coefficient-sensitive estimate to actual-order-six ratios, and the separate conditions relevant to the transported FIB sextic packet. The paper already supplies a zero-density estimate in Corollary 1.5. Neither the sieve nor the zero-density method is a project invention. The analytical source and the application have no independent local Lean certification; they do not establish a Robin or Riemann-hypothesis conclusion.

The theorem fixes $n\ge3$, a number field containing the $n$-th roots of unity, and a finite set $S$ containing the places above $n$ such that the ring of $S$-integers has class number one. The family $\chi_a$ is built from fixed ray data. Its reciprocity law has the form

$$
\chi_a(b)\,\chi_b(a)^{-1}=\alpha([a],[b]),
$$

where the phase $\alpha$ depends only on the two ray-class images. Thus the theorem permits a finite ray-class decomposition; it does not permit an unqualified exchange of the two arguments.

## The large-sieve statement

Let $n\ge3$, let $K$ contain the $n$-th roots of unity, and fix the finite set of places and ray data used to construct the family of $n$-th order Hecke characters $\chi_a$. With $\Theta_n(A,B)$ denoting the operator norm in which both the parameter $a$ and the inner variable $b$ range over $n$-th-power-free ideals, Theorem 1.1 states

$$
\Theta_n(A,B)
\ll_{\varepsilon}
(AB)^\varepsilon
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right).
$$

The theorem is therefore available in principle for $n=6$ over the Eisenstein field, which contains the sixth roots of unity. Its hypotheses concern the specified Hecke-character family and ideal norms; they do not supply a result for an arbitrary row weight or an arbitrary signed subpacket.

## Application to the original common-character detector

The source for the detector is the pinned [primary manuscript](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex): Proposition `prop:detector-witness`, Lemma `lem:inverse-amplification`, the zero-slot case of Lemma `lem:plain`, and Proposition `prop:detector-counts`. These are analytical premises for this application. Their proof is reused, and the different toolchain and certification boundary remain as recorded in the [owning note](openai2026quasirh.md).

Work over $F=\mathbb Q(\sqrt{-3})$, with fixed arithmetic exclusions $S$, the original ideal norm $q_h=Nh$, and retained physical element rows $q_u\asymp U$ for which $(u)$ is sixth-power-free. Retain the source detector's rows whose primitive inducing character is nonprincipal. The finitely many sixth-power-free rows supported entirely at $S$ are handled by the original finite-exception decomposition. Fix one of the finitely many original presentations

$$
\psi_u(h)=\nu(h)\chi_h^{\rm raw}(u)^{\varepsilon_\chi},
\qquad \varepsilon_\chi\in\{1,-1\},
$$

where $\nu$ is the fixed ray twist. The negative orientation means complex conjugation of the zero-extended symbol, including its zero values. Both witnesses use this same character:

$$
M_u(D)=D^{-1/2}\sum_d\mu(d)\psi_u(d)W_M(q_d/D),
\qquad
S_u(N)=N^{-1/2}\sum_n\psi_u(n)W_S(q_n/N).
$$

The annular profiles, common exclusions, and original zero extensions are retained. This common-character product is different from a product whose inverse and plain factors carry different characters.

### Finite correction to the source family

Sections 2.3–2.5 of de Faveri construct the character from

$$
\mathfrak u=(x)E\mathfrak g^6,
\qquad x\equiv1\pmod{\mathfrak c},
\qquad
\chi_{\mathfrak u}^{\rm DF}(h)=
\left(\frac{x m_E}{h}\right)_6
$$

on the coprime locus, with its prescribed zero extension. Here $\mathfrak u$ is the part of $(u)$ away from $S$. The Eisenstein ring is a PID, so choose a fractional generator $\gamma$ of $\mathfrak g$. Since $E\mathcal O_S=m_E\mathcal O_S$, the quotient

$$
\epsilon_u=\frac{u}{x m_E\gamma^6}
$$

is an $S$-unit. The quotient of the $S$-unit group by sixth powers is finite. Comparing the primitive Kummer classes therefore gives, after a finite partition of rows,

$$
\chi_h^{\rm raw}(u)
=\kappa_{\epsilon_u}(h)\chi_{\mathfrak u}^{\rm DF}(h).
$$

The correcting column character $\kappa_{\epsilon_u}$ is fixed in each partition. Do not assume that it is identically one. The $S$-parts of a sixth-power-free row, as well as its unit labels, have only finitely many possibilities; their norms change the row scale only by fixed factors. The original columns already avoid $S$. On these columns both characters vanish when $h$ meets $\mathfrak u$.

The auxiliary $\gamma^6$ introduces no additional zeros. Evaluate with the coprime decomposition allowed in Section 2.3.4, or compare the primitive Kummer characters and then restore the prescribed zeros. Evaluating one unsuitable fractional generator at all columns would create an artificial mask. For the negative orientation, first conjugate the entire product and its coefficients, which preserves its squared norm. Then absorb the fixed twist and finite corrections into column coefficients of the positive-orientation sieve. This application needs no reciprocity exchange of the two sieve variables and no moving quadratic-character reduction to a cubic family.

### Convolution columns and their natural masks

Put $K=DN$. Multiplicativity of the original zero-extended character gives the exact finite identity

$$
M_u(D)S_u(N)
=K^{-1/2}\sum_h B_{D,N}(h)\psi_u(h),
\qquad
B_{D,N}(h)=\sum_{dn=h}\mu(d)W_M(q_d/D)W_S(q_n/N).
$$

For fixed profiles, these coefficients are independent of the row. Their support has $q_h\asymp K$, and they are divisor-bounded. Annular truncation prevents replacing this convolution by the full identity $\mu*1=\mathbf1_{h=1}$.

The columns $h=dn$ need not be sixth-power-free. Write each one uniquely as

$$
h=ab^6,\qquad a\text{ sixth-power-free}.
$$

No coprimality between $a$ and $b$ is imposed. The original symbol satisfies

$$
\chi_{ab^6}^{\rm raw}(u)
=\chi_a^{\rm raw}(u)\mathbf1_{(b,u)=1}.
$$

After absorbing the fixed column twists, let $c_{a,b}$ denote the resulting coefficient divided by $K^{1/2}$. Divisor bounds and ideal counting give

$$
\sum_{a\ {\rm sixth\ power\ free}}|c_{a,b}|^2
\ll_{\mathcal A,\varepsilon}K^\varepsilon q_b^{-6},
\qquad q_a\ll K/q_b^6.
$$

For each fixed $b$, retain the row restriction $(b,u)=1$ before applying the sieve; enlarging this restricted row set is allowed inside the positive squared norm. Theorem 1.1 applies to the sixth-power-free row ideal $\mathfrak u$ and column ideal $a$. Its four terms are monotone in the column length, so each application is bounded using

$$
F_6(U,K)=U+K+U^{5/6}K^{1/3}+U^{1/3}K^{5/6}.
$$

Minkowski's inequality then sums row $\ell^2$ norms with weight $q_b^{-3}$. The ideal series $\sum_b q_b^{-3}$ converges. Thus, conditional on the analytical suppliers,

$$
\sum_{u\ {\rm retained}}|M_u(D)S_u(N)|^2
\ll_{\mathcal A,\varepsilon}
(UK)^\varepsilon F_6(U,K)(1+T_1)^{A_{\mathcal A}}.
$$

There is no new polynomial norm cost from the sixth-power decomposition. Each sieve invocation has a row-independent coefficient vector. To allow the original rowwise choices of real exponent, common twist, and smooth profile, apply the existing smooth-calculus/Sobolev argument to finitely many profile derivatives after those fixed-coefficient bounds. The derivative orders are fixed, and the finite seminorm and polynomial height factor shown above remain explicit. The original cumulative height allowance is still required; each factor does not receive a fresh allowance.

### Comparison with the existing whole-bin detector

The actual witness lengths are $D=U^r$, $N=U^m$, and $\tau=r+m$. For each permitted setting $t\in[1,3/2]$, the source supplies

$$
r\le t+O(1/\log U),\qquad
\tau\ge t-O(\text{loss}),\qquad
0\le m\le1/2+O(\text{loss}),
$$

as well as simultaneous lower bounds

$$
|M_uS_u|^2\gg U^{\delta\tau-\varepsilon},
\qquad |M_u|^2\gg U^{\delta r-\varepsilon},
\qquad |S_u|^2\gg U^{\delta m-\varepsilon}.
$$

Here $\delta=2a-1$ is the original zero-bin parameter. This comparison is restricted to $1/50<\delta\le5/6$; it does not assert that this is the full range of the witness proposition. The lengths are those returned by the detector, not freely shortened to $\tau=t$.

The generic mixed moment gives the count-budget function

$$
J_6(\tau)=\max\{1,\tau,5/6+\tau/3,1/3+5\tau/6\},
\qquad
R_{\rm mix}=J_6(\tau)-\delta\tau.
$$

Since $\tau\ge1-O(\text{loss})$ and $\delta\le5/6$,

$$
R_{\rm mix}\ge7/6-\delta-O(\text{loss}).
$$

This lower bound is on the exponent supplied by this upper-bound formula; it is not a lower bound on the actual moment or row count.

The existing unmarked inverse second moment and plain fourth moment already give, on the same actual witness class,

$$
R_{\rm sep}(r,m)=
\min\{A(r)-\delta r,1-2\delta m\},
\qquad A(r)=\max\{1,(1+5r)/6\}.
$$

For $r\le1$, use $\max(r,2m)\ge2(r+m)/3$. For $r\ge1$, use $r\le t+O(1/\log U)$ and $5/6-\delta\ge0$. Every witness pair returned at setting $t$ consequently satisfies

$$
R_{\rm sep}(r,m)\le E_t(\delta)+O(\text{loss}),
\qquad
E_t(\delta)=
\max\{1-2\delta t/3,1/6+(5/6-\delta)t\}.
$$

Two legal fixed settings suffice for comparison. For $0<\delta\le1/3$, take $t=1$; both terms are at most $7/6-\delta-1/18$. For $1/3<\delta\le5/6$, take $t=5/4$. The differences from $7/6-\delta$ are then

$$
\frac{1-\delta}{6}\ge\frac1{36},
\qquad
\frac\delta4-\frac1{24}>\frac1{24}.
$$

Hence an already supplied zero-slot estimate has a uniform count-budget exponent at most

$$
7/6-\delta-1/36.
$$

The fixed positive reserve absorbs the original arbitrarily small witness and dyadic losses. Both settings have the original common-character, profile, and height contract; the $r=1$ boundary uses the existing amplification estimate. This comparison needs no prime-supply or slot-rounding hypothesis and does not optimize Liu's boundary again.

A fixed-setting improvement alone would miss this comparison. For example, at $\delta=3/4$, combining the mixed moment with both old moments at $t=1$ yields the uniform exponent $3/7$, improving the old $t=1$ exponent $1/2$. But the permitted $t=5/4$ setting already supplies $3/8<3/7$. Thus the generic application above does not improve the whole-bin detector's available uniform bound. In particular, it does not remove the $\delta=3/8$ budget gap in the owning note.

### The remaining coefficient-sensitive estimate

For fixed profiles and one presentation, absorb the fixed column twist and common mask into $c(h)$. Here $c(h)$ is the unnormalized convolution coefficient, without division by $K^{1/2}$; the earlier $c_{a,b}$ included that division. For the actual retained row set $\mathcal U$, define

$$
\mathcal K_U(h,k)=\sum_{u\in\mathcal U}
\chi_h^{\rm raw}(u)^{\varepsilon_\chi}
\overline{\chi_k^{\rm raw}(u)^{\varepsilon_\chi}}.
$$

The original mixed moment is exactly

$$
K\sum_{u\in\mathcal U}|M_uS_u|^2
=\sum_{h,k}c(h)\overline{c(k)}\mathcal K_U(h,k).
$$

Let $h^\flat$ be the sixth-power-free part of $h$. The block $h^\flat=k^\flat$ already has the bound

$$
\left|\sum_{h^\flat=k^\flat}
c(h)\overline{c(k)}\mathcal K_U(h,k)\right|
\ll U\sum_{a\ {\rm sixth\ power\ free}}
\left(\sum_b|c(ab^6)|\right)^2
\ll_\varepsilon UK^{1+\varepsilon}.
$$

Indeed the number of possible $b$ at fixed $a$ is $O((K/q_a)^{1/6})$, so divisor bounds and ideal counting reduce the last sum to $K^\varepsilon\sum_{q_a\ll K}(K/q_a)^{1/3}\ll K^{1+\varepsilon}$. Natural zeros are retained in the identity and only majorized in this positive bound.

At the balanced scale $K\asymp U$, a sufficient stronger input would therefore be

$$
\Re\sum_{h^\flat\ne k^\flat}
c(h)\overline{c(k)}\mathcal K_U(h,k)
\ll_{\mathcal A,\varepsilon} UK\,U^\varepsilon
$$

uniformly on the original coefficients, masks, profiles, and presentations. This is an open coefficient-sensitive off-block estimate. The generic sieve allows an extra $U^{1/6}$ at this scale. A result only at $DN\asymp U$ would still require coverage of the other actual witness lengths; the detector does not promise to return that scale. The trace identity is a way to state the missing input, not a new sieve theorem or a proved cancellation result.

The full transported signed packet below remains a different application. None of these nonnegative moment bounds restores its root numbers and signed parent columns or supplies the original fixed-index Robin target $[-I_\psi(A)]_+=o(A^{-\eta_{\rm R}})$ with $0<\eta_{\rm R}<1/2$. The actual CA/GA1 source, zeros, phases, prime powers, atoms, endpoints, and collisions still have to be retained there.

### Separating the lower-order character blocks

The off-block above has nonprincipal ratios of actual order two, three, or six. The lower-order parts can be paid using existing suppliers, leaving a sufficient contract only for actual order six. This is a source-conditional application of known operator bounds, not a new sieve or a historical originality claim. The analytical application has no complete local Lean certification.

First preserve the physical row domain. Write each retained sixth-power-free element as $u=\zeta\operatorname{gen}(s)v$, where $s$ is its ideal part supported on $S$ and $v$ is a good primary generator. The unit and $S$-part have finitely many possibilities. For a fixed label $j=(\zeta,s)$, use $U_j=U/q_s$ and

$$
c_j(h)=c(h)\chi_h^{\rm raw}(\zeta\operatorname{gen}(s))^{\varepsilon_\chi}.
$$

The actual good row set $\mathcal V_j$ retains the original nonprincipal-row selection and norm profile. On good columns the extra factor has modulus one, so $c_j$ remains divisor-bounded. A physical row divisible by a prime in $S$ has not been set to zero. Subsequent enlargement of $\mathcal V_j$ is used only to bound positive squared norms. The finite ray and source-family corrections are those already specified above; negative orientation conjugates the whole coefficient polynomial.

For $m\in\{2,3,6\}$, let $r_m(h)$ be the ideal with valuations $v_{\mathfrak p}(h)\bmod m$. Define positive block energies on the actual rows by

$$
H_{m,j}=\sum_a\sum_{v\in\mathcal V_j}
\left|\sum_{r_m(h)=a}c_j(h)
\chi_h^{\rm raw}(v)^{\varepsilon_\chi}\right|^2.
$$

All columns are good and use the original multiplicative primary convention. Consequently equality of $r_2$ means the ratio character has order dividing three, equality of $r_3$ means order dividing two, and their intersection is equality of $r_6$. Here the ratio means its actual primitive inducing character on the coprime locus; its prescribed zeros are still retained in every polynomial. In particular a principal ratio is not the constant function one on rows meeting either column.

The two operator suppliers are de Faveri's Theorem 1.1 with $n=3$ and [Goldmakher–Louvel, *A quadratic large sieve inequality over number fields*, Definition 1 and Theorem 1.1](https://arxiv.org/abs/1112.1642). They give respectively

$$
\Theta_3(A,B)\ll_\varepsilon(AB)^\varepsilon
\bigl(A+B+(AB)^{2/3}\bigr),\qquad
\Xi_2(A,B)\ll_\varepsilon(AB)^\varepsilon(A+B).
$$

The first has cubefree indices; the second has squarefree indices. The pinned detector's `eq:quadratic-large-sieve` already verifies the primary quadratic family, its ramified conductor and finite-ray transpose. Those family checks are reused.

For a parity core $a$, write $h=ab^2$ with $a$ squarefree and $q_b\ll B_a=(K/q_a)^{1/2}$. No condition $(a,b)=1$ is imposed. Since

$$
\chi_{ab^2}^{\rm raw}(v)=\chi_a^{\rm raw}(v)
\kappa_b(v),\qquad \kappa_b=\bigl(\chi_b^{\rm raw}\bigr)^2,
$$

the block is bounded by a cubic positive row norm after using $|\chi_a^{\rm raw}(v)|\le1$. De Faveri's Lemma 6.1 already removes cubes from unrestricted good rows. Applying it with Theorem 1.1 gives the all-row, cubefree-column supplier

$$
(U_jB)^\varepsilon
\max_{1\le R\ll U_j^{1/3}}
R\Theta_3(U_j/R^3,B)
\ll_\varepsilon(U_jB)^\varepsilon
\bigl(U_j+U_j^{1/3}B+(U_jB)^{2/3}\bigr).
$$

To retain arbitrary columns, write $b=b_0z^3$ with $b_0$ cubefree. The exact symbol is $\kappa_{b_0}(v)\mathbf1_{(z,v)=1}$, including overlaps between $b_0,z,a$. For each fixed $z$, the coefficient squared norm is $\ll_\varepsilon K^\varepsilon B_a/q_z^3$. The row mask is enlarged only inside that fixed positive norm. Minkowski sums the resulting norms with weight $q_z^{-3/2}$, whose ideal series converges. This gives the parity-block bound

$$
\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon B_a
\bigl(U_j+U_j^{1/3}B_a+U_j^{2/3}B_a^{2/3}\bigr).
$$

For a mod-three core $a$, write $h=ab^3$ with $a$ cubefree and $q_b\ll B_a=(K/q_a)^{1/3}$. The remaining symbol $\bigl(\chi_b^{\rm raw}\bigr)^3$ is quadratic. The same positive square decomposition uses $v=v_0t^2$, $b=b_0z^2$, with squarefree $v_0,b_0$. At fixed $t$, $\mathbf1_{(b,t)=1}$ stays in the coefficient vector; at fixed $z$, $\mathbf1_{(z,v_0)=1}$ restricts the positive outer sum. The $z$ norm weights are $q_z^{-1}$ and pay only a logarithm. The known quadratic supplier therefore gives the mod-three block bound

$$
\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon B_a
\bigl(U_j+U_j^{1/2}B_a\bigr).
$$

Ideal counting pays the core sums: for the parity blocks, $\sum_aB_a\ll K$, $\sum_aB_a^2\ll K\log(2K)$, and $\sum_aB_a^{5/3}\ll K$; for the mod-three blocks, $\sum_aB_a\ll K$ and $\sum_aB_a^2\ll K$. Together with the already bounded sixth-core block, this yields

$$
H_{2,j}+H_{3,j}+H_{6,j}
\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon U_jK.
$$

Fixed changes in annular scales are absorbed in the arithmetic datum. The bound holds for $U_j,K\ge1$, rather than just at $K\asymp U_j$. For rowwise original profile choices, use the previously specified finite smooth-calculus derivatives and the same cumulative height allowance; no fresh height allowance is supplied by a block.

Let $T_j$ be the original unnormalized positive mixed moment on $\mathcal V_j$, and let $E_{6,j}$ be the full Hermitian contraction over pairs satisfying both $r_2(h)\ne r_2(k)$ and $r_3(h)\ne r_3(k)$. These pairs have actual ratio order six. Finite expansion gives

$$
T_j=H_{2,j}+H_{3,j}-H_{6,j}+E_{6,j}.
$$

The exact order-three and order-two contractions are $H_{2,j}-H_{6,j}$ and $H_{3,j}-H_{6,j}$ respectively. Each has a paid upper bound; neither must be nonnegative. Likewise $H_{2,j}+H_{3,j}-H_{6,j}$ is not asserted positive. A sufficient remaining input is now

$$
\Re E_{6,j}\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon U_jK
$$

uniformly on the original coefficients, masks and profiles. The finite physical labels then recover the original $UK$ scale. This residual still contains nonsquarefree columns, shared prime factors, all sixth-power tails and both character orientations. The natural masks cannot be dropped from $E_{6,j}$ by a positive-row comparison. The reduction pays only the lower-order parts; it does not prove the residual, improve the existing whole-bin detector by itself, or restore the signed Robin packet.

## Known estimates for the squarefree Gauss pairing

A restricted pairing of the actual convolution coefficients can be matched to existing cubic estimates. This does not yet identify it as the complete resonant projection of the sixth-order sieve. Use the original primary generators and good-prime exclusions, fix bounded annular profiles and the finite ray twist $\nu$, and restrict both factors to squarefree indices. Define

$$
Q_{\rm sf}(D,N)=
\sum_{\substack{d,n\ {\rm good\ primary\ sf}\\(d,n)=1}}
\mu(d)\nu(dn)W_M(q_d/D)W_S(q_n/N)\gamma_1(dn).
$$

The pinned detector manuscript's `lem:fixed-gauss-phase` already supplies, for coprime squarefree indices,

$$
\gamma_j(dn)=\chi_d(n)^j\chi_n(d)^j\gamma_j(d)\gamma_j(n),
\qquad
\chi_n(d)=\mathcal R(d,n)\chi_d(n).
$$

Its `eq:signal`, also used explicitly in the second Poisson calculation, already gives

$$
\mu(d)\gamma_1(d)
=\alpha(d)G(d)\overline{\gamma_2(d)},
\qquad \alpha(d)=d/|d|.
$$

These are reused source formulas, not new bridge theorems. Put $\kappa_d(n)=\chi_d(n)^2$. On each fixed pair of ray classes, $\mathcal R(d,n)$ is constant, and the pairing, up to this constant, is

$$
\sum_{d,n}a_d b_n\kappa_d(n),
\qquad
 a_d=\mu(d)\nu(d)W_M(q_d/D)\gamma_1(d),
\qquad
 b_n=\nu(n)W_S(q_n/N)\gamma_1(n).
$$

The cubic symbol's zero extension retains $(d,n)=1$; no ordinary $\mu*1$ cancellation has occurred. The coefficients are fixed in each sieve application, and $\|a\|_2^2\ll D$, $\|b\|_2^2\ll N$ for these bounded profiles. Heath-Brown's cubic large sieve, as stated in Theorem 3.12 of [David–de Faveri–Dunn–Stucky, *Non-vanishing for cubic Hecke L-functions*, arXiv:2410.03048v2](https://arxiv.org/html/2410.03048v2#S3.SS6), directly yields

$$
|Q_{\rm sf}(D,N)|
\ll_{\mathcal A,\varepsilon}
(DN)^{1/2+\varepsilon}
\left(D+N+(DN)^{2/3}\right)^{1/2}.
$$

At $D\asymp N$ with $K=DN$, this is $K^{5/6+\varepsilon}$ for the unnormalized pairing. This is an application of the known cubic operator bound; it is neither a new sieve nor a bound for the full mixed moment. In particular no normalized resonant vector or complete residual kernel has been identified by this calculation.

### Exact additive-character transport

The two manuscripts use different additive characters. The pinned detector uses $e(z)=\exp(2\pi i\operatorname{Tr}(z/\lambda))$, whereas David–de Faveri–Dunn–Stucky use $\check e(z)=\exp(2\pi i\operatorname{Tr}(z))$, with $\lambda=\sqrt{-3}$. Write $\widetilde g_3(r,d)=q_d^{-1/2}g_3(r,d)$ in the latter convention. On the retained coprime locus, their Lemma 3.1(a) gives the exact transport

$$
\gamma_2(d)=\kappa_d(\lambda)\widetilde g_3(1,d),
\qquad
\overline{\gamma_2(d)}\kappa_d(n)
=\overline{\widetilde g_3(\lambda^2n,d)}.
$$

Thus the moving shift is $\lambda^2n=-3n$. After a finite ray decomposition, the inner sum in $Q_{\rm sf}$ has the form

$$
T_{n,\xi}(D)=
\sum_{\substack{d\ {\rm good\ primary\ sf}\\(d,n)=1}}
\xi(d)\alpha(d)W_M(q_d/D)
\overline{\widetilde g_3(-3n,d)}.
$$

Here $\xi$ is the fixed ray weight produced by $\nu(d)$, $G(d)$ and the chosen ray filter; the outer coefficient remains $\nu(n)W_S(q_n/N)\gamma_1(n)$. One may expand the finite filter into ray characters, but that does not remove the angular factor $\alpha(d)$ or prove a twisted analytic estimate.

Their Lemma 6.6 supplies precisely

$$
\sum_{0<q_m\le M}|\psi(hm,\sigma+it)|^2
\ll_{\sigma,\varepsilon}
q_h^{1/2}M^{1+\varepsilon}(1+|t|)^2,
\qquad 1<\sigma\le5/4,
$$

where $\psi$ is the cubic Gauss series defined in their (6.1)–(6.2), not an arbitrary coefficient polynomial. It allows nonsquarefree and ramified shifts, so $h=-3$ itself is admissible. It does not by its stated conclusion supply the extra angular/ray-weighted series in $T_{n,\xi}$. Their Lemma 6.1 already provides removal of specified coprimality filters; those identities should be reused where their hypotheses match. The remaining task is a faithful angular/ray-twisted truncation and mean-square interface, with its costs, rather than another proof of Gauss CRT or of filter removal. Lemma 6.7 supplies a truncation formula for its stated untwisted data and includes a possible $4/3$ pole. Its residue cannot be declared zero for the original weighted pairing without a corresponding argument.

The original convolution also contains nonsquarefree $n$, common prime factors of $d,n$, sixth powers, and columns whose valuations lie in $2,\ldots,5$. The original $\gamma_j(c)$ is defined only for squarefree $c$. Those other character columns cannot be discarded because a different full-modulus Gauss sum vanishes on them; permitting nonsquarefree shifts in Lemma 6.6 does not supply their conversion formulas. Negative orientation still requires conjugating the entire original product with its coefficients and ray factors. The full coefficient-sensitive off-block contraction, coverage of the actual witness lengths, and signed Robin restoration remain open. All estimates in this subsection are conditional on the cited analytical suppliers and have no complete local Lean certification.

## The possible FIB interface

The active carrier expression in the current native packet is

$$
a=A_1R_2^2R_3^3R_4^4R_5^5.
$$

The existing [sextic packet analysis](openai2026quasirh.md) already records the primary-generator choice, the unit and modulus-36 finite Fourier factors, the root-number transport, and the source decomposition

$$
u=\epsilon_u n b_2^2b_3^3b_4^4b_5^5.
$$

Those results are the reusable local input for this interface. They do not yet identify the project's transported character, with all its zero extensions and masks, with the particular ray-data family $\chi_a$ fixed in de Faveri's definition, so the reciprocity step remains an interface obligation rather than a second derivation of the local formulas.

If the five radicals are actual pairwise-coprime squarefree ideals, then every prime valuation of $a$ is in ${0,1,2,3,4,5}$, so $a$ is sixth-power-free. Freezing $R_2,R_3,R_4,R_5$ and applying the theorem in the $A_1$ direction gives the four formal output scales

$$
R^2,\qquad A_1R,\qquad A_1^{5/6}R^{4/3},\qquad A_1^{1/3}R^{11/6}.
$$

Combining those scales with the already recorded carrier count produces the source-conditional exponent envelope

$$
\max\left\{\frac5{12},\frac49,\frac{19}{36},\frac49\right\}
=\frac{19}{36}<\frac23.
$$

This is an arithmetic comparison of exponents. It becomes an analytic estimate only after the source packet has been shown to satisfy every hypothesis below.

## Conditions that remain open for this application

The project has the character in the orientation $\chi_p(a)$, while the theorem is stated for $\chi_a(b)$. Sextic reciprocity gives a finite ray-class phase relating them on the coprime locus, but that phase must be partitioned and transported together with the original units, conjugate orientation, and all zero extensions. The extra fixed factors already present in the source row also have to be included before the row parameter is declared sixth-power-free.

The theorem is an $L^2$ operator bound with a coefficient vector in the inner variable. The native packet additionally contains the original Möbius coefficients, moving masks, common smooth profiles, and a complete signed pair of parent columns. It is necessary to prove that these weights can be fixed or decomposed without a new polynomial loss, and that polarization or an equivalent argument preserves the complete signed restoration.

There is also a direction-of-use constraint. The existing sextic packet invokes a fixed-$d$ estimate of the shape

$$
\sum_{Nn\le M}\gamma(n)\overline{\chi_n(d)}
\ll M^{2/3+\varepsilon}N(d)^{1/6+\varepsilon}
       +M^{6/7+\varepsilon}N(d)^{1/14+\varepsilon}.
$$

Theorem 1.1 does not imply this pointwise estimate by substitution. At most, after a valid reciprocity and duality step, it gives a bound of the form

$$
\left|\sum_{Nn\le M}\gamma(n)\chi_n(d)\right|^2
\le \Theta_6(M,N(d))\sum_{Nn\le M}|\gamma(n)|^2,
$$

with the complete inner range and its sixth-power-free support included. A proof using de Faveri must therefore keep the whole compatible $d$-family (or pay and record the reduction to it); it cannot silently replace the fixed-$d$ input in the existing row estimate.

Finally, the frozen carrier sums must be performed on the same actual realization. Independent optimization of the five carrier boxes would not establish a bound for the jointly constrained source. Until these reciprocity, sixth-power-free, profile, restoration, and joint-count steps are supplied, the $19/36$ figure is only a conditional interface calculation. It does not prove the native Robin estimate, Robin's inequality, or the Riemann hypothesis.
