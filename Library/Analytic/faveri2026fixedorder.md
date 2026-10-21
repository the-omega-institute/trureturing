---
bibkey: faveri2026fixedorder
authors: Alexandre de Faveri
year: 2026
title: Optimal large sieve for fixed order characters
doi: null
url: https://arxiv.org/abs/2610.04045v1
claim: Theorem 1.1 supplies a source-conditional mixed moment for the original common-character sextic detector; specified pure-power pieces, a Gauss-row correction, a balanced-sector prime-labelled residue quadratic, one complete continuous primitive-inversion summand and the labelled second-choice/all-other-first reflection for every numerator valuation on a smaller sector are controlled, while the full primitive-residue quadratic, complementary operator and signed restoration remain open.
strata_touched: []
license: citation-only
triage: anchor
---

# Optimal large sieve for fixed order characters

The source is [arXiv:2610.04045v1](https://arxiv.org/pdf/2610.04045v1), submitted 2 October 2026. This card records Theorem 1.1, a conditional application to the original common-character detector, a reduction of its remaining coefficient-sensitive estimate to actual-order-six ratios, classwise all-column pure-dual-power applications under specified length conditions, fixed-ray angular theta and second-moment applications on the coprime squarefree packet, growing-ray, zero-support and weighted-interpolation applications improving the complete classwise pole and paying the specified pure-power subterm on stated original witness sectors, a squarefree-component consumer covering all original witness lengths under the original height reserve, a weighted powerful-part positive majorant extending that collective pure-power payment to every original column, an actual Gauss-row compression with its growing-label Gram condition supplied and coherent correction consumed in every original core packet, a prime-labelled primitive-residue estimate and an exact unchanged-numerator term of its continuous adjoint for the unsplit convolution on a balanced witness sector, the labelled second-choice/all-other-first reflection including every numerator valuation and its centered-mark dual on a smaller growing-label sector, and the separate conditions relevant to the transported FIB sextic packet. The paper already supplies a zero-density estimate in Corollary 1.5. Neither the sieve nor the zero-density method is a project invention. The analytical source and the applications have no independent local Lean certification; they do not establish a Robin or Riemann-hypothesis conclusion.

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

### A source-conditional pure-dual-power contraction

To use Poisson on a complete ideal family, choose a fixed nonnegative smooth annular majorant $W\ge1$ on the actual row norm support, and define

$$
\widetilde T_j=\sum_{v\ {\rm good\ sixth\ power\ free}}
W(q_v/U_j)\left|\sum_hc_j(h)
\chi_h^{\rm raw}(v)^{\varepsilon_\chi}\right|^2\ge T_j.
$$

Define $\widetilde H_{m,j}$ and $\widetilde E_{6,j}$ by expanding this new positive moment. The lower-order bounds apply to these new blocks with the fixed seminorms of $W$. This compares complete positive moments first; it does not compare $E_{6,j}$ to $\widetilde E_{6,j}$ or erase an arbitrary selector from a signed contraction.

For each actual-order-six pair, let $\xi=\xi_{h,k}$ be the primitive character inducing $\chi_h^{\varepsilon_\chi}\overline{\chi_k^{\varepsilon_\chi}}$ on the coprime locus, with its full conductor $\mathfrak f=\mathfrak f_{h,k}$ and trivial infinite type. Put

$$
P=P_{h,k}=\operatorname{rad}\left(hk\prod_{\mathfrak p\in S}\mathfrak p\right),
\qquad R=R_{h,k}=\prod_{\substack{\mathfrak p\mid P\\\mathfrak p\nmid\mathfrak f}}\mathfrak p.
$$

Extend the original good-row ratio by zero to all integral ideals. This extension is exactly $\xi(v)\mathbf1_{(v,R)=1}$: primes of $P$ lying in $\mathfrak f$ are already zeroed by $\xi$, and every remaining original column or $S$-row exclusion is enforced by $R$. This is not an identity for unsplit physical rows. Common prime factors and redundant zero-support primes absent from the primitive conductor belong to $R$. No artificial fractional-generator zeros are inserted.

Let $b_W$ be the upper endpoint of the support of $W$, and define

$$
L_j=(b_WU_j)^{1/6},\qquad
M_{P,L_j}(w)=\sum_{\substack{q_\ell\le L_j\\(\ell,P)=1}}\mu(\ell)q_\ell^{-w},
\qquad
\vartheta(\mathfrak f)=\prod_{\mathfrak p\mid\mathfrak f}(1-q_{\mathfrak p}^{-1}).
$$

The row sixth-power-free indicator is expanded by the finite sum $\sum_{\ell^6\mid v}\mu(\ell)$. Expanding $\mathbf1_{(v,R)=1}$ then uses $r\mid R$. De Faveri's Lemma 3.1 applies to the nontrivial primitive $\xi$ at scale $A_{\ell,r}=U_j/(q_\ell^6q_r)$. In its dual sum, restrict only this specified subterm to ideals $e^6$, where $\overline\xi(e^6)=\mathbf1_{(e,\mathfrak f)=1}$.

For $F=\mathbb Q(\sqrt{-3})$, the source's Mellin factor is

$$
H_W(z)=\widehat W(1-z)\frac{\Gamma(z)}{\Gamma(1-z)}
\left(\frac3{(2\pi)^2}\right)^{z-1/2}.
$$

On $1/6<\Re z<1$, the resulting pair contribution is exactly

$$
\frac{\epsilon(\xi)}{2\pi i}\int
H_W(z)U_j^{1-z}q_{\mathfrak f}^{z-1/2}\zeta_F(6z)
\prod_{\mathfrak p\mid\mathfrak f}(1-q_{\mathfrak p}^{-6z})
\prod_{\mathfrak p\mid R}(1-\xi(\mathfrak p)q_{\mathfrak p}^{z-1})
M_{P,L_j}(6-6z)\,dz.
$$

The root number and conductor are those of the actual primitive ratio, including its ramified part. The dual-power series converges absolutely on this initial line and the $\ell$-sum is finite. Shifting to $0<\Re z<1/6$ extracts the $\zeta_F(6z)$ pole. Thus this specified pure-dual-sixth-power contribution is

$$
\mathcal P_{6,j}=C_WU_j^{5/6}\mathcal C_{6,L_j}[c_j]
+\mathcal I_{6,j},\qquad
C_W=\frac{\operatorname{Res}_{s=1}\zeta_F(s)}6H_W(1/6)>0,
$$

where $\mathcal I_{6,j}$ is the remaining shifted integral and

$$
\mathcal C_{6,L_j}[c_j]=
\sum_{\substack{r_2(h)\ne r_2(k)\\r_3(h)\ne r_3(k)}}
c_j(h)\overline{c_j(k)}\epsilon(\xi_{h,k})
q_{\mathfrak f_{h,k}}^{-1/3}\vartheta(\mathfrak f_{h,k})
\prod_{\mathfrak p\mid R_{h,k}}
(1-\xi_{h,k}(\mathfrak p)q_{\mathfrak p}^{-5/6})
M_{P_{h,k},L_j}(5).
$$

This is a substitution and residue calculation from the existing Poisson formula. It identifies a subterm, not the full contraction $\widetilde E_{6,j}$, a nonnegative resonance, or a certified spectral projection. A sufficient bound for its pole contribution is $\Re\mathcal C_{6,L_j}[c_j]\ll_\varepsilon(U_jK)^\varepsilon U_j^{1/6}K$; the shifted integral and all other dual ideals require a joint upper bound at scale $U_jK$. The classwise applications below control this specified pure-power subterm, including its shifted integral, under an additional length condition, after partitioning the complete positive moment. They do not estimate this earlier cross-class signed contraction or the other dual ideals.

For comparison, absolute values and divisor bounds give only $|\mathcal C_{6,L_j}[c_j]|\ll_\varepsilon K^{4/3+\varepsilon}$. Write $h=gx,k=gy$ with $(x,y)=1$. The good conductor weight is at most $w(x)w(y)$, where $w(x)=\prod_{6\nmid v_{\mathfrak p}(x)}q_{\mathfrak p}^{-1/3}$. Its Dirichlet series converges for $\Re s>2/3$, so $\sum_{q_x\le X}w(x)\ll_\varepsilon X^{2/3+\varepsilon}$. Summing the two cofactors and then $g$ gives $K^{4/3+\varepsilon}$; the finite local products and divisor-bounded coefficients cost only $K^\varepsilon$. At $K\asymp U_j$, the desired pole-contraction scale is instead $K^{7/6+\varepsilon}$, leaving a $K^{1/6}$ saving to obtain. The row Möbius factor $M_{P,L_j}(5)$ is distinct from the original column coefficient $\mu(d)$; it does not establish cancellation of that coefficient contraction.

#### Paying a large higher-multiplicity tail of the pole contraction

The conductor weight also gives an absolute bound for a specified part of the actual pole contraction. This application uses the same $w(x)$ as above, de Faveri's higher-multiplicity decomposition (3.3), and the standard positive Dirichlet-series Rankin bound. It does not estimate the shifted integral or assert cancellation of root numbers.

For a good integral cofactor $x\in I(S)$, write $x=z^6a$ with $a$ sixth-power-free, and define

$$
B(x)=q_{a/\operatorname{rad}(a)}.
$$

Thus $B(x)=1$ for a squarefree sixth-free part; it measures only the excess exponents after the common gcd and sixth powers have been removed. For $1\le Y\le K$, let $\mathcal C_{6,L}^{>Y}[c_j]$ retain exactly the actual-order-six pairs $h=gx,k=gy$, $(x,y)=1$, satisfying $\max(B(x),B(y))>Y$. This is a partition of the original coefficient contraction, with all phases, physical labels, and local masks retained.

For $0<e<2/3$, put $s=2/3+e$ and $d=2/3-e$. The positive weighted Dirichlet series has Euler factors

$$
\sum_{x\in I(S)}\frac{w(x)B(x)^d}{q_x^s}
=\prod_{\mathfrak p\notin S}
\frac{1+\sum_{r=1}^{5}q_{\mathfrak p}^{-1/3-rs+(r-1)d}}
     {1-q_{\mathfrak p}^{-6s}}.
$$

For $r=1,\ldots,5$, the exponent $1/3+rs-(r-1)d$ is $1+(2r-1)e>1$, while $6s>1$. The product therefore converges. Rankin's positive majorization gives

$$
\sum_{\substack{q_x\le X\\B(x)>Y}}w(x)
\ll_e X^{2/3+e}Y^{-2/3+e},
\qquad
\sum_{q_x\le X}w(x)\ll_e X^{2/3+e}.
$$

Before absorbing the local coefficient bounds, the two possible large-$B$ cofactors and the sum over all common gcds give $K^{4/3+2e}Y^{-2/3+e}$. The remaining local factors cost a further $K^{e'}$, for any fixed $e'>0$. Choosing $e,e'$ small enough for a prescribed $\varepsilon$ gives

$$
\left|\mathcal C_{6,L}^{>Y}[c_j]\right|
\ll_\varepsilon K^{4/3+\varepsilon}Y^{-2/3+\varepsilon}.
$$

Indeed, at fixed $g\in I(S)$ both cofactors have norm at most $K/q_g$, and $\sum_{g\in I(S)}q_g^{-4/3-2e}$ converges. The original divisor-bounded $c_j$, conductor factor, $\vartheta(\mathfrak f)$, and finite local products satisfy the same absolute bounds used above; $|M_{P,L}(5)|\le\zeta_F(5)$ uniformly in $L,P$. Dropping coprimality and the actual-order selector occurs only in this positive absolute majorant, without replacing the signed summand. Sixth powers and all common gcds are included by the Euler factors and the outer sum.

For $1\le U_j\le K^2$, take

$$
Y=(K^2/U_j)^{1/4}.
$$

Then $1\le Y\le K^{1/2}$. Since $K^{4/3}Y^{-2/3}=U_j^{1/6}K$, the raw error $K^{2e+e'}Y^e$ is absorbed by choosing $e,e'$ small enough. This tail is consequently $\ll_\varepsilon(U_jK)^\varepsilon U_j^{1/6}K$, which pays its pole contribution at scale $U_jK$. At $U_j\asymp K$, the cutoff is $Y\asymp K^{1/4}$. If $U_j\ge K^2$, the already stated full absolute pole bound $K^{4/3+\varepsilon}$ suffices at that pole scale. These statements cover the specified pole subterm, not the other dual terms.

The complementary pole head retains both $B(h/g),B(k/g)\le Y$ and all original coefficients, including the squarefree sector. Large original multiplicity alone does not force a pair into the tail: common powers cancel in $h/g,k/g$, and sixth powers do not enter $B$. This tail estimate alone does not control the head. The classwise convolution application below covers it under a specified length condition; the full signed goal still requires the other dual terms and coverage of the actual detector lengths. This is an application of the supplied conductor weight and a standard Rankin estimate; no new general tail theorem or complete analytic Lean certification is claimed.

The actual-order restriction matters. For a ratio of order $o\in\{2,3\}$, all pure dual $o$-th powers have character value one. The portion of those powers outside the sixth powers has Dirichlet factor

$$
\zeta_F(oz)\prod_{\mathfrak p\mid\mathfrak f}(1-q_{\mathfrak p}^{-oz})
-\zeta_F(6z)\prod_{\mathfrak p\mid\mathfrak f}(1-q_{\mathfrak p}^{-6z}).
$$

Its $z=1/6$ residue cancels the extracted sixth-power residue for that pair. This prevents treating a uniform sixth-power extraction over all nonprincipal pairs as an uncancellable contribution. Restricting to actual order six removes that specific lower-order cancellation; it does not exclude cancellation by other dual terms or solve the remaining estimate. De Faveri's Lemma 3.3 also retains coupled cross phases for nonsquarefree columns under its stated coprimality and finite-class hypotheses. It does not replace the general $\epsilon(\xi_{h,k})$ above by a separable squarefree Gauss vector. This application remains source-conditional and has no complete local Lean certification or signed Robin consequence.

#### A classwise squarefree-column pole consumer with shared gcds

The original convolution permits a further application of the existing cubic sieve. This application retains every common gcd, but first splits the complete positive moment by squarefree status and a fixed ray class. It does not bound an arbitrary divisor-bounded coefficient vector or compare signed contractions under that split.

Use the pinned detector's multiplicative primary class $t(h)=h\bmod36\mathcal O$ in its fixed finite group $\mathcal T$. Write $c_j(h)=\omega_j(h)B_{D,N}(h)$, with the original fixed multiplicative twists and zero masks in $\omega_j$. For $a\in\mathcal T$, let

$$
\widetilde T^{\rm sf}_{j,a}
=\sum_{v\ {\rm good\ sixth\ power\ free}}W(q_v/U_j)
\left|\sum_{\substack{h\ {\rm squarefree}\\t(h)=a}}
c_j(h)\chi_h^{\rm raw}(v)^{\varepsilon_\chi}\right|^2,
$$

and define $\widetilde T^{\rm nsf}_{j,a}$ using the complementary column set. Finite Cauchy gives

$$
\widetilde T_j\le2|\mathcal T|\sum_{a\in\mathcal T}
\left(\widetilde T^{\rm sf}_{j,a}+\widetilde T^{\rm nsf}_{j,a}\right).
$$

Define $\mathcal C^{\rm sf,a}_{6,L}[c_j]$ by the same pure-power pole extraction inside $\widetilde T^{\rm sf}_{j,a}$. Thus both columns are squarefree and have class $a$, and the principal diagonal is excluded. This is a new classwise contraction, not a restriction whose bound is asserted to dominate the earlier signed $\mathcal C_{6,L}$.

Work in positive orientation; conjugate the entire family and coefficient vector for negative orientation. Write $h=gx,k=gy$ with $g,x,y$ squarefree and pairwise coprime. Then $t(x)=t(y)=a/t(g)$, every $x\ne y$ has actual ratio order six, and

$$
\mathfrak f_{h,k}=xy,\qquad R_{h,k}=\operatorname{rad}(gS).
$$

The original manuscript's `eq:sextic-sieve-pair-gauss` and `eq:sextic-sieve-pair-poisson` give

$$
\epsilon(\xi_{h,k})
=\eta_{a/t(g)}\gamma_1(x)\gamma_{-1}(y),
\qquad
\gamma_{-1}(y)=\chi_y(-1)\overline{\gamma_1(y)}.
$$

Both $\eta_{a/t(g)}$ and $\chi_y(-1)$ are constant on the retained class. The latter sign is retained. The normalization agrees with the earlier $H_W$: for the detector's additive character and measure, the radial transform is

$$
\mathscr W(s)=\frac{2\pi}{\sqrt3}\int_0^\infty
W(t)J_0\!\left(\frac{4\pi\sqrt{ts}}{\sqrt3}\right)dt,
\qquad \mathcal M\mathscr W(z)=H_W(z).
$$

Consequently the pair-Gauss factor is the primitive root number in this extraction, with no omitted ramified factor in the equal-class squarefree ratio. This uses the source formulas and their Fourier convention, not an assumed identification of de Faveri's general $\beta_h$ with $\gamma_1(h)$.

Expand the original $R$-product over $r\mid\operatorname{rad}(gS)$ and $M_{P,L}(5)$ over $\ell$ with $(\ell,gS)=1$. Their character factors separate into functions of $x$ and $y$; their other conditions are $(x,\ell)=(y,\ell)=1$. Moreover,

$$
\sum_{r\mid\operatorname{rad}(gS)}q_r^{-5/6}\ll_{S,\varepsilon}q_g^\varepsilon,
\qquad \sum_{q_\ell\le L}q_\ell^{-5}\le\zeta_F(5).
$$

All masks remain in the separated coefficient vectors. Also $\vartheta(xy)=\vartheta(x)\vartheta(y)$ and $q_{xy}^{-1/3}=q_x^{-1/3}q_y^{-1/3}$. Detect $(x,y)=1$ by $\sum_{e\mid x,y}\mu(e)$. After the original pair formula has been used on its coprime nonprincipal locus, this is only a separable algebraic extension to other pairs. No actual conductor or root-number identity is asserted for the added noncoprime pairs.

For each $e$, a separated scalar sum has the coefficients $c_j(gx)\gamma_1(x)\vartheta(x)q_x^{-1/3}$, the fixed $r,\ell$ twists, and the conditions that $x$ is squarefree, $e\mid x$, $(x,g\ell)=1$ and $t(x)=a/t(g)$. Put $X=K/q_g$. In the actual convolution $dn=gx$, distribute the prime factors of $g$ and $e$ between the two factors:

$$
g=g_dg_n,\quad e=e_de_n,\quad
d=g_de_dd',\quad n=g_ne_nn',\quad x=ed'n'.
$$

The unfixed $d',n'$ are squarefree and coprime. Their two lengths are

$$
D'=D/(q_{g_d}q_{e_d}),\qquad
N'=N/(q_{g_n}q_{e_n}),\qquad D'N'=X/q_e.
$$

Gauss CRT leaves the cubic kernel $\kappa_{d'}(n')$ with its zero extension. All interactions with the fixed $g,e,r,\ell$ and physical labels, as well as $\vartheta$ and the norm weights, are functions of one variable and enter its coefficients. The class constraint has a finite character expansion. Thus the existing cubic operator estimate applies with actual fixed coefficient vectors and gives, after squaring and Cauchy over the divisors of $e$,

$$
|H_{g,e}^{g_d,g_n}|^2
\ll_{\mathcal A,\varepsilon}
K^\varepsilon X^{1/3}q_e^{-1}
\left\{\frac D{q_{g_d}}+\frac N{q_{g_n}}
+(X/q_e)^{2/3}\right\}.
$$

Empty ranges contribute zero; a bounded dyadic shell contributes only to the displayed lower-order terms. Summing $e$ uses a logarithmic bound for $\sum_{q_e\ll X}q_e^{-1}$ and convergence of $\sum_e q_e^{-5/3}$. For each distribution of $g$, the result is

$$
\ll_{\mathcal A,\varepsilon}K^\varepsilon
\left\{X+X^{1/3}\left(D/q_{g_d}+N/q_{g_n}\right)\right\}.
$$

Cauchy over the divisors of $g$ costs only $K^\varepsilon$. Summing all $g_d,g_n$ retains their original bounds $q_{g_d}\ll D,q_{g_n}\ll N$. In particular,

$$
DK^{1/3}\sum_{g_d}q_{g_d}^{-4/3}
\sum_{q_{g_n}\ll N}q_{g_n}^{-1/3}
\ll DK^{1/3}N^{2/3}=KD^{1/3},
$$

with the symmetric bound $KN^{1/3}$ for the other term and $K^{1+\varepsilon}$ for the $X$ term. Subtract the artificially included $x=y=1$ principal diagonal separately at cost $K^{1+\varepsilon}$. The resulting consumer is

$$
\boxed{\left|\mathcal C^{\rm sf,a}_{6,L}[c_j]\right|
\ll_{\mathcal A,\varepsilon}
K^{1+\varepsilon}\left(1+D^{1/3}+N^{1/3}\right)
\|W_M\|_\infty^2\|W_S\|_\infty^2.}
$$

The bound is uniform in $L$. At $D\asymp N\asymp K^{1/2}$ it is $K^{7/6+\varepsilon}$, which pays this classwise pole at scale $U_jK$ when $U_j\asymp K$. More generally, $U_j\ge1$ and $\max(D,N)^2\le U_j$ are sufficient. The same original shared-height accounting applies to the profile and transform costs; no extra independent height budget is introduced.

This is an application of the source Gauss/Poisson identities and the known cubic sieve to the actual convolution. The positive-moment partition avoids needing cross-class terms in that majorant; it does not estimate the earlier cross-class signed contraction. The all-column application below includes nonsquarefree and mixed columns. Other dual terms, unrestricted actual witness lengths and full signed Robin restoration remain open. There is no complete analytic Lean certification or new sieve claim.

#### Extending the classwise pole consumer to all convolution columns

The same cubic supplier applies after fixing the repeated-prime cores. Its uniformity in the coefficient vectors is essential: opposite-core-dependent twists are allowed only inside separate fixed-core applications. This is an application of the existing finite Gauss CRT, cubic sieve and positive Rankin estimates. It is not a claim that de Faveri's general root-number phases separate without their cross terms.

Partition the complete positive moment only by $t(h)$, without partitioning squarefree status. For $a\in\mathcal T$, put

$$
\widetilde T^{\rm all}_{j,a}=
\sum_{v\ {\rm good\ sixth\ power\ free}}W(q_v/U_j)
\left|\sum_{t(h)=a}c_j(h)\chi_h^{\rm raw}(v)\right|^2,
\qquad
T_j\le|\mathcal T|\sum_a\widetilde T^{\rm all}_{j,a}.
$$

Let $\mathcal C^{a,\rm all}_{6,L}$ denote the actual-order-six pole extraction within this classwise moment. It contains squarefree, nonsquarefree and mixed columns, every common gcd and every original sixth-power tail. The whole-family conjugation specified above handles negative orientation. No domination of the earlier cross-class signed pole is asserted.

Write $h=gx,k=gy$, $(x,y)=1$, and decompose uniquely

$$
x=cs_0z,\qquad y=c't_0w.
$$

Here $c,c'$ are powerful ideals: each nonzero prime exponent is at least two. Precisely, $c=\prod_{v_{\mathfrak p}(x)\ge2}\mathfrak p^{v_{\mathfrak p}(x)}$ and $s_0z=\prod_{v_{\mathfrak p}(x)=1}\mathfrak p$, so $(c,s_0z)=1$; use the corresponding decomposition for $y$. The part of $s_0z$ supported on $g$ is $s_0$; the corresponding part for $y$ is $t_0$. Thus $s_0,t_0\mid\operatorname{rad}g$, while $z,w$ are squarefree and coprime to $gcc'S$. Retain the original coprimality constraints between the two cofactors, including the cross-core constraints. Fix $g,c,c',s_0,t_0$ and the two bulk classes $t(z),t(w)$.

Set

$$
f_0=\operatorname{rad}(r_6(c))s_0
\operatorname{rad}(r_6(c'))t_0,\qquad
R=\operatorname{rad}(gcc'S)/f_0.
$$

The quotient is between squarefree ideals. Let $\rho$ be the primitive finite residue character on $f_0$ obtained from $\chi_{cs_0}^{\rm raw}\overline{\chi_{c't_0}^{\rm raw}}$ by omitting its inactive local sixth powers. Its normalized finite Gauss sum $\Gamma(\rho)$ has modulus one; use $\Gamma(1)=1$ if $f_0=1$. This is a primitive finite-modulus Gauss sum, not a full-modulus nonsquarefree Gauss sum. Primes omitted from $f_0$ remain in $R$ and retain their original zeros.

On the original coprime nonprincipal locus, the finite CRT calculation underlying the pinned pair-Gauss formula gives exactly

$$
\begin{aligned}
\epsilon(\xi_{h,k})={}&\Gamma(\rho)\gamma_1(z)\gamma_{-1}(w)\,
[\rho(z)\chi_z(f_0)]
[\rho(w)\overline{\chi_w(f_0)}]\\
&\times[\chi_z(w)\overline{\chi_w(z)}],
\qquad \mathfrak f_{h,k}=f_0zw.
\end{aligned}
$$

Equal original classes imply $t(x)=t(y)$. The total raw ratio is therefore unit-trivial and has no additional ramified conductor; the radial Poisson normalization is the one checked above. The last bracket depends only on the fixed bulk classes by reciprocity. The other moving factors are multiplicative single-variable twists. Retain $\gamma_{-1}(w)=\chi_w(-1)\overline{\gamma_1(w)}$. The fixed phase $\Gamma(\rho)$ may couple the two cores, but its modulus is one.

Any nonunit $z$ or $w$ forces actual ratio order six. Handle $z=w=1$ separately in absolute value before extending the actual-order selector. Expand the $R$-product and the finite $\ell$-sum as above; their costs remain $K^\varepsilon\zeta_F(5)$. All cross-core, row-Möbius and original zero masks stay in the separated bulk coefficients. Detect $(z,w)=1$ by $\sum_{e\mid z,w}\mu(e)$ only after using the root formula on its stated locus. The added noncoprime pairs are an algebraic extension, not new conductor identities.

For $m=gcs_0$, distribute the fixed part of an actual factorization $dn=mz$ as

$$
m=ab,\qquad d=ad',\quad n=bn',\quad z=d'n',
\qquad a\text{ squarefree}.
$$

The squarefreeness of $a$ follows from the original $\mu(d)$. The bulk factors are squarefree, mutually coprime and coprime to $m$. For $X=K/q_m$, the earlier cubic calculation, with all fixed twists retained, supplies uniformly

$$
\sum_e|H^{a,b}_{m,e}|^2
\ll_{\mathcal A,\varepsilon}K^\varepsilon
\left\{X+X^{1/3}(D/q_a+N/q_b)\right\}.
$$

For each fixed pair of cores and each $r,\ell$ and ray component, first apply Cauchy in $e$ to the two scalar sums. Then use this coefficient-uniform supplier for each of the resulting norms. Only afterwards take absolute values and sum the core pairs. In particular the argument never replaces different opposite-core-dependent vectors by one common vector or writes their coupled sum as a coherent squared sum.

The conductor weight assigned to one powerful core is

$$
w(c)=\prod_{6\nmid v_{\mathfrak p}(c)}q_{\mathfrak p}^{-1/3}.
$$

Assign $a_g=(a,\operatorname{rad}g)$ and $a_c=a/a_g$. Then

$$
a=a_ga_c,\quad a_c\mid\operatorname{rad}c,\quad(a_c,g)=1,
\quad b_g=g/a_g,\quad b_c=c/a_c,\quad b=b_gb_cs_0.
$$

This assignment remains exact when $g$ and $c$ share primes. Divisor Cauchy costs $K^\varepsilon$. The following positive core moments are sufficient:

$$
\begin{aligned}
F_0&=\sum_{c\ {\rm powerful}}w(c)q_c^{-1/2}\tau(c)<\infty,\\
F_D(V)&=\sum_{\substack{c\ {\rm powerful},\ a_c\mid\operatorname{rad}c\\
b_c=c/a_c,\ q_{b_c}\le V}}
w(c)q_c^{-1/6}q_{a_c}^{-1/2}
\ll_\varepsilon V^{1/6+\varepsilon},\\
F_N&=\sum_{\substack{c\ {\rm powerful}\\a_c\mid\operatorname{rad}c}}
w(c)q_c^{-1/6}q_{b_c}^{-1/2}<\infty.
\end{aligned}
$$

These are ordinary positive Euler-product estimates. For $F_D$, a prime exponent $r\ge2$ and a choice $\delta\in\{0,1\}$ have Rankin weight

$$
w_{\mathfrak p}(r)q_{\mathfrak p}^{-r/6-\delta/2-(r-\delta)s},
\qquad
w_{\mathfrak p}(r)=
\begin{cases}1,&6\mid r,\\q_{\mathfrak p}^{-1/3},&6\nmid r.\end{cases}
$$

Every local exponent exceeds one for $s>1/6$. The smallest exponents for $F_0$ and $F_N$ are respectively $4/3$ and $7/6$. The same argument gives $\sum_{q_c\le V}w(c)\ll_\varepsilon V^{1/3+\varepsilon}$. Consequently the actual $z=w=1$ sector and its algebraically added counterpart cost at most

$$
K^\varepsilon\sum_{q_g\ll K}(K/q_g)^{2/3+\varepsilon}
\ll_\varepsilon K^{1+\varepsilon}.
$$

Apply the three moments to the square roots of the cubic bounds. Dropping negative $s_0$-norm factors and cross-core constraints is used only in these positive upper bounds; the $s_0$ choices cost $q_g^\varepsilon$. The first term sums to $K^{1+\varepsilon}$. For the $D$ term, $q_b\ll N$ imposes $q_{b_c}\ll N/q_{b_g}$, so $F_D$ gives

$$
K^{1/3}DN^{1/3}
\sum_{q_{a_g}\ll D}q_{a_g}^{-4/3}
\sum_{q_{b_g}\ll N}q_{b_g}^{-2/3}
\ll KD^{1/3}.
$$

The $N$ term uses $F_N$ and is

$$
K^{1/3}N
\sum_{q_{a_g}\ll D}q_{a_g}^{-1/3}
\sum_{b_g}q_{b_g}^{-4/3}
\ll KN^{1/3}.
$$

Thus the complete classwise all-column pole extraction satisfies

$$
\boxed{|\mathcal C^{a,\rm all}_{6,L}[c_j]|
\ll_{\mathcal A,\varepsilon}
K^{1+\varepsilon}(1+D^{1/3}+N^{1/3})
\|W_M\|_\infty^2\|W_S\|_\infty^2.}
$$

This is uniform in $L$ and includes mixed column statuses. The condition $U_j\ge1$, $\max(D,N)^2\le U_j$ pays this pole at scale $U_jK$, including $D\asymp N\asymp K^{1/2}$, $U_j\asymp K$. It is not promised by the original witness theorem. The next application treats the same pure-power subterm's shifted integral. Other dual ideals, unrestricted actual witness lengths and signed Robin restoration remain separate obligations. This source-conditional application has no complete analytical Lean certification and makes no originality claim for its suppliers.

#### Paying the shifted integral of the same pure-power subterm

Keep the all-column classwise moment and its actual coefficients. Define the finite kernel $\mathcal C^{a,\rm all}_{6,L}(z)$ by summing over its actual-order-six pairs the coefficient $c_j(h)\overline{c_j(k)}$ times

$$
\epsilon(\xi_{h,k})q_{\mathfrak f}^{z-1/2}
\prod_{\mathfrak p\mid\mathfrak f}(1-q_{\mathfrak p}^{-6z})
\prod_{\mathfrak p\mid R}(1-\xi_{h,k}(\mathfrak p)q_{\mathfrak p}^{z-1})
M_{P,L}(6-6z).
$$

At $z=1/6$ this is exactly $\mathcal C^{a,\rm all}_{6,L}[c_j]$. Fix $0<\sigma<1/6$ and, in this subsection, write $\tau=1/2-\sigma\in(1/3,1/2)$. The same fixed-core proof supplies the bound, uniformly for $t\in\mathbb R$,

$$
\boxed{|\mathcal C^{a,\rm all}_{6,L}(\sigma+it)|
\ll_{\mathcal A,\sigma,\varepsilon}
K^{1+\varepsilon}(1+D^{2\sigma}+N^{2\sigma})
\|W_M\|_\infty^2\|W_S\|_\infty^2.}
$$

Here are the changes needed from the pole application. The norm phases $q_{\mathfrak f}^{it}$ separate into the two bulk coefficient vectors at fixed cores. The conductor Euler factors are multiplicative and have modulus at most $2^{\omega(\mathfrak f)}\ll_\varepsilon K^\varepsilon$, uniformly in $t$. The $R$ expansion costs $\sum_{r\mid R}q_r^{\sigma-1}\ll_\varepsilon K^\varepsilon$ and the row-Möbius expansion costs at most $\zeta_F(6-6\sigma)$. These factors and all masks remain in the coefficient vectors before applying the cubic supplier.

The conductor core weight becomes

$$
w_\tau(c)=\prod_{6\nmid v_{\mathfrak p}(c)}q_{\mathfrak p}^{-\tau}.
$$

For $m=gcs_0$, $X=K/q_m$, the squared scalar input is now

$$
\sum_e|H_{m,e}^{a,b}(\sigma+it)|^2
\ll_{\mathcal A,\sigma,\varepsilon}K^\varepsilon
\left\{X^{2\sigma+2/3}
+X^{2\sigma}(D/q_a+N/q_b)\right\}.
$$

In particular its first term is $X^{2\sigma+2/3}$, reducing to $X$ only at the pole. The three core moments are

$$
\begin{aligned}
F_{0,\sigma}&=\sum_{c\ {\rm powerful}}
w_\tau(c)q_c^{-\sigma-1/3}\tau(c)<\infty,\\
F_{D,\sigma}(V)&=\sum_{\substack{c\ {\rm powerful},\ a_c\mid\operatorname{rad}c\\
b_c=c/a_c,\ q_{b_c}\le V}}
w_\tau(c)q_c^{-\sigma}q_{a_c}^{-1/2}
\ll_{\sigma,\varepsilon}V^{\tau/2+\varepsilon},\\
F_{N,\sigma}&=\sum_{\substack{c\ {\rm powerful}\\a_c\mid\operatorname{rad}c}}
w_\tau(c)q_c^{-\sigma}q_{b_c}^{-1/2}<\infty.
\end{aligned}
$$

For the first and third moments the minimum local prime exponents are $7/6+\sigma$ and $1+\sigma$. For the second, the Rankin parameter $s>\tau/2$ gives local exponent $\tau+r\sigma+\delta/2+(r-\delta)s>1$ when $6\nmid r$, $r\ge2$, $\delta\in\{0,1\}$; when $6\mid r$, omit $\tau$ and use $r\ge6$. Thus these are the same positive Euler-product applications with their changed exponents. Likewise $\sum_{q_c\le V}w_\tau(c)\ll_{\sigma,\varepsilon}V^{(1-\tau)/2+\varepsilon}$ controls the both-bulks-unit sectors.

After fixed-pair Cauchy and the uniform sieve, sum cores and then gcds in the same order as above. Since $2\sigma+2/3<1$, the first contribution is $\ll K^\varepsilon\sum_{q_g\ll K}(K/q_g)^{2\sigma+2/3}\ll K^{1+\varepsilon}$. The other two are bounded by

$$
\begin{aligned}
K^{2\sigma}DN^\tau
\sum_{q_{a_g}\ll D}q_{a_g}^{-(1+2\sigma)}
\sum_{q_{b_g}\ll N}q_{b_g}^{-(1-\tau)}
&\ll K^{2\sigma}DN^{2\tau}=KD^{2\sigma},\\
K^{2\sigma}N
\sum_{q_{a_g}\ll D}q_{a_g}^{-2\sigma}
\sum_{b_g}q_{b_g}^{-(1+2\sigma)}
&\ll K^{2\sigma}ND^{2\tau}=KN^{2\sigma}.
\end{aligned}
$$

This proves the displayed source-conditional finite-kernel estimate without assuming any simultaneous realization of the opposite-core-dependent coefficient vectors.

The shifted integral for this classwise extraction is

$$
\mathcal I^{a,\rm all}_{6,j}
=\frac1{2\pi i}\int_{\Re z=\sigma}
H_W(z)\zeta_F(6z)U_j^{1-z}
\mathcal C^{a,\rm all}_{6,L_j}(z)\,dz.
$$

On this fixed line, $H_W(z)\zeta_F(6z)$ is absolutely integrable: the smooth annular Mellin transform decays faster than any power, whereas the Gamma quotient and zeta factor have polynomial vertical growth. A fixed finite seminorm of $W$ therefore gives

$$
|\mathcal I^{a,\rm all}_{6,j}|
\ll_{\mathcal A,\sigma,\varepsilon}
U_j^{1-\sigma}K^{1+\varepsilon}
(1+D^{2\sigma}+N^{2\sigma})
\|W_M\|_\infty^2\|W_S\|_\infty^2.
$$

At $\sigma=1/12$, this is $U_j^{11/12}K^{1+\varepsilon}(1+D^{1/6}+N^{1/6})$. If $U_j\ge1$ and $\max(D,N)^2\le U_j$, then $1,D^{2\sigma},N^{2\sigma}\le U_j^\sigma$. Thus both this integral and the pole are $\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon U_jK$. This pays the complete specified pure-dual-sixth-power subterm of the classwise all-column moment, with the original shared-height accounting and fixed transform seminorms. It does not pay the other dual ideals, guarantee the required length condition for the actual witnesses, bound the earlier cross-class signed contraction, or restore the original signed Robin target. The application remains source-conditional and has no complete analytical Lean certification.

#### An absolute shifted-integral estimate without relative length restrictions

The unrestricted shifted integral has a simpler sufficient bound from the absolute conductor-weight Rankin argument already used above. No cubic cancellation or actual convolution structure is needed for this part. Let $\mathcal C_{6,L}(z)$ be the same finite $z$-kernel as in the preceding subsection, summed over the original actual-order-six pairs without a primary-class condition. Retain the full primitive conductor, original zeros, physical labels and finite row-Möbius cutoff.

Fix $0<\sigma<1/6$ and put $\tau=1/2-\sigma$. For an arbitrary good ideal $x$, define

$$
w_\tau(x)=\prod_{6\nmid v_{\mathfrak p}(x)}q_{\mathfrak p}^{-\tau}.
$$

Its Dirichlet series has local factor

$$
\frac{1+q_{\mathfrak p}^{-\tau}
\sum_{r=1}^{5}q_{\mathfrak p}^{-rs}}
{1-q_{\mathfrak p}^{-6s}},
$$

and converges for $s>1-\tau=1/2+\sigma$. Thus $\sum_{q_x\le X}w_\tau(x)\ll_{\sigma,\varepsilon}X^{1/2+\sigma+\varepsilon}$. In the exact gcd decomposition $h=gx,k=gy$, $(x,y)=1$, the full conductor weight satisfies $q_{\mathfrak f}^{-\tau}\le w_\tau(x)w_\tau(y)$; any ramified part only decreases this absolute upper bound. The other finite local products and the $\ell$-sum have the same $K^\varepsilon$ absolute cost as before. After taking absolute values, enlarge the coprimality and actual-order selectors only in this positive upper bound. Allocating the small error parameters gives, uniformly in $t,L$,

$$
\begin{aligned}
|\mathcal C_{6,L}(\sigma+it)|
&\ll_{\mathcal A,\sigma,\varepsilon}
K^{\varepsilon/2}\sum_{q_g\ll K}(K/q_g)^{1+2\sigma+\varepsilon/2}\\
&\ll_{\mathcal A,\sigma,\varepsilon}K^{1+2\sigma+\varepsilon}.
\end{aligned}
$$

This holds for divisor-bounded coefficients supported on $q_h\asymp K$, including the actual convolution; fixed profile factors are absorbed in $\mathcal A$. It also applies to the classwise kernels. The coefficient-sensitive bound above remains stronger at a fixed line in its useful length ranges, but is not needed for the following shifted-integral payment.

For a final $\varepsilon>0$, choose the fixed line $\sigma=\min(1/12,\varepsilon/8)$ and use $\varepsilon_0=\varepsilon/4$ in this absolute bound. The already checked Mellin integrability yields

$$
\boxed{|\mathcal I_{6,j}|
\ll_{\mathcal A,\varepsilon}
U_j^{1-\sigma}K^{1+2\sigma+\varepsilon_0}
\ll_{\mathcal A,\varepsilon}(U_jK)^\varepsilon U_jK
\qquad(U_j,K\ge1).}
$$

The line depends only on the final $\varepsilon$, not on the growing scales. The constants may deteriorate as $\sigma\to0$; no uniformity as $\varepsilon\to0$ is asserted. The original fixed profiles and shared-height budget are retained. This pays the specified pure-power shifted integral even before classwise splitting, at every original length with $U_j,K\ge1$. The original cross-class pole, the classwise pole outside its sufficient length range, the other dual ideals and signed Robin restoration remain unproved here. This is a direct application of the existing absolute Rankin method, without complete analytical Lean certification or an originality claim.

#### Why the remaining pole estimate must use the actual convolution

The proposed $U_j^{1/6}K$ pole scale cannot hold uniformly for arbitrary bounded coefficient vectors. The source pair-Gauss formula supplies an obstruction that retains nonsquarefree columns, a shared prime and every natural mask. This concerns the isolated pole contraction; it is not a counterexample to the original mixed moment or Robin inequality.

Fix a good prime ideal $\mathfrak t$, put $a_0=\mathfrak t^2$, $Q=K/q_{a_0}$ and $P_0=\operatorname{rad}(a_0S)$. Use good primes $p$ in the identity primary class modulo $36\mathcal O$ with $Q/2<q_p\le Q$. Their number is $\gg Q/\log Q$. For this input reuse Wataru Kai, [*Notes on Mitsui's Prime Number Theorem with Siegel zeros*, arXiv:2209.11816v3, Theorem 3.1.1](https://arxiv.org/html/2209.11816v3#S3.SS1.SSS1): take a fixed positive-area convex rectangle inside the norm annulus and scale it by $\sqrt Q$, with fixed modulus $36\mathcal O$ and identity residue. The fixed-modulus exceptional-zero integral is $O(Q^\beta)=o(Q)$ with $\beta<1$. Passing from prime elements to primary prime ideals loses at most the six units.

Partition these primes by the finite tuple of values $\chi_p(r)$ for primes $r\mid P_0$ and by the original physical row-label values. One cell $\mathscr P$ still has $M=|\mathscr P|\gg Q/\log Q$. For distinct $p,q\in\mathscr P$, take $h=a_0p,k=a_0q$. The common $a_0$ cancels in the primitive ratio, while its original zeros remain. The exact data are

$$
\mathfrak f_{h,k}=pq,\quad R_{h,k}=P_0,\quad
\xi_{h,k}(r)=1\ (r\mid P_0),\quad
\epsilon(\xi_{h,k})=\gamma_1(p)\overline{\gamma_1(q)}.
$$

Indeed the identity class makes the pair reciprocity factor and $\chi_q(-1)$ equal to one. Every distinct supported pair has actual order six. For any $1\le L<Q/2$, the finite cutoff also gives the exact equality $M_{P_0pq,L}(5)=M_{P_0,L}(5)$.

Choose $c(a_0p)=\overline{\gamma_1(p)}$ for $p\in\mathscr P$ and zero elsewhere. Thus $|c(h)|\le1$, all supported columns are nonsquarefree, and all off-diagonal phases in the complete pole summand align. Put

$$
w_p=q_p^{-1/3}(1-q_p^{-1}),\qquad
A_{P_0,L}=M_{P_0,L}(5)\prod_{r\mid P_0}(1-q_r^{-5/6}).
$$

The complete specified contraction is exactly

$$
\mathcal C_{6,L}[c]
=A_{P_0,L}\left\{\left(\sum_{p\in\mathscr P}w_p\right)^2
-\sum_{p\in\mathscr P}w_p^2\right\}.
$$

The truncated Möbius factor is uniformly positive:

$$
M_{P_0,L}(5)\ge2-\zeta_F(5)
\ge2-\zeta(5)^2>7/16,
$$

where $\zeta(5)<1+\int_1^\infty x^{-5}dx=5/4$. Therefore

$$
\mathcal C_{6,L}[c]\gg_{a_0,S}Q^{-2/3}M(M-1)
\gg_{a_0,S}\frac{K^{4/3}}{(\log K)^2}.
$$

The fixed physical labels multiply the chosen vector by one common unit, leaving its contraction unchanged. Negative orientation uses the conjugated family and vector. At $U_j\asymp K$ the prescribed $L=(b_WU_j)^{1/6}$ obeys the cutoff condition for large $K$, and this excludes a uniform arbitrary-vector $K^{7/6+\varepsilon}$ bound for $0<\varepsilon<1/6$. With the original $(U_jK)^\varepsilon$ notation, $U_j=K^\theta$, $0<\theta<2$, contradicts that bound whenever

$$
0<\varepsilon<\frac{2-\theta}{6(1+\theta)}.
$$

These vectors are not the actual annular convolution. In every factorization $dn=a_0p$, one factor contains $p$ and the other divides fixed $a_0$. When both actual annular lengths $D,N$ tend to infinity, $B_{D,N}(a_0p)$ is consequently zero for every such prime, once both lower support endpoints exceed $q_{a_0}$. If one length stays bounded, its coefficients are still prescribed by the Möbius and profile factors; the aligned vector above has not been realized by that convolution. Thus a remaining pole estimate must use its coefficient structure, or combine the pole with the other dual terms. Divisor bounds alone cannot supply it. This obstruction and the preceding consumer are applications of the cited sources, without complete analytic Lean certification or an originality claim.

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

where $\psi$ is the cubic Gauss series defined in their (6.1)–(6.2), not an arbitrary coefficient polynomial. It allows nonsquarefree and ramified shifts, so $h=-3$ itself is admissible. It does not by its stated conclusion supply the extra angular/ray-weighted series in $T_{n,\xi}$. Their Lemma 6.1 already provides removal of specified coprimality filters; those identities should be reused where their hypotheses match. The fixed-ray pointwise angular interface below uses a separate finite theta transform; it does not assert this mean-square theorem for the weighted series. Lemma 6.7 supplies a truncation formula for its stated untwisted data and includes a possible $4/3$ pole. Its residue cannot be declared zero for the original weighted pairing without a corresponding argument.

The original convolution also contains nonsquarefree $n$, common prime factors of $d,n$, sixth powers, and columns whose valuations lie in $2,\ldots,5$. The original $\gamma_j(c)$ is defined only for squarefree $c$. Those other character columns cannot be discarded because a different full-modulus Gauss sum vanishes on them; permitting nonsquarefree shifts in Lemma 6.6 does not supply their conversion formulas. Negative orientation still requires conjugating the entire original product with its coefficients and ray factors. The full coefficient-sensitive off-block contraction, coverage of the actual witness lengths, and signed Robin restoration remain open. All estimates in this subsection are conditional on the cited analytical suppliers and have no complete local Lean certification.

### A full fixed-ray angular supplier from the finite theta transform

[Alexander Dunn, *Metaplectic cusp forms and the large sieve*, arXiv:2403.13151v2](https://arxiv.org/html/2403.13151v2#S8.SS4), supplies the finite transformation in (8.30), (8.37), and (8.44)–(8.48). Its stated Propositions 8.12 and 8.15 assume a cusp form with spectral parameter in $1+i\mathbb R$. The residual cubic theta function has parameter $4/3$. The application below reuses the transformation proof and separately verifies the theta constant terms, coefficient support, and Mellin decay; it is not a direct application of the stated cusp-form theorem. The theta input is [Dunn–Radziwiłł, arXiv:2109.07463v3](https://arxiv.org/html/2109.07463v3#S5), (5.7), (5.13)–(5.16), and Appendix A. Only their unconditional theta formulas are used.

Take one multiplicative character in the fixed ray-filter expansion. All constants may depend on its complete original presentation and on $S$; no uniformity in a growing ray modulus is asserted. Write $\kappa_n(d)=(d/n)_3$. Primary cubic reciprocity and the Gauss shift identity, on the original coprime locus, give

$$
\overline{\widetilde g_3(-3n,d)}
=\kappa_d(-3)\kappa_n(d)\overline{\widetilde g_3(1,d)}.
$$

Put $\eta(d)=\xi(d)\kappa_d(-3)$, retaining all fixed supplementary factors, and zero-extend it on the originally excluded classes. With $p_n(d)=\eta(d)\kappa_n(d)\mathbf1_{(d,nS)=1}$, define

$$
\begin{aligned}
R_n(s,\ell)&=\sum_{d\equiv1\ (3)}
p_n(d)\overline{\widetilde g_3(1,d)}\alpha(d)^\ell q_d^{-s},\\
Z_n(w,\ell)&=\prod_{\substack{\mathfrak p\notin S\\\mathfrak p\nmid n}}
\left(1-\eta(\pi)^3\alpha(\pi)^{3\ell}q_{\mathfrak p}^{-w}\right)^{-1},\\
\mathcal C_n(s,\ell)&=Z_n(3s-\tfrac12,\ell)R_n(s,\ell).
\end{aligned}
$$

Here $\pi$ is the primary generator, $\Re s>1$ initially, and $\ell=1$ for the actual inner sum. A finite ray function is handled by summing its original character expansion with its fixed coefficients. Every deleted Euler factor remains deleted even when an inducing primitive character has smaller conductor. The full conjugate column follows by conjugating the entire displayed Gauss/theta coefficient family, its multiplier, finite weights, and profile, with angular mode $\ell=-1$; changing only $\ell$ inside the fixed $\overline{\widetilde g_3}$ family would not give that conjugate.

The theta formula at the primary-supported indices is

$$
\tau(\lambda^{-3}ch^3)
=3^{5/2}\overline{\widetilde g_3(1,c)}|h|,
\qquad c,h\equiv1\ (3),\quad c\text{ squarefree}.
$$

There is no extra condition $(c,h)=1$. Since $p_n(h)^3=\eta(h)^3\mathbf1_{(h,nS)=1}$ and $\alpha(\lambda^{-3})=i$, the corresponding weighted theta Dirichlet series satisfies

$$
\mathcal D_n(s,\ell)=3^{5/2+3s}i^\ell\mathcal C_n(s,\ell).
$$

This identifies the cube completion with the actual coefficients rather than with a replacement zero set.

#### Full ramified and imprimitive finite weights

Choose a fixed complete modulus $\lambda^a f_0$, with $(f_0,3)=1$ and $a\ge4$, that contains the primary filter, $\eta$, and every fixed exclusion. Let $m=a+2$ and $L=\lambda^{2m+4}$. If $\eta_\lambda$ is the desired local function modulo $\lambda^a$, including its zeros, set

$$
H(x)=\begin{cases}\eta_\lambda(x/\lambda),&x\in\lambda\mathcal O,\\0,&x\notin\lambda\mathcal O.\end{cases}
$$

Its period is $\lambda^{m-1}$. On Dunn's finite dual group choose the exact inverse Fourier transform $\psi'$ with $\widehat{\psi'}=H$. Then

$$
\widehat{\psi'}(\lambda^4\mu)=\eta_\lambda(\lambda^3\mu).
$$

No local character value at $\lambda$ is inverted. On a modulus prime to $\lambda$, write $v_0=\lambda^{3-(2m+4)}$; the original argument $\lambda^3\mu$ is $v_0(L\mu)$ there. All unit rescalings are retained.

For the fixed prime-to-$3$ part, expand the function $B(x)=\eta_0(v_0x)$ in the trace-character convention:

$$
B(x)=q_{f_0}^{-1}\sum_{u\bmod f_0}A(u)\check e(ux/f_0).
$$

Group by $h=(u,f_0)$, put $b=f_0/h$, and write $u=hu'$. The branch inverse weight, supported on units modulo $b$, is exactly

$$
P_b(u')=\frac{q_b}{q_{f_0}}A((f_0/b)u'),\qquad (u',b)=1.
$$

The modulus-one branch includes the zero frequency. Summing these branches recovers $B$, including nonunit Fourier frequencies. For good squarefree $n$, let $g_n=\sum_{x\bmod n}\kappa_n(x)\check e(x/n)$, so $|g_n|=q_n^{1/2}$. The normalized inverse weight of $\kappa_n(x)$ is $g_n\overline{\kappa_n(d)}$. For $r=bn$, with $\bar n$ the inverse of $n$ modulo $b$ and $\bar b$ the inverse of $b$ modulo $n$, the complete CRT inverse weight for $B_b(x)\kappa_n(v_0x)$ is

$$
P_{b,n}(d)=P_b(\bar n d_b)\,
\kappa_n(v_0)g_n\overline{\kappa_n(\bar b d_n)}.
$$

This fixes both the normalization and the CRT phases. Applying Dunn's exact finite kernel gives

$$
\mathcal K_{r,L}P(u)
=\frac1{q_r}\sum_{L^2ad\equiv1\ (r)}
P(-d)\left(\frac{Ld}{r}\right)_3\check e(au/r).
$$

In the $n$-part the inverse cubic character cancels the kernel's cubic character. More explicitly,

$$
\mathcal K_{bn,L}P_{b,n}(u)
=\frac{\kappa_n(v_0bL)g_n}{q_n}c_n(u)\,
\frac1{q_b}\sum_{L^2a_bd_b=1\ (b)}
P_b(-\bar n d_b)\left(\frac{Ld_b}{b}\right)_3
\check e(a_bu\bar n/b).
$$

Here $c_n$ is the Ramanujan sum in the same additive-character convention. Multiplication of its argument by $\bar b$ does not change it. The fixed $b$ sum is bounded in terms of the original ray data, hence

$$
|\mathcal K_{bn,L}P_{b,n}(u)|
\ll_{\xi,S}q_n^{-1/2}|c_n(u)|.
$$

Dunn (8.44)–(8.46) makes the transformed cusp index and external unit root depend only on $m,j,r\bmod L$, not on the Fourier numerator $d$. This independence is essential: the finite sum remains a Ramanujan kernel after transformation. Taking absolute values of all original Fourier coefficients would lose this saving.

#### Residual theta and nonzero angular Mellin transforms

The fixed $\lambda$ twist is a finite combination of $\theta(T_tw)$ with $t\in\lambda^{4-m}\mathcal O$. For $\gamma\in\Gamma_1(L)$, $T_t\gamma T_t^{-1}\in\Gamma_1(9)$ and has the same multiplier $\chi(\gamma)$: its lower-left entry is unchanged, its upper-left entry changes by $t$ times that entry, and the cubic supplementary law retains the same ramified residue. Thus Dunn's translation and matrix calculation applies with the actual theta constants included.

The reflected coordinates are

$$
z'=-\frac{\bar z}{r^2(|z|^2+v^2)},\qquad
v'=\frac{v}{q_r(|z|^2+v^2)}.
$$

For $k\ge1$, the pure Wirtinger chain rule at $z=0$ is

$$
\left.\partial_z^kF(z',v')\right|_0
=\frac{(-1)^k}{\bar r^{2k}v^{2k}}
(\partial_{\bar z'}^kF)(0,1/(q_rv)).
$$

In particular, every cusp constant depending only on $v'$ has zero pure angular derivative there. The negative angular mode exchanges $z$ and $\bar z$. This pays the exponential Mellin decay at both ends for $\ell\ne0$; it does not assert that a horizontal derivative of theta is itself a scalar cusp form.

With

$$
B_\ell(s)=\tfrac14(2\pi)^{-2s-|\ell|}
\Gamma(s+|\ell|/2-1/6)\Gamma(s+|\ell|/2+1/6),
\qquad \Lambda=B_\ell\mathcal D,
$$

the finite branch functional equation is

$$
\Lambda_j(s;\widehat P,\ell)
=(-1)^\ell\Omega_{m,j}(r)q_r^{1-2s}
\left(\frac{\bar r}{r}\right)^{-\ell}
\Lambda_{j'}(1-s;\mathcal K_{r,L}P,-\ell).
$$

The nonzero angular completed numerator $\mathcal C_n$ is entire. The raw series $R_n=\mathcal C_n/Z_n$ is holomorphic for $\Re s>1/2$, where the inverse Euler product converges absolutely; the same quotient gives only meromorphic continuation in general. No absence of poles at zeros of $Z_n$ is asserted. The radial mode $\ell=0$ requires its actual weighted cusp constants to vanish separately.

Every fixed higher-level theta component reduces, by an integral matrix and an upper-triangular matrix in $\mathrm{SL}_2(\mathcal O[1/\lambda])$, to finitely many fixed $\lambda$/unit scalings and translations of the original 27 cusp expansions. At good primes their nonzero support has the form $ch^3$, with $c$ squarefree, and coefficient size $\ll |h|$. The $\lambda$ tails in (5.7) have coefficient growth $3^{k/2}$ and norm growth $3^{3k}$, giving a convergent geometric series at $\Re s=1+\delta$. This keeps the fixed ramified tails rather than claiming only good-index support.

For $\delta>0$, the good-prime absolute factor is

$$
L_q=\frac{1+q^{-1-\delta}}{1-q^{-5/2-3\delta}}.
$$

At $\mathfrak p\mid n$, inserting $N((n,\nu))$ changes it to $1+q(L_q-1)$. Since $n$ is squarefree and $|c_n(u)|\le N((n,u))$, the extra product costs $q_n^{\varepsilon'}$, for each fixed $\delta,\varepsilon'>0$. Fixed denominators are units modulo $n$. Thus the dual absolute series at $1+\delta$ is $\ll_{\xi,S,\delta,\varepsilon'}q_n^{\varepsilon'}$. Together with the kernel's $q_n^{-1/2}$, the functional equation and Stirling's formula give

$$
\mathcal C_n(-\delta+it,\pm1)
\ll q_n^{1/2+2\delta+\varepsilon'}(1+|t|)^{2+4\delta}.
$$

The right boundary $1+\delta$ is uniformly absolutely convergent. Phragmén–Lindelöf between these boundaries, using the entire Mellin numerator's finite exponential growth, yields

$$
\mathcal C_n(\tfrac12+\delta+it,\pm1)
\ll q_n^{1/4+(\delta+\varepsilon')/(2+4\delta)}(1+|t|).
$$

On this line $\Re(3s-1/2)=1+3\delta$, so $|Z_n^{-1}|\le\zeta_F(1+3\delta)$. Mellin inversion therefore supplies the actual restricted inner sum:

$$
|T_{n,\xi}(D)|
\ll_{\xi,S,\delta,\varepsilon'}
D^{1/2+\delta}q_n^{1/4+(\delta+\varepsilon')/(2+4\delta)}
\mathcal N_\delta(W_M),
\qquad
\mathcal N_\delta(W)=\int_{\mathbb R}
|\widehat W(\tfrac12+\delta+it)|(1+|t|)\,dt.
$$

For any prescribed $\varepsilon>0$, choose $\delta,\varepsilon'$ small enough to write this as $(Dq_n)^\varepsilon D^{1/2}q_n^{1/4}\mathcal N_\delta(W_M)$. For $W_t(x)=x^{it}W(x)$, $\mathcal N_\delta(W_t)\le(1+|t|)\mathcal N_\delta(W)$. Three logarithmic derivatives control this norm on a fixed compact annulus. The norm-height cost is explicit and uses the original cumulative height allowance. This is a source-conditional analytical application with separately paid theta hypotheses, not a complete local Lean certification, a new general large sieve, or a full sixth-order residual estimate.

### Consumer on the actual restricted pairing

The outer coefficient after the exact additive-character transport remains

$$
b_n=\nu(n)W_S(q_n/N)\gamma_1(n).
$$

On the retained squarefree indices, $|\gamma_1(n)|=1$. Summing the angular supplier with this original coefficient, including its ray-class label, gives

$$
|Q_{\rm sf}(D,N)|
\ll_{\mathcal A,\delta,\varepsilon}
(DN)^\varepsilon D^{1/2}N^{5/4}
\mathcal N_\delta(W_M)\|W_S\|_\infty.
$$

For divisor-bounded outer coefficients, their additional $N^\varepsilon$ cost can be absorbed by choosing the supplier's exponents smaller initially. This is a bound for the original restricted pairing with its actual outer phase; it does not choose a new outer vector, normalize the pairing by a fictitious row count, or supply a mean-square estimate for all mixed columns.

The cubic large sieve and the pointwise angular supplier give

$$
|Q_{\rm sf}(D,N)|\ll (DN)^\varepsilon\|W_S\|_\infty
\min\left\{
(DN)^{1/2}\left(D+N+(DN)^{2/3}\right)^{1/2}\|W_M\|_\infty,
\ D^{1/2}N^{5/4}\mathcal N_\delta(W_M)
\right\}.
$$

For bounded fixed profiles and $D=N^a$, the cubic power of $N$ is $5(a+1)/6$ for $1/2\le a\le2$, $a/2+1$ for $a\le1/2$, and $a+1/2$ for $a\ge2$. The angular power is $a/2+5/4$. It is strictly smaller precisely when $a>5/4$. At balance $D\asymp N$ and $K=DN$, the angular bound is $K^{7/8+\varepsilon}$, which is weaker than the reused cubic bound $K^{5/6+\varepsilon}$. This comparison is for the same restricted pairing and fixed coefficient norms.

The height cost can erase the unbalanced gain. If the common Mellin/norm modulation is $\ll H$, the angular term pays $H$. In $5/4<a\le2$, the power margin is $(4a-5)/12$, so a strict improvement with $H\ll N^h$ requires $h<(4a-5)/12$, with positive room for the $\varepsilon$ losses. For example, at $D=N^{3/2}$ the two exponents are $2$ and $25/12$; the available margin is $1/12$ before the height cost. For $a\ge2$ the margin is $(2a-3)/4$. The actual detector must furnish these lengths and its original cumulative height budget; neither is freely reset in this application.

The estimate is asymmetric. Interchanging $d,n$ in the exact original pairing and converting $\gamma_1(n)$ by the signal identity puts an extra $\mu(n)$ inside the prospective theta sum. That coefficient is not a fixed ray weight. Thus the pointwise angular bound cannot be invoked in the swapped direction without an additional supplier. The cubic operator bound remains available in either direction with the actual coefficient vectors.

This closes a source-conditional fixed-ray angular interface on the coprime squarefree packet and supplies a useful unbalanced consumer. Nonsquarefree indices, shared primes, the actual-order-six full coefficient contraction, and restoration of the original signed Robin expression are separate obligations. In particular it does not prove $[-I_\psi(A)]_+=o(A^{-\eta_R})$ on the actual unbounded $N=C_A$, or replace the signed target by $Q_{\rm sf}$.

### A fixed angular second moment for the same packet

The fixed-ray theta completion also supplies the analytic growth needed to apply the DDDS second-moment argument to the actual angular family. The functional-equation interface uses [Kazhdan–Patterson, *Metaplectic forms*, §§I.6 and II.1](https://www.numdam.org/item/PMIHES_1984__59__35_0.pdf) and the finite Jacquet calculation of [Brubaker–Bump, *On Kubota's Dirichlet Series*, DOI 10.1515/CRELLE.2006.073](https://doi.org/10.1515/CRELLE.2006.073), available in the [public author preprint](https://web.archive.org/web/20210120224343id_/http://sporadic.stanford.edu/bump/kubota.pdf). Their general machinery and the DDDS moment method are reused; the application below matches their characters and coefficients to the original $Q_{\rm sf}$.

Fix the complete original presentation, its excluded primes $S$, and one multiplicative member of its finite ray expansion. For $\ell=\pm1$, put $\chi(c)=\xi(c)\alpha(c)^\ell$ on primary generators. With all original exclusions retained, define initially for $\Re z>3/2$

$$
\begin{aligned}
\Psi_{\chi,a}(r,z)
&=\sum_{\substack{c\equiv1\ (3)\\(c,aS)=1}}
\chi(c)g_3(r,c)q_c^{-z},&
\Psi_\chi&=\Psi_{\chi,1},\\
L_\chi(w)&=L^S(w,\chi^3),&
\mathcal Z_\chi(r,z)&=L_\chi(3z-2)\Psi_\chi(r,z).
\end{aligned}
$$

Here $h$ is fixed and supported at $S$, while $n$ is good, primary and squarefree. The actual consumer has $h=-3$. The full conjugate family is obtained by conjugating its Gauss sums, character, coefficients and spectral variable together.

For every fixed $1<\sigma\le5/4$ and $\varepsilon>0$, the resulting estimate is

$$
\sum_{\substack{n\ {\rm good,\ primary,\ squarefree}\\q_n\le M}}
\left|\Psi_{\chi,n}(hn,\sigma+it)\right|^2
\ll_{\sigma,\varepsilon,\text{fixed presentation}}
M^{1+\varepsilon}(1+|t|)^2.
\tag{A1}
$$

The same estimate holds for $\Psi_\chi(hn,\sigma+it)$ without the growing coprimality filter. There is no uniformity as $\sigma\downarrow1$ or the original ray modulus grows. In particular, the modulus of $n$ is not included in the fixed implied constant.

#### The character and finite Jacquet coefficients

Brubaker–Bump's stated Theorem 1 does not directly supply this angular family. Its $M(\Omega)$ consists of finite-place test data; Proposition 6 explicitly observes that its $\Psi$ depends only on $c_{\rm fin}$, and its archimedean vector is spherical. An angular factor cannot be inserted into that test space without changing the inducing character.

The primary-generator rule defines a unitary Hecke character away from the fixed $S$. Include $3$ and the original ray modulus in its finite modulus and choose the finite unit component cancelling

$$
\chi_\infty(z)=(z/|z|)^{-\ell}.
$$

Then $\chi_S(u)=1$ on $S$-units and $\chi^S(c)=\chi_S(c)^{-1}$ for a good principal generator. Write $u=z/2$ for Brubaker–Bump's spectral parameter. In the twisted induced space use

$$
f\!\left(\begin{pmatrix}b&*\\0&b^{-1}\end{pmatrix}g\right)
=\chi_S(b)|b|_S^{2u}f(g),
\qquad b\in\Omega=\mathcal O_S^\times(F_S^\times)^3,
$$

with the original genuine cubic multiplier. Kazhdan–Patterson allows this inducing quasicharacter. After extracting $\chi_{\rm fin}(c)^{-1}$, the finite coefficient space is Brubaker–Bump's finite-dimensional $M(\Omega)$.

In their notation $w_c=\left(\begin{smallmatrix}0&-c^{-1}\\c&0\end{smallmatrix}\right)$, normalize the finite coefficient by

$$
\Psi_{f,\chi,r,u}(c)
=\chi_{\rm fin}(c)|c|_{\rm fin}^{2u}
\int f_{\rm fin}(w_c n(x))\psi_{\rm fin}(rx)\,dx.
$$

The same small-support vector makes this equal to the prescribed $\Psi(c)$. Unfolding gives the denominator coefficient $\chi^S(c)\Psi(c)g_3(r,c)q_c^{-z}$.

The Weyl intertwiner changes $\chi$ to $\chi^{-1}$. Keeping the character factors in Brubaker–Bump's Proposition 7 and making its change $y\mapsto c^{-2}y^{-1}$ gives the finite Jacquet integral

$$
J_{\chi,\Psi}(r,c)
=\int
(y,c)_S|y|_{\rm fin}^{z-2}\chi_{\rm fin}(y)
\Psi(c^{-1}y^{-1})\psi_{\rm fin}(ry)\,dy.
\tag{A2}
$$

Indeed, the output coefficient normalization contributes $\chi_{\rm fin}(c)^{-1}$ and the input vector contributes $\chi_{\rm fin}(cy)^{-1}$; after that substitution their product is $\chi_{\rm fin}(y)$. This is the character modification of the finite calculation.

Splitting into $y\in\eta(F_S^\times)^3$ retains the same finite transformed functions

$$
\widetilde\Psi_\eta(c)=(\eta,c)_S\Psi(c^{-1}\eta^{-1}).
$$

Only their scalar integrals change. On sufficiently small unit groups the fixed character is trivial. The resulting geometric tails have factors

$$
1-\chi_v(\varpi_v)^3q_v^{-3(z-1)}
$$

in their denominators when $\chi_v^3$ is unramified; a nontrivial unit average gives zero instead. The remaining annuli are finite. The substitution $y\mapsto r^{-1}y$ multiplies a scalar integral by

$$
\chi_{\rm fin}(r)^{-1}|r|_{\rm fin}^{1-z}
$$

and permutes its cube class. For $r=hn$ all $S$-valuations are fixed, and the remaining dependence is through fixed finite unit quotients. Including the fixed local Hecke factors, the coefficient matrices are bounded uniformly in $n,t$ on each fixed line $3/4\le\Re z<1$, and on a fixed line $2-\sigma_0$ with $3/2<\sigma_0<11/6$.

The transformed finite functions expand into fixed cubic ray characters. Their cubes are trivial, so the branch family closes among $\chi$ times these characters and their inverses, with cube normalizers $L_\chi$ and its conjugate. All deleted Euler factors remain deleted. No growing ray conductor is introduced by this finite closure.

#### The archimedean scalar and numerator norm

At the complex place the cover splits. For $|\ell|=1$, use the two-dimensional minimal $\mathrm{SU}(2)$ type. Its Jacquet components at $w n(v)$ are proportional, for one sign, to

$$
\bar v(1+|v|^2)^{-(z+1/2)},
\qquad
-(1+|v|^2)^{-(z+1/2)},
$$

with conjugate coordinates for the other sign. The complex radial Fourier integral and its first Wirtinger derivative have the common scalar denominator $\Gamma(z+1/2)$, numerator $|r|^{z-1/2}$, and Bessel orders $z-3/2$ and $z-1/2$. The reflected character at $2-z$ exchanges the two components. Its Bessel orders are their negatives, so $K_\nu=K_{-\nu}$ matches them with one common scalar. The ratio of the numerator powers has magnitude $q_r^{1-\Re z}$; the remaining angular factors are unitary.

The cubic coroot character is

$$
\omega_\alpha=\chi^3\|\cdot\|^{3(z-1)}.
$$

Thus the root normalizer is $L^S(3z-2,\chi^3)$. Its infinity factor has gamma argument $3z-2+3/2=3z-1/2$. The scalar quotient is

$$
\frac{\Gamma(3z-\tfrac12)}{\Gamma(z+\tfrac12)}
=3\frac{\Gamma(3z-\tfrac32)}{\Gamma(z-\tfrac12)}.
$$

Gauss multiplication expresses this, up to fixed nonzero constants and a fixed positive real power to $z$, as

$$
\mathcal G_1(z)
=c_0c_1^z\Gamma(z-\tfrac16)\Gamma(z+\tfrac16),
\qquad c_1>0.
$$

It agrees with the theta Mellin factor above under $s_{\rm theta}=z-1/2$. Consequently the global Weyl equation and (A2) give a finite closed vector of the form

$$
\mathcal G_1(z)\mathcal Z_j(hn,z)
=q_{hn}^{1-z}
\sum_k P_{jk}(n,z)\mathcal G_1(2-z)\mathcal Z_k(hn,2-z),
\tag{A3}
$$

where fixed positive powers and unitary phases are included in $P_{jk}$. Fixed ramified scalings of $h$ may be included among the finite branches. On the left lines specified above, these matrices are bounded independently of good squarefree $n$ and $t$. Stirling's formula gives

$$
\sum_j|\mathcal Z_j(hn,z)|^2
\ll
q_n^{2-2\Re z}(1+|\Im z|)^{8-8\Re z}
\sum_j|\mathcal Z_j(hn,2-z)|^2.
\tag{A4}
$$

The passage from the general Eisenstein equation to (A3) uses the displayed coefficient and scalar identifications, rather than an angular specialization of the stated spherical theorem.

#### Coprimality, poles and growth

In the local identities of DDDS Lemma 6.1, the exponent-one term gains $\chi(\pi)$ and the exponent-two term gains $\chi(\pi)^2$. The same two-by-two elimination and divisor induction therefore give

$$
\begin{aligned}
\Delta_{\chi,n}(z)\Psi_{\chi,n}(hn,z)
&=\sum_{d\mid n}\mu(d)\chi(d)^2q_d^{1-2z}
\overline{g_3(hn/d,d)}\Psi_\chi(hn/d,z),\\
\Delta_{\chi,n}(z)
&=\prod_{\pi\mid n}\left(1-\chi(\pi)^3q_\pi^{2-3z}\right).
\end{aligned}
\tag{A5}
$$

Here $(n,h)=1$ and $n$ is good and squarefree. Full conjugation changes the Gauss conjugations accordingly.

The existing theta supplier pays the pole and growth question for the required family. In fact,

$$
\mathcal C_{\chi,n}(z)
=L^{Sn}(3z-2,\chi^3)\Psi_{\chi,n}(hn,z)
$$

is its entire angular numerator after $s_{\rm theta}=z-1/2$. The fixed $h$ contributes a fixed supplementary cubic ray character, whose cube is trivial. This matches every fixed branch, with full conjugation where required. Each numerator has finite exponential growth in vertical strips.

Since $L^{Sn}(3z-2,\chi^3)=L_\chi(3z-2)\Delta_{\chi,n}(z)$, equation (A5) becomes

$$
\mathcal C_{\chi,n}(z)
=\sum_{d\mid n}\mu(d)\chi(d)^2q_d^{1-2z}
\overline{g_3(hn/d,d)}\mathcal Z_\chi(hn/d,z).
\tag{A6}
$$

The $d=1$ term is $\mathcal Z_\chi(hn,z)$. Induction over divisors, starting at $n=1$, proves that every required completed $\mathcal Z_\chi(hn,z)$ is entire and has finite exponential growth in strips. In particular the DDDS residue term is absent for this family. No absence of raw-series poles at zeros of its Hecke normalizer is used.

Absolute convergence on $\Re z=\sigma_0>3/2$, equation (A4) on $2-\sigma_0$, and the same strip Phragmén–Lindelöf argument used by DDDS give

$$
\mathcal Z_\chi(hn,\sigma+it)
\ll
q_n^{(\sigma_0-\sigma)/2}
(1+|t|)^{2(\sigma_0-\sigma)}.
\tag{A7}
$$

Choose $\sigma_0$ sufficiently close to $3/2$ for the fixed $\sigma>1$. The finite exponential growth obtained from (A6) supplies the interpolation hypothesis. The finite-$M$ squared supremum divided by $(1+|t|)^2$ used in DDDS's absorption is therefore finite, with its ratio tending to zero at infinity.

#### Reusing the second-moment argument

For each fixed branch the completed convolution is

$$
\mathcal Z_\chi(r,z)
=\sum_{c,b}
\frac{\chi(c)\chi(b)^3g_3(r,c)q_b^2}{q_{cb^3}^{z}},
$$

with the fixed primary and $S$ restrictions. In the Gauss split $c=wv$, the extra $\chi(v)$ is a unit-modulus column coefficient, independent of the numerator variable. The fixed finite branch functions have the same property after their character expansion. Thus the technical Gauss-splitting and cubic-sieve estimates in DDDS's Lemma 6.6 proof apply with the same magnitudes.

Let $\mathfrak Z_M(z)$ sum the squared completed branches over the good squarefree $n$ with $q_n\le M$. The source's short-sum term is

$$
S_2\ll(MX)^\varepsilon
\left(M+M^{1/3}X^{3-2\sigma}
+M^{2/3}X^{8/3-2\sigma}\right),
$$

and its functional-equation remainder, using (A4), satisfies

$$
S_3\ll
\left(\frac{M(1+|t|)^4}{X^2}\right)^{2(\sigma-1)}
\int_{\mathbb R}\mathfrak Z_M(\sigma-it-iy)e^{-|y|/2}\,dy.
$$

The positive short-sum estimate permits restriction to squarefree numerator indices; (A3) and (A6) preserve that same numerator family. There is no residue term. Taking $X=C_\sigma\sqrt M(1+|t|)^2$ and using DDDS's finite-supremum absorption gives

$$
\mathfrak Z_M(\sigma+it)\ll M^{1+\varepsilon}(1+|t|)^2.
$$

The inverse $L_\chi(3z-2)$ is absolutely bounded on $\sigma>1$, proving the unfiltered version of (A1).

For the actual growing coprimality restriction, (A5), $|g_3(hn/d,d)|=\sqrt{q_d}$ and

$$
|\Delta_{\chi,n}(\sigma+it)|^{-1}
\le\zeta_F(3\sigma-2)
$$

give

$$
|\Psi_{\chi,n}(hn,z)|^2
\ll q_n^\varepsilon
\sum_{d\mid n}q_d^{3-4\sigma}|\Psi_\chi(hn/d,z)|^2.
$$

Sum $n=dm$, enlarge the positive sums and apply the unfiltered estimate. The result is bounded by

$$
M^{1+2\varepsilon}(1+|t|)^2
\sum_d q_d^{2-4\sigma-\varepsilon}.
$$

The final sum converges for $\sigma>1$. Renaming $\varepsilon$ proves (A1) with the original coprimality restriction. This step does not invoke a theorem uniform in a growing ray modulus.

#### Consumption by the original coefficient vector

Mellin inversion on $\Re w=1/2+\delta$ and Minkowski's inequality now give

$$
\sum_{\substack{n\ {\rm good,\ squarefree}\\q_n\asymp N}}
|T_{n,\xi}(D)|^2
\ll
D^{1+2\delta}N^{1+\varepsilon}\mathcal N_\delta(W_M)^2.
$$

The unchanged outer vector $b_n=\nu(n)W_S(q_n/N)\gamma_1(n)$ has squared norm $\ll N\|W_S\|_\infty^2$. Cauchy–Schwarz therefore yields

$$
\boxed{
|Q_{\rm sf}(D,N)|
\ll (DN)^\varepsilon D^{1/2}N
\|W_S\|_\infty\mathcal N_\delta(W_M).
}
\tag{A8}
$$

Here $\delta>0$ is fixed sufficiently small in terms of $\varepsilon$, and every original finite filter is retained in its fixed expansion. Divisor-bounded outer weights incur the same absorbable $N^\varepsilon$ loss as above.

For the same fixed profiles this replaces the angular $D^{1/2}N^{5/4}$ term by $D^{1/2}N$, with the same profile norm. Combining with the cubic bound gives

$$
|Q_{\rm sf}(D,N)|\ll
(DN)^\varepsilon\|W_S\|_\infty
\min\left\{
(DN)^{1/2}\left(D+N+(DN)^{2/3}\right)^{1/2}\|W_M\|_\infty,\;
D^{1/2}N\mathcal N_\delta(W_M)
\right\}.
$$

At $D=N=R$ and fixed height the exponent is $3/2+\varepsilon$, compared with the cubic $5/3+\varepsilon$. For $D=N^a$ and bounded fixed profiles, the angular second-moment exponent is $a/2+1$. It equals the cubic exponent for $a\le1/2$ and improves it for $a>1/2$. The exponent margin is $(2a-1)/6$ for $1/2<a\le2$ and $(a-1)/2$ for $a\ge2$.

A common norm modulation of size $H$ still costs $1+H$ through $\mathcal N_\delta$. At balance a power improvement over the height-free cubic comparison requires $H\ll R^h$ with $h<1/6$, leaving positive room for the $\varepsilon$ losses. The original cumulative height allowance and actual witness lengths must satisfy these conditions.

This is a source-conditional application of the existing analytical methods, without complete local Lean certification or a claim of literature novelty. It estimates the original coprime squarefree packet with its actual outer phase. Shared primes, nonsquarefree columns, other dual terms, the full actual-order-six contraction and the signed same-integer Robin remainder remain separate obligations.

### A tame growing-ray application to the complete classwise pole

The fixed-presentation constant in (A1) cannot be reused as a constant uniform in the powerful cores. The local conductor formulas of [Szpruch, *On Shahidi local coefficients matrix*, arXiv:1609.08122v4](https://arxiv.org/pdf/1609.08122v4), Lemma 4.15 and Proposition 4.17, and [Szpruch, *A p-adic analog of Hasse-Davenport product relation involving epsilon-factors*, arXiv:2306.10928v2](https://arxiv.org/pdf/2306.10928v2), Proposition 1, equations (16)–(18) and Lemma 17, supply the required tame factors, including ramified quadratic characters on the cubic cover. The following application matches these factors to (A2), retains the pole's noncharacter weight, and consumes the estimate in the original complete classwise all-column contraction. The local formulas, DDDS method and existing core decomposition are reused results.

#### Extra finite data and its conductor cost

Let $S_0$ be the complete original fixed bad set, containing the primes over $2,3$ and the original modulus. In this subsection $f$ denotes an extra good squarefree modulus, containing all additional deleted primes and finite character conductors; it is distinct from the primitive pair conductor $\mathfrak f_{h,k}$. At each $\mathfrak p\mid f$, the character on local units has order dividing six and conductor at most one. Its unramified values may be arbitrary unitary phases. Keep infinity type $\ell=\pm1$ and write

$$
F=q_f,\qquad E=q_e,\qquad r=hen,\qquad h=-3,
$$

where $e,n$ are good squarefree ideals with $(e,nf)=(n,f)=1$. Delete $S_0f$ in the raw series and its completion:

$$
\mathcal Z_\chi(r,z)=L^{S_0f}(3z-2,\chi^3)\Psi_\chi(r,z).
$$

The local cube quotient at a good prime has at most nine elements. Cube-class indicators and their unit-character Fourier expansions have uniformly bounded coefficient norms. Including the inverse character and all cubic twists therefore costs $C^{\omega(f)}\ll_\eta F^\eta$, for every fixed $\eta>0$. The original $S_0$ space remains fixed. No implied constant below is allowed to depend on $f$.

For the normalized local principal-series parameter in Szpruch's formula, put $u=z-1$: the inducing rule in (A2) is $\chi(b)|b|^z$, while the Borel half-density is $|b|$. At a new good prime, $r$ is a unit and the additive character has conductor zero. Normalize $\operatorname{vol}(\mathcal O_{\mathfrak p})=1$. Resolving (A2) into cube classes reduces its scalar entries to annular integrals of

$$
|y|^{z-2}\omega(y)\psi(ry)\,dy.
$$

For tame unit characters, valuations below $-1$ give zero. Valuation $-1$ contributes at most $q_{\mathfrak p}^{\sigma-3/2}$, by the finite Gauss sum. At nonnegative valuation $k$, only the trivial unit character survives, contributing $(1-q_{\mathfrak p}^{-1})q_{\mathfrak p}^{k(1-z)}$. A cube-class restriction fixes $k$ modulo three, so its tail has the form

$$
\frac{q_{\mathfrak p}^{j(1-z)}}{1-a_{\mathfrak p}q_{\mathfrak p}^{3-3z}},
\qquad j=0,1,2,\qquad |a_{\mathfrak p}|=1.
$$

If $\chi_{\mathfrak p}^3$ is ramified, it has conductor one and every cubic twist remains ramified, by Szpruch's Lemma 4.15. There are no nonnegative tails. Reflection of the coroot factor from $3z-3$ to $4-3z$ has conductor multiplier $q_{\mathfrak p}^{7/2-3\sigma}$. Together with the Jacquet factor $q_{\mathfrak p}^{\sigma-3/2}$, its cost is $q_{\mathfrak p}^{2-2\sigma}$. Equivalently the local epsilon factors have powers $q_{\mathfrak p}^{u-1/2}$ and $q_{\mathfrak p}^{1/2-3u}$.

If $\chi_{\mathfrak p}^3$ is unramified, Brubaker–Bump's deleted-factor bookkeeping gives

$$
\frac{1-a_{\mathfrak p}q_{\mathfrak p}^{3-3z}}
{1-\overline{a_{\mathfrak p}}q_{\mathfrak p}^{3z-4}}.
$$

On a fixed line $\sigma<1$, the denominator inverse is uniformly bounded. The numerator cancels the geometric tails, leaving at most $q_{\mathfrak p}^{2(1-\sigma)}$. Its product with a valuation $-1$ Gauss term costs at most $Cq_{\mathfrak p}^{3/2-2\sigma}$, which is smaller. This covers purely cubic ramification and primes deleted solely to preserve the original zeros. Hilbert factors and unit rescalings are unimodular.

Thus each new local matrix costs at most $C_\sigma q_{\mathfrak p}^{2(1-\sigma)}$. Combining with the already matched archimedean factor in (A3), for the finite closed branch vector one obtains

$$
\sum_j|\mathcal Z_j(hen,z)|^2
\ll_{\sigma,\eta}
(FEq_n)^\eta F^{4-4\sigma}(Eq_n)^{2-2\sigma}
(1+|t|)^{8-8\sigma}
\sum_j|\mathcal Z_j(hen,2-z)|^2.
\tag{B1}
$$

The required left lines are fixed $\sigma=2-\sigma_0$ with $3/2<\sigma_0<11/6$, and $3/4\le\sigma<1$. Numerator variation at $f$ changes only phases and cube classes. The multiplier $e$ remains a numerator shift.

#### The mean square with its original restrictions

For each fixed $f$, the existing theta argument and (A6) apply to the squarefree index $en$. All required branch completions are entire and have finite exponential growth in strips. Those fixed-$f$ constants need not be uniform: they establish finiteness of the DDDS supremum. The uniform final estimate comes from (B1) and the right-line and short-sum bounds.

Reuse the DDDS short-sum estimate for the squarefree numerator family $q_n\le M$, $(n,ef)=1$:

$$
S_2\ll(FEMX)^\eta
\left(M+M^{1/3}X^{3-2\sigma}
+M^{2/3}X^{8/3-2\sigma}\right).
$$

The extra unitary character coefficients are independent of the numerator variable in the Gauss split. The finite expansion costs $F^\eta$, and the numerator multiplier costs $E^\eta$. Equation (B1) bounds the remainder by

$$
S_3\ll(FEM)^\eta
\left(\frac{F^2EM(1+|t|)^4}{X^2}\right)^{2(\sigma-1)}
\int_{\mathbb R}\mathfrak Z_M(\sigma-it-iy)e^{-|y|/2}\,dy.
$$

In the existing finite-supremum absorption take

$$
X=C_{\sigma,\eta}F\sqrt{EM}\,
(FEM)^{\eta/[4(\sigma-1)]}(1+|t|)^2.
$$

Choose $\eta$ sufficiently small relative to the final $\varepsilon(\sigma-1)$. The extra powers fit the final epsilon losses. Substitution in $S_2$ bounds the powers of $F,E,M$ by $1,1/2,1$, respectively, and the height power by two, up to these losses. Removing the absolutely bounded inverse normalizer gives

$$
\sum_{\substack{q_n\le M,\ n\ {\rm good\ sf}\\(n,ef)=1}}
|\Psi_{\chi,en}(hen,\sigma+it)|^2
\ll_{\sigma,\varepsilon}
(FEM)^\varepsilon F E^{1/2}M^{1+\varepsilon}(1+|t|)^2,
\qquad 1<\sigma\le5/4.
\tag{B2}
$$

First obtain the unfiltered statement. To impose $(c,en)=1$, apply (A5) with squarefree $en$ and split its divisor as $d=d_ed_n$. The resulting sums have exponents $5/2-4\sigma+\varepsilon$ on $d_e\mid e$, and $2-4\sigma+\varepsilon$ on $d_n$. Both converge uniformly for sufficiently small $\varepsilon$. This proves the displayed version without adding $e$ to $f$.

The actual pole scalar also contains $\vartheta(z)$, which is not a character. For squarefree coprime $z=ed'n'$, separate its three factors. The outer and fixed factors have modulus at most one. In the inner variable expand

$$
\vartheta(d')=\sum_{v\mid d'}\frac{\mu(v)}{q_v}.
$$

Writing $d'=vc$, normalized cubic Gauss CRT and reciprocity give the numerator shift $v$: the cross factor $\kappa_v(c)\kappa_c(v)$ is $\kappa_c(v)^2$, hence the same as the shift from $g_3(r,c)$ to $g_3(rv,c)$, up to the retained class phase. Conjugate the entire identity for the actual conjugate family. The remaining normalized Gauss factor at $v$ has modulus one and can stay in the outer coefficient. The shifted numerator is $hevn'$ and the denominator excludes $evn'f$. Mellin inversion and Minkowski pay

$$
\sum_v q_v^{-1}(D'/q_v)^{1/2}(Eq_v)^{1/4}
=D'^{1/2}E^{1/4}\sum_v q_v^{-5/4}<\infty.
$$

Different $v$ may have different outer phases; the Minkowski estimate does not identify their vectors. Put

$$
\mathcal P=\|W_M\|_\infty\|W_S\|_\infty,
\qquad
\mathcal B=\|W_S\|_\infty\mathcal N_\delta(W_M),
$$

with the same original seminorm and fixed sufficiently small $\delta>0$ as in (A8). For bulk lengths $D',N'$, the resulting weighted scalar obeys

$$
|Q_{\rm weighted}(D',N';e,f)|^2
\ll K^\varepsilon F E^{1/2}D'(N')^2\mathcal B^2.
\tag{B3}
$$

Every original class restriction, multiplicative twist, zero mask and orientation remains in the corresponding coefficient. Divisor bounds cost epsilon only.

#### Consumption with opposite-core-dependent coefficients

Keep the earlier all-column decomposition $h=gx,k=gy$, $x=cs_0z,y=c't_0w$, and its exact CRT and Möbius extension. For an original factorization $dn=mz$, $m=gcs_0=ab$, reuse

$$
a=a_ga_c,\quad b=b_gb_cs_0,\quad
a_g=(a,\operatorname{rad}g),\quad b_g=g/a_g,\quad
a_c\mid\operatorname{rad}c,\quad b_c=c/a_c.
$$

Because $c$ is powerful and $a_c$ is squarefree, $\operatorname{rad}c\mid b_c$. Nonempty original ranges impose $q_b\ll N$, so $q_{\operatorname{rad}c}\le q_{b_c}\ll N$. The same holds for $c'$. All new finite weights and exclusions are supported on $\operatorname{rad}(gcc')\ell$; the divisor $r\mid R$ introduces no other prime. A common conductor envelope for both sides is therefore

$$
F\ll q_g N^2q_\ell.
\tag{B4}
$$

It is independent of both opposite cores. The fixed coefficient vectors can still differ between separate core-pair applications.

Distribute $e=e_de_n$ between the actual factors, writing $d=ae_dd'$, $n=be_nn'$. The interaction of $e$ with the moving squarefree Gauss factor is cubic, by the already retained reciprocity formula, and is the numerator shift $e$ in (B3). It is not a growing quadratic modulus. The bulk lengths satisfy

$$
D'=\frac D{q_aq_{e_d}},\qquad
N'=\frac N{q_bq_{e_n}},\qquad
D'N'=X/q_e,\qquad X=K/q_m.
$$

Including the original $q_z^{-1/3}$ weight, (B3) gives

$$
|H_{m,e}^{a,b}|^2
\ll K^\varepsilon F X^{1/3}\frac N{q_b}
q_e^{-1/2}q_{e_n}^{-1}\mathcal B^2.
$$

The sum over $e_d$ costs $(D/q_a)^{1/2}$ and the $e_n^{-3/2}$ sum converges. Hence

$$
\sum_e|H_{m,e}^{a,b}|^2
\ll K^\varepsilon F X^{1/3}\frac N{q_b}
\left(\frac D{q_a}\right)^{1/2}\mathcal B^2.
\tag{B5}
$$

For the new part, sum square roots using the positive core moment

$$
\sum_{\substack{c\ {\rm powerful}\\a_c\mid\operatorname{rad}c}}
w(c)q_{a_c}^{-5/12}q_{b_c}^{-2/3}<\infty.
$$

A prime exponent $r\ge2$ and choice $\delta=0,1$ have local exponent $2r/3-\delta/4+1/3$ if $6\nmid r$, and $2r/3-\delta/4$ otherwise. The minima are $5/3$ and $17/12$ at $r=2$; exponents divisible by six give at least $15/4$. Dropping negative $s_0$ factors is used only in positive upper bounds, and its choices cost $q_g^\varepsilon$.

After (B4) and the core sum, the square root of (B5) is bounded by

$$
K^\varepsilon q_\ell^{1/2}K^{1/6}D^{1/4}N^{3/2}
q_{a_g}^{1/12}q_{b_g}^{-1/6}\mathcal B.
$$

First apply Cauchy in $e$ to each fixed pair of scalar vectors. Then take absolute values and sum the core pairs using these uniform square-root envelopes. Cauchy over $a_g\mid\operatorname{rad}g$ costs $q_g^\varepsilon$ and replaces the two possibly different distribution indices by one sum of squared envelopes. Only now split this positive sum at $q_{a_g}=A$. This retains the low–high cross terms without equating opposite-core-dependent vectors.

For $q_{a_g}\le A$, the sums of $q_{a_g}^{1/6}$ and $q_{b_g}^{-1/3}$ cost $A^{7/6}$ and $N^{2/3}$. The low part is

$$
\ll K^\varepsilon D^{5/6}N^4A^{7/6}\mathcal B^2.
\tag{B6}
$$

The extra $q_\ell$ is paid by the original $q_\ell^{-5}$ sum, now $q_\ell^{-4}$; the $r$ divisor sum still costs epsilon. For $q_{a_g}>A$, reuse the earlier coefficient-uniform cubic/core estimate. Its $D$ term has tail $\sum_{q_{a_g}>A}q_{a_g}^{-4/3}\ll A^{-1/3}$; its other terms retain their original bounds. Thus the high part is

$$
\ll K^\varepsilon
\left\{K(1+N^{1/3})+D^{4/3}NA^{-1/3}\right\}\mathcal P^2.
\tag{B7}
$$

The actual $z=w=1$ sector and its algebraically added counterpart retain their $O(K^{1+\varepsilon})$ bound. For $1\le A\le D$, the complete classwise pole therefore satisfies

$$
\boxed{
|\mathcal C^{a,\rm all}_{6,L}[c_j]|
\ll K^\varepsilon
\left\{
K(1+N^{1/3})\mathcal P^2
+D^{4/3}NA^{-1/3}\mathcal P^2
+D^{5/6}N^4A^{7/6}\mathcal B^2
\right\}.
}
\tag{B8}
$$

This is uniform in $L$ and retains squarefree, nonsquarefree and mixed columns and every common gcd.

#### Improvement range and unpaid target

For $\mathcal B\le C H_0\mathcal P$, $H_0\ge1$, take $A=D^{1/3}N^{-2}H_0^{-4/3}$ when this is at least one. It is at most $D$. Then

$$
\boxed{
|\mathcal C^{a,\rm all}_{6,L}[c_j]|
\ll K^\varepsilon\mathcal P^2
\left\{K(1+N^{1/3})
+D^{11/9}N^{5/3}H_0^{4/9}\right\}.
}
\tag{B9}
$$

With fixed power room, $D>N^6H_0^4$ makes this smaller than the earlier $D$-dominant $KD^{1/3}$ estimate and the absolute $K^{4/3}$ estimate. Outside this range keep the existing bound. A common norm modulation $H$ costs $H_0\asymp1+H$ for fixed unmodulated profiles; its budget has not been reset.

These are permitted, not guaranteed, original witness sectors: with $D=U^r$, $N=U^m$, $H_0\ll U^h$, the improvement requires $r>6m+4h$, subject to the original $r\le t$, $r+m\ge t$ and $0\le m\le1/2$, with their small losses. It is not a uniform detector improvement.

In particular (B9) alone does not pay the pole budget. Its new term would require

$$
U\ge D^{4/3}N^4H_0^{8/3}
$$

to make $U^{5/6}\mathcal C$ bounded by $UK$, up to epsilon losses. But the original $r+m\ge t\ge1$ implies $4r/3+4m\ge4/3$ before the small losses, already exceeding one at $H_0=1$. The application supplies only the stated all-column upper-bound improvement. Other dual terms, coverage of the actual witnesses, the earlier cross-class signed contraction and signed Robin restoration remain open. It has no complete local Lean certification and makes no literature-novelty claim.

### Separating zero-only support in the same all-column pole

Primes used only to preserve zero values can be removed by [DDDS, arXiv:2410.03048v3](https://arxiv.org/html/2410.03048v3#S6), Lemma 6.1(iii), before applying the conductor-dependent moment. This application retains their divisor shifts and the original weighted ray-divisor sum. It improves (B8) and pays the classwise all-column pure-sixth-power pole on a nonempty sector of the original witness domain. The full witness domain, other dual terms and signed Robin restoration remain open.

An existing angular Möbius annular application appears in [Dunn–Radziwiłł, *Bias in cubic Gauss sums: Patterson's conjecture*, arXiv:2109.07463v3](https://arxiv.org/pdf/2109.07463v3), Proposition 8.1 and equations (8.5)–(8.8). Its final estimate assumes RH for Größencharakter twists and invokes that hypothesis in (8.6). DDDS §8.2.4 also applies a local-factor divisor expansion to its different polar-term coefficients. The inputs used below are the owned moment (B2) and DDDS's coprimality identity; the known local formula and Rankin method are reused, without a literature-novelty claim for this application.

#### Zero-only primes have an epsilon cost

Let $f$ contain the additional genuine tame character data, with $F=q_f$, and let $a$ be a disjoint squarefree modulus used only for zeros. Keep the fixed bad set $S_0$, $h=-3$, infinity mode $\ell=\pm1$, and squarefree $e,n$ with $(e,nf)=(n,f)=(en,a)=1$. Write $E=q_e$. The source identity with the denominator character retained is

$$
\begin{aligned}
\Delta_{\chi,a}(z)\Psi_{\chi,ena}(hen,z)
&=\sum_{d\mid a}\mu(d)\chi(d)q_d^{-z}
g_3(hen,d)\Psi_{\chi,en}(hend,z),\\
\Delta_{\chi,a}(z)
&=\prod_{\mathfrak p\mid a}
\left(1-\chi(\mathfrak p)^3q_{\mathfrak p}^{2-3z}\right).
\end{aligned}
\tag{C1}
$$

In the two local elimination equations in DDDS's proof, the exponent-one term gains $\chi(\mathfrak p)$ and the exponent-two term gains $\chi(\mathfrak p)^2$, giving the displayed determinant. This is the weighted application of the existing identity, initially on $\Re z>3/2$ and then by continuation on the required fixed line $\sigma>1$. Conjugate the whole identity for the other orientation.

Here $|g_3(hen,d)|=q_d^{1/2}$. The numerator $hend$ is squarefree away from $S_0$. Applying (A5) to the filter $en$, and the unfiltered shifted-numerator version of (B2), bounds the squared mean of $\Psi_{\chi,en}(hend,z)$ by

$$
(FEq_dM)^\varepsilon F(Eq_d)^{1/2}
M^{1+\varepsilon}(1+|t|)^2.
$$

The two positive divisor sums retain the exponents $5/2-4\sigma$ and $2-4\sigma$. The additional outer condition $(n,a)=1$ can be kept in these positive means. No comparison of absolute Dirichlet-series values under deletion is used.

Minkowski in (C1), allowing $d$-dependent outer phases, now leaves

$$
\sum_{d\mid a}q_d^{3/4-\sigma+\eta}
\ll_{\sigma,\varepsilon}q_a^\varepsilon,
$$

for sufficiently small auxiliary $\eta>0$. This is a divisor-product bound, since $\sigma-3/4-\eta>0$, rather than convergence of the sum over all ideals $d$. Also $|\Delta_{\chi,a}(z)|^{-1}\le\zeta_F(3\sigma-2)$. Thus zero-only $a$ costs epsilon in (B2), with no addition to $F$.

The $\vartheta$ expansion used in (B3) remains compatible: $v\mid d'$ is coprime to $a$, so the shifted numerator $hevdn'$ remains squarefree. The sum $\sum_vq_v^{-5/4}$ is unchanged. All original zero masks are enforced before these identities are used.

#### Keep the weighted ray sum before the core sums

Use the same actual all-column decomposition and definitions

$$
h=gx,\quad k=gy,\quad x=cs_0z,\quad y=c't_0w,
\qquad f_c=\operatorname{rad}(r_6(c)),
$$

$$
f_0=f_cs_0f_{c'}t_0,\qquad
R=\operatorname{rad}(gcc'S_0)/f_0.
$$

Write $R_g$ and $r_g$ for the good parts outside $S_0$. The exact root CRT places the additional finite single-variable twists on $f_0$. The exclusion-product divisor $r\mid R$ adds a twist supported on $r_g$. Reciprocity on the original fixed primary classes therefore permits

$$
F\le q_{f_0}q_{r_g}.
$$

The remaining primes of $\operatorname{rad}(gcc'\ell)$ are zero-only and are handled by (C1). Their cost is $K^\varepsilon q_\ell^\varepsilon$, including inactive sixth powers. The original $q_\ell^{-5}$ row weight absorbs this loss uniformly in its finite cutoff.

For $m=gcs_0=ab$, reuse $a=a_ga_c$, $b=b_gb_cs_0$ and the same squarefree distribution constraints. Define the part of (B5) without its conductor factor by

$$
\mathcal L_c^2
=X^{1/3}\frac N{q_b}
\left(\frac D{q_a}\right)^{1/2}\mathcal B^2,
\qquad X=K/(q_gq_cq_{s_0}).
$$

For each fixed $r$, (B5) with this modulus gives

$$
\sum_e|H_{c,r,e}^{a,b}|^2
\ll K^\varepsilon q_\ell^\varepsilon
q_{f_0}q_{r_g}\mathcal L_c^2.
\tag{C2}
$$

Keep the original $q_r^{-5/6}$ weight. The joint relation

$$
q_{f_0}q_{R_g}=q_{\operatorname{rad}(gcc')}
\le q_gq_{\operatorname{rad}c}q_{\operatorname{rad}c'}
$$

is stronger than separately majorizing its factors. Put

$$
\mathcal T_c=(q_{f_c}q_{s_0})^{5/6}
q_{\operatorname{rad}c}^{1/6}.
$$

The weighted conductor sum satisfies

$$
\sum_{r\mid R}q_r^{-5/6}F
\ll K^\varepsilon q_{f_0}q_{R_g}^{1/6}
\le K^\varepsilon q_g^{1/6}\mathcal T_c\mathcal T_{c'}.
\tag{C3}
$$

For any nonempty opposite original factorization, $\operatorname{rad}c'\mid b_{c'}$ and

$$
\mathcal T_{c'}\le q_{\operatorname{rad}c'}q_{t_0}
\le q_{b_{c'}}q_{t_0}\ll N/q_{b_g'}\le CN.
$$

An empty opposite range contributes zero. Consequently the squared norm in the weighted $(r,e)$ variables on the $c$ side has the uniform bound

$$
\ll K^\varepsilon q_\ell^\varepsilon
q_g^{1/6}N\mathcal T_c\mathcal L_c^2.
\tag{C4}
$$

Use the symmetric statement for the other side. This upper envelope depends only on its own core and is uniform in the opposite-core-dependent vectors. The order is Cauchy in weighted $(r,e)$ for each fixed core pair, uniform scalar envelopes, and then positive core sums.

#### The positive core moment used in the consumer

The square roots in (C4) require

$$
\mathcal G(V)=
\sum_{\substack{c\ {\rm powerful},\ a_c\mid\operatorname{rad}c\\
b_c=c/a_c,\ q_{b_c}\le V}}
w(c)q_{a_c}^{-5/12}q_{b_c}^{-2/3}
q_{\operatorname{rad}c}^{1/2}
\ll_\varepsilon V^{1/12+\varepsilon}.
\tag{C5}
$$

For a prime exponent $j\ge2$ and choice $\delta=0,1$, insert the Rankin factor $q_{b_c}^{-s}$. The local exponent is $2j/3-\delta/4-1/2+1/3+(j-\delta)s$ if $6\nmid j$, and $2j/3-\delta/4-1/2+(j-\delta)s$ otherwise. Every exponent exceeds one for $s>1/12$. The critical case $j=2,\delta=1$ is $11/12+s$; $j=2,\delta=0$ gives $7/6+2s$, and multiples of six give at least $13/4$ before the $s$ term. Convergence of this positive Euler product proves (C5).

The square root of $\mathcal L_c^2$ is

$$
K^{1/6}D^{1/4}N^{1/2}
q_{a_g}^{-5/12}q_{b_g}^{-2/3}
q_{a_c}^{-5/12}q_{b_c}^{-2/3}q_{s_0}^{-2/3}\mathcal B.
$$

Equation (C4) adds $q_g^{1/12}N^{1/2}\mathcal T_c^{1/2}$, with $\mathcal T_c^{1/2}\le q_{\operatorname{rad}c}^{1/2}q_{s_0}^{5/12}$. The remaining $s_0$ exponent is $-1/4$. The original constraint $q_{b_g}q_{b_c}q_{s_0}\ll N$ permits (C5) with $V=CN/(q_{b_g}q_{s_0})$. Its extra $s_0^{-1/12}$ leaves a negative exponent $-1/3$, dropped only in this positive bound. Choices of $s_0$ cost $q_g^\varepsilon$.

After summing cores, the square-root envelope at a fixed distribution of $g$ is

$$
K^\varepsilon q_\ell^\varepsilon
K^{1/6}D^{1/4}N^{13/12}
q_{a_g}^{-1/3}q_{b_g}^{-2/3}\mathcal B.
\tag{C6}
$$

All auxiliary epsilon powers are chosen relative to one final epsilon; the original profile and height norms are retained.

#### A hybrid bound that pays an original witness sector

For each fixed pair of cores, first use Cauchy in the weighted $(r,e)$ Hilbert space and triangle over the distributions $a_g$. Low distributions have (C4), uniformly in the opposite core. High distributions retain the existing coefficient-uniform cubic envelope after the same weighted ray sum. After taking absolute values and summing core pairs, the numerical envelopes depend on their own cores. Cauchy over $a_g\mid\operatorname{rad}g$ costs $q_g^\varepsilon$ and yields a sum of squared numerical envelopes. Splitting this sum at $q_{a_g}=A$ retains low–high cross terms and requires no common coefficient vector.

Squaring (C6), use $\sum_{q_{a_g}\le A}q_{a_g}^{-2/3}\ll A^{1/3}$ and convergence of $\sum_{b_g}q_{b_g}^{-4/3}$. The low part is

$$
\ll K^\varepsilon D^{5/6}N^{5/2}A^{1/3}\mathcal B^2.
\tag{C7}
$$

The high part is the unchanged (B7). Keep the existing $K^{1+\varepsilon}$ treatment of $z=w=1$ and its algebraically added counterpart. The $\ell$ sum now has weight $q_\ell^{-5+\varepsilon}$ and converges uniformly in $L$. For $1\le A\le D$ this proves the complete classwise all-column pure-sixth-power pole bound

$$
\boxed{
|\mathcal C^{a,\rm all}_{6,L}[c_j]|
\ll K^\varepsilon\left\{
K(1+N^{1/3})\mathcal P^2
+D^{4/3}NA^{-1/3}\mathcal P^2
+D^{5/6}N^{5/2}A^{1/3}\mathcal B^2
\right\}.
}
\tag{C8}
$$

No original Möbius phase, column status, repeated prime or common gcd has been omitted. For $\mathcal B\le CH_0\mathcal P$, $H_0\ge1$, set $A=D^{3/4}N^{-9/4}H_0^{-3}$ when $D\ge N^3H_0^4$. Then $1\le A\le D$ and

$$
\boxed{
|\mathcal C^{a,\rm all}_{6,L}[c_j]|
\ll K^\varepsilon\mathcal P^2
\left\{K(1+N^{1/3})+D^{13/12}N^{7/4}H_0\right\}.
}
\tag{C9}
$$

With fixed power room in $D>N^3H_0^4$, this improves the earlier cubic and absolute comparisons. Where (B9) improves, the ratio of the new term to its term is $D^{-5/36}N^{1/12}H_0^{5/9}$, which is also smaller with power room in the stated range. Retain the minimum with all previous estimates elsewhere.

For the original row scale $U=U_j\ge1$, bounded $\mathcal P$ and the same original row-transform costs, sufficient conditions to pay this pole at $(UK)^\varepsilon UK$ are

$$
\boxed{N^2\le U,\qquad D\ge N^3H_0^4,
\qquad DN^9H_0^{12}\le U^2.}
\tag{C10}
$$

Indeed the pole factor is $U^{5/6}$; $N^2\le U$ pays $KN^{1/3}$, and division of the new term by $K$ leaves $D^{1/12}N^{3/4}H_0$, paid by the last condition.

At the original $t=1$ witness setting, write $D=U^r$, $N=U^m$ and $H_0\ll U^h$. Retain $r\le1$, $r+m\ge1$, $0\le m\le1/2$ and their original arbitrarily small losses. If $9m+12h<1$ with fixed reserve, then $r+9m+12h<2$, and $r>3m+4h$ follows from $r\ge1-m$ and $4h<(1-9m)/3$. Thus (C10) holds after absorbing the small losses. This includes a nonempty interval $0\le m<1/9$ at fixed height. The witness theorem does not guarantee that returned witnesses lie in this sector, and no length or shared height budget has been reset.

This source-conditional application pays the specified classwise all-column pure-sixth-power pole only on that sector. It supplies no bound for the remaining dual ideals, the earlier cross-class signed pole, all other witness sectors or signed same-integer Robin restoration. RH and the full Robin inequality remain unproved; no complete analytical Lean certification is claimed.

### Weighted interpolation before the ray-divisor sum

The two owned estimates for each actual scalar norm can be compared before summing the original ray divisors. This application reuses (C1)–(C2), (B5), the coefficient-uniform cubic core norm and the unrestricted pure-power shifted-integral bound. The elementary interpolation inequalities are used inside this consumer, without being claimed as new results.

A related conductor-aspect cubic application is [de Faveri, arXiv:2610.04045v1](https://arxiv.org/pdf/2610.04045v1), §8, Proposition 8.1 and equations (8.1)–(8.3). Its inner character index is squarefree, and the proof explicitly requires the transformed coefficients to be independent of the two variables combined into its new numerator. Remark 8.2 leaves the cube-free extension unworked because of root-number complications. That proposition is not a direct bound for the scalar vectors below; the present application uses the already matched inputs, with no literature-novelty claim.

#### Same scalar norm, two owned bounds

Fix an original core pair and its nonempty original factorizations:

$$
h=gcs_0z,\quad k=gc't_0w,\quad
a=a_ga_c,\quad b=b_gb_cs_0,\quad
g=a_gb_g,\quad c=a_cb_c.
$$

Keep $a_g=(a,\operatorname{rad}g)$, $a_c\mid\operatorname{rad}c$, and the original cross-core coprimality conditions. Put

$$
f_c=\operatorname{rad}(r_6(c)),\quad
u_c=q_{f_c}q_{s_0},\quad
f_0=f_cs_0f_{c'}t_0,\quad
R=\operatorname{rad}(gcc'S_0)/f_0,\quad
X=K/(q_gq_cq_{s_0}).
$$

For the same actual scalar vector $H_{c,r,e}^{a,b}$ at each $r\mid R$, write

$$
\mathscr R_{c,r}^{a,b}=\sum_e|H_{c,r,e}^{a,b}|^2.
$$

It may still depend on the opposite core; neither of the two estimates changes its coefficients. C2 gives, with the original profile norms,

$$
\mathscr R_{c,r}^{a,b}
\ll K^\epsilon q_\ell^\epsilon q_{f_0}q_{r_g}\mathcal L_c^2,
\quad
\mathcal L_c^2=X^{1/3}\frac N{q_b}
\left(\frac D{q_a}\right)^{1/2}\mathcal B^2.
\tag{D1}
$$

The coefficient-uniform cubic bound for that same vector is

$$
\mathscr R_{c,r}^{a,b}\ll K^\epsilon
\left\{X+X^{1/3}\left(\frac D{q_a}+\frac N{q_b}\right)\right\}\mathcal P^2.
\tag{D2}
$$

All $r$-twists, zero masks, finite class weights and orientations occur in the vectors before either estimate. In D1, zero-only support has already been removed by C1, at epsilon cost. D2 is uniform in these bounded coefficient weights. Fixed original bad-prime factors cost constants.

On a nonempty opposite factorization, $\operatorname{rad}c'\mid b_{c'}$ and

$$
q_{f_{c'}}q_{t_0}\le q_{b_{c'}}q_{t_0}
\ll N/q_{b_g'}\le CN.
$$

Thus $q_{f_0}\le CN u_c$, uniformly in the opposite core. Empty opposite ranges contribute zero. This is the same original $b'$-support argument as C4, without summing $r$ yet. Since $q_{r_g}\le q_r$, D1 permits the uniform host-core bound $q_r\mathcal A_c$ with

$$
\mathcal A_c=Nu_c\mathcal L_c^2.
$$

#### Compare before summing the ray divisors

Set the two positive numerical cubic components

$$
\mathcal E_c=\left(X+X^{1/3}\frac N{q_b}\right)\mathcal P^2,
\qquad
\mathcal J_c=X^{1/3}\frac D{q_a}\mathcal P^2.
$$

The elementary inequalities

$$
\min(A,E+J)\le E+\min(A,J),\qquad
\min(A,J)\le A^{2/3}J^{1/3}
$$

are applied inside the positive norm bound. They do not split or change the actual coefficient vector. Combining D1-D2, and retaining the original weight $q_r^{-5/6}$, gives

$$
\begin{aligned}
\sum_{r\mid R}q_r^{-5/6}\mathscr R_{c,r}^{a,b}
&\ll K^\epsilon q_\ell^\epsilon
\left\{\mathcal E_c\sum_{r\mid R}q_r^{-5/6}
+\mathcal A_c^{2/3}\mathcal J_c^{1/3}
\sum_{r\mid R}q_r^{-1/6}\right\}\\
&\ll K^\epsilon q_\ell^\epsilon
\left\{\mathcal E_c+\mathcal A_c^{2/3}\mathcal J_c^{1/3}\right\}.
\end{aligned}
\tag{D3}
$$

Both divisor sums cost epsilon, since $q_R\ll K^C$ for a fixed $C$; no sum over all ideals of exponent $1/6$ is claimed convergent. Auxiliary epsilon powers are allocated relative to one final epsilon. In particular D3 does not first pay the $q_g^{1/6}$ conductor cost in C3.

For each fixed core pair, Cauchy in the weighted $(r,e)$ Hilbert space bounds its original contraction by the product of these two root-norm envelopes. The envelopes are uniform in the opposite cores. One may then take absolute values and sum the core pairs using the own-core numerical envelopes. This does not give different opposite-core-dependent vectors a common realization.

#### Exact cancellation of the core weight

The interpolated square-root contribution in D3 equals

$$
\begin{aligned}
\mathcal A_c^{1/3}\mathcal J_c^{1/6}
={}&K^{1/6}D^{1/3}N^{2/3}
q_g^{-1/2}q_c^{-1/2}q_{s_0}^{-1/6}
q_{f_c}^{1/3}\mathcal B^{2/3}\mathcal P^{1/3}.
\end{aligned}
\tag{D4}
$$

Indeed the combined $a$ and $b$ factors each have exponent $-1/2$. Use $ab=gcs_0$ and $u_c=q_{f_c}q_{s_0}$. The existing outer core weight is exactly $w(c)=q_{f_c}^{-1/3}$, so it cancels $q_{f_c}^{1/3}$ in D4.

The remaining positive core sum has an epsilon bound:

$$
\sum_{\substack{c\ \mathrm{powerful}\\q_c\le CK}}
q_c^{-1/2}\tau(c)\ll_\epsilon K^\epsilon.
\tag{D5}
$$

Here $\tau(c)$ may be the ideal divisor function or a fixed divisor-bounded multiplicity covering the original $a_c$ choices. For any fixed $s>0$, its Rankin series has local first nonunit term $O(q_{\mathfrak p}^{-1-2s})$, since a powerful exponent is at least two, and hence converges. Take $s$ sufficiently small in terms of the final epsilon. The bounded choices of $s_0\mid\operatorname{rad}g$ and of the original squarefree distribution $a_g$ cost $q_g^\epsilon$. The negative $s_0$ factor is dropped only in this positive upper bound. All core supports may be enlarged here; the original supports were retained when deriving D1-D4.

Consequently, for fixed $g$, the summed interpolated root envelope is

$$
\ll K^\epsilon q_\ell^\epsilon
K^{1/6}D^{1/3}N^{2/3}q_g^{-1/2}
\mathcal B^{2/3}\mathcal P^{1/3}.
\tag{D6}
$$

Squaring and summing $q_g\ll K$ uses only $\sum_{q_g\ll K}q_g^{-1}\ll\log(2K)$, and yields $K^\epsilon D N^{5/3}\mathcal B^{4/3}\mathcal P^{2/3}$.

The two components of $\mathcal E_c$ are the unchanged cubic $X$ and $N/q_b$ components. Their existing core/gcd bounds give $K^{1+\epsilon}(1+N^{1/3})\mathcal P^2$. After fixed-pair Cauchy and the core sums, separate the three numerical root envelopes by $(x+y+z)^2\le3(x^2+y^2+z^2)$. This retains all cross terms, including interpolated/uninterpolated ones. The actual $z=w=1$ sector and its algebraically added counterpart keep the owned $O(K^{1+\epsilon})$ bounds. The original $q_\ell^{-5}$ sum absorbs the auxiliary $q_\ell^\epsilon$ uniformly in its cutoff. There is no split of the signed source moment by an unproved positivity claim.

#### Complete consumer and its original witness sector

These steps give the complete classwise all-column pure-sixth-power pole bound

$$
\boxed{
|\mathcal C^{a,\mathrm{all}}_{6,L}[c_j]|
\ll K^\epsilon\left\{
K(1+N^{1/3})\mathcal P^2
+D N^{5/3}\mathcal B^{4/3}\mathcal P^{2/3}
\right\}.
}
\tag{D7}
$$

It is uniform in $L$ and uses the original coefficients, nonsquarefree and mixed columns, common gcds, finite labels, zero masks and shared height. With $\mathcal B\le CH_0\mathcal P$, $H_0\ge1$, retain the minimum with all owned earlier bounds. The new term improves the old cubic $KD^{1/3}\mathcal P^2$ term when $D>N^2H_0^4$ with power reserve. Relative to the optimized C9 term, its ratio is $(H_0^4/K)^{1/12}$; hence it improves C9 in its useful range when that ratio has power room. No claim is made to improve every previous term at every length.

For the original row scale $U=U_j\ge1$ and bounded original $\mathcal P$, a sufficient payment condition is simply

$$
\boxed{N^4H_0^8\le U.}
\tag{D8}
$$

Indeed $N^{2/3}H_0^{4/3}\le U^{1/6}$ pays the new term after the original pole factor $U^{5/6}$; D8 also pays $N^{1/3}$ and $1$. There is no added $D$ constraint. For original $t=1$ witnesses with $N=U^m$ and $H_0\ll U^h$, fixed reserve in $4m+8h<1$ absorbs the original arbitrarily small losses. At fixed height this includes $0\le m<1/4$. No actual witness length or height has been reset, and the detector still does not guarantee that its returned witnesses occupy this sector.

The unrestricted pure-power shifted integral is already paid in the owning note at every $U_j,K\ge1$, and is reused directly. Combining that result with D7-D8 pays the complete specified pure-dual-sixth-power subterm on this wider sector, not the complementary dual ideals. Other witness sectors, the earlier cross-class signed pole and the signed same-integer Robin restoration remain open. This consumer is an application of owned analytical inputs; no complete Lean certification or literature-novelty claim is made.

### Complete squarefree pure-power consumer at the original witness lengths

The exact positive squarefree/nonsquarefree column partition, (C1)–(C2) and the per-ray comparison (D1)–(D3) give a stronger consumer for the already specified squarefree component. The application removes its former $D^{1/3}$ loss and covers every original witness length under the stated height reserve. The Gauss identities, angular moment, cubic sieve and interpolation inequality are reused; this is not a bound for the entire original signed contraction or a literature-novelty claim.

#### Exact squarefree source and absence of an extra core conductor

Use the original $c_j(h)=\omega_j(h)B_{D,N}(h)$, $K=DN$, original annular profiles, zero masks, physical labels and the finite primary class $a$. The already owned finite Cauchy partition is

$$
T_j\le2|\mathcal T|\sum_a
(\widetilde T^{\mathrm{sf}}_{j,a}+\widetilde T^{\mathrm{nsf}}_{j,a}).
$$

The object here is exactly $\mathcal C^{\mathrm{sf},a}_{6,L}[c_j]$, the specified pure-sixth-power pole extraction inside the first positive component. This does not assert a signed-pole inequality between the original extraction and the two projected extractions. The nonsquarefree component and its interactions in other formulations are not discarded.

For a squarefree column pair $h=gx,k=gy$, the ideals $g,x,y$ are squarefree and pairwise coprime. In the all-column decomposition this means

$$
c=c'=s_0=t_0=1,\qquad f_0=1,
\qquad R=\operatorname{rad}(gS_0).
$$

The primitive ratio conductor remains $xy$ and is not set to one. The original classwise root-number formula, reciprocity phase and $\gamma_{-1}(y)$ sign are unchanged. All $g\ell$ exclusions are zero-only and C1 handles them at epsilon cost. The ray-divisor twist has genuine conductor at most $Cq_{r_g}\le Cq_r$, for $r\mid R$. Unlike the general opposite-core bound $q_{f_0}\ll Nu_c$, this costs no factor $N$.

#### Same vector and the exact length-product identity

Distribute an actual factorization $dn=gx$ by $g=ab$ with $a=g_d,b=g_n$, retaining the squarefree constraints and original support. Put

$$
X=K/q_g,\qquad D_a=D/q_a,\qquad N_b=N/q_b,
\qquad D_aN_b=X.
\tag{E1}
$$

The original $e=e_de_n$ distribution and Gauss CRT are reused. Let $H^{a,b}_{g,r,e}$ be that same actual scalar vector, including its $r,\ell$ twists, finite ray filters and zero masks. The angular bound C2/B5 and the cubic bound give, respectively,

$$
\sum_e|H^{a,b}_{g,r,e}|^2
\ll K^\epsilon q_\ell^\epsilon q_r
X^{1/3}N_bD_a^{1/2}\mathcal B^2,
\tag{E2}
$$

$$
\sum_e|H^{a,b}_{g,r,e}|^2
\ll K^\epsilon
\{X+X^{1/3}(D_a+N_b)\}\mathcal P^2.
\tag{E3}
$$

They are bounds for the same coefficients; neither deletes a phase or uses monotonicity of absolute Dirichlet-series values. Empty original ranges contribute zero. The fixed original bad-prime factors are constants. Apply the already used comparison $\min(A,E+J)\le E+A^{2/3}J^{1/3}$ with $E=(X+X^{1/3}N_b)\mathcal P^2$ and $J=X^{1/3}D_a\mathcal P^2$. Keep the original $q_r^{-5/6}$ weight and use only the divisor products $\sum_{r\mid R}q_r^{-5/6},\sum_{r\mid R}q_r^{-1/6}\ll K^\epsilon$. E1 makes the interpolated energy exactly

$$
\left(X^{1/3}N_bD_a^{1/2}\mathcal B^2\right)^{2/3}
\left(X^{1/3}D_a\mathcal P^2\right)^{1/3}
=X\mathcal B^{4/3}\mathcal P^{2/3}.
$$

Consequently the weighted norm has the uniform numerical envelope

$$
\sum_{r\mid R}q_r^{-5/6}\sum_e|H^{a,b}_{g,r,e}|^2
\ll K^\epsilon q_\ell^\epsilon
\{X(\mathcal P^2+\mathcal B^{4/3}\mathcal P^{2/3})
+X^{1/3}N_b\mathcal P^2\}.
\tag{E4}
$$

The interpolated term has the same $X$ energy as the already paid cubic constant term. Its bound is independent of how the fixed squarefree $g$ is distributed between the original factors. This is where the joint length identity is consumed, rather than treating $D_a,N_b$ as independently attainable extrema.

#### Complete gcd, diagonal and row-cutoff accounting

Use the original fixed-pair Cauchy in weighted $(r,e)$, then the numerical root envelopes and divisor Cauchy over $a\mid g$. Cross terms between the $X$, interpolated and $N_b$ branches are kept by the same three-term numerical square inequality as D7. The divisor multiplicities cost $K^\epsilon$.

The $X$ and interpolated terms sum with

$$
\sum_{q_g\ll K}K/q_g\ll K\log(2K).
$$

For the $N_b$ term, retain $q_a\ll D,q_b\ll N$ and reuse the existing sum

$$
K^{1/3}N
\sum_{q_a\ll D}q_a^{-1/3}
\sum_b q_b^{-4/3}
\ll KN^{1/3}.
$$

Enlargement to all ideal pairs occurs only in these positive upper bounds. The actual $x=y=1$ principal diagonal and its algebraically added counterpart keep their owned $O(K^{1+\epsilon}\mathcal P^2)$ treatment. The original $q_\ell^{-5}$ factor absorbs $q_\ell^\epsilon$, uniformly in $L$. Whole-family conjugation handles the negative orientation. Thus the complete same squarefree-component pole satisfies

$$
\boxed{
|\mathcal C^{\mathrm{sf},a}_{6,L}[c_j]|
\ll K^{1+\epsilon}
\{(1+N^{1/3})\mathcal P^2
+\mathcal B^{4/3}\mathcal P^{2/3}\}.
}
\tag{E5}
$$

There is no upper length restriction on $D$, and every common gcd and original coefficient is retained. At bounded height, the former $KD^{1/3}$ term is replaced by $K$; the remaining $KN^{1/3}$ term is unchanged. This is an actual same-source consumer and can be combined with the prior full-column bounds where those are better.

#### All original witness lengths, with the original height reserve

Let $U=U_j\ge1$, $\mathcal B\le CH_0\mathcal P$, $H_0\ge1$, and bounded original $\mathcal P$. Sufficient conditions to pay the specified pole after its original $U^{5/6}$ factor are

$$
\boxed{N^2\le U,\qquad H_0^8\le U.}
\tag{E6}
$$

They give $N^{1/3},H_0^{4/3}\le U^{1/6}$. The original witness theorem already has $N=U^m$ with $0\le m\le1/2+O(\text{loss})$, for every permitted $t\in[1,3/2]$ and the actually returned $D$. Thus every original witness LENGTH is covered, including $m=1/2$, at $(UK)^\epsilon UK$ after assigning the original arbitrarily small losses relative to final epsilon. For height retain the original common cumulative allowance: fixed reserve $h<1/8$ in $H_0\ll U^h$ is sufficient. This does not claim coverage at arbitrary heights or give each polynomial a new height budget.

Reuse the owned unrestricted shifted-integral estimate, which also applies to this classwise squarefree component. Its sum with E5 pays the complete specified squarefree pure-dual-sixth-power subterm at all original witness lengths under E6 and its stated epsilon/height convention. It does not pay the nonsquarefree component or the complementary dual ideals, estimate the earlier cross-class signed pole, or restore the signed same-integer Robin target. The full RH and Robin objectives remain unchanged and unproved; no Lean certification or literature-novelty claim is made.

### A weighted powerful-part majorant for all original columns

This is a source-conditional application to the original complete positive moment, using the already owned E1-E6 consumer and unrestricted shifted integral. It is not a bound for the earlier signed all-column pole, a new sieve theorem, or a claim of literature priority. RH and strict Robin remain unproved. The point is to include all original nonsquarefree columns in a positive majorant whose specified pure-power pieces can collectively be paid at every original witness length.

Related prior work is [Xu–Sang, *A sharp lower bound for the sextic large sieve*, arXiv:2610.17675v1](https://arxiv.org/html/2610.17675v1), Lemma 4.1 and §5, equations (5.3)–(5.7). It controls moving exclusions and powerful components in the squarefree projection of a Gauss-sum witness for a lower operator bound. Its projected residual modulus is not required to be squarefree, and its specified Gauss coefficients differ from the Möbius-annular convolution below. Those statements are not substituted for this consumer. The already recorded [Liu source](liu2026quasirh.md), [v2, Lemma 9.1 and equations (9.1)–(9.2)](https://arxiv.org/html/2610.12234v2#S9.SS1), explicitly reuses the original source's Möbius moment: its auxiliary factors have prime supports, coefficients independent of the outer variable, and fixed positive length gaps. No identification of that family with an arbitrary two-factor convolution is assumed here.

#### Partition before Poisson, retaining the actual convolution

Use the same $T_j$, $U=U_j\ge1$, $K=DN$, original nonnegative row weight, good sixth-power-free physical rows, multiplicative column twists, zero extensions, finite labels, annular profiles and common cumulative height allowance. The original finite exceptional rows retain their existing treatment. Every column has the unique decomposition

$$
h=cx,\quad c\text{ powerful},\quad x\text{ squarefree},\quad(c,x)=1,
\qquad q_c\le C K.
\tag{F1}
$$

A powerful ideal has only prime exponents zero or at least two, including the unit. This is a decomposition of the columns before taking the squared norm, not of the primitive ratio after forming a pair.

For an actual original factorization $dn=cx$, the squarefreeness of $d$ gives uniquely

$$
a\mid\operatorname{rad}c,\quad b=c/a,\quad d=ad',\quad n=bn',
\qquad d'n'=x,\quad(d'n',c)=1.
$$

No coprimality of $a$ and $b$ is imposed: when $a$ contains a prime of $c$, that prime is still present in $b$. Set

$$
D_a=D/q_a,\quad N_b=N/q_b,\quad K_c=K/q_c,
\qquad D_aN_b=K_c.
\tag{F2}
$$

Multiplicativity gives $\mu(ad')=\mu(a)\mu(d')$ on this exact support. Thus, writing $\omega_j$ for the original fixed multiplicative column twist, the coefficients are exactly

$$
\begin{aligned}
c_j(cx)&=\omega_j(c)\sum_{a\mid\operatorname{rad}c}\mu(a)b_{j;c,a}(x),\\
b_{j;c,a}(x)&=\omega_j(x)\mathbf1_{x\ {\rm sf},\,(x,c)=1}
\sum_{d'n'=x}\mu(d')W_M(q_{d'}/D_a)W_S(q_{n'}/N_b).
\end{aligned}
\tag{F3}
$$

Use the already fixed finite-character expansion for any original finite labels; its number and constants are independent of $c$. At fixed $c$, a class condition on $cx$ is the corresponding transported class condition on $x$. Empty original ranges contribute zero. In every nonempty packet, the reduced lengths are bounded below by fixed positive annular constants; the existing estimates apply after fixed annular enlargement when a length is below one. In particular $K_c\gg1$ on these packets. No original witness has been shortened or reselected.

#### A positive majorant with no coupled core conductor

Choose $s=1/2+\eta$, $\eta>0$, depending only on the final error exponent. Reuse the powerful-ideal Rankin bound:

$$
Z_s=\sum_{c\ {\rm powerful}}q_c^{-s}<\infty.
$$

Weighted Cauchy in the column-core variable gives a factor $Z_s$ and weights $q_c^s$. The exact zero-extended multiplicativity $\chi_{cx}^{\rm raw}(v)=\chi_c^{\rm raw}(v)\chi_x^{\rm raw}(v)$ holds also on rows meeting $c$. For fixed $c$, $\chi_c^{\rm raw}(v)$ is common to every term. Its zero support is a row restriction. Remove it only by enlarging this positive row norm, using $|\chi_c^{\rm raw}(v)|\le1$. Do not delete a factor from an absolute Dirichlet-series value.

Next use finite Cauchy over $a\mid\operatorname{rad}c$ and over the original finite primary classes $\kappa\in\mathcal T$. Let $\widetilde T^{\rm sf}_{j;c,a,\kappa}$ be the resulting actual squarefree-column moment with coefficients $b_{j;c,a}$, class $\kappa$, the same physical rows and row cutoff, and the retained column mask $(x,c)=1$. These steps give

$$
T_j\ll Z_s|\mathcal T|
\sum_{\substack{c\ {\rm powerful}\\q_c\le CK}}
q_c^s\tau(\operatorname{rad}c)
\sum_{a\mid\operatorname{rad}c}\sum_{\kappa\in\mathcal T}
\widetilde T^{\rm sf}_{j;c,a,\kappa}.
\tag{F4}
$$

The fixed bound for $\omega_j(c)$ is absorbed in the original arithmetic datum; if its original divisor-bounded form is used instead, its arbitrarily small $q_c$ power is allocated to the final epsilon. All cross terms are retained by this positive inequality. No inequality between the original signed pole and the poles of the packets is asserted.

After this positive enlargement the common $c$ is absent from the character family. The sole moving-column restriction it leaves is $(x,c)=1$, a zero-only mask. Formula C1 handles this mask at $q_c^\delta$ cost for arbitrarily small $\delta>0$. It introduces no genuine character conductor or extra $N$ factor. Its total epsilon factor is bounded using the original $K$, since $q_c\le CK$; no uniformity in $c$ is inferred from a fixed-modulus constant. For squarefree packet pairs the primitive ratio conductor is still the product of the two coprime cofactors; it is not replaced by one.

#### Summing the specified pure-power terms over every core

Apply E1-E5 to each actual packet with lengths $(D_a,N_b)$, retaining its zero-only mask, class, common gcds, Gauss phases and every original coefficient. The scalar vectors are exactly those for that packet; no coherent vector across different $(c,a)$ is assumed. With the original uniform profile norms $\mathcal P,\mathcal B$, the specified pole contraction satisfies

$$
|\mathcal C^{\rm sf,\kappa}_{6,L}[b_{j;c,a}]|
\ll K^\delta K_c^{1+\delta}
\left\{(1+N_b^{1/3})\mathcal P^2
+\mathcal B^{4/3}\mathcal P^{2/3}\right\}.
\tag{F5}
$$

The auxiliary $\delta>0$ is chosen sufficiently small relative to the final epsilon. The global $K^\delta$ includes the zero-only $c$-mask and all original divisor multiplicities; constants have no further dependence on $c,a$ or $L$. The reduced profiles have the same normalized shape and derivatives as the originals. Original norm modulations contribute only unit-modulus fixed factors at $a,b$, so their heights and cumulative allowance are not renewed.

Because $N_b\le N$ and $\#\{a:a\mid\operatorname{rad}c\}=\tau(\operatorname{rad}c)$, the weighted sum of F5 has, apart from its displayed norms, the numerical upper bound

$$
\begin{aligned}
K^{1+2\delta}
\sum_{\substack{c\ {\rm powerful}\\q_c\le CK}}
\tau(c)^2q_c^{-1/2+\eta}
&\ll_{\eta,\delta,\delta'}K^{1+2\delta+\eta+\delta'}.
\end{aligned}
$$

Here the owned critical powerful-core estimate D5 is used with its divisor-bounded multiplicity; factor $q_c^\eta\le(CK)^\eta$ only in this positive upper bound. Allocate $\eta,\delta,\delta'$ relative to one final epsilon. The factor $Z_s$ may grow as epsilon tends to zero; it is a scale-independent constant, and no uniformity in epsilon is asserted. Consequently the weighted absolute sum of the specified pole contractions in the positive majorant F4 is

$$
\boxed{
\ll_\varepsilon K^{1+\varepsilon}
\left\{(1+N^{1/3})\mathcal P^2
+\mathcal B^{4/3}\mathcal P^{2/3}\right\}.
}
\tag{F6}
$$

This includes every original column, with no upper restriction on $D$. In particular it does not drop the nonsquarefree columns. The apparent loss from the number of powerful packets is absorbed at the critical half-norm exponent; counting packets without their $K_c$ scale would not give F6.

The actual principal diagonal of a squarefree packet costs $\ll U K^\delta K_c^{1+\delta}\mathcal P^2$ by the original row and divisor counts, so its weighted aggregate is $\ll(UK)^\varepsilon UK\mathcal P^2$ by the same sum. The algebraically added unit-bulk diagonals are already included in E5 and are not charged twice. The unrestricted pure-power shifted-integral bound applies to each packet at the same original $L_j$, uniformly at every $U,K_c\gg1$. Its $\ll(U K_c)^\delta U K_c$ bound sums by the same critical-core estimate to $\ll(UK)^\varepsilon UK$, with the original profile and cumulative-height costs. No new integral estimate is needed.

#### Original witness coverage and the remaining actual dual terms

For bounded original $\mathcal P$, $\mathcal B\le C H_0\mathcal P$ and $H_0\ge1$, the sufficient conditions remain

$$
\boxed{N^2\le U,\qquad H_0^8\le U.}
\tag{F7}
$$

Indeed $N_b\le N$ and the original pole factor is $U^{5/6}$. F6 then pays the collective specified poles at $(UK)^\varepsilon UK$. Together with the just reused shifted-integral bound and principal diagonal, the complete specified pure-dual-sixth-power pieces of the all-column positive majorant F4 are collectively paid. The original $0\le m\le1/2+O(\text{loss})$ for $N=U^m$ is covered, including the endpoint after allocation of the original arbitrarily small losses, for every permitted $t\in[1,3/2]$ and actually returned $D$. Fixed reserve $h<1/8$ in $H_0\ll U^h$ is sufficient for the original cumulative height requirement.

The majorant F4 still contains the original complementary dual ideals of each squarefree packet and any remaining terms of the source decomposition. They must be estimated with the same positive weights and the same actual profiles and row cutoff. This argument supplies no bound for their total, no estimate for the earlier signed all-column or cross-class pole, and no signed same-integer Robin restoration. It removes the separate nonsquarefree-column pure-power debt along this positive-majorant route; it does not prove a bound for the whole original positive moment or RH. No complete local Lean certification or literature-novelty claim is made.

### Actual Gauss compression on all original column packets

The applications below are conditional on the cited analytical inputs. The input for the actual adjoint is bramble_trace's manuscript [*Primitive sextic Kubota means and a sharp sixth-power-free large sieve*, paper 10/v2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download), Theorem 1, Corollary 5 and §§7–8. Its §8 leaves the actual Gram condition (8.1) as an explicit hypothesis. The application here supplies that condition on a growing ideal-label family and consumes the resulting correction in F4. It reuses the known character-sum and matrix estimates; no literature-priority or independent analytic Lean-certification claim is made.

#### The actual Gram, including all original zeros

Fix one original finite physical presentation, its row scale $U$, and its fixed smooth nonnegative nonzero annular row majorant $\Omega$. Retain the original fixed finite prime exclusions $S$; here “good” means prime to every finite prime in $S$, for rows and labels. A restricted physical row set is enlarged only inside its positive squared norm. Work in this good sixth-power-free ideal row space, with the original multiplicative primary representatives. For $L\ge1$, let $\mathcal R_L$ consist of distinct sixth-power-free **ideals** $R$ prime to $S$, with $q_R\le L$; unit representatives of the same ideal are not distinct labels. Put

$$
v_R(z)=U^{-1/2}\sqrt{\Omega(q_z/U)}\,
\gamma_1(z)\overline{\chi_z(R)}\,\mathbf1_{z\ {\rm squarefree}},
\qquad V=(v_R)_{R\in\mathcal R_L},\qquad G=V^*V.
\tag{G1}
$$

The same $V$ is used for every core packet in this presentation. Its zero extension on nonsquarefree rows embeds the vectors in the original larger row space. This auxiliary label cutoff $L$ is unrelated to the original row-Möbius cutoff $L_j=(b_\Omega U)^{1/6}$, which is unchanged. Since $|\gamma_1(z)|=1$ on squarefree good rows,

$$
G_{R,T}=U^{-1}\sum_{z\ {\rm good,sf}}
\Omega(q_z/U)\chi_z(R)\overline{\chi_z(T)}.
\tag{G2}
$$

Define

$$
C_\Omega=
\frac{\operatorname{Res}_{s=1}\zeta_F(s)}{\zeta_F(2)}
\int_0^\infty\Omega(y)\,dy
\prod_{\mathfrak p\in S}(1+q_{\mathfrak p}^{-1})^{-1}>0,
\qquad
d_R=C_\Omega\prod_{\mathfrak p\mid R}(1+q_{\mathfrak p}^{-1})^{-1},
\qquad D_L=\operatorname{diag}(d_R).
\tag{G3}
$$

Here $S$ in the product denotes its finite primes. The uniform estimate needed below is

$$
\boxed{\ \|G-D_L\|\ll_{\varepsilon,\Omega,S}
(UL)^\varepsilon U^{-1/2}L^{3/2}.\ }
\tag{G4}
$$

For its character-sum input, directly reuse [Lemke Oliver–Thorner, Appendix A to Pasten, *Shimura curves and the abc conjecture*, arXiv:1705.09251v4](https://arxiv.org/pdf/1705.09251v4), Lemma A.3. At its parameter $T=1$, over the fixed field $F$, it states for a possibly imprimitive finite Hecke character $\xi$ modulo $\mathfrak q$, with primitive conductor $\mathfrak f$,

$$
\sum_b\xi(b)\Omega(q_b/Y)
=\delta(\xi)\operatorname{Res}_{s=1}\zeta_F(s)
\frac{\varphi_F(\mathfrak q)}{q_{\mathfrak q}}
Y\int_0^\infty\Omega(y)\,dy
+O_{\varepsilon,\Omega}\!\left(
q_{\mathfrak f}^{1/4+\varepsilon}q_{\mathfrak q}^{\varepsilon}Y^{1/2}\right).
\tag{G5}
$$

A fixed finite partition of the annular profile puts it in that lemma's logarithmic support convention. Its imprimitive character is zero at every prime of $\mathfrak q$, including primes absent from $\mathfrak f$; those zeros are not deleted.

For $R\ne T$, reduce the good-prime exponents of $RT^5$ modulo six. Some exponent is nonzero because the labels are distinct sixth-power-free ideals. The ratio in G2 therefore has a nontrivial tame component at that good prime. Sextic reciprocity gives a finite Hecke character of trivial infinite type, with

$$
q_{\mathfrak f}\ll_S q_{\operatorname{rad}(RT)}\le L^2,
\qquad q_{\mathfrak q}\ll_S q_{\operatorname{rad}(RT)}\le L^2.
$$

The conductor and primary-convention facts are those of [Gao–Zhao, *Moments and One level density of sextic Hecke L-functions*, arXiv:2201.01885v2](https://arxiv.org/pdf/2201.01885v2), §§2.1, 3.1–3.2, including the conductor statement following (3.6). At a good prime the nonzero reduced exponent gives a nonprincipal local character of conductor exponent one. Changing between their multiplicative $E$-primary representatives and the chosen primary representatives contributes only the fixed bad-prime/unit characters. Such factors cannot cancel that good-prime component. Primes at which the exponents agree remain zero-only primes in $\mathfrak q$. Thus $\delta(\xi)=0$ in G5 for this ratio.

Expand $\mu^2(z)=\sum_{d^2\mid z}\mu(d)$, keeping the exact zero-extended character. Apply G5 at $Y=U/q_d^2$ to each inner sum. The error is bounded using $\sum_{q_d\ll\sqrt U}q_d^{-1}\ll\log(2U)$, and hence

$$
|G_{R,T}|\ll (UL)^\varepsilon U^{-1/2}
q_{\mathfrak f}^{1/4}
\ll (UL)^\varepsilon U^{-1/2}L^{1/2}\quad(R\ne T).
\tag{G6}
$$

For $R=T$, use the principal character with modulus supported on $SR$ in the same expansion. The main term is $d_R$: its local factor is $(1-q_{\mathfrak p}^{-1})/(1-q_{\mathfrak p}^{-2})$. The truncated main-term tail and G5 give $G_{R,R}=d_R+O((UL)^\varepsilon U^{-1/2})$. All modulus dependence is explicit in G5. There are $O_S(L)$ ideal labels, so the maximum absolute row sum proves G4.

Since $d_R\gg_\varepsilon L^{-\varepsilon}$, for fixed $0<\varkappa<1/3$, $L\le U^{1/3-\varkappa}$ and all sufficiently large $U$,

$$
G>0,\qquad \|G\|+\|G^{-1}\|\ll_{\varkappa,\varepsilon,\Omega,S}(UL)^\varepsilon.
\tag{G7}
$$

Choose the internal epsilon smaller than the fixed $\varkappa$ reserve before absorbing G4 in the smallest diagonal. The threshold depends on these fixed data. No invertibility assertion is made for a possibly empty bounded row annulus. This is a lower spectral estimate for the actual Gram, not an upper sieve bound used as a lower bound.

#### Actual adjoint, projection and coherent coefficients

Let $A_{U,X}$ have the same sixth-power-free rows, squarefree columns $q_n\asymp X$, and entries $\sqrt{\Omega(q_z/U)}\chi_n(z)$. All original finite column twists and the core mask stay in its actual column vector $b$. The negative orientation is treated by conjugating the whole family. The owned optimal sieve gives

$$
\|A_{U,X}\|^2\ll(UX)^\varepsilon\mathscr F_6(U,X),\qquad
\mathscr F_6(U,X)=U+X+U^{5/6}X^{1/3}+U^{1/3}X^{5/6}.
\tag{G8}
$$

Because $V$ is supported on squarefree rows, $A^*V$ is exactly the manuscript's §7 adjoint. The original fixed exclusions $S$ are covered by its stated fixed-extra-exclusion scope. Write $\rho_{\mathrm{prim},\nu;S}$ for the residue at $u=7/6$ of that primitive Gauss series with these same exclusions, and use the Mellin transform $\widehat\Omega(s)=\int_0^\infty\Omega(y)y^{s-1}\,dy$. Original column twists remain in $b$; they are not inserted as arbitrary row weights in that Gauss series. With precisely the manuscript's own fixed reciprocity section $\nu_{[n]}$, Corollary 5 gives

$$
\begin{aligned}
A^*V&=W+E,\\
W(n,R)&=U^{1/6}\widehat\Omega(2/3)
\rho_{\mathrm{prim},\nu_{[n]};S}(nR),\\
\|E\|^2&\le\|E\|_{\rm HS}^2
\ll(UXL)^\varepsilon X L^{3/2}.
\end{aligned}
\tag{G9}
$$

The sum over labels retains its cost $\sum_{q_R\le L}q_R^{1/2}\ll L^{3/2}$. Repeated factors in $nR$ are allowed by that corollary. No uniformity in a growing extra bad-prime conductor or infinity type is assumed.

By G7, $P=VG^{-1}V^*$ is the actual common row projection. Reuse the manuscript's §8 finite-matrix comparison, now with its Gram hypothesis supplied. With $T=A^*V$, $\|T\|\le\|A\|\sqrt{\|G\|}$ and $W=T-E$, it gives

$$
\begin{aligned}
\|A^*PA-WG^{-1}W^*\|
&\le\|G^{-1}\|(2\|T\|\|E\|+\|E\|^2)\\
&\ll(UXL)^\varepsilon
\left\{\sqrt{X\mathscr F_6(U,X)}L^{3/4}+XL^{3/2}\right\}.
\end{aligned}
\tag{G10}
$$

For the actual packet coefficients, define

$$
Q_P(b)=\|PAb\|^2,\qquad
Q_\rho(b)=(W^*b)^*G^{-1}(W^*b).
$$

Thus $|Q_P(b)-Q_\rho(b)|$ is at most the right side of G10 times $\|b\|^2$. Every coefficient and the cross-label couplings through $G^{-1}$ remain. This is a coherent quadratic-form estimate; a positive label average has not replaced a coherent sum. The primitive residues here are those of the manuscript's sextic Gauss series, not the earlier isolated $\zeta_F(6z)$ term in F5–F6.

#### Consumption with the same powerful-core weights

Use F4's actual vectors $b_{j;c,a,\kappa}$ at $X=K_c=K/q_c$, the same projection $P$, the same $\Omega,U$, the original row cutoff and cumulative height allowance. Reuse the already owned coefficient support and D5 critical powerful-core sum:

$$
\sum_{c,a,\kappa}q_c^{1/2+\eta}\tau(\operatorname{rad}c)
\|b_{j;c,a,\kappa}\|_2^2
\ll_\varepsilon K^{1+\varepsilon}\mathcal P^2.
$$

Indeed each coefficient norm costs $K^\delta K_c^{1+\delta}\mathcal P^2$ and the remaining numerical sum is the same $\sum_c\tau(c)^2q_c^{-1/2+\eta}$ as in F6. F4's $\eta$ and every auxiliary exponent are allocated within the final epsilon; an independently fixed positive $\eta$ is not discarded. Empty ranges vanish; nonempty bounded subunit scales use the existing fixed annular enlargement. No condition $(a,c/a)=1$ is introduced.

The bracket in G10 is nondecreasing in $X$. Multiply its actual-vector consequence by the same F4 weights and sum, obtaining

$$
\begin{aligned}
&\sum_{c,a,\kappa}q_c^{1/2+\eta}\tau(\operatorname{rad}c)
\left|Q_P(b_{j;c,a,\kappa})-Q_\rho(b_{j;c,a,\kappa})\right|\\
&\qquad\ll(UKL)^\varepsilon K\mathcal P^2
\left\{\sqrt{K\mathscr F_6(U,K)}L^{3/4}+KL^{3/2}\right\}.
\end{aligned}
\tag{G11}
$$

At $U\asymp K$, $L=K^{1/9-\varkappa}$, $0<\varkappa<1/9$, G7 has a fixed reserve and G11 is

$$
\ll K^{13/6-3\varkappa/4+\varepsilon}\mathcal P^2.
\tag{G12}
$$

Choose the final $\varepsilon<3\varkappa/4$. This saves a fixed power against the generic unnormalized $K^{13/6}$ positive-moment scale. It includes all original columns through F4, independently of the original $D/N$ ratio. It is not an error bound at the stronger $K^2$ consumer scale.

For each packet the exact remaining decomposition is

$$
\|Ab\|^2=Q_\rho(b)+\bigl(Q_P(b)-Q_\rho(b)\bigr)
+\|(I-P)Ab\|^2.
$$

The aggregate primitive-residue quadratic and the full orthogonal complement still require coefficient-sensitive upper bounds with the same weights. Positivity supplies no such upper bound. F6 pays a different isolated pure-power contraction and does not automatically pay either term here. This application controls an actual shared-row correction with its Gram hypothesis supplied; it does not bound the full F4 majorant, prove J, restore the signed Robin inequality, or prove RH.

### A prime-labelled residue cut for the original unsplit convolution

The [averaged Type-I manuscript, version 1](https://rstation.ai/api/v1/papers/riemann_hypothesis_8/versions/1/download), Theorem 1, estimates primitive sextic residues with squarefree outer modulus and unrestricted quotient. Its §8 already treats an unshifted Möbius/plain convolution. The application here retains a growing annulus of prime-ideal labels, including their overlaps with the Möbius variable. It uses the [primitive-mean manuscript, version 2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download), §7, for the exact adjoint. The applications below are conditional on the cited analytical inputs. They are paper derivations without local Lean certification or a literature-priority claim.

Work before F4, with the original unrestricted columns and one physical presentation:

$$
b(h)=\omega_j(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N),\qquad K=DN.
\tag{H1}
$$

All original exclusions and finite masks remain. Here $\omega_j(h)$ includes $\nu(h)\chi_h^{\rm raw}(\zeta\operatorname{gen}(s))^{\varepsilon_\chi}$ from the physical-label decomposition. Conjugate the whole family for negative orientation. This is a different exact projection decomposition of the original positive moment; F6's payments in its F4 majorant do not transfer to its complement.

#### Complete fixed filters and the residual section

Let $S_0$ be the primes above $2,3$, and let $Q$ be the product of the original fixed exclusions in $S\setminus S_0$. Choose a fixed modulus $B$, supported on the original $S$, detecting every original finite character, primary sector and common arithmetic mask. Reciprocity expresses $\chi_h^{\rm raw}(\zeta\operatorname{gen}(s))$ as a ray function of $h$: its good-prime conductor divides the support of $s$, and the supplementary factors belong to the fixed $S_0$ data. Those character values remain in $\omega_j$.

For the exact section $\nu_{[h]}$ of the primitive-mean manuscript's §7 and $p\nmid S$, define

$$
\phi_{p,j,\tau}(m)=
\overline{\omega_j(p^{-1}m)}
\mathbf1_{\nu_{[p^{-1}m]}=\tau}\mathbf1_{(m,S)=1}.
\tag{H2}
$$

Include all original fixed numerator masks in this function. The inverse is taken modulo $B$. Thus $p$ only permutes a fixed finite family of functions. If $B_{D,N}$ denotes H1's convolution without $\omega_j$, the actual pairing is exactly

$$
T_p=\sum_h b(h)\overline{\rho_{\mathrm{prim},\nu_{[h]};S}(ph)}
=\sum_{h,\tau}B_{D,N}(h)
\overline{\phi_{p,j,\tau}(ph)\rho_{\mathrm{prim},\tau;S}(ph)}.
\tag{H3}
$$

The Type-I manuscript's explicit numerator projector (6.6) assumes an $S_0$-supported modulus. The following fixed-level check supplies the broader filter in H2. First insert $\mathbf1_{(c,Q)=1}$ in its bottom-row Eisenstein section (2.1). On a deep fixed congruence subgroup, the bottom-row substitution preserves this support and the original ray weight because $c'\equiv c$ modulo the level. The same Kubota law therefore holds. This is a finite cusp Eisenstein combination, whose normalized residue $f_{\tau,Q}$ has Fourier coefficients

$$
t_{\tau,Q}(n)=q_n^{1/12}\rho_{\mathrm{full},\tau;S}(n).
$$

It is square-integrable, with cusp constants of exponent $5/6$ or zero. The fixed-form square-sum bound of that manuscript's Lemma 3 applies to its finite cusp components. Its unfiltered sixth-power step remains valid outside $S$: the vector is spherical there, and the fixed $Q$-place support requires only that the modulus be a unit, which local unit sixth powers preserve. The original $S_0$-place section has the same invariance. The manuscript's finite Gauss identity then gives

$$
\rho_{\mathrm{prim},\tau;S}(n)=w_S(n)\rho_{\mathrm{full},\tau;S}(n),
\qquad w_S(n)=\prod_{\substack{p\mid n\\p\notin S}}\frac{q_p}{q_p+1}.
\tag{H4}
$$

Only $n$ avoiding $S$ is needed. On that support, eliminating the finitely many $Q$-exclusions with the primitive-mean manuscript's (3.3) at $u=7/6$ gives denominators $1-q_p^{-2}$ and fixed numerator shifts. Gao–Zhao's Lemma 2.6 and the unexcluded primitive/full density therefore imply $\rho_{\mathrm{full},\tau;S}(n)\ll_{S,\varepsilon}q_n^{1/6+\varepsilon}$. No changing local conductor is used.

To impose a numerator function $\phi$ modulo $B$, put $T_a=\left(\begin{smallmatrix}1&a\\0&1\end{smallmatrix}\right)$ with $a=b/B$. For $\gamma=\left(\begin{smallmatrix}A&H\\C&D\end{smallmatrix}\right)$ in a sufficiently deep $\Gamma(M_0B^2)$,

$$
T_a\gamma T_a^{-1}
=\begin{pmatrix}A+aC&H+a(D-A)-a^2C\\C&D-aC\end{pmatrix}
\in\Gamma(M_0).
$$

Write $D'=D-bC/B$. At every good prime dividing $C$, one has $D'\equiv D$: at a prime dividing $B$, $v(C)\ge2v(B)$ ensures $v(C/B)\ge1$; elsewhere $B$ is a unit. Hence $D'\equiv D\pmod{\operatorname{rad}(C_{\rm good})}$. The sextic character with denominator $C_{\rm good}$ factors through this radical even for nonsquarefree $C$. Reciprocity now gives the same Kubota multiplier for $\gamma$ and $T_a\gamma T_a^{-1}$; their $S_0$ supplementary factors agree because both lower-right entries are $1$ at the fixed deep bad-place level. For $C=0$ both multipliers are $1$.

Consequently the exact finite Fourier projector

$$
\widehat\phi(b)=q_B^{-1}\sum_{u\bmod B}\phi(u)e(-ub/B),\qquad
f_{\tau,Q,\phi}(z,y)=\sum_{b\bmod B}\widehat\phi(b)f_{\tau,Q}(z+b/B,y)
$$

has coefficient $\phi(n)t_{\tau,Q}(n)$ and the same multiplier on one fixed subgroup. This retains all Fourier frequencies and zero values. Rational translation preserves the eigenvalue and square integrability on that fixed cover. Choose its level supported on $S$. Every outer modulus below avoids $S$, so the Type-I manuscript's §5 finite cusp calculation, Lemma 3 and Proposition 4 apply, including their finite reciprocity components and kernel. The additional fixed row exclusions do not increase its positive sieve norms. Filtration is applied after H4; no sixth-power invariance of $\phi$ is assumed.

#### The overlapping progression modulus

For a good sixth-power-free ideal $a$, allowing exponents $0,\ldots,5$, the same fixed-form calculation gives

$$
\begin{aligned}
&\sum_{a\mid n}\phi(n)\rho_{\mathrm{prim},\tau;S}(n)\mathcal W(q_n/Y)\\
&\quad=C_{\tau,Q,\phi}Z_SY^{5/6}\widehat{\mathcal W}(5/6)
\frac{v(\operatorname{rad}a)}{q_a}
+O_\varepsilon((Yq_a)^\varepsilon Y^{1/3}),
\end{aligned}
\tag{H5}
$$

where $Z_S=\prod_{p\notin S}(1-1/(q_p(q_p+1)))$ and $v(r)=\prod_{p\mid r}q_p^2/(q_p^2+q_p-1)$. Constants depend on the complete fixed data and finitely many profile seminorms.

Here is the additional modulus step. In the manuscript's (5.4)–(5.8), keep the full imprimitive $g_6(-n,r)$ for $r\mid a$, rather than its squarefree factorization. All CRT phases, $\chi_r(M)$, cusp coefficients and the Mellin kernel remain. For each nonunit sixth-power-free $r$, the character on units is nonprincipal, so only $r=1$ contributes a cusp constant. The prime-power Gauss formula gives

$$
|g_6(n,r)|\le q_r^{1/2}q_{(n,r)}^{1/2}.
$$

At exponent $1\le k\le5$ it is nonzero only when $v_p(n)=k-1$, with magnitude $q_p^{k-1/2}$. On a dual dyad of length $H$, Lemma 3 and $\sum q_{(n,r)}\ll_M H\tau(r)$ give the Cauchy bound $\ll(Hq_r)^\varepsilon q_r^{1/2}H$. The dual scale is $q_r^2/Y$; retain the residual kernel's small-argument cost $(q_r^2/(YH))^{1/12+\varepsilon}$ and arbitrary large-argument decay. Summing the dyads and $r\mid a$ yields

$$
\sum_{a\mid n}\phi(n)t_{\tau,Q}(n)\mathcal W(q_n/Y)
=\frac{C_f}{q_a}Y^{11/12}\widehat{\mathcal W}(11/12)
+O((Yq_a)^\varepsilon q_a^{1/2}).
$$

Remove $q_n^{1/12}$ through the profile. The full-residue error becomes $Y^{-1/12}q_a^{1/2}$. In H4 use $w_S=1*h_S$, where $h_S(p)=-1/(q_p+1)$, $h_S(p^k)=0$ for $k\ge2$. Its exact divisor expansion is

$$
\sum_{a\mid n}\phi(n)\rho_{\mathrm{prim},\tau;S}(n)\mathcal W(q_n/Y)
=w_S(a)\sum_{\substack{g\ {\rm squarefree}\\(g,aS)=1}}h_S(g)
\sum_{ag\mid n}\phi(n)\rho_{\mathrm{full},\tau;S}(n)\mathcal W(q_n/Y).
$$

For $q_g\le G$ the errors total $\ll(Yq_a)^\varepsilon Y^{-1/12}q_a^{1/2}G^{1/2}$. The complementary tail is $\ll Y^{7/6+\varepsilon}/(q_aG)$ by the point bound on $\phi$'s support. Choose $G=Y^{5/6}/q_a$ when this is at least $1$; the omitted main tail is smaller. For larger $q_a$, direct counting gives $Y^{7/6+\varepsilon}/q_a\le Y^{1/3+\varepsilon}$. The Euler main is $Z_Sv(\operatorname{rad}a)/q_a$, proving H5. The numerator function stays attached to $n$ throughout.

#### The actual prime-labelled quadratic

Take prime ideals $p\nmid S$ with $L\le q_p<2L$. Use G7 for their actual sub-Gram $G_P$ and the primitive-mean manuscript's §7 residue matrix $W_P$ on unrestricted columns. This unrestricted adjoint is already supplied there; no new generic norm statement is needed. Let $\mathcal N$ be a fixed finite seminorm envelope for the actual profiles, common Mellin-separation transforms and reciprocal-$L$ costs. It is not assumed bounded for all original growing-height profiles.

In H3 put $m=pdn$. If $p\nmid d$, the outer modulus $a=pd$ is squarefree. The fixed-form averaged estimate at $Y=q_pK$, $A=q_pD$, with coefficient norm $\ll D^{1/2+\varepsilon}\mathcal N$, has error $\ll(KL)^\varepsilon\mathcal N q_p^{1/2}K^{1/3}D^{2/3}$. If $d=pe$, Möbius support gives $(e,p)=1$; the outer modulus $p^2e$ is sixth-power-free. Applying H5 to each $e\asymp D/q_p$ costs $\ll(KL)^\varepsilon\mathcal N K^{1/3}Dq_p^{-2/3}$. Both branches preserve the original overlaps.

For the main terms use only the owned $B_0=7/8$ zero-free and reciprocal-strip inputs for fixed finite-order Hecke characters. For each such $\xi$,

$$
\sum_{(d,pS)=1}\frac{\mu(d)v(d)\xi(d)}{q_d}V(q_d/D)
\ll\mathcal N D^{B_0-1+\varepsilon}q_p^\varepsilon.
$$

Its Dirichlet series is $L(s,\xi)^{-1}$ times an Euler product normally convergent for $\Re s>0$, since $v(p)=1+O(q_p^{-1})$. Smooth Mellin inversion shifts to $B_0+\varepsilon$; the deleted $p$-factor costs a subpower. Retain all reciprocal-$L$/profile costs in $\mathcal N$. H2 gives only finitely many main constants, independent of $d,e$. The $d=pe$ main has an additional $q_p^{-B_0}$ and is absorbed. Thus, with $2L\le D$ up to fixed annular constants,

$$
|T_p|\ll(KL)^\varepsilon\mathcal N
\left(K^{5/6}D^{-1/8}q_p^{-1/6}
+K^{1/3}D^{2/3}q_p^{1/2}+K^{1/3}Dq_p^{-2/3}\right).
\tag{H6}
$$

The actual coherent quadratic is $Q_\rho^P(b)=(W_P^*b)^*G_P^{-1}(W_P^*b)$. G7 and ideal counting on the prime annulus give

$$
\begin{aligned}
Q_\rho^P(b)\ll&(UKL)^\varepsilon\mathcal N^2U^{1/3}
\left(K^{5/3}D^{-1/4}L^{2/3}
+K^{2/3}D^{4/3}L^2+K^{2/3}D^2L^{-1/3}\right).
\end{aligned}
\tag{H7}
$$

Indeed $\sum_pq_p^{-1/3}\ll L^{2/3}$, $\sum_pq_p\ll L^2$, and $\sum_pq_p^{-4/3}\ll L^{-1/3}$. The coherent $h$-sum in every $T_p$ has been estimated before this positive label sum. The cross-label matrix is controlled by the actual inverse Gram norm.

For $U\asymp K$, $L=K^\ell$, $0<\ell<1/9$, and

$$
K^{1/2}\le D\le K^{1/2}L^{1/6-\delta},\qquad0<\delta<1/6,
$$

G7 holds and H7 becomes

$$
Q_\rho^P(b)\ll K^{2-\zeta+\varepsilon}\mathcal N^2,\qquad
\zeta=\min\left\{\frac18-\frac{2\ell}3,
\frac13-\left(\frac{20}9-\frac{4\delta}3\right)\ell,
2\delta\ell\right\}>0.
\tag{H8}
$$

For bounded $\mathcal N$ and small enough $\varepsilon$, this pays the prime-labelled primitive-residue quadratic below $K^2$ on that original balanced sector. It does not pay the remainder pairing or projection replacement at $K^2$, the full projection energy, all labels, the complement, every original length or height, or F4's different squarefree-column quadratic. The original height reserve has not been certified for $\mathcal N$. Signed Robin restoration and RH remain open.

### An unchanged-numerator term in the primitive continuous adjoint

Reuse H1–H5, G7 and the two manuscripts cited above, with all original masks, ray sections and unrestricted columns. This is a `repo-derived` application of their local inversions and standard self-adjoint cusp spectral theory, conditional on the same analytical inputs. It gives no literature-priority or local Lean claim. Patterson's [Metaplectic forms and Gauss sums I, Theorem 5.1](https://www.numdam.org/item/CM_1987__62_3_343_0/) supplies qualitative continuation, not the quantitative coherent estimate used here.

Put $u=1+\eta+it$, $0<\eta<1/12$, and use the primitive-mean manuscript's raw full series $D_{\nu;S}(r,u)$ and primitive series $H_{\nu;S}(r,u)$. Define
$$
\lambda_q=q_q^{5-6u},\qquad \mathcal v_u(r)=\prod_{q\mid r,\ q\notin S}(1-\lambda_q)^{-1},\qquad
z_u(q)=\frac{\lambda_q}{1-\lambda_q},\quad z_u(q^k)=0\ (k\ge2).
\tag{I1}
$$
Extend $z_u$ multiplicatively. Thus $\mathcal v_u=1*z_u$, $|z_u(g)|\ll q_g^{-1-6\eta+\varepsilon}$ on squarefree $g$, and $\mathcal v_u$ is uniformly bounded. Apply the manuscript's §3 local inversions in a fixed order. At numerator valuation $1\le j\le4$ they read $D_{Qq,j}=(D_{Q,j}-a_jD_{Q,4-j}^{\nu\epsilon_{q,j}})/(1-\lambda_q)$, with the original $a_j=\nu(q)^{j+1}q_q^{j+1/2-(j+1)u}\gamma_{j+1}(q)\chi_q(k)^{-(j+1)}$ and reciprocity section. At $j=5$ only $D_{Q,5}/(1-\lambda_q)$ remains. At $j\ge6$, the Type-I manuscript's Lemma 2 in raw normalization is $D_Q(q^6n,u)=q_q^{6-6u}D_Q(n,u)+(1-\lambda_q)D_{Qq}(n,u)$, so $D_{Qq,j}=(D_{Q,j}-q_q^{6-6u}D_{Q,j-6})/(1-\lambda_q)$. Consequently
$$
H_{\nu;S}(r,u)=\mathcal v_u(r)D_{\nu;S}(r,u)+R_{\nu;S}(r,u).
\tag{I2}
$$
Here $R$ contains every nonempty second-choice branch of this specified finite recursion, with its changed numerator, phase, ray section and exclusions. No off-pole residue density or scalar sixth-power periodicity is used. With H1's actual $b$, define $C_p^0(t)=\sum_h b(h)\overline{\mathcal v_u(ph)D_{\nu_{[h]};S}(ph,u)}$. In the exact Mellin integral of the primitive-mean manuscript's §7 adjoint, this gives $E^*b=e^0+e^{\rm ref}$ without changing the row kernel; $e^{\rm ref}$ retains all of $R$.

#### Quantitative height control on the actual fixed cusp family

The unnormalized fixed-$Q$ sections and H2's rational numerator projectors have a common fixed group and finite unitary weight-zero Kubota multiplier. Its transformation law makes the multiplier a character. Pass to its finite-index kernel, intersect the finitely many required subgroups, and take a fixed torsion-free cover. The resulting finite-volume $X=\Gamma'\backslash\mathbb H^3$ is independent of $p,h,t$. The same finite bottom-row-orbit calculation as the Type-I manuscript's §2.1 identifies every actual section and rational translate as $\sum_j a_j(u)E_j(u)$, where $E_j$ has incoming term $y^u$ at cusp $j$. Each $a_j(u)$ is a finite sum of fixed constants times fixed positive scales to power $u$, hence bounded on this vertical line. This identifies the complete actual cusp family, not an unspecified full-series vector.

Use the nonnegative self-adjoint Laplacian $\Delta$. Its essential spectrum begins at $1$, and its spectrum below $1$ is discrete, with accumulation only at $1$. Choose $\eta$ in the required interval with $1-\eta^2\notin\operatorname{spec}\Delta$. Such choices exist arbitrarily close to zero; this is not a spectral-gap assumption or a numerical choice certificate. Constants may depend on this fixed $\eta$. For
$$
\Lambda(u)=u(2-u)=1-\eta^2+t^2-2i\eta t,
\qquad \|(\Delta-\Lambda(u))^{-1}\|\le(2\eta|t|)^{-1}\quad(|t|\ge1),
\tag{I3}
$$
the remaining compact $t$-range has bounded resolvent by the chosen spectral avoidance. Choose a fixed cusp cutoff $\chi$, put $P_j=\chi(y)y^u$ in cusp $j$, $F_j=(\Delta-\Lambda)P_j$, and $G_j=-(\Delta-\Lambda)^{-1}F_j$. The source $F_j$ has fixed compact annular support and $\|F_j\|_{H^m}\ll(1+|t|)^{m+1}$. Hence $\|G_j\|_2\ll1$. Recursion with $\Delta G_j=\Lambda G_j-F_j$ and global integration-by-parts/Bochner estimates on this complete constant-curvature quotient gives $\|G_j\|_{H^m}\ll(1+|t|)^{B_m}$ for each fixed $m$; no cusp injectivity-radius bound is needed. Prescribed incoming data and $L^2$ uniqueness first identify $E_j=P_j+G_j$ in the absolute half-plane and then by continuation on the chosen line.

At cusp $l$, the constant term of $G_j$ is $b_{jl}(u)y^{2-u}$, and its $L^2$ integral gives $|b_{jl}|^2\operatorname{area}_lY_0^{-2\eta}/(2\eta)\le\|G_j\|_2^2$. For its nonconstant part, horizontal Poincaré on the fixed period lattice gives $\|y^kG_j^\perp\|_2\le C_k\sum_{|\alpha|=k}\|(y\partial_x)^\alpha G_j\|_2\le C'_k\|G_j\|_{H^k}$. Thus all fixed polynomial cusp weights have polynomial $t$ cost. Normalize by the Type-I manuscript's exact $\mathcal A(u)=2\pi(c_*/2)^{u-1}/(V_0\Gamma(u))$. Stirling gives $|\mathcal A(u)|^{-2}\ll e^{-\pi|t|}(1+|t|)^{1+2\eta}$, so the squared compact, constant and weighted nonconstant norms of every actual normalized section have this exponential times a polynomial.

In Lemma 3's regularized Rankin identity subtract all four constant products, with exponents $2+2\eta,2-2\eta,2+2it,2-2it$, at every cusp. At fixed $2s_0>2+2\eta$, the test Eisenstein series has fixed polynomial cusp growth. The preceding weighted bounds control the full cusp differences and the constant products against the test series' nonconstant part. The compact integral and every truncation/scattering correction are also $\ll e^{-\pi|t|}(1+|t|)^B$: their cutoff is fixed and correction denominators have no poles to the right of $2+2\eta$. The positive Bessel Mellin factor is
$$
B_u(2s_0)=\frac{2^{2s_0-3}c_*^{-2s_0}}{\Gamma(2s_0)}
\Gamma(s_0+\eta)\Gamma(s_0-\eta)\Gamma(s_0+it)\Gamma(s_0-it).
$$
It is comparable to $e^{-\pi|t|}$ times a fixed power of $1+|t|$. The regularized identity is holomorphic for $\Re v>2+2\eta$; Parseval initially identifies a positive coefficient Dirichlet series with finite abscissa. Landau positivity therefore supplies convergence for $\Re s>1+\eta$. Dividing the complete transform by $B_u(2s_0)$, and taking $s_0=1+\eta+\varepsilon$, proves, for every actual fixed cusp component,
$$
\sum_{0<q_{n/M}\le H}|t_{u,k}(n/M)|^2\ll(1+|t|)^{B} H^{1+\eta+\varepsilon},
\qquad t_u(n)=q_n^{(u-1)/2}D_{\nu;S}(n,u).
\tag{I4}
$$
All constants depend only on fixed data, $\eta,\varepsilon$ and fixed seminorms. Fixed-$t$ convergence or formal Gamma cancellation alone would not supply I4.

#### Progression and Euler-denominator transport

Apply the Type-I manuscript's §§5–6 transform with I4, retaining both cusp exponents $u,2-u$. Let $\phi$ be any original H2 fixed numerator mask, $\mathcal W$ a smooth annular profile, and $\mathfrak M_a(Y)$ the unweighted main $q_a^{-1}\sum_{z\in\{1,2-u\}}C_z(u)Y^z\widehat{\mathcal W}(z)$. The same finite cusp family supplies its constants. For squarefree $a\asymp A\le Y$ the averaged unweighted error is
$$
\left|\sum_a\alpha_a\left(\sum_{a\mid n}\phi(n)D_{\nu;S}(n,u)\mathcal W(q_n/Y)-\mathfrak M_a(Y)\right)\right|
\ll(AY)^\varepsilon(1+|t|)^{B} Y^{5/12-\eta}A^{1/6+\eta}\|\alpha\|_2.
\tag{I5}
$$
Indeed the rightmost real kernel pole is $\eta/2$, the dual dyadic coefficient exponent is $7/12+\eta/2$, and the kernel cost is $(K_r/H)^{\eta/2+\varepsilon}$ with $K_r=q_r^2/Y$. Removing $q_n^{(u-1)/2}$ gives I5; Gamma-quotient bounds are polynomial jointly in transform height and $t$. For sixth-power-free $a$, the H5 imprimitive step instead has gcd-Cauchy bound $q_r^{1/2}H^{1+\eta/2}$ and gives pointwise unweighted error $\ll(Yq_a)^\varepsilon(1+|t|)^{B} Y^{-\eta}q_a^{1/2+\eta}$. Only $r=1$ contributes a cusp constant. Both small-height mains are retained; the large-height constants give the Gamma-cancelled poles.

Expand $\mathcal v_u(n)=\sum_{g\mid n}z_u(g)$ after the original filters. For squarefree $a$, split $g=eg_0$, $e\mid a$, $(g_0,a)=1$. The $e$-sum gives $\mathcal v_u(a)$; $ag_0$ remains squarefree. On $q_{g_0}\asymp G$ the aggregated coefficient norm is $\ll G^{-1/2-6\eta+\varepsilon}\|\alpha\|_2$ by divisor Cauchy and counting. I5 then costs $G^{-1/3-5\eta+\varepsilon}$, which is summable; $(A/Y)^\eta\le1$. Therefore the weighted averaged error is $\ll(AY)^\varepsilon(1+|t|)^{B} Y^{5/12}A^{1/6}\|\alpha\|_2$, and the main is
$$
\mathfrak M_a^{\rm wt}(Y)=\frac{v_u(\operatorname{rad}a)}{q_a}Z_u
\sum_{z\in\{1,2-u\}}C_z(u)Y^z\widehat{\mathcal W}(z),\quad
Z_u=\prod_{q\notin S}(1+z_u(q)/q_q),\quad
v_u(a)=\prod_{q\mid a}(1-\lambda_q+\lambda_q/q_q)^{-1}.
\tag{I6}
$$
The products and main tails converge uniformly in $t$ for fixed $\eta>0$. For sixth-power-free $a$, the small-$g$ pointwise error is $Y^{-\eta}q_a^{1/2+\eta}G^{1/2-5\eta+\varepsilon}$. The primitive-mean manuscript's full-series convexity bound $D_{\nu;S}(n,u)\ll(1+|t|)^{B}q_n^{1/4-\eta/2+\varepsilon}$ follows from its absolute line $3/2+\varepsilon$ and reflected line $1/2-\varepsilon$, including fixed-$Q$ components. It bounds the large-$g$ tail by $Y^{5/4-\eta/2+\varepsilon}/(q_aG^{1+6\eta})$. Set $G=Y^{5/6}/q_a$ when this is at least $1$. Both errors and main tails are $\ll(Yq_a)^\varepsilon(1+|t|)^{B}Y^{5/12+\eta}$. For $q_a>Y^{5/6}$, direct counting and the same point bound suffice on the nonempty annular support. Thus the pointwise weighted main I6 has this error for sixth-power-free $a$, without an arbitrary-modulus claim.

#### Consumption with the original prime-labelled vector

Let $\mathcal N_{\rm cont}$ be a fixed finite seminorm envelope for the original profiles, the Mellin integrals weighted by the polynomial powers just obtained, and the reciprocal-$L$ costs below. No original growing-height allowance is certified for this envelope. Apply H2–H3 at $m=pdn$. For $p\nmid d$, I6's averaged error uses $Y=q_pK$, $A=q_pD$, $\|\alpha\|_2\ll D^{1/2+\varepsilon}\mathcal N_{\rm cont}$, giving $K^{5/12}D^{2/3}q_p^{7/12}$. For $d=pe$, $(e,p)=1$, the outer $p^2e$ is sixth-power-free; the pointwise weighted error summed over $e\asymp D/q_p$ is $K^{5/12+\eta}Dq_p^{-7/12+\eta}$. All original overlaps are present.

The mains use the owned $B_0=7/8$ inputs for fixed finite-order Hecke characters, now with $\mu(d)v_u(d)\xi(d)/q_d$. The corresponding Dirichlet series is $L(s,\xi)^{-1}$ times an Euler product normally convergent on $\Re s>0$, uniformly in $t$, because $v_u(q)=1+O(q_q^{-1-6\eta})$. This half-plane suffices for the $B_0+\varepsilon$ shift; no convergence across $\Re s=0$ is asserted. The two constants depend on $u$ and the fixed $p$-class, not $d,e$. The $z=1$ main costs $KD^{-1/8}q_p^\varepsilon$; $z=2-u$ is smaller, and the $d=pe$ main has an extra $q_p^{-B_0}$. Consequently
$$
|C_p^0(t)|\ll(KL)^\varepsilon(1+|t|)^{B}\mathcal N_{\rm cont}
\left(KD^{-1/8}+K^{5/12}D^{2/3}q_p^{7/12}+K^{5/12+\eta}Dq_p^{-7/12+\eta}\right).
\tag{I7}
$$
Integrate against the actual adjoint's rapidly decreasing row Mellin profile, including $U^\eta$, and use G7 on the same prime sub-Gram. This yields
$$
\begin{aligned}
Q_{E0}:=(e^0)^*G_P^{-1}e^0\ll(UKL)^\varepsilon\mathcal N_{\rm cont}^2U^{2\eta}
\left(K^2D^{-1/4}L+K^{5/6}D^{4/3}L^{13/6}
+K^{5/6+2\eta}D^2L^{-1/6+2\eta}\right).
\end{aligned}
\tag{I8}
$$
On H8's same sector $U\asymp K$, $L=K^\ell$, $0<\ell<1/9$, $K^{1/2}\le D\le K^{1/2}L^{1/6-\delta}$, $0<\delta<1/6$, the reserves before the displayed $\eta$ losses are $1/8-\ell$, $1/2-(43/18-4\delta/3)\ell$, and $1/6-(1/6-2\delta)\ell$. The first is the smallest. Choose the spectrally permissible $0<\eta<(1/8-\ell)/32$. The losses are $2\eta,2\eta,(4+2\ell)\eta$, so
$$
Q_{E0}\ll K^{2-\zeta_0+\varepsilon}\mathcal N_{\rm cont}^2,\qquad
\zeta_0=(1/8-\ell)/2>0.
\tag{I9}
$$
For bounded profile envelopes and sufficiently small $\varepsilon$, H8 and I9 control the complete known vector $w+e^0$, where $w=W_P^*b$. The actual projection energy is still $\|G_P^{-1/2}(w+e^0+e^{\rm ref})\|_2^2$. H8 and I9 do not estimate the nonempty local branches, including their character phases and original coefficients. This is one complete exact primitive-inversion summand for unrestricted original $h$; it is not a bound for the whole projection or its complement. Other lengths/heights, F4 transfer, signed Robin restoration and RH remain open.

#### The labelled reflection with every numerator valuation

This `repo-derived` application uses I1–I9's analytical premises. Fix a good label $p$, put $Q=q_p$, and eliminate $p$ first. Select its second choice and the first choice at every other prime. For $ph=p^jm$, $p\nmid m$, $1\le j\le4$, the exact contribution is $C_{p,j}=-\sum_{p\nmid m}b(p^{j-1}m)\overline{\mathcal v_u(m)a_jD_{\nu\epsilon_{p,j};S}(p^{4-j}m,u)/(1-\lambda_p)}$, with I1's actual $a_j$, finite ray interchange and original $\nu_{[p^{j-1}m]}$ sector. At $j=5$ there is no second choice. The entire $j\ge6$ part is treated below. No squarefree surrogate for $h$ is used.

Split the original variables exactly as $d=p^ed_0$, $n=p^{j-1-e}n_0$, where $e=0,\ldots,\min(1,j-1)$ and $p\nmid d_0n_0$. The coefficient is $(-1)^e\mu(d_0)V(q_{d_0}/D_e)W(q_{n_0}/N_{j,e})$, with $D_e=D/Q^e$, $N_{j,e}=N/Q^{j-1-e}$ and $Y_j=K/Q^{j-1}$. Keep unfiltered $t_u(z)=q_z^{(u-1)/2}D_{\nu\epsilon;S}(z,u)$ distinct from the actual coefficient $\phi_j(z)t_u(z)$. Since $z=p^{4-j}m$, transport H2's mask by $h=p^{2j-5}z$ modulo $B$, including H1's physical mask, all section indicators, zeros and conjugation. The rescaled coefficient is $\chi_p(m)^{-(j+1)}\phi_j(p^{4-j}m)q_m^{(u-1)/2}D_{\nu\epsilon;S}(p^{4-j}m,u)$. Every cusp constant and $t_{[R]}$ below belongs to this filtered form; take the finite maximum over the actual ray permutations, including even $j$.

Put $s_j=4-j$, $b_j=5-j$ and $k_j=j+1$. Modulo $p^{b_j}$ let $\psi_{p,j}(z)=\mathbf1_{p^{s_j}\mid z}\chi_p(z/p^{s_j})^{-k_j}$ and $\tau_{p,j}=\sum_{a\bmod p}\chi_p(a)^{-k_j}e(-a/p)=\overline{g_{k_j}(1,p)}$. Then $\widehat\psi_{p,j}(v)=Q^{-b_j}\tau_{p,j}\chi_p(v)^{k_j}\mathbf1_{p\nmid v}$ and $\gamma_{k_j}(p)\tau_{p,j}=\sqrt Q$. This retains the odd-character sign when $j$ is even; for $j=1$, $\tau_{p,1}=g_4(1,p)$. Dunn–Radziwiłł's [Lemma 5.2 and Proposition 5.3](https://arxiv.org/html/2109.07463v3#S5) exhibit the unit-supported Fourier mechanism for cubic theta coefficients; their cubic residual estimate is not applied here.

For squarefree $(a,pS)=1$, average the actual filtered $f_j(v/p^{b_j}+b/a,y)$ with weights $q_a^{-1}\widehat\psi_{p,j}(v)$. Its multiplier is $\kappa^{-1}$ and Bessel order $u-1$. Reduce $b/a=h/r$, $r\mid a$, $(h,r)=1$, and put $R=p^{b_j}r$, $V=vr+hp^{b_j}\pmod R$. Lift $V\equiv1\pmod M$ and choose $d\equiv1\pmod M$, $Vd\equiv1\pmod{MR}$. The Type-I manuscript's (5.1)–(5.3) give multiplier $\chi_R(d)^{-1}$, height $1/(q_Ry)$ and $f_{j,[R]}=f_j\circ\sigma_R$, depending only on $R\bmod M$. Their matrix calculation needs no squarefreeness of $R$, so this is I4's fixed cusp family. In $\mathcal A_{p,j,r}(n)=\sum_{v,h}\widehat\psi_{p,j}(v)\chi_R(d)^{-1}e(-nd/(MR))$, the $p$-character cancels since $k_j+b_j=6$. CRT gives
$$
\mathcal A_{p,j,r}(n)=\frac{\tau_{p,j}}{Q^{b_j}}\chi_p(r)^{-k_j}e(-n\overline R/M)c_{p^{b_j}}(n)g_{\overline\chi_r}(-n\overline M\,\overline{p^{b_j}},r),\qquad c_{p^{b_j}}(p^{s_j}m)=Q^{b_j}(\mathbf1_{p\mid m}-Q^{-1}).\tag{I10}
$$
Here $\overline R$ is inverse modulo $M$, $\overline M$ inverse modulo $R$, and $\overline{p^{b_j}}$ inverse modulo $r$; the full finite Gauss sum is $1$ at $r=1$. The identity $c_{p^{b_j}}(n)=Q^{b_j}\mathbf1_{p^{b_j}\mid n}-Q^{b_j-1}\mathbf1_{p^{s_j}\mid n}$ retains every zero, ray phase and the mark's center.

Write the filtered average as $F_{p,j,a}(y)$. Its large-height constants vanish since $\sum_v\widehat\psi_{p,j}(v)=\psi_{p,j}(0)=0$. Including both small-height constants, its exact transformed identity is
$$
\begin{aligned}
F_{p,j,a}(y)={}&q_a^{-1}(C_{p,j,\rm in}y^{-u}+C_{p,j,\rm out}y^{u-2})\\
&+(q_ay)^{-1}\sum_{r\mid a}q_R^{-1}\sum_{n\ne0}\mathcal A_{p,j,r}(n)t_{j,[R]}(n/M)K_{u-1}\!\left(\frac{c_*|n/M|}{q_Ry}\right),\\
C_{p,j,\rm in}={}&\tau_{p,j}(1-Q^{-1})Q^{-b_ju}c_{j,[p^{b_j}],\rm in},\qquad C_{p,j,\rm out}=\tau_{p,j}(1-Q^{-1})Q^{b_ju-2b_j}c_{j,[p^{b_j}],\rm out}.
\end{aligned}\tag{I11}
$$
Only $r=1$ contributes constants, since $g_{\overline\chi_r}(0,r)=0$ otherwise. Mellin integration with $G_u(s)=2^{2s-2}c_*^{-2s}\Gamma(s+(u-1)/2)\Gamma(s-(u-1)/2)$ gives dual expression $q_a^{-1}\sum_{r\mid a}q_R^{1-2s}G_u(1-s)\sum_{n\ne0}\mathcal A_{p,j,r}(n)t_{j,[R]}(n/M)/q_{n/M}^{1-s}$, with both constant subtractions. I4–I5 justify continuation and smooth inversion. For $q_m\asymp Y$, the original Fourier scale is $X_j=Q^{s_j}Y$; the dual scale is $Q^{6-j}q_r^2/Y$ before reindexing and $Q^2q_r^2/Y$ after $n=p^{s_j}m$. The whole marked coefficient $t_{j,[p^{b_j}r]}(p^{s_j}m/M)$ remains in this equality.

Recover the $m$-coefficients by multiplying $F_{p,j,a}(y/Q^{s_j/2})$ by $Q^{s_j(1-u/2)}$. After the actual reflected scalar, the exact two cusp multipliers are $\nu(p)^{j+1}(1-Q^{-1})\lambda_p/(1-\lambda_p)$ and $\nu(p)^{j+1}(1-Q^{-1})Q^{j-1-ju}/(1-\lambda_p)$, with their actual finite ray components; retain the branch's minus sign and conjugation. Their polar functionals have sizes $Y$ and $Y^{2-u}$ and density $1/q_a$. Expand $\mathcal v_u(m)=\sum_{g\mid m}z_u(g)$ after the original filters, retaining the finite range $g\le CY$ in this sector. Both $g,d_0$ avoid $p$, and $a=\operatorname{lcm}(d_0,g)$ is squarefree. The split $g=eg_0$, $e\mid d_0$, $(g_0,d_0)=1$ gives $\sum_g|z_u(g)|/q_{\operatorname{lcm}(d_0,g)}\ll_\eta q_{d_0}^{-1}$ by a bounded local product and an absolutely convergent series. Both complete polar contributions are therefore $\ll(1+|t|)^B\mathcal N_{\rm all}Y/Q$ up to subpowers, using $\sum_{d_0\asymp D_e}|\mu(d_0)|/q_{d_0}\ll1$. No infinite main Euler product is substituted for these finite sums.

For the entire marked dual, I10 gives $|\mathcal A_{p,j,r}(n)|\le Q^{1/2}q_r^{1/2}$. I4 and Cauchy give $\sum_{q_{n/M}\asymp H}|t_{j,[R]}(n/M)|\ll(1+|t|)^BH^{1+\eta/2+\varepsilon}$. Smooth inversion has prefactor $X_jq_a^{-1}\sum_{r\mid a}q_R^{-1}$ and kernel argument $q_{n/M}X_j/q_R^2$. I5's kernel is $\ll(1+|t|)^Bx^{-\eta/2-\varepsilon}$ near zero and rapidly decreasing at infinity, with fixed profile derivatives. At $K_R=q_R^2/X_j$, summing all dual dyads gives $\ll(1+|t|)^BQ^{1/2}q_r^{1/2}K_R^{1+\eta/2+\varepsilon}$: below $K_R$ the dyadic bounds decrease geometrically with $H/K_R$, and above it rapid decay supplies geometric summability. This holds also for $K_R<1$ by the fixed fractional-lattice gap. Before removing Fourier normalization the bound is $\ll(X_jQq_a)^\varepsilon(1+|t|)^BX_j^{-\eta/2}Q^{b_j+1/2+b_j\eta}q_a^{1/2+\eta}$. Removing $q_z^{(u-1)/2}$ costs another $X_j^{-\eta/2}$; the actual reflected scalar has magnitude $\ll Q^{-1/2-(j+1)\eta}$. Thus
$$
\operatorname{Err}_{j,\rm unwt}(Y,a,p)\ll(YQq_a)^\varepsilon(1+|t|)^B Y^{-\eta}Q^{5-j-j\eta}q_a^{1/2+\eta}.\tag{I12}
$$
For the same finite Euler sum split at $G$. The small-$g$ error is $Y^{-\eta}Q^{5-j-j\eta}q_a^{1/2+\eta}G^{1/2-5\eta+\varepsilon}$. The split $g=eg_0$, $e\mid a$, retains the gcd factors, with bounded $e$-product at fixed $\eta$. I6's full-series convexity at $p^{4-j}m$, including the actual reflected scalar, bounds the large-$g$ original sum by $Q^{1/2-j/4-(3+j/2)\eta}Y^{5/4-\eta/2+\varepsilon}/(q_aG^{1+6\eta})$. The gcd sum costs only $q_a^\varepsilon$ since $|z_u(e)|q_e^{1+6\eta}\ll q_e^\varepsilon$. The omitted finite two-polar tail is $\ll Y(Qq_a)^{-1}G^{-1-6\eta}$ up to subpowers, smaller for $\eta<1/12$. Set $G=Y^{5/6}Q^{-3+j/2}/q_a$ when $G\ge1$. The errors are respectively $Y^{5/12-31\eta/6}Q^{7/2-3j/4+(15-7j/2)\eta}q_a^{6\eta}$ and $Y^{5/12-11\eta/2}Q^{7/2-3j/4+(15-7j/2)\eta}q_a^{6\eta}$. Use $q_a\ll Y$ on nonempty support; for $G<1$ direct counting of the whole branch and both polar terms at $q_a>Y^{5/6}Q^{-3+j/2}$ gives the same bound. Bounded subunit scales use the fixed annular enlargement. Consequently
$$
\operatorname{Err}_{j,\rm wt}(Y,a,p)\ll(YQq_a)^\varepsilon(1+|t|)^B Y^{5/12+\eta}Q^{7/2-3j/4+12\eta}.\tag{I13}
$$
Apply at $a=d_0,Y=Y_j$ in each exact original $e$-sector and sum $|\mu(d_0)|$ at cost $D_e$. With the finite polar terms and common smooth separation, let $\mathcal N_{\rm all}$ include the fixed finite profile/Mellin seminorms and polynomial height costs. Then
$$
|C_{p,j}(t)|\ll(KL)^\varepsilon(1+|t|)^B\mathcal N_{\rm all}\left(KQ^{-j}+K^{5/12+\eta}D Q^{47/12-7j/6+12\eta}\right),\qquad1\le j\le4.\tag{I14}
$$
To include every high valuation, use I1's raw sixth-step identity without reducing $j$ modulo six. On all $p^5\mid h$, put $h=p^5m$ with $m$ unrestricted at $p$. The entire $j\ge6$ contribution is exactly $C_{p,\ge6}=-\sum_m b(p^5m)\overline{Q^{6-6u}\mathcal v_u(pm)D_{\nu_{[p^5m]};S}(m,u)}$. Here $\mathcal v_u(pm)=(1-\lambda_p)^{-1}\sum_{g\mid m,\,p\nmid g}z_u(g)$, including when $p\mid m$; the $p$-denominator occurs once. This identity retains the phase of $Q^{6-6u}$ and leaves no high-valuation remainder.

Split the original variables as $d=p^ed_0$, $n=p^{5-e}n_0$, $e=0,1$, $p\nmid d_0$, with $n_0$ unrestricted at $p$. The coefficient is exactly $(-1)^e\mu(d_0)V(q_{d_0}/D_e)W(q_{n_0}/N_e)$, where $N_e=N/Q^{5-e}$, $D_e=D/Q^e$, $Y=K/Q^5$. Transport the original mask and section by $h=p^5m$; this is a fixed finite family. Reuse I5–I7 at $a=d_0,Y$, deleting $p$ from the finite $g$-sum and multiplying by $(1-\lambda_p)^{-1}$. Error coefficient norms only decrease. The main has $Z_u^{(p)}=\prod_{q\notin S,\,q\ne p}(1+z_u(q)/q_q)$ in place of $Z_u$, with $v_u(d_0)$ unchanged. I6's finite Euler and polar-tail errors justify this main expression. I7's fixed-character $B_0=7/8$ shift still applies after deleting $p$: the extra factor is bounded, independent of $d_0$. Both polar exponents remain. Each $e$-sector therefore costs $\ll(KL)^\varepsilon(1+|t|)^B\mathcal N_{\rm all}Q^{-6\eta}(YD_e^{-1/8}+Y^{5/12}D_e^{2/3})$. Their unweakened $Q$-powers are $-5+e/8$ and $-25/12-2e/3$, giving
$$
|C_{p,\ge6}(t)|\ll(KL)^\varepsilon(1+|t|)^B\mathcal N_{\rm all}\left(KD^{-1/8}Q^{-39/8}+K^{5/12}D^{2/3}Q^{-25/12}\right).\tag{I14a}
$$
Now $C_p^{\rm all}=\sum_{j=1}^4C_{p,j}+C_{p,\ge6}$ is the actual labelled second-choice/all-other-first contribution for every original $h$; $j=5$ contributes zero. The worst new low-valuation exponent is $19/12$ at $j=2$. I14a and all $j\ge2$ terms are dominated by the $j=1$ bound, so $|C_p^{\rm all}(t)|\ll(KL)^\varepsilon(1+|t|)^B\mathcal N_{\rm all}(K/Q+K^{5/12+\eta}DQ^{11/4+12\eta})$. Integrate with the original adjoint row Mellin profile, including $U^\eta$, and apply G7 on the same actual prime inverse Gram. Counting $L\le Q<2L$ yields
$$
Q_{\rm all}:=(e^{\rm all})^*G_P^{-1}e^{\rm all}\ll(UKL)^\varepsilon\mathcal N_{\rm all}^2U^{2\eta}\left(K^2L^{-1}+K^{5/6+2\eta}D^2L^{13/2+24\eta}\right).\tag{I15}
$$
Keep H8's original balanced sector $U\asymp K$, $K^{1/2}\le D\le K^{1/2}L^{1/6-\delta}$, $0<\delta<1/6$, and require $L=K^\ell$, $0<\ell<1/(41-12\delta)$. Then $N/Q^5\gg K^{1/2-(31/6-\delta)\ell}\to\infty$, so the rescaled high-tail lengths lie in the ranges used above; bounded nonempty cases use the fixed annular enlargement. Put $r_{\ell,\delta}=1/6-(41/6-2\delta)\ell>0$. This sector is inside H8's $\ell<1/9$ and includes $0<\ell<1/42$. Choose a spectrally permissible fixed $0<\eta<\min\{(1/8-\ell)/32,\ell/8,r_{\ell,\delta}/(8+48\ell)\}$. I15's reserves are $\ell-2\eta$ and $r_{\ell,\delta}-(4+24\ell)\eta$, so
$$
Q_{\rm all}\ll K^{2-\zeta_{\rm all}+\varepsilon}\mathcal N_{\rm all}^2,\qquad \zeta_{\rm all}=\min\{\ell/2,r_{\ell,\delta}/2\}>0.\tag{I16}
$$
For bounded explicit envelopes and small $\varepsilon$, H8, I9 and I16 control $w+e^0+e^{\rm all}$ below $K^2$. All label valuations are included only for this specified second-choice/all-other-first contribution. The local identities and the primitive-mean manuscript's §6 generic all-valuation mean are reused; that generic mean alone does not supply this original-coefficient consumer. The [structured angular manuscript, v3, §13](https://rstation.ai/api/v1/papers/riemann_hypothesis_5/versions/3/download) concerns a different marked theta inverse, whose estimate is not transferred. The [joint original-coefficient consumer](openai2026quasirh.md#coherent-simultaneous-high-valuation-branches) also sums every simultaneous high-valuation second-choice subset at other primes, with uniform growing arithmetic deletions. Its [composite marked extension](openai2026quasirh.md#coherent-valuation-four-and-high-branches) also includes every simultaneous original-valuation-four selection. The [joint powerful-prime consumer](openai2026quasirh.md#joint-control-of-all-powerful-prime-reflection-choices), on its stated smaller sector and bounded common costs, additionally sums every simultaneous original-valuation-two and -three choice. The [original-coefficient critical-band localization](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#454-原系数一重数反射的临界带定位), in its smaller sector and common-cost contract, additionally controls the P/S/O complement of the other-prime original-valuation-one choices, leaving its T band; the [conjugate-common refinement](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#455-临界反射族的共轭公共因子细分) controls every such mode with common-part norm above R1 under the same parameters, leaving exactly T_rat and a nonunit unpaired split core; whole projection/complement, other original lengths/heights, F4 transfer and signed Robin restoration remain unpaid. Outside the displayed sector I16 is not supplied. The original growing-height allowance is not certified for $\mathcal N_{\rm all}$. Neither RH, strict Robin, literature originality nor local Lean certification follows.

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

### A joint contour target above the sixth-power pole

The pure-power and complementary pieces should not be treated as two
independent positive terms when their only singularity is the extracted
$\zeta_F(6z)$ pole. For a fixed physical label and actual-order-six class,
write the unsplit finite kernel as

$$
\mathscr F_{j,a}(z)=
\sum_{(h,k)\in\Omega^a_{6,j}}
c_j(h)\overline{c_j(k)}B_{hk}(z)L(z,\overline{\xi_{hk}}).
$$

On the initial absolute-convergence line this is the same finite
Poisson expression as the sum of the pure sixth-power and complementary
parts. The latter has the opposite residue at $z=1/6$, so the combined
expression has no residue there. A contour stopped at

$$
\Re z=\frac16+\delta,\qquad \delta>0,
$$

would therefore avoid an artificial pole payment. This is an exact
rearrangement of the meromorphic expression, not a positivity argument.

The corresponding sufficient analytic input is a bound for the complete
kernel, with the original convolution coefficients and all masks retained:

$$
\boxed{
\int_{\mathbb R}|H_W(\tfrac16+\delta+it)|
\,|\mathscr F_{j,a}(\tfrac16+\delta+it)|\,dt
\ll_{\mathcal A,\delta,\varepsilon}
(U_jK)^\varepsilon U_j^{\delta+1/6}K.
}
\tag{J}
$$

Indeed, the outside factor is $U_j^{1-z}$, so (J) pays the joint
contour at the target scale $U_jK$ whenever the remaining length powers
are compatible with the detector's actual $(D,N)$ pair. At the balanced
case $U_j\asymp K$, the kernel target is of order
$K^{7/6+\delta}$.

This route has two precise boundaries. The absolute Rankin estimate in
this card uses the weight
$q_x^{-(1/2-\sigma)}$ and is proved only on
$0<\sigma<1/6$; it cannot be continued across the pole by simply
reusing its Euler-product convergence argument. Conversely, de Faveri's
large sieve at $n=6$ gives the right $K^{7/6+\varepsilon}$ scale for a
positive character moment at balanced lengths, but its stated theorem
does not directly estimate $\mathscr F_{j,a}$: after the finite theta
transform, a complementary dual prime leaves a moving quadratic twist
coupled to the cubic Gauss factor. In a local finite-field model the
resulting kernel changes from a Ramanujan distribution to a quadratic
Gauss distribution; its total squared energy is unchanged, but the
pointwise supplier is different.

Thus (J) is the smallest joint target for the contour-above-pole route.
It is not supplied by the existing positive-moment estimate, the
pure-power consumer, or the absolute shifted-integral estimate. A proof
of (J) would still need the detector's actual length coverage and the
final signed Robin restoration; neither follows from residue cancellation
alone. Until those steps are proved, the Robin and Riemann-hypothesis
conclusions remain open.

The later de Faveri--Dunn--Hoffstein paper records the relevant obstruction
from the other side: its cubic and quartic lower bounds show that the
corresponding character families are not perfectly orthogonal, and its
fixed-order conjecture predicts the $K^{7/6+o(1)}$ balanced scale for order
six. See the separate [non-orthogonality card](faveridunnhoffstein2026nonorthogonality.md).
Those results do not estimate (J), but they rule out replacing its complete
signed kernel by a diagonal orthogonality heuristic.

A closer lower-order precedent is Hamdar's cubic first-moment calculation:
at the cubic transition point, the principal cube term and infinitely many
dual cubic-Gauss residues cancel only after the two meromorphic pieces are
matched. See the separate [cubic cancellation card](hamdar2025cubicawaycentral.md).
That source also records why the transfer is currently blocked at order six:
the required higher-order Gauss-series residue formulas are not available.

The sextic-twist literature adds a second boundary condition: the full
composite-even family can mix unitary and orthogonal sectors, with a slower
Gauss-sum equidistribution rate than the totally sextic subfamily. See the
[sextic mixed-family card](bergryanyoung2023sextictwists.md). Thus a
quadratic--cubic factorization of (J) needs cross-sector estimates rather
than an independence assumption.
