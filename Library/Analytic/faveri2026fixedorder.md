---
bibkey: faveri2026fixedorder
authors: Alexandre de Faveri
year: 2026
title: Optimal large sieve for fixed order characters
doi: null
url: https://arxiv.org/abs/2610.04045v1
claim: Theorem 1.1 supplies a source-conditional mixed moment for the original common-character sextic detector, with sixth-power convolution masks retained; its generic count budget is dominated by existing legal detector settings, while the transported signed packet still has separate restoration obligations.
strata_touched: []
license: citation-only
triage: anchor
---

# Optimal large sieve for fixed order characters

The source is [arXiv:2610.04045v1](https://arxiv.org/pdf/2610.04045v1), submitted 2 October 2026. This card records Theorem 1.1, a conditional application to the original common-character detector, and the separate conditions relevant to the transported FIB sextic packet. The paper already supplies a zero-density estimate in Corollary 1.5. Neither the sieve nor the zero-density method is a project invention. The analytical source and the application have no independent local Lean certification; they do not establish a Robin or Riemann-hypothesis conclusion.

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
