---
bibkey: connesconsanimoscovici2024semilocal
authors: Alain Connes, Caterina Consani, and Henri Moscovici
year: 2024
title: Zeta zeros and prolate wave operators — semilocal adelic operators
doi: null
url: https://arxiv.org/abs/2310.18423v2
claim: The unsmoothed physical Euler-metric cross block is noncompact. The actual completion pays the archimedean reference trace; a localized Hardy estimate pays the geometric defect under an additional prime-growth condition. The original growing-place-set upper and full arithmetic comparison remain unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Dual semilocal transport and the signed trace interface

The inspected primary manuscript is [arXiv:2310.18423v2](https://arxiv.org/pdf/2310.18423v2), 4 May 2024, 30 pages, SHA-256 `8bc197642ee9ca4f2393b6cbfd3db292be6a315ce76ad61bfb845d9fedb47f2e`. The source results below are reused without reproving them, numerical reproduction, or new Lean declarations. Selected statement and proof inspection is not a complete proof audit.

## The two maps retain a joint relation

For a finite place set $S\ni\infty$, the source defines $H_\infty=L^2(\mathbb R)_{\rm ev}$ and $H_S=L^2(X_S)^{K_S}$ with its characters, Haar measures and unitary Mellin maps $U_\infty=\mathcal F_\mu w_\infty$ and $U_S=\mathcal F_\mu w_S$. The superscript denotes invariance under the source compact group, not a finite-dimensional approximation. Write $L_p(z)=(1-p^{-z})^{-1}$.

Proposition 4.1(i), equation (47), manuscript p.17, and Proposition 4.6(ii), equation (57), p.22, respectively give

$$
U_S\eta_S f(s)=
\prod_{p\in S\setminus\{\infty\}}L_p(1/2-is)\,U_\infty f(s),
$$

$$
U_S\theta_S f(s)=
\prod_{p\in S\setminus\{\infty\}}(1-p^{-1/2-is})\,U_\infty f(s).
$$

Proposition 4.7(iii), manuscript pp.22–23, states on the full even $L^2$ domain

$$
\langle\theta_S f,\eta_S g\rangle_{H_S}
=\langle f,g\rangle_{H_\infty}.
$$

This joint cancellation is stronger information than separate norm envelopes. Nonunitarity alone does not rule out a useful paired estimate. Conversely the displayed identity is a mixed pairing: it is not an assertion that either individual map preserves the norm or a positive quadratic form with an additional operator inserted.

## What is actually transported

Proposition 4.1(ii) and (iv) transports the support and Fourier-support cutoff **subspaces** under $\eta_S$. Proposition 4.7(i) intertwines $\theta_S$ with the physical Fourier transforms. Theorem 4.6, manuscript p.23, proves that

$$
\theta_S:\mathcal S_\lambda(\mathbb R,e_\infty)
\longrightarrow\mathcal S_\lambda(X_S,\alpha)
$$

is a bounded invertible Hilbertian isomorphism, where each Sonin space consists of physical functions vanishing, together with their Fourier transforms, on $\lvert x\rvert<\lambda$. These physical inputs are not arbitrary additive compact Weil tests. The theorem does not state that $\eta_S$ gives the same Sonin-space identification or that the isomorphism is unitary in the common unweighted norms.

Proposition 4.8 and §4.8, manuscript pp.23–24, identify the same entire-function vector space $B_\lambda$ under these maps. The paper explicitly records that $B_\lambda$ inherits **different inner products** from the embeddings for different $S$. An unchanged entire function therefore does not by itself retain its quadratic weight.

The grading obstruction is also explicit. Theorem 4.1(ii) transports the polynomial filtration, but Remark 4.2(i), manuscript p.19, states

$$
N_S\eta_S\ne\eta_SN_\infty\qquad(S\ne\{\infty\}).
$$

Its orthogonalization depends on $S$. Remark 4.2(iii), equation (50), also records

$$
\lvert\cdot\rvert_S^2\eta_S f
\ne\eta_S(\lvert\cdot\rvert^2 f).
$$

These are obstructions to those specified operator intertwinings. They do not refute RH or every possible joint transport estimate, and failure of the grading intertwining does not settle an alternative argument using only Sonin projections.

## The remaining comparison uses the same test and compression

The [archimedean source theorem](connesconsani2021archimedean.md) compares its Weil functional with a positive trace formed with an **orthogonal** Sonin projection. To transfer that proof one must account for the actual orthogonal projection in $H_S$, its $S$-dependent metric, and the resulting trace correction. An identification of subspaces or a dual bilinear identity is not the missing signed correction estimate. No claim that the projection cannot be transported is made here; its relevant comparison has not been obtained.

The target remains the project's [full common Weil form](frankliebseiringer2006hardy.md), including poles, prime powers and Gamma terms on one actual test. The maps above act on physical $L^2$ vectors; the multiplicative test used to integrate the scaling action is a different object. Applying $\theta_S$ to that test without a proved interface changes the problem.

A useful next supplier would preserve that same arithmetic form and bound the defect between it and the positive semilocal compressed trace, for a support family exhausting all admissible tests or for an already equivalent constrained criterion. The small prime-free archimedean bound, the source's operator candidate, and the [fixed-test trace remainder](connes1999trace.md) do not supply that defect bound. No actual full-Weil signed comparison or cofinal positivity has been established here; RH remains unproved.

## Orthogonal compression retains one joint metric defect

For the same physical cutoff $\lambda=1$ as the
[archimedean trace source](connesconsani2021archimedean.md), let $P$ be
its orthogonal Sonin projection and $\mathcal K=\operatorname{ran}P$.
Fix a finite $S\ni\infty$ and write $S_{\rm fin}=S\setminus\{\infty\}$.
Put $A=\theta_S$ and $Q_S=A^*A$ on $H_\infty$. Equations (47), (57)--(58) and the proof of Theorem 4.6
supply bounded invertibility on the full Hilbert spaces and
$\eta_S=(A^*)^{-1}$. In the source's common Mellin coordinates,

$$
Q_S=\prod_{p\in S_{\rm fin}}
\bigl[(1+p^{-1})I-p^{-1/2}(D(p)+D(p^{-1}))\bigr],
\qquad D(a)f(x)=a^{-1/2}f(x/a).
\tag{1}
$$

The source's character and half-density conventions are retained.
For this fixed finite set,
$m_SI\le Q_S\le M_SI$, where
$m_S=\prod_p(1-p^{-1/2})^2>0$ and
$M_S=\prod_p(1+p^{-1/2})^2$.
Thus $R_S=(P Q_S P)|_{\mathcal K}$ has a bounded inverse on
$\mathcal K$. Reuse the ordinary closed-range projection formula:

$$
P_S=A P R_S^{-1}P A^*.
\tag{2}
$$

Here $P_S$ is the actual orthogonal semilocal Sonin projection;
$P R_S^{-1}P$ means zero-extension from $\mathcal K$, not an inverse
on the whole physical space. The mixed pairing instead gives
$A P\eta_S^*=A P A^{-1}$, generally an oblique projection.

For a common $h\in C_c^\infty(\mathbb R_+^*)$, let $D(h)$ and
$D_S(h)$ integrate the respective unitary scaling actions with
$d^*a=da/a$. The multiplier formulas give
$D_S(h)A=A D(h)$ and $Q_SD(h)=D(h)Q_S$.
The whole operator $D(h)P$ is trace class: in the archimedean source,
Proposition 2.2(iii), equation (43) and its proof on manuscript p.14
supply $D(h)T$ as trace class; equation (81), pp.26--27, gives
$T=P+K$ with $K=\sum_n\lambda(n)^2|\zeta_n\rangle\langle\zeta_n|$
trace class by Remark 4.6(i). Hence $D(h)P=D(h)T-D(h)K$ is
trace class.
All fixed-$S$ factors in (2) are bounded, so trace cyclicity is legal
and gives the concrete same-test correspondence

$$
\begin{aligned}
\operatorname{Tr}(D_S(h)P_S)
&=\operatorname{Tr}(D(h)P)+\Delta_S(h),\\
\Delta_S(h)
&=\operatorname{Tr}_{\mathcal K}
\bigl[R_S^{-1}P Q_S(I-P)D(h)P\bigr].
\end{aligned}
\tag{3}
$$

These are applications of existing projection and trace results,
without a new generic projection theorem. No commutation of $P$ with
$Q_S$ or with $D(h)$ is assumed. The oblique compression has exactly
the archimedean trace by the mixed pairing; replacing it by $P_S$
retains $\Delta_S(h)$.

## The unsmoothed physical metric block is not compact

There is a concrete obstruction to estimating the two complementary
blocks separately in Hilbert--Schmidt norm. For the actual physical
projection and every nonempty finite $S_{\rm fin}$,

$$
\boxed{\|(I-P)Q_SP\|_{\rm ess}\ge
\left[\frac12\left\{
\prod_{p\in S_{\rm fin}}(1+4/p+1/p^2)
-\prod_{p\in S_{\rm fin}}(1+1/p)^2
\right\}\right]^{1/2}>0.}
\tag{4}
$$

The essential norm is distance in operator norm to the compact
operators. This is a paper application of the physical projection
and the specific finite Euler metric, with no literature-priority or
Lean-verification claim.

Expand (1) as $Q_S=\sum_{q\in\mathcal R_S}c_qD(q)$, where

$$
\mathcal R_S=\left\{\prod_{p\in S_{\rm fin}}p^{\epsilon_p}:
\epsilon_p\in\{-1,0,1\}\right\},\qquad
c_q=\prod_{\epsilon_p=0}(1+p^{-1})
\prod_{\epsilon_p\ne0}(-p^{-1/2}).
$$

Unique factorization makes these ratios distinct, and
$c_q=c_{q^{-1}}$. Choose a small interval $I\subset(1,\infty)$
such that all $qI$, $q\in\mathcal R_S$, are pairwise disjoint and
$qI\subset(0,1)$ for every $q<1$. This is possible because the ratio
set is finite and $\min_{q<1}q^{-1}>1$.
For a nonzero smooth $\phi$ compactly supported in $I$, take the even
physical vectors

$$
f_n(x)=c\bigl[\phi(x)e^{2\pi i n x}
+\phi(-x)e^{-2\pi i n x}\bigr],
\qquad \|f_n\|_{H_\infty}=1,
$$

where $c>0$ is independent of $n$. They are weakly null, and their
Fourier mass in every fixed bounded interval tends to zero.
For $q\ge1$, $D(q)f_n$ is still outside the physical cutoff and has
the same Fourier property. Write
$T=E\widehat E E$ for the archimedean source's two outside-cutoff
projections. Then $T D(q)f_n-D(q)f_n\to0$.
Equation (81)'s compact $T-P$ sends these weakly null sequences to
zero, proving

$$
(I-P)D(q)f_n\longrightarrow0\quad(q\ge1).
$$

For $q<1$, $D(q)f_n$ is supported inside the physical cutoff, so
$P D(q)f_n=0$ exactly. In particular $Pf_n-f_n\to0$ and boundedness
of $Q_S$ yields

$$
(I-P)Q_SP f_n
=\sum_{q<1}c_qD(q)f_n+o(1),\qquad
\|(I-P)Q_SP f_n\|^2\longrightarrow\sum_{q<1}c_q^2.
$$

Disjoint supports give the norm equality, while inversion symmetry
and the finite product expansion give

$$
\sum_{q<1}c_q^2
=\tfrac12\left\{\prod_p[(1+p^{-1})^2+2/p]
-\prod_p(1+p^{-1})^2\right\}.
$$

Every compact operator sends $f_n$ to zero in norm; this proves (4).
The weakly null unit vectors $Pf_n/\|Pf_n\|$ give the same lower
bound when the domain is restricted to $\mathcal K$.
For $S_{\rm fin}=\{p\}$ the test-sequence limit and lower bound
are $p^{-1/2}$; no equality for the essential norm is asserted.
Also $(I-P)Q_SP R_S^{-1/2}$ on $\mathcal K$ is not compact:
otherwise multiplication by bounded $R_S^{1/2}$ would make the
unnormalized block compact. In particular this normalized block is
not Hilbert--Schmidt.

The [quasi-inner compactness theorem](connesconsani2020quasiinner.md)
uses a different Hardy projection. It does not supply compactness for
this physical Sonin block. The sequence above depends on fixed $S$
and escapes to high physical Fourier frequency; it is not the actual
integrating test $h_X$. For smooth $h_X$, the complete joint block in
(3) remains trace class. Thus (4) refutes the separate unsmoothed
Hilbert--Schmidt premise, without precluding a small smoothed trace
or any alternative joint estimate.

For the [actual paid completion](../Estimation/trureturing2026pricegapconvexity.md#a-smooth-paid-completion-narrows-the-signed-local-correction-boundary),
$h_X(a)=H_X(\log a)$ with $H_X=c_X-F_X$, each $X$ and finite $S_X$
has the trace-class interface (3), even though its support grows.
No upper estimate for $\Delta_{S_X}(h_X)$ paying the original Robin
margin is obtained. The full pole,
finite-prime and archimedean comparison still requires a signed
estimate on this same test; (3)--(4) do not supply the original strict
Robin upper or a proof of RH.

## The actual completion pays the archimedean reference trace

Apply the [existing actual-test completion WT7--WT8](../Estimation/trureturing2026pricegapconvexity.md#a-smooth-paid-completion-narrows-the-signed-local-correction-boundary),
with its unchanged windows, horizon, smoothing and all maximizing ties.
Write $F=F_X$, $c=c_X$, $H=c-F$ and
$h_G(a)=G(\log a)$. Its estimates give
$\widehat c\ge|\widehat F|$, $\|c\|_1+\|F\|_1\ll_\tau L_X$ and
$|\mathcal A(c)|\ll_\tau L_XY_X^2=o(M_XL_X)$; MT5 also gives
$\mathcal A(F)=o(L_X)$.
The following is a repo-derived quantitative application of those
estimates and the source trace identity, not a new operator-order or
positivity theorem.

The archimedean source's equations (49)--(50), manuscript p.14,
and the asymptotic on p.16 make $\delta(a)$ bounded on
$\mathbb R_+^*$, including $a=1$ and the inverse tail. Equation (89),
p.28, and Remark 4.6(i) give

$$
|\epsilon(a)|\le \|\delta\|_\infty+\sum_n\lambda(n)^2
=:C_\epsilon<\infty.
$$

Here $\delta$ is the source's scalar trace-remainder function, not a
Robin margin. The matrix coefficients in (89) have absolute value at
most one by unitarity. Theorem 4.7, equations (83)--(84), therefore
bounds its exact correction by

$$
|E_\infty(h_G)|\le C_\epsilon\|G\|_1.
\tag{5}
$$

The source half-density convention is retained:
$W_\infty(h_G)=-\mathcal W_{\mathbb R}(a^{-1/2}G(\log a))
=\mathcal A(G)$; see Appendix A, equation (145).
Equation (5) applies directly to the actual growing-support $H$ and
gives $|E_\infty(h_H)|\ll_\tau L_X$.

For every finite $S\ni\infty$, including the archimedean case, the
common unitary scaling representation and the same Fourier majorant
give

$$
0\le D_S(h_H)\le2D_S(h_c).
\tag{6}
$$

Take traces of the positive compressions $P_SD_S(\cdot)P_S$;
(3)'s fixed-$S$ trace-class justification applies. In particular,

$$
\boxed{0\le\operatorname{Tr}(D(h_H)P)
=\mathcal A(c)-\mathcal A(F)+E_\infty(h_H)
\ll_\tau L_XY_X^2=o(M_XL_X).}
\tag{7}
$$

No small-support assertion for $H$ is used. Only the already
constructed $c$ has fixed small support.
Put $T_S(X)=\operatorname{Tr}(D_S(h_c)P_S)\ge0$.
The same positive order and the exact joint defect (3) imply

$$
\boxed{-O_\tau(L_XY_X^2)\le\Delta_S(h_H)\le2T_S(X).}
\tag{8}
$$

The lower-bound constant is independent of the finite prime set.
The upper-bound quantity is not yet controlled as that set grows.
In WT7's actual notation $c=\sum_{j\ge0}a_j\psi(2^j\cdot)$, all
$a_j$ and all Fourier transforms of these bumps are nonnegative.
Monotone convergence for positive compressed traces therefore gives

$$
T_S(X)=\sum_{j\ge0}a_jt_{S,j},\qquad
t_{S,j}:=\operatorname{Tr}
\bigl(D_S(h_{\psi(2^j\cdot)})P_S\bigr)\ge0.
\tag{9}
$$

All these tests have support inside the same prime-free additive
interval $(-\tau,\tau)$. A paid bound on the actual weighted sum in
(9) would control this geometric defect on the unchanged
large-support $H_X$. Bounds for each $j$ separately are only one
possible sufficient route. No estimate for that sum uniformly along
$S=S_X$ is supplied. Even such a geometric payment would still need
the same-test comparison with the complete arithmetic Weil form,
including its pole, finite-prime and Gamma corrections. Equations
(5)--(9) supply neither that comparison nor the original strict Robin
upper; no Lean verification is asserted.

## A localized Hardy estimate gives an explicit finite-place cost

Keep the physical cutoff $\lambda=1$, the actual orthogonal projection
$P_S$ of (2), and WT7's same nonnegative bumps
$\psi_j(x)=\psi(2^jx)$. The following is a repo-derived application
of the existing physical transport, Hardy commutator kernel and Gamma
estimates. The generic projection ordering and commutator are reused;
no literature-priority or Lean-verification claim is made.
The new quantitative interface is

$$
\boxed{t_{S,j}\ll_\psi 1+j+C_S,\qquad
C_S=\sum_{p\in S_{\rm fin}}\frac{\log p}{\sqrt p-1}.}
\tag{10}
$$

The implied constant is independent of the finite prime set and $j$.
This cost avoids the Euler condition-number product, but does not
replace $\sqrt p-1$ by $p-1$.

### Transport the actual subspace and keep the input weight

Use the unitary plus-sign logarithmic Mellin coordinates on
$L^2(\mathbb R,dt)$, so $D(a)$ is multiplication by $e^{it\log a}$.
Let $\Pi$ be the image of the physical outside-cutoff projection,
$H_+=\operatorname{ran}\Pi$ its upper Hardy space, and
$H_-=\operatorname{ran}(I-\Pi)$. For $Jg(t)=g(-t)$, the physical
even Fourier transform is $M_\rho J$, where

$$
\rho(t)=\pi^{-it}
\frac{\Gamma(1/4+it/2)}{\Gamma(1/4-it/2)},\qquad
\alpha_S(t)=\prod_{p\in S_{\rm fin}}
(1-p^{-1/2}e^{it\log p}),\qquad
W_S=\frac{\alpha_S}{\overline{\alpha_S}},\quad U_S=\rho W_S.
$$

These conventions are the reflected variable $t=-s$ of the source's
unitary Mellin transform. The [owned archimedean source](connesconsani2021archimedean.md),
Appendix D, Remark D.2 and Appendix E, equations (159)--(161),
manuscript pp.52--53, supply the Hardy projection, Gamma ratio and
Cauchy difference-quotient kernel. The semilocal source's equations
(57)--(58) and Theorem 4.6 supply the actual $\alpha_S$ transport.

For finite $S$, both $\alpha_S$ and its inverse preserve $H_+$,
while $\overline{\alpha_S}$ and its inverse preserve $H_-$.
Thus the Mellin image of the actual semilocal Sonin space is exactly

$$
\alpha_S(H_+\cap\rho H_-)=H_+\cap U_SH_-.
\tag{11}
$$

Write $\widetilde P_S$ for its orthogonal projection. This is a
unitary representation of (2), including its inverse compressed
metric, rather than the oblique projection $APA^{-1}$.
Set $\mathsf H_S=(I-\Pi)M_{\overline{U_S}}\Pi$. This contraction
is isometric on the intersection (11), so
$\widetilde P_S\le\mathsf H_S^*\mathsf H_S$.

With $\widehat\psi(t)=\int\psi(x)e^{-itx}dx$, the actual integrated
bump has multiplier
$w_j(t)=2^{-j}\widehat\psi(2^{-j}t)\ge0$; evenness removes the
Mellin sign change. The Cauchy commutator kernel gives

$$
\begin{aligned}
t_{S,j}
&=\operatorname{Tr}
(M_{\sqrt{w_j}}\widetilde P_SM_{\sqrt{w_j}})
\le\|\mathsf H_SM_{\sqrt{w_j}}\|_2^2\\
&\le\|[M_{\overline{U_S}},\Pi]M_{\sqrt{w_j}}\|_2^2\\
&=\frac1{4\pi^2}\int_{\mathbb R}\int_{\mathbb R}
w_j(s)\frac{|U_S(t)-U_S(s)|^2}{(t-s)^2}\,dt\,ds.
\end{aligned}
\tag{12}
$$

Indeed $\mathsf H_S=(I-\Pi)[M_{\overline{U_S}},\Pi]$.
There is no interchange of $\Pi$ with $M_{\sqrt{w_j}}$: the weight
in the squared kernel is on its input variable $s$. The finite
integral below justifies the localized Hilbert--Schmidt operator and
then the positive trace comparison. One may first use compactly
supported input vectors in the Cauchy kernel identity and extend by
the resulting Hilbert--Schmidt bound. The full commutator need not
be Hilbert--Schmidt; no unsmoothed dilation trace is used.

### Bound the localized kernel before summing the actual coefficients

Unimodularity gives
$|U_S(t)-U_S(s)|^2\le2|\rho(t)-\rho(s)|^2+
2|W_S(t)-W_S(s)|^2$. Logarithmic differentiation of the finite product
gives $\|W_S'\|_\infty\le2C_S$. For a unimodular
$L$-Lipschitz function $W$,

$$
\int_{\mathbb R}\frac{|W(s+h)-W(s)|^2}{h^2}\,dh
\le\int_{\mathbb R}\min(L^2,4/h^2)\,dh=8L.
$$

For the Gamma ratio,
$\rho'/\rho=i(\operatorname{Re}\operatorname{digamma}(1/4+it/2)-\log\pi)$.
The standard [digamma asymptotic](https://dlmf.nist.gov/5.11.E2)
and continuity on the remaining compact segment give
$|\rho'(t)|\ll\log(3+|t|)$. On $|h|\le1$ use
$L_s=C\log(3+|s|)$ and the amplitude cap together:

$$
\frac{|\rho(s+h)-\rho(s)|^2}{h^2}
\le\min(L_s^2,4/h^2).
$$

Its integral is at most $8L_s$; the part $|h|>1$ is at most $8$.
Consequently the full inner Gamma integral is
$O(\log(3+|s|))$, with one logarithm. Since $\widehat\psi$ is
nonnegative and Schwartz,

$$
\int w_j(t)dt=2\pi\psi(0),\qquad
\int w_j(t)\log(3+|t|)dt\ll_\psi1+j.
$$

Substitution in (12) proves (10). All estimates use the actual fixed
smooth frequency weight; no independent-prime or Bohr-mean
orthogonality is assumed.

Put $K_X=1+\log D_X$, with WT7's $D_X\ge2$.
Splitting its coefficient bound
$a_j\ll L_X\min(1,D_X2^{-j})$ at
$\lceil\log_2D_X\rceil$ gives
$\sum_j a_j\ll L_XK_X$, in addition to the already owned
$\sum_j(1+j)a_j\ll L_XK_X^2$.
The positive sum (9) therefore yields

$$
\boxed{T_S(X)\ll_\psi L_X(K_X^2+C_SK_X).}
\tag{13}
$$

For $S_{\rm fin}\subseteq\{p:p\le V\}$, the
[owned prime-count upper bound](../Arith/rosser1962approximate.md#global-prime-counts-and-the-classical-pnt-interface)
gives $\vartheta(v)\ll v$. Partial summation and
$(\sqrt p-1)^{-1}\ll p^{-1/2}$ give $C_S\ll\sqrt V$.
Since $K_X\ll Y_X$ and $Y_X^2/M_X\to0$ are already paid, (8) and
(13) pay the actual geometric defect whenever the additional condition

$$
\frac{C_SK_X}{M_X}\longrightarrow0
\qquad\text{holds; sufficiently,}\qquad
V=o\bigl((M_X/K_X)^2\bigr).
\tag{14}
$$

In this restricted regime $\Delta_S(h_H)=o(M_XL_X)$ for the same
$H_X=c_X-F_X$, original windows, ties and horizon. Restricting the
place growth is an additional hypothesis on this geometric estimate;
it is not a license to omit support-relevant primes from the original
arithmetic form. The original allowance
$\log V=O((\log X)^4)$ does not imply (14). Its weighted upper
bound remains unproved, as does the separate full same-test arithmetic
comparison. Equations (10)--(14) do not establish the original strict
Robin upper or RH.
