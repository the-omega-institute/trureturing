---
bibkey: connesconsanimoscovici2024semilocal
authors: Alain Connes, Caterina Consani, and Henri Moscovici
year: 2024
title: Zeta zeros and prolate wave operators — semilocal adelic operators
doi: null
url: https://arxiv.org/abs/2310.18423v2
claim: The actual all-primes orthogonal Sonin trace grows at least as sqrt(V)/log(V)^3 for a fixed bump. On the original qualifying cofinal family, the unchanged full-support completion has a geometric defect exceeding the Robin budget scale. The complete same-test arithmetic comparison remains unresolved.
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

### The squared-commutator majorant itself has a large prime cost

There is a separate limitation of the last member of (12). For the
actual all-primes family $S(V)=\{\infty\}\cup\{p:p\le V\}$, denote
that finite squared-kernel integral by $\Xi_{V,j}$. Then for all
sufficiently large $V$, uniformly in $j\ge0$,

$$
\boxed{\Xi_{V,j}\ge c_\psi 2^{-j}\frac{\sqrt V}{\log V}.}
\tag{15}
$$

This is a lower bound on the localized full commutator majorant,
not on $t_{S(V),j}$ or on its intermediate one-sided Hankel bound.

To check (15), write $W_{S(V)}=e^{i\Theta_V}$ with a smooth phase
on a neighborhood of zero. Put $r_p=p^{-1/2}$ and $\ell_p=\log p$.
The actual product gives

$$
-\Theta_V'(s)=2\sum_{p\le V}\ell_p
\frac{r_p\cos(s\ell_p)-r_p^2}
{1-2r_p\cos(s\ell_p)+r_p^2}.
$$

For $|s|\le(4\log V)^{-1}$, every cosine is at least
$\cos(1/4)>1/\sqrt2\ge r_p$. Thus every summand has the same
positive sign, and its ratio is bounded below by a fixed positive
constant times $r_p$. Reuse the
[owned dyadic prime count](../Arith/rosser1962approximate.md#dyadic-prime-count-lower-bound):
there are at least $3V/(10\log V)$ primes in $(V/2,V]$, each
contributing at least $\log(V/2)/\sqrt V$ to
$\sum\ell_p/\sqrt p$. Together with $C_{S(V)}\ll\sqrt V$ above,
this proves

$$
c\sqrt V\le-\Theta_V'(s)\le C\sqrt V
\qquad\bigl(|s|\le(4\log V)^{-1}\bigr)
$$

for fixed $c,C>0$ and sufficiently large $V$.
The phase derivative of $\rho$ is bounded near zero, so the same
two-sided bounds, after changing $c,C$, hold for minus the local
phase derivative of $U_{S(V)}=\rho W_{S(V)}$.

Choose a fixed $d>0$ with $2Cd<\pi/2$. For
$|s|\le(8\log V)^{-1}$ and
$d/\sqrt V\le h\le2d/\sqrt V$, the entire segment $[s,s+h]$
lies in the preceding derivative range once $V$ is sufficiently large.
The absolute phase increment lies in $[cd,2Cd]$, so
$|U_{S(V)}(s+h)-U_{S(V)}(s)|^2$ is bounded below by a fixed
positive constant. Also
$w_j(s)\ge2^{-j}\widehat\psi(0)/2$ on this $s$ interval,
uniformly in $j\ge0$ and sufficiently large $V$; here
$\widehat\psi(0)>0$ and continuity suffice.
Integrate just this rectangle in the nonnegative integral (12).
Its $s$ length is $1/(4\log V)$ and
$\int_{d/\sqrt V}^{2d/\sqrt V}h^{-2}dh=\sqrt V/(2d)$,
which proves (15).

Consequently this particular full-commutator majorant cannot have a
uniform polynomial-in-$\log V$ cost, even for $j=0$ and the same
fixed bump. Its upper bound (10) is not being contradicted: (15)
places a smaller lower bound on the larger comparison object.
Improving the actual projection estimate can still use information
lost in $\widetilde P_S\le\mathsf H_S^*\mathsf H_S$ or in the
second inequality of (12). No reversal of either inequality, lower
bound on the true trace, or obstruction to RH follows.


### The one-sided Hankel majorant retains the large cost

Keeping the middle member of (12) also loses too much for a uniform
polynomial-in-$\log V$ estimate. The following application uses the
actual WT7 factor $\psi=u*u^*$ and the already obtained (15);
the pair-of-projections algebra and Schwartz commutator theorem are
reused. It is a repo-derived paper calculation, without a new generic
operator theorem, literature-priority claim or Lean verification.

For $v_j(t)=2^{-j/2}\widehat u(2^{-j}t)$, one has
$|v_j|^2=w_j$. Multiplication by $v_j$ or by $\sqrt{w_j}$ gives
the same squared Hilbert--Schmidt norm: the two multipliers differ
by a measurable unitary multiplier. Write

$$
\begin{gathered}
\mathsf G_S=\Pi M_{\overline{U_S}}(I-\Pi),\qquad
D_S=\Pi-M_{U_S}\Pi M_{\overline{U_S}},\\
B_{S,j}=\|\mathsf H_SM_{v_j}\|_2^2,\qquad
B^{\rm op}_{S,j}=\|\mathsf G_SM_{v_j}\|_2^2.
\end{gathered}
$$

Let $\Xi_{S,j}$ denote the last integral of (12) for a general
finite $S$. The two off-diagonal blocks have orthogonal output
ranges. Ordinary projection algebra gives

$$
\mathsf H_S^*\mathsf H_S+\mathsf G_S^*\mathsf G_S=D_S^2,
\qquad
\mathsf H_S^*\mathsf H_S-\mathsf G_S^*\mathsf G_S
=\operatorname{diag}_{\Pi}(D_S),
$$

where $\operatorname{diag}_{\Pi}(T)=\Pi T\Pi+(I-\Pi)T(I-\Pi)$.
In particular $B_{S,j}+B^{\rm op}_{S,j}=\Xi_{S,j}$.
The weighted difference requires a localization correction; one
cannot commute the multiplier past $\Pi$.

The owned archimedean source, Appendix D, Lemma D.1, manuscript
pp.51--52, makes $[\Pi,M_f]$ trace class for Schwartz $f$.
For each fixed finite $S$, $U_S$ and all its derivatives have at
most polynomial growth: finite Euler factors and their reciprocals
have bounded derivatives, and the Gamma ratio has polynomial
derivative bounds. Consequently $\overline{v_j}U_S$ is Schwartz.
Put $V_j=M_{v_j}$. The exact decomposition

$$
V_j^*D_SV_j
=[M_{\overline{v_j}},\Pi]M_{v_j}
-[M_{\overline{v_j}U_S},\Pi]M_{\overline{U_S}v_j}
$$

therefore proves that the sandwich is trace class. These fixed-$S$
trace-class assertions do not claim a uniform trace-norm bound in
$S$. Its full localized difference-quotient kernel is Schwartz, so
the diagonal trace formula, with the convention of (11)--(12), gives

$$
d_{S,j}:=\operatorname{Tr}(V_j^*D_SV_j)
=\frac1{2\pi}\int_{\mathbb R}w_j(t)
\frac{U_S'(t)}{iU_S(t)}\,dt.
$$

This is the reflected normalization of the source's Appendix E,
equations (161)--(163), manuscript p.53. The plus sign can also be
checked with $U(t)=e^{iat}$, $a>0$: then $D$ is the positive
projection onto the logarithmic physical strip $[0,a)$.
For the actual finite Euler product,

$$
\frac{W_S'(t)}{iW_S(t)}
=-2\sum_{p\in S_{\rm fin}}\log p
\sum_{k\ge1}p^{-k/2}\cos(kt\log p).
$$

The inner derivative series is absolutely uniformly convergent for
each finite $S$. Every Euler term integrates to zero, since

$$
\int w_j(t)\cos(kt\log p)\,dt
=2\pi\psi_j(k\log p)=0,
\qquad k\log p\ge\log2>\tau2^{-j}.
$$

Thus $d_{S,j}=d_j$ is independent of $S$, with

$$
d_j=\frac1{2\pi}\int w_j(t)
\bigl[\operatorname{Re}\operatorname{digamma}(1/4+it/2)
-\log\pi\bigr]dt,\qquad |d_j|\ll_\psi1+j.
$$

This cancellation uses the actual prime-free bump, rather than an
independent-prime average. To compare it with the weighted block
difference, put $R=2\Pi-I$ and $C_j=[\Pi,V_j]$. Direct algebra gives

$$
V_j^*\operatorname{diag}_{\Pi}(D_S)V_j
-\operatorname{diag}_{\Pi}(V_j^*D_SV_j)
=C_j^*D_SRV_j+RV_j^*D_SC_j.
$$

All traces here are now legal. A difference of orthogonal
projections has $\|D_S\|\le1$, so the trace error is at most
$2\|v_j\|_\infty\|C_j\|_1$. Positive dilations commute with the
Hardy projection, and hence
$\|C_j\|_1=2^{-j/2}\|[\Pi,M_{\widehat u}]\|_1$ and
$\|v_j\|_\infty=2^{-j/2}\|\widehat u\|_\infty$.
Consequently, uniformly over finite $S$ and $j\ge0$,

$$
\boxed{2B_{S,j}=\Xi_{S,j}+d_j+e_{S,j},\qquad
|e_{S,j}|\le C_u2^{-j}.}
\tag{16}
$$

Combining (16) with the existing (15), for all sufficiently large
$V$ and uniformly $j\ge0$, gives

$$
\boxed{B_{S(V),j}\ge
c_\psi2^{-j}\frac{\sqrt V}{\log V}-C_{u,\psi}(1+j).}
\tag{17}
$$

In particular $B_{S(V),0}\ge c_\psi\sqrt V/\log V-O_{u,\psi}(1)$.
Thus a uniform polynomial-in-$\log V$ estimate for this one-sided
majorant is also excluded. This does not lower-bound
$t_{S(V),j}$: the true orthogonal projection retains only the
singular-value-one subspace of $\mathsf H_S$, whereas
$\mathsf H_S^*\mathsf H_S$ also charges fractional principal-angle
channels. Nor is a lower bound on the actual completion sum asserted
without a lower bound on its actual coefficients. The original
growing-place-set projection estimate and full same-test arithmetic
comparison remain unresolved; (16)--(17) do not prove or refute RH.


## Actual Euler-weighted Sonin vectors give a true trace lower bound

The all-primes family admits a lower bound for the actual orthogonal
projection, independently of the comparison majorants in (15)--(17).
Keep exactly (11)'s physical cutoff, common unitary Mellin coordinates
and WT7's fixed bump. For $S(V)=\{\infty\}\cup\{p:p\le V\}$, put
$\ell=\log V$ and $N_V=\lfloor\sqrt V/\ell^3\rfloor$. The
source-specific paper application below gives constants $c_\psi>0$
and $V_0$ such that

$$
\boxed{t_{S(V),j}\ge c_\psi2^{-j}
\frac{\sqrt V}{(\log V)^3}
\qquad(V\ge V_0,\ j\ge0).}
\tag{18}
$$

This uses actual trial vectors in $\alpha_{S(V)}\mathcal K$, not a
lower bound transferred from $\mathsf H_S^*\mathsf H_S$. Burnol's
Sonin existence and analytic continuation, the owned bump decay,
the complete smooth explicit formula, the classical zero-free
region, and standard polynomial inequalities are reused. This is
an application on the present operators, without a new generic
concentration theorem, literature-priority claim or Lean verification.

### A fixed actual Sonin vector supplies every polynomial direction

Use [Burnol's source](burnol2002sonine.md), printed p.690, section 2
and Theorem 1: $K_\lambda$ is nonzero for every $\lambda>0$, and
its uncompleted Mellin transforms have entire representatives.
Fix $\lambda>1$ and a nonzero physical $G\in K_\lambda$; write
$g$ for its unitary plus-sign Mellin image. Choose a nonzero even
rescaling $h$ of the [owned Tlas bump](tlas2020bump.md#match-the-function-and-fourier-convention),
supported in $(-r,r)$ with $0<r<\log\lambda$. The owned absolute
Fourier envelope gives

$$
|\widehat h(t)|\le C e^{-c\sqrt{|t|}}\qquad(t\in\mathbb R).
$$

Let $f_0=\widehat h\,g$. The physical vector with this Mellin
image is the Bochner integral $\int h(x)D(e^x)G\,dx$; evenness of
$h$ removes the Fourier sign change. Both gaps of every integrand
have radius at least $\lambda e^{-r}>1$. The closedness of the
physical $K_1$ therefore puts $f_0$ in its Mellin image
$\mathcal K$. The same integral with $h^{(k)}$ has Mellin image
$(-it)^kf_0$, by integration by parts. Thus

$$
t^kf_0\in\mathcal K\quad(k\ge0),\qquad
\int |t|^{2k}|f_0(t)|^2dt\le A B^{2k}(k!)^4.
\tag{19}
$$

The moment bound follows by taking the supremum of
$|t|^{2k}e^{-2c\sqrt{|t|}}$ and using $g\in L^2$; all constants
are fixed before $V$. The entire $\widehat h$ has a discrete real
zero set, so $f_0\ne0$. Burnol's analytic continuation supplies an
analytic representative at zero. It has some finite order $m\ge0$,
and hence $|f_0(t)|\ge c_0|t|^m$ on a fixed neighborhood of zero.
No nonvanishing value at zero is assumed.

### The actual finite Euler product has a peak and an away envelope

Write

$$
E_V=\sum_{p\le V}p^{-1/2}\sim\frac{2\sqrt V}{\ell},\qquad
\alpha_V(t)=\prod_{p\le V}(1-p^{-1/2}e^{it\log p}).
$$

The ordinary PNT follows from the
[owned Johnston--Yang input](johnstonyang2022pnt.md). Expansion of
the logarithm, absolutely for every finite product, gives uniformly
in real $t$

$$
\log|\alpha_V(t)|
=-\operatorname{Re}\sum_{p\le V}p^{-1/2+it}
+O(\log\ell),\qquad
\log|\alpha_V(t)|\le E_V.
$$

The last bound also follows directly from $\log(1+r)\le r$.
Fix $b>0$ and set
$I_V=[\pi/\ell-b/\ell^2,\pi/\ell+b/\ell^2]$.
For $t\in I_V$,

$$
|t\log p-\pi|^2\ll_b
\ell^{-2}\bigl(1+\log^2(V/p)\bigr),\qquad
\sum_{p\le V}\frac{\log^2(V/p)}{\sqrt p}\ll E_V.
$$

For the second estimate, split at $\sqrt V$. The smaller primes
cost $O(V^{1/4}\ell^2)=o(E_V)$; Chebyshev's upper prime count and
partial summation on the remaining range give $O(\sqrt V/\ell)$.
Since $\cos(\pi+u)\le-1+u^2/2$, this proves

$$
\inf_{t\in I_V}\log|\alpha_V(t)|
\ge E_V-O_b(E_V/\ell^2)-O(\log\ell).
\tag{20}
$$

The required uniform upper envelope away from zero is also supplied
by existing analytic inputs. For every fixed $\varepsilon>0$ and
$C>0$, there is $\delta_\varepsilon>0$ such that, eventually,

$$
\log|\alpha_V(t)|\le(1-\delta_\varepsilon)E_V
\qquad(\varepsilon\le|t|\le V^C).
\tag{21}
$$

Here is the parameter correspondence, including the large-height
uniformity. Put $q_\varepsilon=(1+4\varepsilon^2)^{-1/2}<1$.
Choose fixed $0<c<1$ and $0\le\phi\le1$ in
$C_c^\infty((c,1))$ so that

$$
r_\phi=\int_0^1(1-\phi(u))u^{-1/2}du
\le(1-q_\varepsilon)/4.
$$

Apply the [owned complete smooth explicit formula](connesconsani2021archimedean.md),
Appendix B, equations (147)--(150), manuscript p.50, to the actual
auxiliary test

$$
f_{V,t}(x)=\frac{x^{-1/2+it}\phi(x/V)}{\log x}.
$$

It is compact smooth on $\mathbb R_+^*$ once $cV>1$. Its prime
term is $S_\phi(V,t)=\sum_{p\le V}p^{-1/2+it}\phi(p/V)$ plus
the complete higher-power sum, whose absolute value is
$O(\log\ell)$. Its main pole contribution is

$$
\frac{V^{1/2+it}}{\ell}
\left(\int_0^1\phi(u)u^{-1/2+it}du+O_\phi(\ell^{-1})\right).
$$

The other pole and archimedean contributions are
$O_\phi(V^{-1/2}/\ell)$, uniformly in $t$. For every nontrivial
zero $\rho=\beta+i\gamma$, integration by parts in $\log u$
gives, for each fixed integer $A\ge2$,

$$
|\widetilde f_{V,t}(\rho)|
\le C_{\phi,A}\frac{V^{\beta-1/2}}{\ell}
(1+|\gamma+t|)^{-A}.
$$

The amplitude derivatives are uniform for $0\le\beta\le1$; the
large frequency is $\gamma+t$, not a derivative loss of size $t$.
Reuse the [already owned Vinogradov--Korobov region](../ArithSums/nicolas2025comparison.md#a-smaller-moving-cut-from-joint-density-and-zero-free-support),
Johnston--Yang Lemma 2.10, printed p.6, from
[Ford's Theorem 5](https://arxiv.org/pdf/1910.08205v1), p.4. With
$T=2V^C$, the zeros of $|\gamma|\le T$ have

$$
\beta\le1-\eta_T,\qquad
\eta_T\gg_C\ell^{-2/3}(\log\ell)^{-1/3}.
$$

The finite low zeros are included by decreasing $\eta_T$.
The owned unit-height multiplicity count
$N(u+1)-N(u)=O(\log(3+|u|))$ bounds the sum of the decay factors
by $O_C(\ell)$, uniformly for $|t|\le V^C$. Thus the complete
near-zero sum is

$$
O_{\phi,C}\!\left(\sqrt V
e^{-c_C\ell^{1/3}/(\log\ell)^{1/3}}\right)=o(E_V).
$$

Zeros near $-t$ are retained. For $|\gamma|>T$,
$|\gamma+t|\ge|\gamma|/2$ and $\beta\le1$ give a far-zero
cost $O_{\phi,A,C}(\sqrt V\,T^{1-A}\log T/\ell)=o(E_V)$.
Both signs and actual multiplicities remain. This splits an
absolutely convergent complete smooth zero sum; it invokes no
truncated formula at an inadmissible height. Consequently

$$
S_\phi(V,t)=\frac{V^{1/2+it}}{\ell}
\int_0^1\phi(u)u^{-1/2+it}du+o_{\phi,C}(E_V)
\quad(|t|\le V^C).
$$

Ordinary fixed-amplitude PNT bounds the positive omitted prime
mass by $(r_\phi+o(1))\sqrt V/\ell$, for every $t$.
Since $\int_0^1u^{-1/2+it}du=(1/2+it)^{-1}$, these two
approximation errors give

$$
\frac{\left|\sum_{p\le V}p^{-1/2+it}\right|}{E_V}
\le(1+4t^2)^{-1/2}+r_\phi+o_{\phi,C}(1).
$$

Equation (21) follows with, for example,
$\delta_\varepsilon=(1-q_\varepsilon)/4$. Constants and the
starting threshold may depend on fixed $C$ and $\varepsilon$.
Ordinary PNT has only been used on fixed amplitudes, not
differentiated with a frequency as large as $V^C$.

### Uniform concentration includes arbitrary polynomial cancellations

Choose fixed $\varepsilon>0$ so that
$\widehat\psi(t)\ge\widehat\psi(0)/2>0$ for $|t|\le\varepsilon$,
and use (21) at this same $\varepsilon$ with $C=4$.
Consider the actual subspace

$$
\mathcal E_V=\{\alpha_Vf_0P:\deg P<N_V\}
\subseteq\alpha_V\mathcal K=\operatorname{ran}\widetilde P_{S(V)}.
$$

Membership follows from (19). The map from polynomials is injective,
since $\alpha_V$ has no real zeros and $f_0$ is nonzero on $I_V$
for large $V$. Hence $\dim\mathcal E_V=N_V$.
For $n=N_V-1$, $a=b/\ell^2$ and
$H_P=\int_{I_V}|P(t)|^2dt$, the standard interval
$L^2$-to-sup polynomial estimate and Chebyshev extrapolation give

$$
|P(t)|^2\le\frac{N_V^2}{2a}
\left(\frac{4(1+|t|)}a\right)^{2n}H_P
\qquad(t\in\mathbb R).
\tag{22}
$$

These inequalities apply to complex polynomials as well, by taking
a phase-adjusted real part at the evaluation point. Normalizing
by $H_P$ controls arbitrary coefficients and zeros in the shrinking
peak interval; no well-conditioned monomial Gram matrix is assumed.
The local finite-order bound for $f_0$ and (20) give the actual
denominator certificate

$$
\|\alpha_V f_0P\|_2^2
\ge c\ell^{-2m}
e^{2E_V-O(E_V/\ell^2)-O(\log\ell)}H_P.
\tag{23}
$$

Equations (19), (21) and (22) bound the normalized mass on
$\varepsilon\le|t|\le V^4$ by

$$
\exp\!\left[-2\delta_\varepsilon E_V+O(E_V/\ell^2)
+O_{f_0}\bigl(n\log(n+2)+n\log\ell+\log(N_V\ell)\bigr)\right]
=o(1).
$$

Indeed $n\log(n+2)+n\log\ell=o(E_V)$ for the stated $N_V$.
On $|t|>V^4$, use the global $\log|\alpha_V|\le E_V$ and
$|\widehat h(t)|\le Ce^{-c\sqrt{|t|}}$. Since $V^2\gg n$,
the supremum of the polynomial-envelope tail bounds its normalized
mass by

$$
\exp\!\left[O(E_V/\ell^2+n\log V+n\log\ell
+\log(N_V\ell))-c'V^2\right]=o(1).
$$

The remaining integral is bounded by the fixed $\|g\|_2^2$.
Both bounds are uniform over every nonzero $P$ of degree $<N_V$.
Thus there is $r_V\to0$ such that every unit vector of
$\mathcal E_V$ has at least $1-r_V$ of its mass in
$[-\varepsilon,\varepsilon]$.

For this same interval and every $j\ge0$,
$w_j(t)\ge2^{-j}\widehat\psi(0)/2$. Sum its expectation over
any orthonormal basis of $\mathcal E_V$ and use positive projection
order inside the actual range. This gives

$$
t_{S(V),j}\ge
2^{-j}\frac{\widehat\psi(0)}2N_V(1-r_V),
$$

which proves the paper bound (18), uniformly in $j$. Orthonormality
here uses the actual $\alpha_V$-weighted norm; the inverse metric
in (2) has not been discarded.

### Consequences and the unchanged arithmetic obligation

In particular the true fixed-bump trace $t_{S(V),0}$, as well as the
two larger majorants, cannot have a uniform polynomial-in-$\log V$
upper bound. It is therefore insufficient to repair only the
principal-angle loss in (12) while retaining that proposed upper
bound. The original required scale is $M_XL_X$, not a fixed
polynomial in $\log V$; (18) does not exclude all payments at that
scale or all choices of actual finite-place sets.

For WT7's actual nonnegative coefficients, (9) and (18) also give

$$
T_{S(V)}(c_X)\ge c_\psi\frac{\sqrt V}{(\log V)^3}
\sum_{j\ge0}a_j2^{-j},\qquad
\sum_{j\ge0}a_j2^{-j}=\frac{\|c_X\|_1}{\|\psi\|_1}.
\tag{24}
$$

The last identity uses $\psi\ge0$ and monotone integration. The
following actual-coefficient argument compares (24) with $M_XL_X$
and separately bounds the signed geometric defect on the same test.
A positive trace alone does not determine the complete same-test
arithmetic Weil functional. That comparison and the original strict
Robin upper remain unproved.


## The unchanged full-support completion has a large geometric defect

The actual WT7 coefficients also have a lower mass bound. It links
(18) to the unchanged MR5 test and rules out the small geometric
upper allowance for the all-primes-through-support choice. This is
a repo-derived application of the preceding concentration estimate
and the existing MR1, MR5 and WT7 definitions, with no new generic
positivity theorem, literature-priority claim or Lean verification.
Retain the original qualifying source-window hypotheses and their
cofinal family; existence of that conditional family is not asserted.

### Every actual core contributes a fixed positive integral mass

Use the original $0<a<1$, least core $b_X$, endpoint-inclusive
largest core $C_X=B^{\rm end}_{\max,X}$, horizon $U=\mathsf U_X$
and smoothing $h_B=Q_X\sqrt B$. The existing estimates give
$U/C_X\to\infty$ and $h_B/B\to0$ uniformly over all original
cores, including ties. Thus, eventually,

$$
h_B\le B/8,\qquad
c_B:=\frac{1-a}{\sqrt B}-\frac{s_B}{U\log U}
\ge\frac{1-a}{2\sqrt B}
\quad(b_X\le B\le C_X).
$$

MR1's nonnegative $w_B$ is constant with value $c_B$ to the left
of $B$. Its same smoothing therefore satisfies
$\widetilde w_B(r)=c_B$ on $[B/4,B/2]$. Because $b_X\to\infty$,
this interval is outside MR5's calibration region $r<\sqrt2$.
All residence weights remain the original ones. The actual $F_X$
is nonnegative, and evenness, Tonelli and restriction of a
nonnegative integral give

$$
\begin{aligned}
\|F_X\|_1
&\ge\int_{\sqrt2}^{\infty}r^{-1/2}
\widetilde{\mathsf W}_X(r)dr\\
&\ge\int_{t_0}^{t_m}c_{\mathcal B_X(t)}
\int_{\mathcal B_X(t)/4}^{\mathcal B_X(t)/2}r^{-1/2}dr\,dt\\
&\ge\frac{(\sqrt2-1)(1-a)}2L_X.
\end{aligned}
\tag{25}
$$

This does not choose a favorable core: the restriction is made
inside the same nonnegative joint integral for each actual core.
WT7's existing upper bound is $\|F_X\|_1\ll L_X$.
Write $m_\psi>0$ for WT7's fixed spectral floor, avoiding confusion
with the analytic zero order in (23). Since $0\in I_0$ and
$F_X\ge0$, the triangle inequality is sharp at zero, so

$$
a_0=m_\psi^{-1}\|F_X\|_1\asymp L_X,
\qquad
\sum_{j\ge0}a_j2^{-j}\asymp L_X,
\qquad \|c_X\|_1\asymp L_X.
\tag{26}
$$

The upper estimates in (26) are reused from WT7, not inferred from
a lower bound. Combining with (24) yields the actual completion
estimate $T_{S(V)}(c_X)\gg L_X\sqrt V/(\log V)^3$.

### The same actual positive test retains a spectral floor

The fixed WT7 $u$ is a nonzero nonnegative smooth function. Strict
triangle inequality on its support gives
$|\widehat u(2)|<\widehat u(0)$: $e^{-2ix}$ cannot have a constant
phase on a nonempty open interval where $u>0$. Hence

$$
m_\psi\le\widehat\psi(2)<\widehat\psi(0).
$$

Choose one fixed $\varepsilon>0$ and $\kappa_\psi>0$ such that
$\widehat\psi(t)\ge(1+\kappa_\psi)m_\psi$ for
$|t|\le\varepsilon$. WT7's other Fourier summands are
nonnegative. For the same actual $H_X=c_X-F_X$,

$$
\widehat H_X(t)\ge
a_0\widehat\psi(t)-|\widehat F_X(t)|
\ge\kappa_\psi\|F_X\|_1\gg L_X
\qquad(|t|\le\varepsilon),
\tag{27}
$$

while $\widehat H_X\ge0$ on all of $\mathbb R$. No replacement
test or extra smoothing has been introduced. Apply the preceding
uniform concentration argument at this same fixed $\varepsilon$;
(21) holds for every fixed positive choice. Positive projection
order on its actual trial subspace gives

$$
\operatorname{Tr}(D_{S(V)}(h_{H_X})P_{S(V)})
\gg L_X\frac{\sqrt V}{(\log V)^3}.
$$

Equation (7) already pays the archimedean trace by $O(L_XY_X^2)$.
Thus the exact same-test defect (3), rather than merely its upper
majorant in (8), satisfies

$$
\boxed{\Delta_{S(V)}(h_{H_X})
\ge cL_X\frac{\sqrt V}{(\log V)^3}-C L_XY_X^2.}
\tag{28}
$$

The constants and the $V$ threshold are independent of $X$ and
its original windows; the existing estimates on $X$ apply beyond
their one common start. All operators use the original orthogonal
metric and actual test.

### Compare with the actual unchanged full-support horizon

Take exactly the MR1 support cutoff
$V=\mathsf V_X=\mathsf U_X+Q_X\sqrt{C_X}$. Either prescribed FH1
horizon, with its stated SC2 or VC2 ceiling, satisfies

$$
\mathsf V_X/\mathsf U_X\to1,\qquad
\frac{\log\mathsf V_X}{\log X}\to\infty,\qquad
Y_X=o(\log\mathsf V_X).
$$

Indeed its stated ceilings have $Y_X\gg\log X$, and the two
horizons have $\log\mathsf U_X/Y_X\to\infty$. The small
smoothing extension is $o(\mathsf U_X)$ by $Q_X/\sqrt{C_X}\to0$
and $\mathsf U_X/C_X\to\infty$. These are lower-growth
consequences of the prescribed horizons, not an inference from the
upper estimate $\log\mathsf V_X=O((\log X)^4)$.
Since $M_X=X^{1/2-\eta}\log X$, they imply

$$
\frac{\sqrt{\mathsf V_X}}
{M_X(\log\mathsf V_X)^3}\to\infty,
\qquad
\frac{Y_X^2(\log\mathsf V_X)^3}{\sqrt{\mathsf V_X}}\to0.
$$

Consequently (28) gives

$$
\boxed{\frac{\Delta_{S(\mathsf V_X)}(h_{H_X})}
{M_XL_X}\longrightarrow+\infty.}
\tag{29}
$$

Thus a uniform $O(M_XL_X)$ upper allowance for this actual
geometric defect fails for the unchanged completion and the full
all-primes-through-support set. The result is stronger than the
majorant obstructions (15)--(17): it uses the actual orthogonal
projection, actual coefficients and actual $H_X$. It does not
give the complete arithmetic Weil functional a sign. A different
same-test comparison could retain a compensating correction, and
a different completion or finite-place scheme is not covered by
(29). The original strict Robin upper and RH remain unproved.

## The remote pole-null completion has a negligible semilocal trace

The remote completion in WT11--WT14 also has a controlled effect on
the actual semilocal trace. This is a different question from the
large positive trace of $H_X$: it asks whether the auxiliary test
added far away can change the trace comparison by the Robin-scale
amount. Keep the fixed nonnegative autocorrelation $\psi$ used in
WT7 and write

$$
q_R(x)=2\psi(x)+\psi(x-R)+\psi(x+R),
\qquad e_X=\varepsilon_Xq_{R_X}.
$$

With the same Fourier convention as (12), translation gives the exact
multiplier identity

$$
\widehat q_R(t)=2(1+\cos Rt)\widehat\psi(t).
\tag{30}
$$

Since $\widehat\psi\ge0$,

$$
|\widehat e_X(t)|
\le4\varepsilon_X\widehat\psi(t).
\tag{31}
$$

In the unitary Mellin coordinates used in (11), $D_S(h_G)$ is the
multiplication operator by the Fourier multiplier $\widehat G$ (up to
the reflected variable convention, which does not change (31)). Thus
the self-adjoint operator inequality

$$
-4\varepsilon_XD_S(h_\psi)
\le D_S(h_{e_X})
\le4\varepsilon_XD_S(h_\psi)
\tag{32}
$$

holds. Compressing by the positive orthogonal projection $P_S$ and
using the fixed-$S$ trace-class statement in (3), together with the
trace of the positive operator on the right, gives

$$
\boxed{
\left|\operatorname{Tr}\bigl(D_S(h_{e_X})P_S\bigr)\right|
\le4\varepsilon_X\,t_{S,0},
\qquad
t_{S,0}:=\operatorname{Tr}\bigl(D_S(h_\psi)P_S\bigr).
}
\tag{33}
$$

The quantity $t_{S,0}$ is the $j=0$ member of the already established
localized projection estimate (10). Therefore, uniformly over finite
place sets,

$$
\left|\operatorname{Tr}\bigl(D_S(h_{e_X})P_S\bigr)\right|
\ll_\psi \varepsilon_X(1+C_S),
\qquad
C_S=\sum_{p\in S_{\rm fin}}\frac{\log p}{\sqrt p-1}.
\tag{34}
$$

This uses the actual orthogonal projection and does not replace it by
the oblique transport or by the commutator majorant.

For the original test's support scale $\mathsf V_X$, keep the explicit
family $S_X=\{\infty\}\cup\{p:p\le\mathsf V_X\}$. This family
need not contain every prime through the remote completion's enlarged
support. The owned prime-count estimate gives
$C_{S_X}\ll\sqrt{\mathsf V_X}$.
WT13 gives

$$
\varepsilon_X\ll_\psi L_X
\exp\!\left(\frac{A_X-R_X}{2}\right),
\qquad A_X=\log\mathsf V_X,
\tag{35}
$$

because $N_X\ll_\psi L_Xe^{A_X/2}$ and
$\mathcal P(q_{R_X})\asymp_\psi e^{R_X/2}$. Combining (34)--(35),

$$
\frac{\left|\operatorname{Tr}(D_{S_X}(h_{e_X})P_{S_X})\right|}{L_X}
\ll_\psi
\bigl(1+e^{A_X/2}\bigr)
\exp\!\left(\frac{A_X-R_X}{2}\right)
=o(1),
\tag{36}
$$

for the WT13 choice $R_X=K(1+A_X+\log X)^2$. The last limit follows
from the prescribed support bound $A_X=O((\log X)^4)$ and the fixed
$K$ in WT13; it is a direct comparison of the displayed exponents.
Consequently,

$$
\boxed{
\operatorname{Tr}(D_{S_X}(h_{H_X+e_X})P_{S_X})
=\operatorname{Tr}(D_{S_X}(h_{H_X})P_{S_X})+o(L_X).
}
\tag{37}
$$

Together with WT12 and WT14, equation (37) shows that the remote
completion changes the signed arithmetic--semilocal-trace residual
with this prescribed $S_X$ by $o(L_X)$. A future joint lower bound
formed with that same family therefore transfers from the pole-null
test back to $H_X$.

The stronger comparison using every prime through the completed
test's support remains unfinished. That support reaches
$R_X+\tau$ in logarithmic coordinates, so the prime-count estimate
for the enlarged family only gives $C_S\ll_\psi e^{R_X/2}$.
Combined with (35), the resulting upper bound in (34), divided by
$L_X$, is $O_\psi(e^{A_X/2})$; it does not establish an $o(1)$
payment. Completing this stronger comparison requires a sharper
trace estimate or a joint signed bound that retains the growing
correction on the same enlarged place set. Neither (37) nor this
insufficient upper estimate refutes such a comparison.

The joint lower bound itself also remains unfinished: the residual
for $H_X$ contains the complete prime-power term and the growing
metric correction $\Delta_{S_X}(h_{H_X})$. Robin's inequality and
RH remain unproved.
