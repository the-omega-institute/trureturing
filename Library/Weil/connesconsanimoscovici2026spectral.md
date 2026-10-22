---
bibkey: connesconsanimoscovici2026spectral
authors: Alain Connes, Caterina Consani, Henri Moscovici
year: 2026
title: Zeta Spectral Triples
doi: 10.4171/elm/37/3
url: https://arxiv.org/abs/2511.22755v1
claim: The full bounded-support Weil operator has discrete lower-bounded spectrum, and an explicit auxiliary transform converges to Xi. Existing form-core, Carleman and min-max results give an explicit even-section error. At c27 a joint weighted prime bound supplies a positive even high-complement floor after mode1280, but a directed four-row witness excludes the resulting diagonal-floor Schur target at this cutoff. The actual exterior Schur sign, cofinal positivity and actual ground-state comparison remain missing.
strata_touched: []
license: citation-only
triage: anchor
---

# Spectral construction and the actual Weil comparison

The [EMS publication record](https://doi.org/10.4171/elm/37/3) identifies the chapter published on 23 June 2026. The complete primary text inspected here is [arXiv:2511.22755v1](https://arxiv.org/pdf/2511.22755v1), 27 November 2025. Its PDF SHA-256 is `c98d89f7fc999d038e15e80a9aaaee2af797c17711c4329ca7ce48ad49cb336b`. The publisher-edition full text was unavailable; equality of that edition with the inspected preprint is not asserted. The source results below are references for reuse, without independent proof verification, numerical reproduction or Lean implementation.

## Established results to reuse

The following locators refer to the inspected preprint's printed pages.

| Locator | Source result | Condition or limit relevant to this project |
|---|---|---|
| Proposition 3.4, pp.8–9 | The Fourier/Laurent-polynomial space is a form core; finite-section minima converge to the full lower bound. | No effective error rate or nonnegative lower bound is supplied. This proposition is attributed to the earlier Connes–Consani work. |
| Theorem 3.6, p.9 | The canonical full Weil operator at fixed support has discrete lower-bounded spectrum. | A lower bound need not be nonnegative; discreteness does not determine its sign. |
| Theorem 5.10, p.23 | A modified scaling operator is selfadjoint in the specified quotient metric, and its regularized determinant is expressed using an entire Fourier transform with only real zeros. | The finite-section minimum must be simple, its eigenvector even, and its Dirichlet evaluation normalized to one. |
| Lemma 7.3, pp.31–32 | The transform of the specified auxiliary $k_\lambda$ converges to Riemann's $\Xi$ uniformly on closed substrips of $\lvert\operatorname{Im}z\rvert<1/2$. | This concerns the auxiliary prolate-based function, not a proved approximation of the actual Weil ground eigenfunction. |

The theorem's quotient metric is the restriction of

$$
QW_\lambda^N-\epsilon_N\langle\cdot,\cdot\rangle,
$$

where $\epsilon_N$ is the original finite-section minimum. Its positivity is a property of the shifted quotient. The construction supplies no sign bound for $\epsilon_N$. The [distributional precursor and its explicit negative example](connesvansuijlekom2025quadratic.md) give another reason to preserve this distinction. Rebuilding the spectral construction would not supply the missing unshifted estimate.

## Common-function parameter map

Use $L>0$ for the project's additive half-width, avoiding the source's use of an interval-length parameter:

$$
\lambda=e^L=\sqrt c,\qquad u=e^x,\qquad g(u)=f(\log u),
\qquad d^*u=du/u=dx.
$$

Thus $\operatorname{supp}f\subseteq[-L,L]$ corresponds to $\operatorname{supp}g\subseteq[\lambda^{-1},\lambda]$, and additive evenness corresponds to multiplicative inversion symmetry. Equations (3.7)–(3.11) retain the prime-power weights, Gamma multiplier and both pole evaluations. In particular,

$$
\widehat g(\pm i/2)=\int f(x)e^{\pm x/2}\,dx.
$$

For even $f$ these evaluations agree; they are not required to vanish. The auxiliary construction's zero-integral condition is a condition on its profile, not permission to restrict the project's arbitrary even tests. The [existing joint pole–prime–Gamma account](frankliebseiringer2006hardy.md) continues to own that common-test decomposition.

## The source's remaining steps

Section 8, pp.32–33, explicitly leaves two steps unresolved: the actual Weil minimum must be simple with an even eigenvector, and $k_\lambda$ must approximate a correctly scaled actual ground eigenfunction sufficiently accurately to transfer convergence of transforms. The corresponding properties of the prolate-wave operator do not establish those properties for the Weil operator.

One concrete comparison target is, for the same actual ground eigenfunction $\xi_\lambda$ and an explicitly controlled nonzero normalization $a_\lambda$,

$$
\int_{\lambda^{-1}}^\lambda
|a_\lambda\xi_\lambda(u)-k_\lambda(u)|
\max(u^\sigma,u^{-\sigma})\,\frac{du}{u}\longrightarrow0,
\qquad 0\le\sigma<1/2.
$$

This is an outstanding weighted-transform interface, not a bound proved by this note. Norm convergence at changing support does not by itself provide its weights or normalization. The [effective prolate concentration bounds](karnikrombergdavenport2021prolate.md) concern another operator and do not supply this comparison.

For the positivity route, the outstanding supplier instead concerns the actual full-form even-sector finite-section error. If $m_L^+$ is the true even-sector minimum and $m_{L,N}^+$ a retained minimum, the needed certified comparison has the form

$$
0\le m_{L,N}^+-m_L^+\le r(L,N),
$$

with a lower certificate for $m_{L,N}^+$ large enough to pay $r(L,N)$. Core density alone supplies no explicit $r$. The application below supplies a conservative explicit error for this actual section; it supplies neither a positive retained certificate nor cofinal positivity. The separate ground-state route still lacks the weighted comparison above.

An unbounded FIB support schedule selects a cofinal family of windows. The explicit section error below applies at each selected half-width, but the schedule supplies none of the actual simplicity, evenness, normalization, weighted comparison or positive certificates. Existing generic cofinal and Schur results are reused. RH remains unproved.

## An explicit error for the actual even Fourier sections

Keep the same full complex Weil form, with $L>0$ and
$I=(-L,L)$, as in the [source normalization](liu2026tailcompensation.md#source-normalization-and-support).
Write $d=2L$, extend each test by zero outside $I$, and put

$$
A(t)=\Re\operatorname{digamma}(1/4+it/2)-\log\pi,
\quad A_0=A(0),\quad
k(s)=\frac{e^{-s/2}}{1-e^{-2s}}\quad(s>0).
$$

The Fourier basis is $e_n(x)=d^{-1/2}e^{2\pi inx/d}$.
The primary's equations (2.6), (3.19)--(3.21) and Proposition 3.4
identify this same zero-extension form core after $\lambda=e^L$
and translation of $[0,2L]$ to $I$; the translated basis differs
only by $(-1)^n$. The form-core theorem and generic bounded-perturbation
and block min--max principles are reused. This `repo-derived` application
is the following explicit comparison for the actual Gamma, pole and
prime terms, not a new general spectral theorem or priority claim.
No Lean certification is asserted.

Earlier high-Fourier-complement coercivity and finite-to-infinite
certification are attributed to Hiroyuki Yoshida,
*On Hermitian Forms attached to Zeta Functions*, Advanced Studies in
Pure Mathematics **21** (1992), 281–325,
[DOI:10.2969/aspm/02110281](https://doi.org/10.2969/aspm/02110281),
Lemma 3 on p.290 and §6 on pp.309–310, by the “Relation to existing
work” subsection of the [pinned Liu manuscript](https://github.com/luciferyu666/certified-weil-positivity/blob/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/frozen-source/publication/manuscript.tex).
This historical attribution is secondary: Yoshida's original lemma
has not been inspected here. The exact overlap of Yoshida's Lemma 3
with G1–G5 remains unsettled. The
[existing quantitative tail and coupling application](../Fourier/montgomery1978largesieve.md)
also remains available. G1–G5 record the particular periodic-Gamma
comparison below, with no priority claim over these earlier methods.

[Suzuki’s inspected earlier primary](suzuki2023aspects.md) supplies the
high-complement estimate in a primitive metric and the corrected finite
form, and distinguishes smooth-source from completed-space nondegeneracy.
Those methods are reused; their existence does not supply the actual
corrected sign or the all-support hypothesis required here.

### Compare periodic and zero-extended Gamma energies

Let $D_L$ be the diagonal selfadjoint operator with eigenvalues
$A(\pi n/L)$ on $e_n$, and write $q_{D_L}$ for its closed form.
The standard [digamma integral, DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16), gives

$$
A(t)-A_0=2\int_0^\infty k(s)(1-\cos ts)\,ds.
$$

Consequently the zero-extended Gamma form is
$Q_\Gamma(f)=A_0\|f\|_2^2+
\int_0^\infty k(s)\|f-f(\cdot-s)\|_2^2ds$.
For Fourier polynomials, compare this expression with the periodic
translation energy, first with the same small-shift cutoff. Summing
periodic correlations gives

$$
Q_\Gamma(f)=q_{D_L}(f)+\langle f,B_Lf\rangle,
\qquad
B_L(x,y)=\sum_{m\in\mathbb Z\setminus\{0\}}
 k(|x-y+md|).
\tag{G1}
$$

The comparison keeps the cancellation at zero; the divergent integral
$\int_0^\infty k(s)ds$ is not extracted as a separate diagonal term.
The displayed kernel specifies a bounded integral form, with its two
endpoint singularities interpreted by the following existing estimate.

Reuse [the actual Gamma boundary bound T40](desogus2026threegates.md#pay-the-gamma-singularity-at-the-common-boundary),
$k(s)\le C_k/s$, $C_k=(1-e^{-2})^{-1}$, and the classical Carleman
bound there. Endpoint coordinates turn each of the $m=1,-1$ terms
into a kernel bounded by $C_k/(r+s)$, hence each has operator norm
at most $\pi C_k$. For $|m|\ge2$,
$|x-y+md|\ge(|m|-1)d$; their geometric row and column sums give

$$
\boxed{\|B_L\|\le C_\Gamma(d):=
2\pi C_k+
\frac{2d e^{-d/2}}{(1-e^{-d/2})(1-e^{-2d})}.}
\tag{G2}
$$

The far-image series converges in operator norm. A positive pointwise
kernel does not assert that $B_L$ is a positive operator.

Both forms in G1 have the same Fourier-polynomial core: for the actual
form use the cited Proposition 3.4, while for $q_{D_L}$ use its
diagonal description. The bounded correction therefore extends G1
to the actual closed form. Its domain is exactly

$$
\left\{f\in L^2(I):
\sum_{n\in\mathbb Z}
[A(\pi n/L)-A_0]|\langle e_n,f\rangle|^2<\infty\right\}.
\tag{G3}
$$

On this form domain the notation is $q_{D_L}(f)$;
$\langle f,D_Lf\rangle$ additionally requires the operator domain.
The finite pole and prime terms are bounded, so they preserve this
form domain and core.

### Retain the full arithmetic perturbation in the error

The combined true pole pair has norm at most $4\sinh L$.
The complete paired prime translations have norm at most
$2\sum_{2\le n<e^{2L}}\Lambda(n)/\sqrt n$; every higher prime power
is included. The shift at $n=e^{2L}$, when present, is zero almost
everywhere. Define the explicit finite constant

$$
K_L=C_\Gamma(2L)+4\sinh L+
2\sum_{2\le n<e^{2L}}\frac{\Lambda(n)}{\sqrt n}.
\tag{G4}
$$

Thus the actual closed form is $Q_L=q_{D_L}+\langle\cdot,V_L\cdot\rangle$
with $V_L$ bounded selfadjoint and $\|V_L\|\le K_L$. Each component
preserves reflection. Restrict to the complex even Hilbert space and
its actual Fourier section
$E_N^+=\operatorname{span}_{\mathbb C}
\{e_0,(e_n+e_{-n})/\sqrt2:1\le n\le N\}$, $N\ge0$.
Let $m_L^+$ and $m_{L,N}^+$ be the actual full and retained Rayleigh
infima, respectively. No simplicity or assertion that the overall
ground state is even is used.

The standard digamma series and asymptotic make $A(t)$ increasing for
$t\ge0$ and divergent to $+\infty$; see
[DLMF 5.7.6](https://dlmf.nist.gov/5.7.E6) and
[5.11.2](https://dlmf.nist.gov/5.11.E2).
The true complementary floor is therefore
$A(\pi(N+1)/L)-K_L$, the coupling norm is at most $K_L$, and the
constant vector gives $m_{L,N}^+\le A_0+K_L$. Put
$\delta=A(\pi(N+1)/L)-A_0-2K_L>0$. For the retained/tail
form-domain decomposition $f=u+v$, the existing bounded-block
min--max estimate specializes to

$$
Q_L(f)-m_{L,N}^+\|f\|^2
\ge\delta\|v\|^2-2K_L\|u\|\|v\|
\ge-\frac{K_L^2}{\delta}\|u\|^2.
$$

Taking Rayleigh infima, together with the variational upper bound, gives

$$
\boxed{0\le m_{L,N}^+-m_L^+
\le r(L,N):=\frac{K_L^2}{A(\pi(N+1)/L)-A_0-2K_L},
\quad A(\pi(N+1)/L)>A_0+2K_L.}
\tag{G5}
$$

The denominator condition is explicit and holds eventually for each
fixed $L$. Thus $r(L,N)\to0$ for fixed $L$, with logarithmically
slow frequency decay. This conservative bound supplies no practical
matrix size or lower certificate. For a certified retained lower
bound $\underline m_{L,N}\le m_{L,N}^+$, it gives the actual bound
$m_L^+\ge\underline m_{L,N}-r(L,N)$.

G5 applies separately at the half-widths of the existing unbounded
FIB support schedule. Cofinal positivity still requires retained
positive certificates dominating these actual errors at those scales.
The ground-state simplicity, parity and weighted-transform comparison
needed by the separate spectral route are not supplied. The complete
Robin comparison and RH remain unproved.

## A joint prime bound for the actual c27 even high complement

Reuse the [weighted Schur formula A1](liu2026tailcompensation.md)
from Liu's Appendix B.4, the existing Neumann--Gamma comparison in
[PT7--PT10](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#5-整个高补空间的统一下界),
and G1--G3 above. The new input is their scalar parameter application at
$c=27$, $d=\log27$, $L=d/2$. It is not a new general operator theorem,
a reproduction of an earlier fixed-window sign certificate or a priority
claim. In particular, the source's old width-dependent constants are not
transported to this interval.

The full complex Neumann form identity and this even restriction are
already supplied by [CO4--CO8, section 3](https://github.com/the-omega-institute/trureturing/blob/c94c6abb6fcd9ad2d85c50666fa6abcfdbd8c2f5/docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#3-restore-the-exact-neumann-gamma-completion).
That source's $L$ is the full length $d$ here, and its Neumann mode
$\nu_{2k}=(-1)^kv_k$, where $v_0=e_0$ and
$v_k=(e_k+e_{-k})/\sqrt2$ for $k\ge1$. Neumann conditions belong to the comparison
operator and impose no additional condition on the original tests.

On $I=(-L,L)$ retain every prime power

$$
\mathcal P_{27}=\{2,3,4,5,7,8,9,11,13,16,17,19,23,25\},\qquad
C_{\rm p}=\sum_{n\in\mathcal P_{27}}\frac{\Lambda(n)}{\sqrt n}
(S_{\log n}+S_{-\log n}).
$$

The shift at $27$ is zero almost everywhere. For the common positive
weight $q(u)=1+(29/50)(u/L)^2$, A1 bounds the complete complex quadratic
form by its weighted row $r_q$, including all simultaneously active
shifts. Put $b=29/50$ and $R=59/10$. Write $x=u/L\in[0,1]$ and enclose
$t_n=\log n/L$ by $t_n^-\le t_n\le t_n^+$. On each outward support
cell, retain a negative or positive shift whenever it can be active
anywhere in that cell. With outward upper weights $w_n^+$ set

$$
W=\sum_{\rm negative,positive}w_n^+,\qquad
B=\sum_{\rm negative}w_n^+t_n^-
-\sum_{\rm positive}w_n^+t_n^+,\qquad
D=\sum_{\rm negative,positive}w_n^+(t_n^+)^2.
$$

The same quadratic envelope as A2 gives, on the entire cell,

$$
(1+bx^2)(R-r_q(Lx))\ge
b(R-W)x^2+2bBx+(R-W-bD).
$$

Directed logarithm enclosures on a $10^{-12}$ grid and checked integer
square-root lower bounds give an exact rational minimum greater than
$1/400$ on every cell. Minima include the two endpoints and any interior
vertex of a convex quadratic; there is no sampling mesh. The coincident
switches from $3$ and $9$ use $t_3=2/3$ and $t_9=4/3$ exactly. Individual
support endpoints have measure zero. Reflection covers $x<0$. Thus

$$
\boxed{|\langle f,C_{\rm p}f\rangle|\le\frac{59}{10}\|f\|_2^2
\quad(f\in L^2(I;\mathbb C)).}
\tag{G6}
$$

For comparison, the classical finite-path adjacency norm gives
$\|S_s+S_s^*\|=2\cos(\pi/(\lceil d/s\rceil+1))$ for $0<s<d$.
The integer-ratio case uses the almost-everywhere chain length, so no
extra endpoint vertex is counted. Adding these separate bounds yields
$P_{27}=8.54672965014089\ldots$, larger than G6. G6 uses one common
weight for the complete sum; it does not combine separately attainable
optima as though they had a common maximizing test.

### Apply the existing even Gamma comparison

For completeness, G1 realizes the same Neumann comparison on the even
core. With $b_j=2j+1/2$, its image kernel is

$$
B_L(x,y)=\sum_{j\ge0}\frac{2\cosh(b_j(x-y))}{e^{b_jd}-1}.
$$

For even complex $f$, every sinh moment vanishes. Consequently

$$
\langle f,B_Lf\rangle=
\sum_{j\ge0}\frac{2}{e^{b_jd}-1}
\left|\int_I f(x)\cosh(b_jx)\,dx\right|^2\ge0.
$$

Finite mixtures give this identity first. The absolute kernel bound G2
justifies their form limit; G3 extends the comparison from the Fourier
core to the closed form domain. This is the already used even
Neumann--Gamma domination, without the full-space negative allowance
$-C_\Gamma(d)$. The even pole pair is also nonnegative. Hence for every
even form-domain $f$ perpendicular to the actual cosine modes $0,\ldots,N$,

$$
Q_L(f)\ge
\left[A\!\left(\frac{2\pi(N+1)}d\right)-\frac{59}{10}\right]\|f\|_2^2.
\tag{G7}
$$

The existing interval digamma routine gives the following scalar signs:

| Prime debt | $N$ | Enclosure of the G7-type scalar floor |
|---|---:|---:|
| Separate bounds $P_{27}$ | 16972 | $[-0.000010642,-0.000010640]$ |
| Separate bounds $P_{27}$ | 16973 | $[0.000048274,0.000048275]$ |
| Joint bound $59/10$ | 1202 | $[-0.000086409,-0.000086408]$ |
| Joint bound $59/10$ | 1203 | $[0.000744501,0.000744502]$ |
| Joint bound $59/10$ | 1280 | $[0.06273617862538,0.06273617862539]$ |

Monotonicity of $A$ identifies the first positive scalar floor in these
two comparisons as $N=16973$ and $N=1203$, respectively. These are
thresholds of these sufficient estimates, not necessary truncation
sizes. In particular, G7 supplies $Q_L(f)\ge\|f\|_2^2/16$ on the entire
even complement after mode $1280$, subject to the stated paper-level
form identification. A negative scalar lower bound supplies no negative
Weil test.

The [reproducible scalar packet](https://github.com/the-omega-institute/trureturing-experiments/tree/main/docs/reports/weil-c27)
retains every outward support cell and exact rational minimum. It calls
only the fixed existing `psi_iv` arithmetic routine, SHA-256
`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`,
from project commit `4804c4020d7d9f165a2e2683c42b01e3d47a8be4`;
the old certificate is not run or used as a sign input. This is a scalar
computer-assisted input and paper application, not a Lean result.
The actual retained block and the coupling to its full infinite
complement remain to be certified. The high-complement floor alone
does not establish c27 positivity, cofinal Weil positivity, Robin or RH.

Precision is an additional obstacle already quantified by prior work.
[Zhu v2](https://arxiv.org/html/2608.24827v2), section 11.4, equation (17)
and Table 3, reports an unconditional geometric-side interval upper
bound $8.61\times10^{-121}$ from an explicit real even test at physical
half-width $1.6$. Equation (17) retains the same $2|\int f\cosh(x/2)|^2$
pole term and complete $2\Lambda(n)/\sqrt n$ autocorrelation prime sum.
Since $1.6<\log27/2$, extension by zero gives, on that source-reported
certificate,

$$
m_{\log27/2}^+\le m_{1.6}^+\le8.61\times10^{-121}.
$$

The primary equation and table have been inspected; their certificate
was not rerun here. This variational upper bound is not a positivity
result, and is not used as an input to G6--G7. The reported trial quotient
is below the high-complement floor, so that floor cannot lower-bound the
full even form. The upper bound does not upper-bound the retained
compression: variational restriction gives $m_L^+\le m_{L,N}^+$.
A positivity certificate still requires the retained block and its
complete coupling allowance.

### Transport the trial upper bound to the actual retained Schur margin

The same source-reported trial certificate also bounds the actual
Schur margin in the original1281-dimensional orthonormal cosine
coordinates. This is an application of the existing variational Schur
identity and the Neumann spectral projection estimate, not a new
general theorem or a rerun of Zhu's interval certificate.

Put $a=\log27/2$, $L=8/5$ and $b=8.61\times10^{-121}$. Section11.1
and Table3 of the inspected Zhu v2 source use200 odd-index Dirichlet
sine modes, with highest index399. Taking that reported geometric-side
certificate as input, there is a nonzero real even $f_*$ in this trial
space with $Q(f_*)\le b\|f_*\|_2^2$. Its zero extension to $(-a,a)$
has the same full Weil energy. It lies in $H^1(-a,a)$ because each
trial mode vanishes at $\pm L$, and its derivative satisfies

$$
\|f_*'\|_2^2\le
\left(\frac{399\pi}{2L}\right)^2\|f_*\|_2^2.
$$

Let $P$ retain the actual even modes0 through1280. Parseval for the
Neumann derivative form, with first discarded frequency $1281\pi/a$,
gives

$$
\|(I-P)f_*\|_2^2
\le\left(\frac{a}{1281\pi}\right)^2\|f_*'\|_2^2
<\frac1{36}\|f_*\|_2^2.
$$

Here $8/5<a<5/3$ and
$399(5/3)/((16/5)1281)=3325/20496<1/6$. Thus
$\|Pf_*\|_2^2>35\|f_*\|_2^2/36$, in particular $Pf_*\ne0$.
On the same closed-form block identification and positive exterior
$H_N$ used above, the existing variational identity yields

$$
S_N=A_N-C_N^*H_N^{-1}C_N,\qquad
\langle Pf_*,S_NPf_*\rangle
=\inf_y Q(Pf_*+y)\le Q(f_*),
$$

where the infimum is over the exterior form domain. Consequently,
conditional on that source certificate and the stated form interfaces,

$$
\lambda_{\min}(S_N)<\frac{36}{35}b
=8.856\times10^{-121}<9\times10^{-121}.
$$

The same upper ceiling applies to every legal residual lower target
$A_N-U(X)\preceq S_N$, in these original orthonormal coordinates.
It does not bound the retained compression $A_N$ alone. The exterior
part of $f_*$ is retained in the variational completion; no inequality
$Q(Pf_*)\le Q(f_*)$ is assumed.

There is also a directional requirement on a successful inverse
comparison. Normalize $v_*=Pf_*/\|Pf_*\|_2$ and, for a chosen exterior
embedding $E$ and trial $X$, put $R_X=C_N-H_NEX$. The existing
inverse-residual identity gives

$$
\langle v_*,[S_N-(A_N-U(X))]v_*\rangle
=\langle R_Xv_*,(W-H_N^{-1})R_Xv_*\rangle.
$$

Thus if $A_N-U(X)\succeq0$, its nonnegative comparison loss in this
same direction must be strictly below $9\times10^{-121}$. This is a
necessary directional bound, not a required uniform operator-norm
error or a proved estimate of the actual residual.

This determines neither sign. It rules out treating a computed
$10^{-11}$ scale as the expected positive minimum, even when the
auxiliary finite solve is well conditioned. A proof using additive
error allowances must compare them with its actual directional margin;
the upper ceiling supplies no lower bound and dictates no universal
precision requirement. A change of coordinates must transport the
mass norm along with the form.

### Reuse precision-parametric arithmetic suppliers

The [actual c27 arithmetic packet](https://github.com/the-omega-institute/trureturing-experiments/tree/main/docs/reports/weil-c27)
reuses the existing pole--Gamma--prime Fourier assembly with FLINT's
`acb.digamma` and `acb.polygamma(1)`. These existing special-function
algorithms are called directly; no new general expansion or spectral
criterion is introduced. The application supplies every mode from 0
through 1280 and the coupling samples 1281, 32768 and 32769, with all
fourteen prime powers retained.

The two exponentially decaying Gamma corrections use a precision-chosen
cutoff. With $b_j=2j+1/2$, $q=27^{-2}$ and $d=\log27$, the omitted
contributions to the boundary symbol and complex Fourier diagonal are
bounded respectively by

$$
\frac{27^{-b_R}}{2b_R(1-q)},\qquad
\frac{2\,27^{-b_R}}{d b_R^2(1-q)}.
$$

These are the elementary geometric tails of the existing assembly:
$\omega/(b^2+\omega^2)\le1/(2b)$ and
$|(b-i\omega)^{-2}|\le1/b^2$. The implementation adds both tails to
its directed special-function and arithmetic balls before export.
At 768 working bits, $R=69$ supplies all 1,284 scalar pairs on a
$2^{-640}$ grid, with observed interval width at most one grid unit.
All output rows agree exactly with the 1024-bit execution. Eight c3
diagonal samples and seven nonzero c3 symbol samples lie within the
older read-only scalar routines' intervals; their sign certificate
was not rerun. The archived packet and precise basis convention are
specified in the linked reproduction instructions.

This is a parameter application and numerical scalar input. It removes
the old routine's fixed special-function remainder for this assembly;
it supplies no retained-block sign or infinite coupling Gram. Matrix
reconstruction, all middle modes, the full tail and their propagated
errors still need certification. No c27 positivity or RH conclusion
follows from the scalar table.

### Reuse signed infinite moments of the actual symbol

The same [arithmetic input interface](https://github.com/the-omega-institute/trureturing-experiments/tree/main/docs/reports/weil-c27)
also evaluates normalized discrete tail moments

$$
\mathsf T_p=M^{p-1}\sum_{m>M}\frac{s_m}{m^p},\qquad
\mathsf U_p=M^{p-1}\sum_{m>M}\frac{s_m^2}{m^p},\quad p\ge2.
$$

It directly calls FLINT's finite-series, Bernoulli, Lerch and Hurwitz
suppliers. The reused analytic remainder is Johansson,
[*Arbitrary-precision computation of the gamma function*](https://doi.org/10.5206/mt.v3i1.14591),
Eq28 and Theorem3.3/Eq35, printed pp.13–14: at derivative order1,
the digamma Stirling remainder is bounded by
$(1+\sqrt{\pi(J+1/2)})|B_{2J}|/(2J|z|^{2J})$
for $J\ge1$, $\Re z\ge0$, $z\ne0$. These primary-source conditions
were inspected. No special-function algorithm or general moment
criterion is reproved.

Write $L=\log c$, $\beta=\pi/L$, $a=1/4$, $q=c^{-2}$,
$\delta=c^{-1/2}$, $\alpha=a/\beta$ and
$K=L(\cosh(L/2)-1)/\pi$. The actual symbol satisfies

$$
s_m=-P_c(m)-\frac{Km}{m^2+\alpha^2}
-\frac12\Im\psi(a+i\beta m)
-\frac\delta2\Im\Phi(q,1,a+i\beta m).
$$

The last term is a positive Gamma endpoint correction; the
nonoscillatory constant is $-\pi/4$. Both are retained. Finite
geometric identities for the pole and endpoint correction, and a
Cauchy coefficient bound on the finite Stirling sum, give a polynomial
$\sum_jc_j(M/m)^j$ and a common bound

$$
\left|s_m-\left(\sum_jc_j(M/m)^j-P_c(m)\right)\right|
\le\mathcal A_Jm^{-2J}+\mathcal B_Jm^{-2J-1}\quad(m>M).
$$

The linked reproduction source gives all coefficients and remainder
constants. It uses finite identities on the unbounded Gamma index,
without assuming a convergent infinite inverse-mode expansion.
With $A=M+1$ and $z(u)=e^{2\pi i\log u/L}$, all finite moment
centers use the existing kernel

$$
\mathsf L_p(u)=M^{p-1}z(u)^A\Phi(z(u),p,A),\qquad
\mathsf L_p(1)=M^{p-1}\zeta(p,A).
$$

Exact rational phase folding modulo $c^{\mathbb Z}$ and conjugation
reuses the [existing alias relation](../Fourier/montgomery1978largesieve.md#exact-aliases-of-the-existing-prime-symbol).
The square keeps every signed polynomial--prime and ordered
prime--prime product. In particular the c27 identity $z(3)z(9)=1$
retains the negative sum-frequency Hurwitz terms. Independent-phase
averaging is not used.

For $\epsilon=\mathcal A_JA^{-2J}+\mathcal B_JA^{-2J-1}$ and the
existing $|s_m|\le B_*$, the same scalar tail

$$
F_p=\frac{\mathcal A_J}{M^{2J}}\mathsf L_{p+2J}(1)
+\frac{\mathcal B_J}{M^{2J+1}}\mathsf L_{p+2J+1}(1)
$$

bounds the $\mathsf T_p$ error; $(2B_*+\epsilon)F_p$ bounds the
$\mathsf U_p$ error. The interface adds both to its directed
special-function and finite-arithmetic errors before export. This is
an application of existing scalar suppliers, without a mathematical
priority or Lean-certification claim. The shared moments can feed
the existing coupling jets; coefficient/matrix amplification, all
middle modes, the jet remainder and retained sign still need their
own certificates. No complete c27 or cofinal positivity follows.

The archived input covers powers $2,3,4,8,16,32,64,128$ at $M=32768$,
$J=32$ and 2304 working bits. All sixteen normalized moment intervals
have width at most one $2^{-640}$ grid unit, including both error
sources. The analytic U-error component is below $2^{-816}$ for each
row. All six T/U endpoint pairs at powers2,4,128 agree exactly with an
independent 2560-bit execution. Exact-phase, finite-cutoff-shift and
Hurwitz-progression checks support the interface; they do not supply
a matrix error or positivity certificate.

### A uniform error for the actual infinite far-coupling Gram

The [same arithmetic input](https://github.com/the-omega-institute/trureturing-experiments/tree/main/docs/reports/weil-c27)
applies the finite geometric mechanism of the existing
[Cauchy jets](../../D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.lean)
to the actual discrete divided difference. The continuous Gamma
realization is not substituted for the discrete coupling. In the
phase-adjusted even basis its rows are

$$
C_{m0}=-\frac{\sqrt2s_m}{\pi m},\qquad
C_{mn}=\frac{2(ns_n-ms_m)}{\pi(m^2-n^2)},\quad m>M>N,\ 1\le n\le N.
$$

For $x_n=n/M$, $t=M/m$ and $0\le k<R$, retain all features

$$
A_k(v)=\mathbf1_{k=0}\frac{v_0}{\sqrt2}
+\sum_{n=1}^Nx_n^{2k}v_n,\qquad
B_k(v)=\sum_{n=1}^Ns_nx_n^{2k+1}v_n.
$$

The jet $J_m(v)=2(\pi m)^{-1}\sum_{k<R}t^{2k}(tB_k-s_mA_k)$
has the exact common Gram

$$
J^*J=\alpha P^*HP,\quad\alpha=\frac4{\pi^2M},\qquad
H_{AA,kl}=\mathsf U_{2k+2l+2},\quad
H_{AB,kl}=-\mathsf T_{2k+2l+3},\quad
H_{BB,kl}=M^{2k+2l+3}\zeta(2k+2l+4,M+1),
$$

where $P$ lists the A and B features. Absolute convergence follows from
the existing symbol bound. This keeps every actual signed cross term.
For the centered unphased basis, multiply column $n$ of $P$ by
$(-1)^n$; exterior row parity disappears in the Gram.

The finite geometric identity gives $(C-J)_{m0}=0$ and
$(C-J)_{mn}=C_{mn}(n/m)^{2R}$. With $q_0=N/M$,
$\kappa=1-N/(M+1)$ and the existing $|s_m|\le B_*$, the bound
$|C_{mn}|\le2B_*/(\pi(m-n))$ and the integral inverse-power tail give

$$
\|C\|^2\le c_2:=\frac{B_*^2}{\pi^2M}
\left(\frac{4N}{\kappa^2}+2\right),\qquad
\|C-J\|^2\le r_2:=
\frac{4B_*^2Nq_0^{4R}}{\pi^2\kappa^2M(4R+1)}.
$$

Here the norms can first be bounded by the corresponding Frobenius
norms. The whole Gram error is

$$
\|C^*C-J^*J\|\le\eta_{\rm geom}:=2\sqrt{c_2r_2}+r_2.
$$

Using $r_2$ alone would omit the cross with the retained jet. At
$N=1280$, $M=32768$, the geometric Gram error divided by $h_{M+1}$
has base-two logarithm about $-302.1202$ at $R=32$, and $-527.0689$
at $R=56$. These are scalar evaluations of the displayed error, not
retained eigenvalue or positivity readings.

The number of supplied moment diagonals can be smaller than the jet
order would require for its full Gram. Let $H^{(d)}$ keep only $k+l<d$
in every block. For $q_0>0$, scale by
$D_q=\operatorname{diag}((q_0^{2k})_k,(q_0^{2k})_k)$ and put
$\widetilde P=D_q^{-1}P$. The actual features give

$$
\|\widetilde P\|^2\le L_R^2:=1/2+RN(1+B_*^2q_0^2).
$$

The elementary bounds $|\mathsf T_p|\le B_* /(p-1)$,
$\mathsf U_p\le B_*^2/(p-1)$ and
$M^{p-1}\zeta(p,M+1)\le1/(p-1)$ imply, using $B_*\ge1$, that every
absolute row sum of $D_q(H-H^{(d)})D_q$ is at most

$$
\tau_d=\frac{q_0^{2d}}{1-q_0^2}
\left(\frac{B_*^2}{2d+1}+\frac{B_*}{2d+2}\right).
$$

The symmetric row bound therefore supplies
$\|J^*J-\alpha P^*H^{(d)}P\|\le
\eta_{\rm core}:=\alpha L_R^2\tau_d$.
At $d=2R-1$ there are no omitted entries, so use $\tau_d=0$.
For $N=0$ the omitted features vanish and the error is zero directly.
The default $d=R$ keeps all moments in the first feature row and column,
including the exact zero-mode contribution. Missing signed entries are
paid by $\eta_{\rm core}$; the sparse core is not assumed positive.

Finite input errors are paid on the same matrix. Write
$p_2=1/2+N(1+B_*^2q_0^2)/(1-q_0^4)$ and let $\epsilon_s$ bound
the original low-symbol midpoint errors. For the dyadic midpoint of
$1/\sqrt2$, let its error be $\epsilon_a$. Exact rational powers
in $P_0$ give

$$
\|P\|_F\le\sqrt{p_2},\qquad
\|P-P_0\|_F\le e_P:=
\sqrt{\epsilon_a^2+\epsilon_s^2Nq_0^2/(1-q_0^4)}.
$$

Every normalized moment interval has width at most two $2^{-b}$ grid
units, so its single sparse midpoint matrix satisfies
$\|H^{(d)}-H_0\|\le e_H=2R2^{-b}$. Since $H$ is the genuine positive
moment Gram, masking entries gives
$\|H^{(d)}\|\le\|H^{(d)}\|_F\le\|H\|_F\le\operatorname{Tr}H$.
Its trace is at most
$H_*=\sum_{k<R}(B_*^2/(4k+1)+1/(4k+3))$. For
$p_0=\sqrt{p_2}+e_P$ and $|\alpha-\alpha_0|\le\epsilon_\alpha$,
the full additional error is at most

$$
\eta_{\rm round}=
\alpha\bigl[H_*(2\sqrt{p_2}e_P+e_P^2)+p_0^2e_H\bigr]
+\epsilon_\alpha p_0^2(H_*+e_H).
$$

This also pays prefactor rounding and permits $H_0$ to be indefinite.
Use the existing increasing
$h_m=\log(m/\log27)-\log27/(\pi m)-59/10$ and an upward dyadic
$D\ge h_{M+1}^{-1}>0$. The explicit sufficient far-debit input is

$$
\sum_{m>M}h_m^{-1}C_m^*C_m
\preceq D\alpha_0P_0^*H_0P_0
+D(\eta_{\rm geom}+\eta_{\rm core}+\eta_{\rm round})I.
$$

The small scalar allowance approximates $DC^*C$. The varying inverse
weight is bounded above by $D$, which adds separate one-sided slack.
This contributes to the sufficient diagonal-floor Schur debit; it does
not identify an exact block of the full exterior inverse.

The R56 application uses 112 features with $d=56$: 56 U-moments through
power112, 56 T-moments through113 and 56 Hurwitz moments through114.
The seven applicable published scalar moments are reused. The full
111-diagonal alternative remains optional. The executable supplies exact rational factors
and checks the total weighted operator allowance against $2^{-500}$,
including all moment, feature and prefactor errors. This is a
paper-level discrete application and numerical input, not a new
geometric-series or Schur theorem. Every middle row $1281\le m\le32768$,
the retained sign and cofinal positivity remain separate obligations.

The archived `far-coupling.json.zlib` input uses 2304 working bits and a
640-bit grid. All 168 required moment intervals have width at most one
grid unit. The exact rational factors have dimensions $112\times1281$
and $112\times112$; the exported scalar allowance has base-two logarithm
approximately $-524.573894274258476$. The highest U112/T113 endpoints
agree exactly with independent 2560-bit executions. Packet SHA-256:
`ac35edacd7f55de470586e3b8a5915bcaa49b9d2c4c9c2ee073eeaaa8c9c73e7`.
This supplies only the stated sufficient far majorant under the existing
identification and exterior-floor inputs, without Lean verification.

### Four middle rows already exclude the diagonal-floor target at N1280

The same actual arithmetic supplier gives a short test of whether this
particular Schur budget can fit. Let $A_N$ be the actual retained block,
keep $C_m$ as above, and define the sharper G7 diagonal floor

$$
d_m=\Re\psi\left(\frac14+\frac{i\pi m}{\log27}\right)
-\log\pi-\frac{59}{10}.
$$

For the original centered unphased cosine basis, take the integer vector
$v=-e_{1277}+2e_{1278}-e_{1280}$, with $\|v\|^2=6$. Only four
exterior rows are needed. Directed FLINT evaluation gives, for
$m=1281,\ldots,1284$,

$$
1/16<d_m<1/15,\qquad 0<h_m<1/15,
$$

and the common actual-vector quantities

$$
\langle v,A_Nv\rangle=30.70294244311003905\ldots,
\qquad
15\sum_{m=1281}^{1284}|C_mv|^2=33.30890128199787908\ldots.
$$

Consequently, for either $w=d$ or $w=h$, the full sufficient
diagonal-floor target satisfies

$$
\left\langle v,\left(A_N-\sum_{m>N}w_m^{-1}C_m^*C_m\right)v\right\rangle
\le\langle v,A_Nv\rangle-15\sum_{m=1281}^{1284}|C_mv|^2
<-13/5.
$$

Omitted rows add nonnegative debit, so supplying them more accurately
cannot make this specified target positive at N1280. The same witness
excludes charging all coupling by the uniform inverse floor16. The
actual retained quadratic is positive, so the test does not establish
negative full Weil energy or an RH counterexample. It tests the
sufficient inverse majorant, rather than the sign of the actual exterior
Schur complement.

The linked experiment's `diagonal_floor_witness.py` reuses four published
scalar rows and supplies only the missing rows1282,1283,1284. Its saved
512-bit-grid interval for the weakened target is
$-2.60595883888784003\ldots$, with upper endpoint below $-13/5$.
Result SHA-256:
`f45f3a333b50aa60c38c5b2ee9be416a165a1c719ba7dfb3ca6dfbe251bf1840`.
This is a directed numerical witness under the existing Fourier/form
identification, without Lean verification or a novelty claim. The
high-floor and far-input estimates remain valid; a changed cutoff or
stronger correlated exterior comparison has a separate proof obligation.

The existing G7 bound also locates the loss. Its positive floor after
mode1203 applies to $v+y$ for every exterior form-domain vector $y$ after
mode1280. With $\kappa=A(2\pi\cdot1204/d)-59/10>0$, orthogonality gives
$Q_L(v+y)\ge\kappa(6+\|y\|^2)$. Thus the actual exterior Schur quadratic
on this particular $v$ is positive. This reuses G7 and does not determine
the Schur sign on arbitrary retained vectors.

### Reuse the inverse-residual supplier with the actual prime compression

Keep the same exterior projection $Q_N$, $N=1280$. On its even range put

$$
\Gamma_N=\operatorname{diag}_{m>N} A(2\pi m/d),\qquad
P_N=Q_NC_{\rm p}Q_N,\qquad
B_N=\Gamma_N^{-1/2}P_N\Gamma_N^{-1/2}.
$$

These are the actual compressed prime shifts and the existing Neumann
Gamma comparison, not a constant reference on the whole even space.
G6--G7 give $\Gamma_N\succeq477I/80$, $\|P_N\|\le59/10$ and
$\|B_N\|\le472/477$. Hence the bounded reference
$T_N=I-B_N\succeq5I/477$ is positive. If $H_N$ denotes the actual
closed exterior operator, the same even Gamma and pole comparison gives
$H_N\succeq\Gamma_N^{1/2}T_N\Gamma_N^{1/2}$ in form sense.

Reuse the [source inverse-residual identity](liu2026tailcompensation.md#a-common-256-mode-consumer)
with reference $T_N$, trial $X=I$ and lower bound $5/477$. Its inverse
majorant is $I+B_N+(477/5)B_N^2$. Consequently the actual coupling
$C_N$ and its common filtered columns $Z_N=\Gamma_N^{-1/2}C_N$ satisfy

$$
C_N^*H_N^{-1}C_N
\preceq Z_N^*Z_N+Z_N^*B_NZ_N
+\frac{477}{5}(B_NZ_N)^*(B_NZ_N).
$$

This is a parameter application of the existing residual identity. It
retains the signed prime correlation and its squared residual on the
same forcing columns. The original scalar-floor comparison discarded
that information. The bounded preconditioning specifies the positive
reference without extending the source's old support constants or
assuming a sign for the full Weil operator.

The three compressed quantities on the right have not been supplied or
tested for the required retained sign. They require the complete actual
coupling and exterior prime compression. Compressing $B_N$ to a finite
subspace before forming the squared residual requires paying the
discarded rows.
The far-input packet alone supplies none of those full compressed
quantities. No successful repaired certificate, new general operator
theorem, Lean verification or cofinal positivity is asserted.

### Actual finite-column residual trial at the same retained cutoff

A second application of the same source identity uses actual exterior
Fourier columns as a finite-support trial for $H_N^{-1}C_N$. Keep
$N=1280$, $M=32768$ and the existing positive diagonal majorant $W$:
its exact dyadic weights satisfy $W_{mm}\ge h_m^{-1}$ through $M$,
and equal the archived constant $D\ge h_{M+1}^{-1}$ beyond $M$.
This application assumes the existing Fourier/form identification,
the selected exterior Fourier vectors in $D(H_N)$ and the comparison
$H_N^{-1}\preceq W$ on the same actual exterior operator.

Let $E$ select exterior modes1281 through1284 and put
$Z=H_NE$, $F=E^*H_NE$, $B=E^*C_N$. For the existing obstruction
$v=-e_{1277}+2e_{1278}-e_{1280}$, supply the complete common Gram

$$
\begin{pmatrix}G&J^*\\J&L\end{pmatrix}
=[C_Nv,Z]^*W[C_Nv,Z],\qquad K=L-F,\quad T=J-Bv.
$$

The source residual inequality, evaluated on a fixed dyadic trial $x$,
then supplies the forcing-charge majorant

$$
\langle C_Nv,H_N^{-1}C_Nv\rangle
\le U(x)=G-2\operatorname{Re}(x^*T)+x^*Kx.
$$

An exact optimizer is not required: FLINT proposes the finite solve,
the trial is rounded to64-bit dyadics, and the whole residual is
evaluated with directed balls. This keeps the actual selected
diagonal and the signed cross terms of $C_Nv-H_NEx$.

The experiment supplies only the31483 previously absent scalar pairs
1285–32767 through the unchanged arithmetic oracle. The published
1281,32768 and earlier witness rows1282–1284 are reused. All middle
rows1281–32768 contribute to the Gram. Its infinite far part reuses
all168 published moment intervals and the same112-feature mechanism;
extending the feature columns through1284 requires recomputing the
geometric and rounding amplification. The weighted far error has
$\log_2\epsilon\simeq-524.0636624$. It is paid before the trial,
with column norms $(\sqrt6,1,1,1,1)$, rather than reusing the former
total allowance.

Directed numerical intervals, conditional on the stated analytic
inputs, enclose the following values:

| Actual exterior trial | Debit expression $U(x)$, approximate | $\langle v,A_Nv\rangle-U(x)$, approximate |
|---|---:|---:|
| none | 50.9913204560 | -20.2883780129 |
| 1281 | 36.3114689536 | -5.6085265105 |
| 1281–1282 | 24.6961199103 | 6.0068225328 |
| 1281–1284 | 18.9893075926 | 11.7136348505 |

The existing retained value is30.70294244311003905… . Two actual
columns repair this sufficient estimate on the specified vector.
Its true Schur positivity already follows from G7 after1203; this
is a test of a stronger estimate, not previously unknown positivity.
The scalar and joint-Gram checks at1024 bits reproduce the archived
scientific endpoints without regenerating the former table or moments.
Programs, exact intervals, source/input hashes and reproduction commands
are in the [experiment packet](https://github.com/the-omega-institute/trureturing-experiments/tree/76b876b2ce4d6f2d9c6e3cf73d8b3495ea8f9ec4/docs/reports/weil-c27).

The full1281-dimensional retained midpoint test is more restrictive.
Using64 and128 actual exterior columns gives computed minimum
eigenvalues about $-3.98\times10^{-6}$ and $-2.50\times10^{-11}$,
respectively. These floating proposals do not pay scalar, far-feature
or floating arithmetic errors and certify neither sign. In the latter
case24 eigenvalues have computed absolute value at most $10^{-7}$.
The directed obstructions below pay the common-form errors on complete
retained directions and exclude these two specified sufficient families.
The fixed-vector pilot does not prove full retained positivity, the
original Robin tail, cofinal Weil positivity or RH. No new general
residual theorem, originality or Lean-verification claim is made.

### Directed obstructions to two fixed-column families

Keep the preceding common-form, exterior-domain and inverse-comparison
premises, $N=1280$, and the archived diagonal $W$. For $k=64$ or128,
let $E$ select the actual exterior columns1281 through$1280+k$.
Each fixed family can be excluded without constructing another
full1281-square Gram or recomputing the old eigensolver proposal.

Use the same $Z=H_NE$, $F=E^*H_NE$, $B=E^*C_N$ and the complete
joint Gram $G=C_N^*WC_N$, $J=Z^*WC_N$, $L=Z^*WZ$. Put
$K=L-F$ and $T=J-B$. The first$k$ weighted exterior rows already
give the finite lower matrix

$$
K\succeq F^*W_kF-F\succeq40I.
$$

Omitted rows of $Z^*WZ$ are positive semidefinite; FLINT encloses
all$k$ eigenvalues of the corresponding finite lower matrix above40.
Each case uses its own archived full1281-coordinate dyadic direction
$v$ and fixed$k$-coordinate dyadic trial $x$. Reuse square completion:

$$
\begin{aligned}
m(x)&=Q(v-Ex)-\|C_Nv-Zx\|_W^2,\\
r&=Tv-Kx=Z^*W(C_Nv-Zx)-Bv+Fx,\\
v^*(A_N-G+T^*K^{-1}T)v
&=m(x)+r^*K^{-1}r\le m(x)+\|r\|^2/40.
\end{aligned}
$$

The [fixed-family experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/394343e7a959876b74a00ac520034d3d62457893/docs/reports/weil-c27)
supplies the complete middle rows, the existing far moment core
extended through the selected last column, and its recomputed
quadratic and gradient operator allowances. Under the stated analytic
premises, the directed upper bounds are:

| Exterior columns $k$ | Upper bound for $m(x)+\|r\|^2/40$ | Approximate residual correction |
|---|---:|---:|
| 64 | $<-3.98\times10^{-6}$ | $1.67\times10^{-32}$ |
| 128 | $<-2.49\times10^{-11}$ | $7.17\times10^{-34}$ |

For every matrix trial $X$, completion of the same square gives
$A_N-U(X)\preceq A_N-G+T^*K^{-1}T$. Thus no $X$ for this specified
$E,W$ can make the sufficient lower target positive semidefinite.
The trial error has already been paid; a more accurate solve or
invertible coordinate change cannot repair either specified family.
This does not determine the actual Schur sign or RH.
Changing the exterior space or inverse majorant has a separate
obligation. The calculation reuses the existing residual identity,
source data and library algorithms, without a new general theorem,
originality claim or Lean verification.

### Reusing inverse approximation methods on the actual exterior

The optimized correction above is already a block SR1/shorting update:

$$
W_E=W-(WZ-E)K^{-1}(WZ-E)^*,\qquad
C_N^*W_EC_N=G-T^*K^{-1}T.
$$

Indeed, with $D=W-H_N^{-1}\succeq0$, one has
$WZ-E=DZ$ and $K=Z^*DZ$. This is the existing square completion in
inverse form. Rodomanov–Nesterov,
[*Greedy Quasi-Newton Methods with Explicit Superlinear Convergence*](https://arxiv.org/pdf/2002.00657v3),
equation (2.3), gives the rank-one SR1 formula; its finite-dimensional
setting is fixed in §1.3. The block identification here uses the preceding
algebra, rather than attributing an infinite-dimensional block theorem to
that paper. Its relative sandwich (2.7) and Lemma 2.2 do not supply a
uniform convergence rate here: $W$ has a strictly positive constant tail,
whereas $H_N$ is unbounded, so $W\preceq\eta H_N^{-1}$ cannot hold for
any finite $\eta$. Relabeling the same fixed family as SR1 does not
escape either obstruction.

Two residuals must be kept distinct. The correction
$\|Tv-Kx\|^2/40$ measures the optimization error inside the specified
family. The residual of the actual inverse equation is instead
$C_Nv-H_NEx$. Adding the archived middle and far debit intervals in
the128-column packet gives its weighted energy approximately
$4.3635328423409634\times10^{-10}$, while the optimization correction
is approximately $7.169494010542168\times10^{-34}$. These are evaluations
on the same exact dyadic trial, without another solve or data generation.
Neither quantity alone determines the actual Schur sign. The separate
small-Rayleigh upper ceiling uses another test and supplies no lower
margin for this direction.

The following primary sources supply methods to reuse, with their
remaining interfaces stated explicitly. Locators refer to the inspected
arXiv versions, rather than presumed publisher numbering.

| Inspected source | Reusable result | Interface still required here |
|---|---|---|
| Zimmerling–Druskin–Simoncini, [arXiv:2407.21505v3](https://arxiv.org/pdf/2407.21505v3), §5.1, Proposition 3 and (22), pp.12–13; Algorithms 1–2 | For finite real SPD $\mathcal A$, an orthonormal starting block and nonbreakdown, block Gauss and Gauss–Radau enclose $B^*(\mathcal A+sI)^{-1}B$ in Loewner order for $s>0$. Their difference bounds the error. | Identify full-operator moments/recurrences and pay the discarded exterior, or certify a lifted trial by its full residual. The average of the bounds is not the upper bound. |
| Meurant–Tichý, [arXiv:2502.14979v1](https://arxiv.org/pdf/2502.14979v1), Proposition 7.1/(7.2), Theorems 7.4 and 7.6, pp.10–15 | The prescribed-node block extension and block-CG Radau error relations use a supplied $0<\mu<\lambda_{\min}(\mathcal A)$. The upper-error conclusion uses the stated full-rank and exact-termination conditions. | A Ritz value does not certify the lower endpoint. Finite-precision recurrences, rank loss and the actual infinite tail require their own enclosures. |
| Caruso–Michelangeli, [arXiv:1908.10110v2](https://arxiv.org/pdf/1908.10110v2), Theorem 2.4, Corollary 2.5 and Remark 2.7, pp.7–8 | Unbounded nonnegative selfadjoint operators admit convergence under analytic-vector hypotheses, or the stated quasi-analytic alternatives. The minimization parameter $\xi$ must satisfy $\sigma\le\xi$ for convergence at regularity level $\sigma$. | The hypotheses have not been checked for $C_Nv$. Energy convergence does not imply residual convergence for an unbounded operator, and this theorem supplies no required finite-step numerical certificate. |

For the last row, the zero-initial-guess alternative requires
$g\in\bigcap_{n\ge0}D(H_N^n)\cap\operatorname{ran}H_N$ and
$\sum_{n\ge1}\|H_N^ng\|^{-1/n}=\infty$.
In that source, energy and residual levels are respectively $\sigma=1$
and2; choosing an energy-minimizing iteration does not automatically
give the residual-level conclusion.
The inspected PDF SHA-256 values, in table order, are
`fc623e1894666ec015d50d5fb16c05be1d1437d08d264edf21463dfd07f5cf00`,
`0b6a692094a792649f6b354334f7fc5c638c61779eb7e880e4c9560812be5851`
and `a0357d7d6b56f5e41e9ee799d076b650f40be066adc1f4f8c4cf68089e0f94a6`.
These source readings do not constitute independent proof verification
or a claim that no other relevant result exists.

The positive shift in the first row can be parameterized without assuming
the missing retained sign. The existing bounded majorant gives
$H_N\succeq\eta I$ with $\eta=\|W\|^{-1}$; choose
$0<\mu<\eta$ and formally set $\mathcal A=H_N-\mu I$, $s=\mu$.
This specifies the source's shift, but $\mathcal A$ is still unbounded:
running its algorithm on a finite compression alone does not bound
the actual $H_N^{-1}$.

A proposal algorithm can instead be separated from acceptance. Reuse
the [existing inverse-residual identity](liu2026tailcompensation.md#a-common-256-mode-consumer)
with a finite-rank trial $Y$ into $D(H_N)$ and the actual residual
$R=C_N-H_NY$. It supplies

$$
\begin{aligned}
U_Y&=C_N^*Y+Y^*C_N-Y^*H_NY+R^*WR,\\
S_N-(A_N-U_Y)&=R^*(W-H_N^{-1})R\succeq0,
\qquad S_N=A_N-C_N^*H_N^{-1}C_N.
\end{aligned}
$$

Consequently a finite-domain approximation to an actual inverse action,
or to the inverse action on an actual residual, can enrich the exterior
space beyond the two excluded families. Krylov or CG is an existing
proposal mechanism; the complete directed residual and the final signed
lower comparison are the acceptance obligations. A small residual by
itself is not a positive lower certificate, and one tested retained
direction does not certify the entire retained matrix.

The archived middle rows and weighted far moments can be reused only on
their certified column range with their paid remainder amplification.
Adding new trial columns requires their actual $H_N$ action and the
corresponding amplification; changing $W$ requires compatible weighted
moments or a proved comparison. The separate
[partition-based tail floor](desogus2026threegates.md) cannot be assigned
to a different Lanczos complement without a proved inclusion or an
independent tail bound. No new inverse-approximation theorem, successful
enriched completion, actual Schur positivity, cofinal positivity or Lean
verification is asserted by this parameter map.


### A residual-driven completion on the former128-column witness

Keep the same full dyadic $v$ from the128-column obstruction, the same
actual exterior $H_N$ and archived $W$. Write its former trial as
$y_0=E_{128}x_0$ and let $V$ select exterior modes1281 through2048.
The existing finite linear solve applied to

$$
(V^*H_NV)z=V^*(C_Nv-H_Ny_0)
$$

proposes a correction to the actual inverse equation. Round
$y=y_0+Vz$ to768 exact96-bit dyadic coordinates. The640 coordinates
beyond the old exterior span are nonzero. This changes the trial space;
it is not another solve of the excluded fixed-family optimization.

The [enrichment experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/9e286ae630f756dc470b23a6d2a7093465138574/docs/reports/weil-c27)
evaluates the complete actual residual $r=C_Nv-H_Ny$ using every
middle row1281–32768 and the same168 infinite far moments. Extending
the112-feature columns through2048 pays a new operator allowance
approximately $1.80743\times10^{-135}$, using the complete existing
symbol bound. It reuses the old directed $Q(v-y_0)$ and computes only
its exact correction

$$
Q(v-y)=Q(v-y_0)-2\operatorname{Re}\langle y-y_0,C_Nv-H_Ny_0\rangle
+\langle y-y_0,H_N(y-y_0)\rangle.
$$

The existing inverse-residual identity, under the same common-form,
exterior-domain and inverse-comparison premises, gives

$$
Q(v-y)-\|r\|_W^2\le v^*S_Nv\le Q(v-y).
$$

| Quantity on the unchanged complete $v$ | Approximate directed value |
|---|---:|
| Old complete residual energy | $4.3635328423409634\times10^{-10}$ |
| New complete residual energy | $1.0904887215065086\times10^{-10}$ |
| New sufficient lower target | $2.8606682320961359\times10^{-10}$ |
| New upper trial energy | $3.9511569536026445\times10^{-10}$ |

The exact endpoints place the new residual energy below one quarter
of the old value and imply
$2.86\times10^{-10}<v^*S_Nv<3.96\times10^{-10}$ under those premises.
The finite solve only proposes $y$; the complete residual supplies the
infinite-exterior comparison. This certifies one scalar direction and
does not establish full retained positivity. It changes neither earlier
fixed-family exclusion, determines no other retained direction and
supplies no cofinal positivity or RH proof. The original orthonormal
mass is retained; these values are quadratics rather than asserted
normalized eigenvalues. No old scalar, moment, Gram or eigensolver
production, new general inverse theorem or Lean verification is claimed.


### A finite Trummer representation and a joint residual obstruction

The finite displacement machinery is existing numerical linear algebra.
Poloni, [arXiv:0903.4569v3](https://arxiv.org/pdf/0903.4569v3), p.3,
defines the same-node, injective-node **Trummer-like** case: the generators
determine the off-diagonal entries, while the actual diagonal must be
supplied independently. Lemma1, p.3, gives the finite Schur generator
update. Theorem4, p.11, gives the sum, product and inverse displacement
rules; equation(6), p.12, updates the separately stored diagonal.
Algorithms5–6, pp.21–22, supply the Trummer-like solve/inverse interfaces.
The inspected PDF SHA-256 is
`8e66a68746455a54ee68a143cd6e0843736113419a28bb7b8e37ce0612bacf8e`.
Section7, p.17, explicitly discusses generator growth and the need for
actual residual checks. These algorithms supply no arithmetic positivity
theorem or universal stability guarantee. The arXiv source includes
Matlab and Fortran implementations; no implementation is copied here.

For a finite actual even compression, put $D=\operatorname{diag}(n^2)$,
$\kappa=2/\pi$, $J_2=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$
and $G=(a,b)$, where
$a_n=(-1)^nk_n$, $b_n=a_nns_n$, $k_0=1/\sqrt2$ and $k_n=1$ otherwise.
The existing actual arithmetic entries give

$$
DQ-QD=\kappa GJ_2G^*,\qquad
Q_{mn}=\kappa\frac{a_mb_n-b_ma_n}{m^2-n^2}\quad(m\ne n).
$$

The Gamma, prime and pole diagonal remains unchanged. No infinite
generator identity is inferred: these generator columns need not be
square summable.

Let $V$ select exterior modes1281–2048, $F=V^*H_NV$, $B=V^*C_N$,
$X=F^{-1}B$ and $Y=VX$. The existing exterior floor makes $F$ positive.
Two right-hand sides $U=F^{-1}G_E$ determine the updated finite
generators $G'_P=G_P-B^*U$ and reconstruct every column of $X$:

$$
X_{mn}=\kappa\frac{U_{m1}G'_{n2}-U_{m2}G'_{n1}}{m^2-n^2}
\quad(m\in E,\ n\in P).
$$

The selected residual is exactly zero. For the finite remaining middle
$O=\{2049,\ldots,32768\}$, the same finite Schur update gives
$G'_O=G_O-Q_{OE}U$ and the actual residual $R_O=Q_{OP}-Q_{OE}X$.
Put $T=R_O^*W_OG'_O$. The finite product rule yields

$$
D_P(R_O^*W_OR_O)-(R_O^*W_OR_O)D_P
=\kappa\bigl(TJ_2(G'_P)^*+G'_PJ_2T^*\bigr).
$$

Thus $A_N-B^*F^{-1}B-R_O^*W_OR_O$ has displacement rank at most4,
with its diagonal separately evaluated. This eliminates a new dense
middle-Gram multiplication. It does not determine the sign. The far
part retains all168 archived moments, the112-feature transform
$P_P-P_EX$, and the complete symbol/error allowance. Its transported
scalar charge is bounded by
$\epsilon(1+\|X\|_F^2)$, approximately $2.07733\times10^{-135}$.
It is not replaced by an infinite generator sum or an assumed positive
moment midpoint.

The [complete joint experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/443c0e6b5debab077cc317e35478638a3befc28c/docs/reports/weil-c27)
constructs one explicit sufficient lower target on all1281 original
orthonormal coordinates. Symmetric diagonal pivoting certifies1263
positive pivots before an uncertain pivot leaves18 coordinates.
Reconstructing the same complete target and applying the library's
validated dense solve to that positive block gives an18-dimensional
Schur complement. All18 diagonal upper endpoints are negative; for
the first remaining coordinate, mode0, the diagonal is less than
$-5.77\times10^{-31}$. One negative diagonal already rejects this
explicit sufficient target. It does not establish18 negative
eigenvalues, negativity of the actual $S_N$, or exclusion of every
other trial with the same support.

The two-right-hand-side trial is the exact implicit $F^{-1}B$; it is
different from the rounded scalar trial above. The result retains all
finite middle rows and the paid infinite far part. The existing
inverse-residual comparison still supplies the analytic acceptance
interface under the same common-form, domain and inverse-majorant
premises. Full c27 Schur positivity, a successful joint lower target,
cofinal positivity and RH remain unresolved. This is a numerical
application of existing displacement/Schur methods, with no new general
algorithm, priority or Lean-verification claim.


### The fixed768-column family fails after trial optimization

The chosen-trial obstruction leaves open whether another trial on the
same support could succeed. The [support optimization experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/a5fec125e7ecaf443205d4c72c0cbae9b270585d/docs/reports/weil-c27)
uses the existing square-completion comparison above to settle this
question for the same selected modes1281–2048 and archived $W$.

Take the saved complete target's positive1263-coordinate principal
block $P$ and lift remaining Schur coordinate0 by
$(-P^{-1}be_0,e_0)$. Round to the stored exact256-bit dyadic retained
vector $v$, keeping all1281 coordinates and its exact mass
$\|v\|^2\simeq2.0458788430940653$. Its saved-target quadratic remains
below $-5.77\times10^{-31}$. This is a different direction from the
earlier128-column witness repaired by scalar enrichment.

For this fixed $v$, write

$$
Z=H_NV,\quad F=V^*H_NV,\quad
K=Z^*WZ-F,\quad t=Z^*WC_Nv-V^*C_Nv,
$$

and $m(x)=Q(v-Vx)-\|C_Nv-Zx\|_W^2$. All finite middle rows1281–32768
enter the weighted Gram. The same finite displacement product rule,
with actual diagonals and overlapping selected rows, certifies
$K\succeq I/16$ by768 positive pivots of its finite lower matrix.
The omitted actual far Gram is positive semidefinite; the signed
moment midpoint is not assumed to be positive.

The existing square-completion identity then gives

$$
\sup_xm(x)=m(x_0)+(t-Kx_0)^*K^{-1}(t-Kx_0)
\le m(x_0)+16\|t-Kx_0\|^2.
$$

The finite solve only proposes the stored exact384-bit dyadic $x_0$.
The full residual calculation reuses all168 moments,112 far features
and the original extended-support operator-error upper bound. It pays
$\varepsilon\|v-Vx_0\|^2$ for the quadratic and
$\varepsilon\|v-Vx_0\|$ for each gradient coordinate. The finite Gram
generators and direction-dependent actions are separately archived,
so alternative floor and optimization consumers need no middle-row
production.

The directed result gives
$m(x_0)\simeq-4.22459205900814696498591\times10^{-31}$ and a stored
correction bound at most $2^{-512}$. The exact upper endpoint for
$\sup_xm(x)$ is below $-4.22\times10^{-31}$. Therefore **every** trial
matrix on this fixed768-column support with this same $W$ fails to
make its inverse-residual lower target positive semidefinite.
This excludes the ideal sufficient family, rather than only the
earlier target with its conservative uniform far allowance.

The common-form, exterior-domain and inverse-majorant premises are
unchanged. The conclusion gives neither negative actual Weil energy
nor exclusion of other supports or majorants. It does not undo the
earlier positive scalar enclosure on a different direction. Full
actual Schur positivity, cofinal positivity and RH remain open.
This is an application of existing finite displacement and
square-completion methods, without a new general theorem, normalized
eigenvalue or Lean-verification claim.


### Retaining actual positive Gamma boundary channels in the inverse

The fixed-support exclusion holds for its specified $W$. A different
majorant can retain the positive even Gamma boundary energy already
displayed after G6. Reuse that series, the
[existing variational inversion and Woodbury application](fukushima2011dirichlet.md#keep-the-high-constraint-and-the-exact-ground-term),
and the actual residual identity above. This is an application to the
same exterior, not a new general inverse theorem.

For $b_j=2j+1/2$ and exterior cosine index $n>N$, define

$$
h_{j,n}=\frac{2b_j(-1)^n}{\sqrt d\,[b_j^2+(2\pi n/d)^2]}.
$$

Integrating the existing cosh boundary response against the original
orthonormal cosines identifies its $j$th positive term as
$(1-e^{-b_jd})h_jh_j^*$. For a finite bin $[a,b)$ of rates, set

$$
c_a=1-e^{-b_ad},\qquad
U_{[a,b)}=\sqrt{\frac{c_a}{b-a}}\sum_{j=a}^{b-1}h_j.
$$

Finite Cauchy--Schwarz and monotonicity of $1-e^{-b_jd}$ give
$\sum_{j=a}^{b-1}(1-e^{-b_jd})h_jh_j^*\succeq
U_{[a,b)}U_{[a,b)}^*$. Every column has infinite exterior support
and belongs to $\ell^2$. Keep nineteen disjoint bins with endpoints
$0,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765$,
and collect these columns in $U$.

The archived $W$ rounds the reciprocals of the elementary logarithmic
Gamma-minus-prime comparison upward, with a constant far weight $D$.
Consequently $W^{-1}$ is bounded above by that diagonal lower
comparison. The existing positive even pole term can be dropped while
retaining these Gamma channels, giving, on the same actual form domain,

$$
H_N\succeq W^{-1}+UU^*,\qquad
H_N^{-1}\preceq W_{\rm G}:=
W-WU(I+U^*WU)^{-1}U^*W\preceq W.
$$

This changes the majorant that was fixed in the exclusion; no new
finite support trial or finite solve on that excluded family is used.
For exactly the saved direction $v$ and saved trial $y=Vx_0$, put
$r=C_Nv-H_Ny$, $\beta=U^*Wr$ and $S=I+U^*WU$. Then

$$
Q(v-y)-\|r\|_{W_{\rm G}}^2
=Q(v-y)-\|r\|_W^2+\beta^*S^{-1}\beta
\le v^*S_Nv.
$$

#### A paid infinite-support directional update

The [boundary-channel experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/968e46e90748065c12ee915937f4019805a5ed91/docs/reports/weil-c27)
consumes the saved dyadic $v,x_0$, original margin, diagonal weights,
scalar rows and far residual energy. It archives the previously unsaved
residual action on rows1281–32768, using direct rows through4096 and
the existing finite geometric expansion thereafter. The order128
remainder is bounded by its absolute coefficient sum and geometric
tail. It generates neither the old Gram nor new scalar or far moments.

FLINT's existing digamma implements the finite rate sum directly:

$$
\sum_{j=a}^{b-1}\frac{b_j}{b_j^2+\omega^2}
=\frac12\Re\left[
\psi\left(b+\frac14+\frac{i\omega}2\right)
-\psi\left(a+\frac14+\frac{i\omega}2\right)\right].
$$

Write $U_0,r_0,W_0$ for the complete finite middle rows and let
$E_\infty$ be the archived upper bound for the actual far residual
energy. If $|U_{k,m}|\le a_k/m^2$ for $m>M$, the sufficient bounds are

$$
\eta_k=\frac{Da_k^2}{3M^3},\quad
\|U_\infty^*W_\infty U_\infty\|\le\delta:=\sum_k\eta_k,
\quad
|\beta_k-(U_0^*W_0r_0)_k|\le\sqrt{\eta_k E_\infty}.
$$

The Gram norm uses the trace bound for a positive matrix, not an
entrywise outer-product comparison. For bin $k=[a,b)$ one can take
$a_k=2\sqrt{c_a/((b-a)d)}(b-a)(a+b-1/2)(d/(2\pi))^2$.
Put $S_0=I+U_0^*W_0U_0$ and
$\beta_0=U_0^*W_0r_0$. A stored exact256-bit dyadic vector $z$ gives
the directed lower gain

$$
\beta^*S^{-1}\beta\ge
2\Re z^*\beta_0-z^*S_0z
-2\sum_k|z_k|\sqrt{\eta_kE_\infty}-\delta\|z\|^2.
$$

The exact endpoints, using512 working bits and a256-bit output grid,
give a gain greater than $6.60\times10^{-31}$ and the updated bound

$$
\boxed{v^*S_Nv>2.37\times10^{-31}.}
$$

This numerical implication is conditional on the stated actual
common-form and exterior-domain identifications, the existing even
boundary and diagonal comparisons, and sound reused enclosures.
It repairs this unchanged complete retained direction and its unchanged
trial. It does not certify the full retained Schur matrix or optimality
for the updated majorant. The finite rate bins are a choice of positive
channels, with no claim that Fibonacci endpoints are necessary or
optimal. Full c27 positivity, cofinal positivity, Lean verification of
this application and RH remain unresolved.

### A coefficient-uniform Gamma update and its fixed-trial obstruction

The preceding repair concerns its saved $v,x_0$. It does not supply a
common trial for all retained coefficients. For that question reuse
instead the original exact map $Y=EF^{-1}B$ from the complete structured
target, where $E$ consists of exterior modes1281–2048. Its residual
$R=C_N-H_NY$ vanishes on those selected rows. Keep the same $W$, nineteen
Gamma channels, full actual exterior and original orthonormal retained
modes0–1280. Define

$$
Q_Y=A_N-C_N^*Y-Y^*C_N+Y^*H_NY,\qquad
T_{\rm G}=Q_Y-R^*W_{\rm G}R\preceq S_N.
$$

This uses the existing residual comparison; $T_{\rm G}$ is a sufficient
lower target, not the actual Schur matrix. Split exterior rows at
$M=32768$ and write

$$
A_0=U_0^*W_0U_0,\qquad \Beta_0=U_0^*W_0R_0,\qquad
R_\infty^*W_\infty R_\infty\preceq
G_R:=P^*KP+aI.
$$

Here $P,K,a$ are the archived112-feature signed far core and its complete
operator allowance for this same trial. Only $G_R$ majorizes the actual
positive Gram; neither $K$ nor $P^*KP$ is assumed positive. The existing
Gamma trace estimate gives $U_\infty^*W_\infty U_\infty\preceq\delta I$,
with $\delta\le0.000106746689$. All middle rows enter $A_0$;
$\Beta_0$ needs only rows2049–32768 because of the exact selected-row
cancellation.

Let $L_{\rm old}=Q_Y-R_0^*W_0R_0-G_R$ be the archived complete lower
target. For any common $\rho>0$, the existing variational inverse
identity and weighted Cauchy give

$$
\boxed{
L_\rho=L_{\rm old}+
\Beta_0^*[I+A_0+(1+\rho^{-1})\delta I]^{-1}\Beta_0
-\rho G_R\preceq T_{\rm G}\preceq S_N.
}
$$

Indeed, insert the common linear channel trial
$z=[I+A_0+(1+\rho^{-1})\delta I]^{-1}\Beta_0v$.
The far mixed term costs $\rho\|R_\infty v\|_W^2+
\rho^{-1}\|U_\infty z\|_W^2$, in addition to the far channel Gram
already subtracted in the variational expression. This accounts for
$1+\rho^{-1}$, not just $\rho^{-1}$. This is an application of those
existing identities, not a new inverse algorithm or RH criterion.

The [joint boundary experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/e3a10ac489f0a3b51817ef46ba8be56d62fc6b22/docs/reports/weil-c27)
supplies only the previously unsaved two residual generators and
$19\times1281$ common thin projection. It reuses the scalar rows,
weights, full target and signed infinite moments. The finite geometric
expansions include their absolute remainders. The derived target keeps
the original four finite displacement generators and the signed kernel
$\operatorname{diag}((1+\rho)K,-[I+A_0+(1+\rho^{-1})\delta I]^{-1})$;
it does not replace the far covariance by a scalar norm.
The inherited target matrix uses a640-bit grid, while its original
allowance metadata uses the512-bit grid identified by the original
pivot packet. These two scales are decoded separately.

At $\rho=1/32$, the complete1281-coordinate target has1263 certified
positive pivots; the next interval contains zero. A validated solve
forms the remaining18-coordinate Schur block. Eigenvalue isolation
is inconclusive, but each diagonal upper endpoint is negative. One
negative diagonal suffices to reject $L_{1/32}$; it does not count
negative eigenvalues or determine the sign of $S_N$.

#### The failure persists in the ideal updated target for this trial

To distinguish a conservative Young bound from a failure of the ideal
$T_{\rm G}$, reuse the saved Schur inverse action at remaining mode0.
Round the full lifted vector to exact256-bit dyadics and call it $v$;
its squared norm is approximately2.058687316. No finite solve is
repeated. Put $S_0=I+A_0$, $\beta_0=\Beta_0v$, and
$E_v=v^*G_Rv$. If $\beta=U^*WRv$, weighted Cauchy gives

$$
\|\beta-\beta_0\|\le e:=\sqrt{\delta E_v},\qquad
S_0\preceq S:=I+U^*WU\preceq S_0+\delta I.
$$

For any exact channel trial $z$, the same variational formula and
$S_0\succeq I$ give the lower and upper gain bounds

$$
2\Re z^*\beta_0-z^*S_0z-2e\|z\|-\delta\|z\|^2
\le\beta^*S^{-1}\beta
\le\beta_0^*S_0^{-1}\beta_0+2e\|\beta_0\|+e^2.
$$

The old far approximation has a two-sided operator error at most $a$.
Consequently its paid lower target differs from the ideal old target
by between zero and $2a\|v\|^2$. Including that discrepancy, the directed
consumer gives the following rounded values on this unnormalized $v$:

| Quantity | Value or enclosing range |
|---|---:|
| $v^*L_{\rm old}v$ | $-3.821226857\times10^{-31}$ |
| Upper bound $E_v$ for actual far residual energy | $2.812318944\times10^{-32}$ |
| Gamma gain | between $2.643731998\times10^{-31}$ and $2.680490019\times10^{-31}$ |
| $v^*L_{1/32}v$ | $-1.177716569\times10^{-31}$ |
| Ideal $v^*T_{\rm G}v$ | strictly between $-1.18\times10^{-31}$ and $-1.14\times10^{-31}$ |

The exact directed endpoints, rather than the displayed rounded
centers, establish these signs. The1024-bit consumer uses the saved
finite projections, far covariance and lifted action. These are
numerical implications under the same actual form/domain and inverse
comparison premises, without Lean verification.

Thus a sharper payment for the tails or a different $\rho$ cannot
certify this unchanged $Y,W_{\rm G}$ target: its ideal value is already
negative in this direction. Reoptimizing the trial on $E$, adding
Gamma channels or changing the inverse comparison are different
questions. The next application addresses the first. The earlier saved $v,x_0$ repair remains
valid because it uses a different trial and direction. No negative
upper bound for the actual Schur form has been obtained. Full c27
positivity, cofinal positivity and RH remain unresolved.

### Optimizing the trial for the changed Gamma comparison

Keep the same nineteen-channel $W_{\rm G}$, full retained dyadic
direction $v$, selected768-mode isometry $E$, $F=E^*H_NE$ and
$Z=H_NE$. Parameterize every trial on this support by
$y=Yv+Et$, where $Y=EF^{-1}B$ is the original exact Galerkin map.
Its ideal sufficient margin and gradient are

$$
m_{\rm G}(t)=v^*Q_Yv+t^*Ft-\|Rv-Zt\|_{W_{\rm G}}^2,
\qquad
g_{\rm G}(t)=Z^*W_{\rm G}Rv-K_{\rm G}t,
\quad K_{\rm G}=Z^*W_{\rm G}Z-F.
$$

The following computation applies the existing variational inverse,
finite displacement products and square completion. It supplies no
new general inversion theorem. The scalar rows, finite weighted
support Gram, original complete target, signed far moments and saved
direction are reused.

Write $D_0=U_0^*W_0Z_0$, $G_Z=Z_0^*W_0Z_0$ and
$S_0=I+U_0^*W_0U_0$. For any selected coefficient $t$, the same
channel variational formula gives

$$
\begin{aligned}
t^*Z^*W_{\rm G}Zt
&=\min_z\left\{\|Z_0t-U_0z\|_{W_0}^2
 +\|Z_\infty t-U_\infty z\|_{W_\infty}^2+\|z\|^2\right\}\\
&\ge t^*(G_Z-D_0^*S_0^{-1}D_0)t.
\end{aligned}
$$

Thus the finite matrix
$K_{{\rm G},0}=G_Z-F-D_0^*S_0^{-1}D_0$ is a lower bound for
$K_{\rm G}$. Dropping the complete far square preserves the
direction of this bound and its joint channel dependence.
The existing structured interval LDL, with the rank19 correction
and independent diagonal retained, certifies all768 positive pivots
of $K_{{\rm G},0}-I/16$. Consequently

$$
\boxed{K_{\rm G}\succeq K_{{\rm G},0}\succeq I/16.}
$$

Only the previously unsaved $19\times768$ action $D_0$ and two
mixed inverse generators are produced. The action includes every
row1281–32768 and the actual selected diagonal. Direct rows end
at4096; a384-term finite geometric expansion covers the remainder,
with uniform ratio $2048/4097$ and its absolute remainder paid.

For the mixed action $J_0=Z_0^*W_0R_0$, let $G_E,G_O$ be the
original selected and middle generators, $G_P$ the archived
transformed retained generator, and put

$$
V=F^{-1}G_E,\quad \widetilde G_O=G_O-Z_0V,\quad
T_Z=Z_0^*W_0G_O,\quad T_R=R_0^*W_0\widetilde G_O,\quad
V_A=F^{-1}(T_Z-G_ZV).
$$

The finite displacement product reconstructs the disjoint-node action as

$$
(F^{-1}J_0)_{mn}=\frac{\kappa}{m^2-n^2}
\left[(V_A)_{m0}(G_P)_{n1}-(V_A)_{m1}(G_P)_{n0}
 +V_{m0}(T_R)_{n1}-V_{m1}(T_R)_{n0}\right],
$$

where $\kappa=2/\pi$, $1281\le m\le2048$ and $0\le n\le1280$.
The old $V,G_Z,T_Z,T_R,G_P$ are reused; only $V_A$ needs two
new right sides. This identifies the required common action
without a new middle Gram or full retained solve.

The [changed-trial consumer](https://github.com/the-omega-institute/trureturing-experiments/tree/eff515f544bb5ffa572322c78889a2d528b5bcf9/docs/reports/weil-c27)
fixes an exact384-bit dyadic correction $t_0$ proposed by the changed
finite normal system. It encloses its full ideal margin and gradient,
including the existing signed far error on the transformed original
columns and the entire Gamma mixed tail. It adds back the full
interval for the original paid allowance on its512-bit metadata grid;
the original matrix still uses its distinct640-bit grid.
Square completion now gives

$$
\sup_t m_{\rm G}(t)
\le m_{\rm G}(t_0)+16\|g_{\rm G}(t_0)\|^2.
$$

On this same unnormalized $v$, the directed endpoints imply

$$
-4.102\times10^{-32}<m_{\rm G}(t_0)<-3.652\times10^{-32},
\qquad \|g_{\rm G}(t_0)\|<1.943\times10^{-17},
$$

and the computed optimization correction is less than
$6.041\times10^{-33}$. The combined upper endpoint gives

$$
\boxed{\sup_t m_{\rm G}(t)<-3.04\times10^{-32}.}
$$

These are conditional numerical implications under the same actual
common-form, exterior-domain, inverse-comparison and sound enclosure
premises. The finite normal system proposes the trial; its solution
is not substituted for the infinite exterior inverse. All scientific
endpoint pairs and exact trial coefficients are checked by a cached
higher-precision consumer. No old scientific producer is rerun.

Thus every trial supported on these same768 modes fails to certify
this retained direction with this fixed nineteen-channel $W_{\rm G}$.
This also excludes a common linear trial on this support for all
retained coefficients. Enlarging or changing the trial support,
adding Gamma channels and improving the inverse comparison remain
distinct unresolved possibilities. The bound is an upper bound on
the best sufficient target in this family, not an upper bound on the
actual Schur form. No actual negative Weil test, full c27 positivity,
cofinal positivity, Lean verification of this application or RH
resolution is established.

### Keep the even pole and resolve the discarded rate contrasts

The nineteen-channel exclusion concerns its specified comparison.
Two further positive contributions can be retained using the existing
even pole formula and finite orthogonal projection. Neither operation
changes the actual exterior $H_N$, its original orthonormal mass,
the selected support or the complete retained direction.

For $d=\log27$, the first Gamma bin is the singleton $[0,1)$,
with $b_0=1/2$ and $c_0=1-e^{-d/2}$. Its exterior cosine moments obey

$$
\int_I\phi_n(x)\cosh(x/2)\,dx
=\sqrt2\sinh(d/4)h_{0,n}.
$$

On even complex tests the full pole is
$2|\int_I f(x)\cosh(x/2)\,dx|^2$. Consequently its exterior rank-one
matrix can be combined with the existing singleton Gamma channel:

$$
c_0+4\sinh^2(d/4)=e^{d/2}-1=e^{d/2}c_0.
$$

Thus retaining the pole requires only scaling that channel by
$s=e^{d/4}=27^{1/4}$. Scale row and column0 of the saved finite
channel Gram by $s$, and row0 of both $\Beta_0=U_0^*W_0R_0$ and
$D_0=U_0^*W_0Z_0$ by $s$. The additional far trace allowance is
$(s^2-1)\eta_0$, where

$$
\eta_0=\frac{Dc_0}{3M^3d}\left(\frac d{2\pi}\right)^4.
$$

No new finite action is needed for this pole update. The pole was
already present in the actual form and residual; its newly retained
role is in the lower comparison used to bound the exterior inverse.
For non-even tests the pole pair need not be positive, so this
construction is restricted to the existing even sector.

To retain information inside each old rate bin $[a,b)$, keep its
coefficient weight $c_a$ and split at an integer $m$.
Put $p=m-a$, $q=b-m$ and $\ell=p+q$. Alongside the old mean keep
the contrast

$$
V_{a,m,b}=\sqrt{c_a}\left[
\sqrt{\frac q{p\ell}}\sum_{j=a}^{m-1}h_j
-\sqrt{\frac p{q\ell}}\sum_{j=m}^{b-1}h_j\right].
$$

The mean and contrast have orthonormal coefficient vectors on the
same rate family. More levels use the same $c_a$ throughout that
original bin. Finite Bessel projection therefore gives

$$
U_{[a,b)}U_{[a,b)}^*+
\sum_{\text{retained details}}V V^*
\preceq c_a\sum_{j=a}^{b-1}h_jh_j^*
\preceq\sum_{j=a}^{b-1}(1-e^{-b_jd})h_jh_j^*.
$$

This is a classical orthogonal projection application. The original
channels are retained exactly; a contrast resolves a rate distinction
that their means discarded. One midpoint split of every non-singleton
original bin adds16 contrasts, for35 total channels. Fibonacci
endpoints select these bins but are not required by the argument.
The same actual-test comparison must still be certified after the
additional channels; the old Hessian floor is not assumed to survive.

The finite contrast actions use the existing digamma rate sums and
finite Cauchy products. Only the new mean/detail cross block, detail
Gram and detail projections against all retained and selected support
columns are generated. The nineteen parent aggregates, scalar rows,
transformed residual generator and signed far moments are reused.
Every finite middle row1281–32768 is included. Direct support rows end
at4096; the384-term remainder uses ratio2048/4097. The full-coefficient
projection uses512 terms and ratio1280/2049 on rows2049–32768.
Both absolute remainders are paid.

For a detail from the displayed split, the function
$b/(b^2+\omega^2)$ is $1/\omega^2$-Lipschitz, and the means of
the two arithmetic progressions of rates differ by $\ell$. Hence

$$
|V_n|\le a_Vn^{-2},\qquad
a_V=2\sqrt{c_a/d}\sqrt{pq\ell}\left(\frac d{2\pi}\right)^2,
\qquad \eta_V=\frac{Da_V^2}{3M^3}.
$$

The enlarged positive far Gram has norm bounded by its trace, using
the old trace allowance plus the additional $\eta_V$. This preserves
all cross-channel terms; it is not an entrywise Loewner estimate.
Use the assembled common $S_0,D_0,\Beta_0$ in the same finite
shorting and gradient estimates above.

For each of the following changed comparisons, all768 directed
pivots again certify $K_{{\rm G},0}\succeq I/16$. The exact saved
dyadic direction and support are unchanged:

| Positive terms retained in the inverse comparison | Certified upper for $\sup_t m(t)$ |
|---|---|
| Original nineteen means and the complete even pole | $-3.0484\times10^{-32}$ |
| Those terms and16 rate contrasts | $-2.9782\times10^{-32}$ |

The inequalities are strict. For the35-channel comparison, its
saved384-bit trial satisfies

$$
-4.047\times10^{-32}<m(t_0)<-3.5939\times10^{-32},\qquad
\|g(t_0)\|<1.962\times10^{-17},
$$

and the optimization correction is less than $6.158\times10^{-33}$.
The same square completion bounds every trial on these768 modes,
including any common linear trial. These numerical implications
retain the actual common-form/domain and sound comparison/enclosure
premises. The [cached application](https://github.com/the-omega-institute/trureturing-experiments/tree/440b807ade6716976010adaf42c876b339ff9275/docs/reports/weil-c27)
preserves the new actions, exact trials and directed endpoints;
higher-precision cached consumers check them without repeating
scientific production.

Retaining these extra positive terms improves the comparison but
still excludes certification of this direction by this specified
family. This does not exclude arbitrary finer channels, other
supports or the full Gamma comparison, and does not upper-bound the
actual Schur form. A full-family saturation bound or a quantitatively
stronger comparison is a separate missing estimate. No new general
projection theorem, Lean result, actual c27/cofinal positivity or RH
resolution is asserted.

### A common finite dual bound for the complete Gamma comparison

Keep the same complete retained dyadic direction $v$, the same
$768$-mode support $E$ and the same archived diagonal
$\Lambda=W^{-1}$. Write $B_{\rm GP}=\Gamma_{\rm b}+P_{\rm even}$ for
the **complete** Gamma boundary and positive even pole, and set

$$
T=\Lambda+B_{\rm GP},\qquad H\succeq T>0.
$$

Here $H$ is the actual exterior operator. The common-form/domain and
sound comparison premises above are retained. This comparison keeps
all Gamma rates, rather than another selection of finite bins.
For every channel matrix satisfying $UU^*\preceq B_{\rm GP}$,
inverse monotonicity gives $m_U(t)\le m_T(t)$ for the same support
correction $t$. Thus a strictly negative upper for
$\sup_t m_T(t)$ would exclude every such channel refinement with
this fixed $E,\Lambda,v$.

Use actual support coordinates $x_0=F^{-1}B_{\rm ret}v$, where
$F=E^*HE$ and $B_{\rm ret}$ is the actual retained/support coupling.
Define

$$
Q=v^*Av-x_0^*Fx_0,\qquad Z=HE,\qquad
r=Cv-Zx_0,\qquad E^*r=0.
$$

Then $m_T(t)=Q+t^*Ft-(r-Zt)^*T^{-1}(r-Zt)$.
Choose one nonzero finite exact dyadic vector $w$ disjoint from $E$.
Restrict the existing inverse variational formula to the common dual
space $X=[E,w]$. With

$$
B_0=E^*TE,\quad b=E^*Tw,\quad \beta=w^*Tw,\quad
a=w^*r,\quad z=w^*Z,\quad D=F-B_0,
$$

this gives, for every common $t$,

$$
m_T(t)\le\mathcal U_X(t)
=Q+t^*Ft-
\binom{-Ft}{a-zt}^{\!*}
\begin{pmatrix}B_0&b\\b^*&\beta\end{pmatrix}^{-1}
\binom{-Ft}{a-zt}.
$$

All quantities are evaluations on this same $v,w$ and actual source.
No Fourier tail is discarded from $r$ or $T$: only the dual trial
space is restricted, and its vectors have finite support.

The earlier prime comparison supplies a strictly positive $D$ without
a new theorem. Indeed, with $A_\Gamma$ the periodic Gamma diagonal and
$C_{\rm p}$ the complete prime translation sum,

$$
H-T=A_\Gamma-\Lambda-C_{\rm p},\qquad
D\succeq I/632.
$$

The slack follows from the archived G6 bound
$q(59/10-r_q)>1/400$ and $q\le79/50$, together with
$\Lambda\preceq A_\Gamma-(59/10)I$.
Moreover $z^*-b=-E^*C_{\rm p}w$, since $w$ is disjoint from $E$.
These cancellations are available for subsequent consumers.

Finite block inversion and square completion now give the exact
supremum of this **restricted upper bound**:

$$
\sup_t\mathcal U_X(t)=Q-\frac{|a|^2}{h},\qquad
h=\beta-zF^{-1}z^*+(z-b^*)D^{-1}(z^*-b)>0.
$$

For example, eliminating $B_0$ gives
$K=FB_0^{-1}F-F>0$ and
$K^{-1}=D^{-1}-F^{-1}$; one scalar completion then yields the
displayed expression. This is the same finite inversion/variational
method already used above, not a new general Schur theorem.

The complete boundary kernel also reuses existing arithmetic inputs.
For cached actual scalars $s_n,a_n$, add back the fourteen prime-power
sine and cosine terms to obtain

$$
s_n^{\rm GP}=s_n+\sum_{r<27}w_r\sin(\omega_n\log r),\qquad
a_n^{\rm GP}=a_n+2\sum_{r<27}w_r(1-\log r/d)\cos(\omega_n\log r).
$$

Off-diagonal $B_{\rm GP}$ entries use the same actual divided-difference
formula with these scalars. Its independent positive-mode diagonal is

$$
(B_{\rm GP})_{nn}
=a_n^{\rm GP}-\frac{s_n^{\rm GP}}{\pi n}
-\bigl(\Re\psi(1/4+i\omega_n/2)-\log\pi\bigr).
$$

The sine correction in this diagonal is essential. The equivalent
full-rate digamma/trigamma representation follows from
[DLMF 5.7.6](https://dlmf.nist.gov/5.7.E6) and
[DLMF 5.15.1](https://dlmf.nist.gov/5.15.E1). No finite nineteen-channel
trace allowance is used for the full boundary. The current-direction
$Q$ is evaluated from the actual cached scalars and selected inverse;
the older support cache's quadratic belongs to a different direction.

For one exact $384$-bit $w$ on modes $2049$–$4096$, proposed from the
saved thirty-five-channel inverse action, the new directed
[finite application](https://github.com/the-omega-institute/trureturing-experiments/tree/5d7fde18a45ad653a13589cf1435ae856c3091a3/docs/reports/weil-c27)
gives

$$
Q\simeq2.971626487064166\times10^{-30},\qquad
\sup_t\mathcal U_X(t)\simeq6.323379216251768\times10^{-31}>0.
$$

This positive **upper bound** leaves complete-Gamma saturation
undetermined. It is neither a positive sufficient margin nor an
actual Schur-sign conclusion.

A control locates a loss already present in this chosen dual space.
Keep the exact same $v,w$ and archived $t_0$, but use the earlier
thirty-five-channel/pole $T_{35}$ in the finite compression. Its
$35$-dimensional Woodbury inverse gives

$$
\mathcal U_{X,35}(t_0)
\simeq4.847374044137042\times10^{-31}>0,
\qquad
m_{35}(t_0)<-3.5939\times10^{-32}.
$$

Consequently this dual restriction loses more than
$5.2067\times10^{-31}$ at that common trial, even for the already
excluded comparison. In particular, its supremum cannot certify a
negative bound for that comparison. The incomplete dual space must
be addressed before interpreting the complete-Gamma upper as a test
of saturation. Increasing a cutoff or adding further dual vectors
still needs its own common-action estimate; no success is inferred.

The archived program and directed endpoints retain this inconclusive
application and the diagnostic control. They add no scalar supplier,
old optimizer, generic inversion algorithm, Lean result, actual c27
Schur sign, cofinal positivity or RH resolution.

### Extend the common dual action with a finite Hankel enclosure

The complete-rate finite quadratic need not be assembled as a large
square matrix. Reuse the preceding full-rate scalar array and define
$k=2\pi/d$, $\omega_n=kn$, $\Phi_n=-\omega_ns_n^{\rm GP}$.
For any common real centering constant $c$, put

$$
e_n=\Phi_n-\frac\pi4\omega_n-c,\qquad
J_{mn}=\frac{(-1)^{m+n}}{2(m+n)}.
$$

The linear term contributes exactly $J_{mn}$ to the boundary
kernel off the diagonal. On a finite set of distinct positive
integer nodes $n\ge L$, let

$$
e_* =\max_n|e_n|,\quad
\delta_* =\max_n|(B_{\rm GP})_{nn}-1/(4n)|,\quad
\eta=\frac{8e_*}{dk^2(2L+1)}.
$$

Since $|m^2-n^2|\ge2L+1$ for distinct nodes, the finite triangle
inequality gives

$$
|w^*(B_{\rm GP}-J)w|
\le\eta\bigl(\|w\|_1^2-\|w\|_2^2\bigr)
+\delta_*\|w\|_2^2.
$$

Both maxima are evaluated on the actual supplied finite scalar
array, with the independent actual diagonal. The choice of $c$
affects sharpness only. This application needs no special-function
asymptotic remainder, infinite-node regularity or full trace bound.

For the current real coefficients, the existing FLINT polynomial
product evaluates the Hankel part: if
$p(x)=\sum_n(-1)^nw_nx^n$, then

$$
w^*Jw=\sum_{j\ge2L}\frac{[x^j]p(x)^2}{2j}.
$$

The sum is finite. This is polynomial convolution and the same
finite triangle method, rather than a new matrix algorithm.

Keep the preceding exact dyadic prefix $w_P$ on modes $2049$–$4096$
and append $w_T$ on every remaining archived middle mode through
$32768$. Reuse the complete current-direction $Q$, all prefix
scalar components and the old $a,z,b,\beta$ actions. Only the new
tail is rounded, at the same $384$-bit scale and power-of-two
normalization. New residual/support actions use the existing finite
geometric Cauchy products; their direct endpoint checks and absolute
remainders are retained. The prime cancellation
$z^*-b=-E^*C_{\rm p}w$ supplies the new mixed difference.

The new quadratic reuses the actual prefix value through

$$
\beta=\beta_P+
 w_T^*\Lambda w_T+
 \bigl(w^*Jw-w_P^*Jw_P\bigr)+\varepsilon_J.
$$

The parent prefix is exactly the same vector. The displayed
Hankel difference includes both prefix/tail cross terms. Charge
only the new pairs in the triangle bound:

$$
|\varepsilon_J|\le
\eta\left[
(\|w\|_1^2-\|w\|_2^2)
-(\|w_P\|_1^2-\|w_P\|_2^2)\right]
+\delta_{*,T}\|w_T\|_2^2.
$$

Here $e_*$ covers all finite nodes and $\delta_{*,T}$ only new tail
diagonals. The new common action has $30720$ exact dual coordinates
and $31488$ complete boundary-scalar rows. Its paid quadratic
allowance is below $2.272\times10^{-5}$; this is an outward interval
allowance, not a claim of a narrow $640$-bit quadratic enclosure.
The [archived application](https://github.com/the-omega-institute/trureturing-experiments/tree/0dcb5d65cb62704e1cbe81846f76cbbf84e9d41e/docs/reports/weil-c27)
uses the preceding unchanged bound and diagnostic consumers.

The resulting complete-Gamma restricted upper lies between
$2.88818\times10^{-31}$ and $2.88820\times10^{-31}$, so it remains
inconclusive. At the same archived fixed $t_0$, the thirty-five-channel
control now gives

$$
\mathcal U_{X,35}(t_0)
\simeq-1.012916950382631\times10^{-32}<0.
$$

Thus this changed finite dual vector recovers a negative upper at
that fixed comparison/trial. This does not establish negativity of
$\sup_t\mathcal U_{X,35}(t)$, the complete-Gamma optimum or actual
Schur energy. The contrast with the earlier positive fixed-trial
control locates improvement in the common dual action, without
assigning a sign to the still unresolved comparison.

Existing scalar tables, inverses, residual generators, finite Cauchy
products and polynomial multiplication are reused. The new production
took $50.78$ seconds at $1024$ working bits; this is an application
measurement. The inherited actual form/domain and sound-comparison
premises remain. No new general theorem, Lean verification, actual
c27/cofinal positivity or RH resolution is supplied.

### Certify the optimization defect in the complete finite dual space

A positive upper from one dual vector does not decide whether the
entire available finite dual space is insufficient. The existing
inverse variational and weighted residual estimates give a two-sided
diagnostic without changing the original mass or comparison.

Let $J$ denote the coordinate embedding for modes $2049$–$32768$,
$G=B_{\rm GP}$ and $T=\Lambda+G$. With the same $E,F,D,r,Q$ as above,
write

$$
T_J=J^*TJ,\quad Z_J=J^*HE,\quad B_J=E^*TJ,\quad
K_J=Z_J^*-B_J=-E^*C_{\rm p}J,
$$

$$
M_J=T_J-Z_JF^{-1}Z_J^*+K_J^*D^{-1}K_J.
$$

The same finite dual upper for $w\in J$ is
$Q-|w^*r_J|^2/(w^*M_Jw)$, where $r_J=J^*r$.
The inherited $T\succeq\Lambda$ and $D>0$ give
$M_J\succeq\Lambda_J$. Indeed,

$$
\begin{pmatrix}F&Z_J^*\\Z_J&T_J+K_J^*D^{-1}K_J\end{pmatrix}
=
\begin{pmatrix}E^*TE&B_J\\B_J^*&T_J\end{pmatrix}
+
\begin{pmatrix}I\\K_J^*D^{-1}\end{pmatrix}
D
\begin{pmatrix}I&D^{-1}K_J\end{pmatrix}.
$$

The second summand is positive semidefinite. Minimize the quadratic
form in its $E$ coordinate; the diagonal lower bound still leaves
$\Lambda_J$ on the $J$ coordinate. This is finite block elimination,
not a new Gamma floor or a weighted infinite-trace estimate.

Consequently the best upper obtainable from this complete finite
space is

$$
\mathcal U_J=Q-r_J^*M_J^{-1}r_J.
$$

For an arbitrary exact finite dyadic $y$, set

$$
L(y)=2\Re(y^*r_J)-y^*M_Jy,\qquad e=r_J-M_Jy.
$$

Completing the square and using the original $W_J=\Lambda_J^{-1}$
give

$$
0\le r_J^*M_J^{-1}r_J-L(y)
=e^*M_J^{-1}e\le e^*W_Je,
$$

$$
Q-L(y)-e^*W_Je\le\mathcal U_J\le Q-L(y).
$$

A negative right endpoint excludes the specified complete-Gamma
comparison on the same $v,E,\Lambda$. A positive left endpoint
instead excludes success of this finite dual restriction, without
deciding larger finite spaces or the infinite comparison. If the
interval crosses zero, neither conclusion follows. A large residual
upper bound alone is not a lower bound on the true optimization loss.

Only the missing $r_J$ and $M_Jw$ profiles are needed for the first
application: choose $y=\vartheta w$ with an exact dyadic $\vartheta$
and reuse the accepted $Q,a,z,b$ and the full-rate scalar array.
The saved scalar bound did not retain these profiles or its two
inverse vectors. Its existing finite solver supplies
$p=F^{-1}z$ and $q=D^{-1}(z-b)$; then

$$
M_Jw=\Lambda_Jw+J^*G(Jw-Eq)+J^*HE(q-p).
$$

This includes both mixed terms on the same actual object.
The saved residual generators supply the missing $r_J$ by the same
finite geometric Cauchy expansion and its absolute remainder.

For these squared integer nodes, apply the classical
[Toeplitz/Hankel convolution](https://www.netlib.org/utk/people/JackDongarra/etemplates/node384.html)
through existing [FLINT ball polynomial multiplication](https://flintlib.org/doc/arb_poly.html).
For positive distinct $m,n$,

$$
\frac1{m^2-n^2}=\frac1{2m}
\left(\frac1{m-n}+\frac1{m+n}\right).
$$

The Toeplitz kernel has zero diagonal; subtract the Hankel self
term $u_m/(2m)$ before dividing the sum by $2m$. If
$\Phi_n=-\omega_ns_n$ and $K_{mn}=1/(m^2-n^2)$ off the diagonal,
the unphased operator is

$$
\operatorname{diag}(g)+\frac d{\pi^2}
\bigl(\operatorname{diag}(\Phi)K-K\operatorname{diag}(\Phi)\bigr).
$$

Transport the parity factors $(-1)^n$ on input and output.
The independent actual diagonal $g$ is retained. The GP symbol
already contains the pole. This exact finite action needs no
special-function asymptotic, new scalar table or new convolution
algorithm. The adapter consumes Python-FLINT's existing `arb_poly`
multiplication; all directed input balls are inherited without a
binary64 conversion.

The [archived application](https://github.com/the-omega-institute/trureturing-experiments/tree/9c03df10d88643ac843cf7c2c8a5cb4f7fbff5a6/docs/reports/weil-c27)
contains all $30720$ residual and effective-action coordinates and the
two $768$-coordinate inverse actions. With the same accepted exact
$w$, an exact $512$-bit dyadic $\vartheta$ and original weights, the
complete finite optimum satisfies

$$
2.48441\times10^{-31}
<\mathcal U_J
<2.88819\times10^{-31}.
$$

The weighted residual allowance is below $4.03773\times10^{-32}$.
Thus even the best dual direction in this entire finite $J$ cannot
make this restricted comparison upper negative. Further direction
optimization inside the same $J$ cannot cross zero; the actual
comparison supremum may still have either sign. Larger dual spaces
and the actual Schur sign are not decided.

The missing-profile production took $54.63$ seconds at $1024$ working
bits, including direct actual-row checks at $2049,4096,32768$.
This is an application timing, not an asymptotic performance claim.
The old scalar suppliers, complete retained quadratic, channel
optimizers and floor computation were not rerun.

These are applications of existing finite variational, block and
inverse-defect estimates. They supply no new general theorem or
algorithm, Lean verification, actual c27 Schur sign, cofinal
positivity or RH resolution.

### Pay the infinite defect and recover one positive primal direction

The preceding finite lower is also useful for a positive primal
certificate once the missing infinite residual is paid. This is an
application of the same inverse-residual square completion, not a
new positivity criterion. All actual common-form/domain and sound
$H\succeq T=\Lambda+G>0$ premises remain in force; $G$ includes the
complete Gamma boundary and the even pole.

Let $O$ embed all exterior coordinates outside $E$. For a finite
$y$ in those coordinates, write $Z_O=O^*HE$, $K=Z_O^*-E^*TO$ and

$$
p_y=F^{-1}Z_O^*y,\qquad q_y=D^{-1}Ky,\qquad
t_y=q_y-p_y,\qquad g=-Eq_y+Oy.
$$

Define $My=T_Oy-Z_Op_y+K^*q_y$ on this finite input and put
$e=O(r_O-My)$. No boundedness assertion for $M$ on arbitrary
infinite inputs is required. Finite support, the square-summable
columns of $HE$ and bounded $T$ make these actions well defined.
The support equations give

$$
Ft_y+Z^*g=0,\qquad r-Zt_y=Tg+e,\qquad E^*e=0,
$$

$$
g^*Tg-t_y^*Ft_y=y^*My,\qquad g^*e=y^*O^*e.
$$

Consequently, for $L(y)=2\Re(y^*r_O)-y^*My$,

$$
\begin{aligned}
m_T(t_y)
&=Q+t_y^*Ft_y-(r-Zt_y)^*T^{-1}(r-Zt_y)\\
&=Q-L(y)-e^*T^{-1}e\\
&\ge Q-L(y)-e^*We.
\end{aligned}
$$

Here $T^{-1}\preceq W$ uses the original archived diagonal.
Bounded/coercive $T$ and the inherited actual domain suffice; no
exchange of infinite extrema is used. The actual inverse-residual
identity further gives

$$
v^*S_Nv-m_T(t_y)
=(r-Zt_y)^*(T^{-1}-H^{-1})(r-Zt_y)\ge0.
$$

Thus a positive global paid lower establishes a sufficient comparison
and actual Schur positivity in this single direction. A positive
finite restricted upper alone had supplied neither conclusion.

Take precisely the archived $y=\vartheta w$ supported on
$J=2049{:}32768$. If $p=F^{-1}z$ and $q=D^{-1}(z-b)$ are the exact
inverse vectors enclosed by the saved profiles, then
$t_y=\vartheta(q-p)$. This is an exact implicit finite correction;
it does not round the profiles to independent dyadic midpoints.
On $J$, the residual is the already saved $r_J-\vartheta M_Jw$.
The accepted finite lower therefore already pays that part of
$e^*We$. Only $m>M_0=32768$ remains.

The archived symbol polynomial supplies that disjoint tail without
another scalar or moment computation. Put $A_0=M_0+1$, $d=\log27$,
$k=2\pi/d$, $\gamma_0=d/\pi^2$ and

$$
c_0=\frac14-\frac{27^{-1/2}}{1-27^{-2}}
+2(\cosh(d/2)-1),\qquad
\rho_n=-kns_n^{\rm GP}-\frac{\pi kn}4-c_0.
$$

The saved smooth polynomial has coefficients $C_0,\ldots,C_{63}$
in $M_0/m$, with exact analytic $C_0=-\pi/4$. Its existing
pointwise remainder satisfies
$\epsilon(m)=a(M_0/m)^{64}+b(M_0/m)^{65}$, $a,b\ge0$.
It follows that $m\epsilon(m)\le A_0\epsilon(A_0)$. In particular,
the saved uniform symbol error at $A_0$ can be used as

$$
R_\infty=
|-kM_0C_1-c_0|
+kA_0\left(\sum_{j=2}^{63}|C_j|(M_0/A_0)^j
+\epsilon(A_0)\right),\qquad
|\rho_m|\le R_\infty\quad(m>M_0).
$$

The constant coefficient is used analytically, rather than multiplying
its exported interval width by unbounded $m$. Coefficients use the
saved $640$-bit grid; the remainder uses its distinct $832$-bit grid.
The smooth symbol already includes the pole, while prime sine terms
are separate. No pole or prime contribution is charged twice.

For positive $n\le M_0<m$, the exact off-diagonal kernel is

$$
G_{mn}=(-1)^{m+n}\left[
\frac1{2(m+n)}+
\gamma_0\frac{\rho_m-\rho_n}{m^2-n^2}\right].
$$

With $a_n=A_0-n\ge1$, the elementary integral bound gives

$$
\sum_{m>M_0}\frac1{(m^2-n^2)^2}
\le\frac{a_n^{-2}+a_n^{-1}}{(A_0+n)^2}=:s_n^2.
$$

Weighted Minkowski therefore supplies, for every finite $x$ on these
nodes and the original constant far weight $D_{\rm far}$,

$$
\|G_{\rm far}x\|_W\le\sqrt{D_{\rm far}}
\left[\frac{\|x\|_1}{2\sqrt{M_0}}
+\gamma_0\sum_n|x_n|(R_\infty+|\rho_n|)s_n\right]
=:\mathcal B_G(x).
$$

This includes the adjacent node $n=M_0$, without a separated-ratio
assumption. All finite $\rho_n$ come from the existing full-rate
scalar array. There is no diagonal in this disjoint action.

For $x$ on $E$, the existing actual-symbol budget
$B_*=2\cosh(d/2)+\sum_{r<27}\Lambda(r)/\sqrt r$ gives
$|H_{mn}|\le2B_*/[\pi(m-n)]$ and hence

$$
\|H_{{\rm far},E}x\|_W
\le\sqrt{D_{\rm far}}\frac{2B_*}{\pi}
\frac{\|x\|_1}{\sqrt{M_0-2048}}
=:\mathcal B_H(x).
$$

The effective action and its residual obey

$$
(Mw)_{\rm far}=G_{{\rm far},J}w
+H_{{\rm far},E}(q-p)-G_{{\rm far},E}q,
$$

$$
\|e_{\rm far}\|_W\le\sqrt{E_r}
+|\vartheta|\bigl(\mathcal B_G(w)
+\mathcal B_H(q-p)+\mathcal B_G(q)\bigr).
$$

Here $E_r$ is the upper energy allowance from the matching saved
current-direction file, not the older support-direction residual.
All three actions refer to the same exact $w,p,q$ and original mass.

The [cache-only application](https://github.com/the-omega-institute/trureturing-experiments/tree/349b56740f5c3355783529672b9049fff5aa1e69/docs/reports/weil-c27)
gives

$$
E_{\rm far}<1.264968\times10^{-31},\qquad
m_T(t_y)>1.2194448\times10^{-31}>0,
$$

under the inherited premises. Consequently this saved original
direction also has $v^*S_Nv>1.2194448\times10^{-31}$ under those
premises. The consumer took $0.36$ seconds at $1024$ working bits;
it reads accepted data and evaluates scalar norm bounds only.
No scalar supplier, moment producer, finite action, inverse solve,
optimizer, floor computation or increased cutoff is used.

This is an application of existing variational and tail estimates.
It establishes neither complete retained-matrix positivity nor a
uniform family of directions. Cofinal Weil positivity and RH remain
unresolved, and this numerical application has no Lean verification.

### A common retained-coordinate correction from the saved dual vector

The preceding positive value uses one saved retained direction. To
transport the same dual vector to all retained coefficients, reuse
the inverse-residual square completion and the ordinary rank-one
and Young bounds. No new general positivity theorem is needed.
Let $R$ be the full retained-to-exterior residual map, so that
$Rv=r(v)$ and $E^*R=0$. Keep the same finite dual $w$, exact
implicit profiles $p,q$, comparison $T$, diagonal $W$ and
finite-input action $M$. Write

$$
u=Mw,\qquad h=w^*M_Jw,\qquad
\delta=u^*Wu-h,\qquad
b=R^*(Wu-Jw).
$$

The finite floor gives $h\ge (Jw)^*\Lambda Jw$. Consequently

$$
\delta=\|u-\Lambda Jw\|_W^2
+h-(Jw)^*\Lambda Jw\ge0.
$$

For every retained $v$ and scalar $\alpha$, the same support
correction $\alpha(q-p)$ gives

$$
m_T(\alpha(q-p);v)
\ge v^*(Q-R^*WR)v
+2\Re(\overline\alpha\,b^*v)-\delta|\alpha|^2.
$$

Here $Q$ denotes the retained matrix of the earlier initial-trial
quadratic. If $\delta>0$, optimizing this displayed sufficient
expression gives the rank-one gain $bb^*/\delta$. It is not an
identity with the optimized actual Schur matrix. If $\delta=0$,
the nonnegative decomposition forces $b=0$, and division by
$\delta$ is not allowed.

Only a finite part of the new common column needs to be produced:

$$
b_{\rm fin}=R_J^*(W_Ju_J-w),\qquad
b_{\rm tail}=R_{\rm far}^*W_{\rm far}u_{\rm far},\qquad
b=b_{\rm fin}+b_{\rm tail}.
$$

The saved vector $R_Jv_0$ cannot substitute for $b_{\rm fin}$,
which has one entry for each of the1281 retained coordinates.
The existing two-generator residual and disjoint Cauchy product
provide precisely this missing adjoint action, including mode0.

Let $L_0$ be the archived complete lower target and retain its
correlated far majorant

$$
F_{\rm up}=P\mathcal K P^*+\varepsilon I
\succeq R_{\rm far}^*W_{\rm far}R_{\rm far}.
$$

The core $\mathcal K$ is signed. Its original upward operator
allowance $\varepsilon$ remains part of $F_{\rm up}$; positivity
is a consequence of the Gram majorization, not an assumption
about that core or its midpoint. The allowance uses the original
result's512-bit grid, although the target matrix uses640 bits.

Reuse $E_M\ge\|u_{\rm far}\|_W^2$ by squaring upward the accepted
effective-action tail norm. This is distinct from the much smaller
scaled residual debit in the preceding single-direction certificate.
For any $\rho>0$, choose common exact upper endpoints
$\delta_{\rm up}\ge\delta$ and $E_M$, and put
$d_\rho=\delta_{\rm up}+E_M/\rho>0$. The common trial
$\alpha(v)=b_{\rm fin}^*v/d_\rho$ and Young's inequality give

$$
\boxed{
L_{\rm new}=L_0-\rho F_{\rm up}
+\frac{b_{\rm fin}b_{\rm fin}^*}{d_\rho}
\preceq S_N.
}
$$

Every term refers to the same residual map, dual vector and
comparison. The column is an exact implicit action enclosed by
balls; replacing it by an uncharged midpoint outer product would
not give this lower bound. This target need not dominate the
earlier19-channel target, because the subtraction also changes
coupling to the good coordinate block. Its sign must therefore
be checked on the complete retained matrix. Positivity on the
old18-coordinate lift or on one saved vector is insufficient.

The [common-column application](https://github.com/the-omega-institute/trureturing-experiments/tree/52c36b144997ab55463ee07d67df65fcf9c1129a/docs/reports/weil-c27)
archives the code, complete new target and its small-block sign test.
The common-column packet encloses all1281 entries. Its1024-bit
production took10.48 seconds; an independent1536-bit cached
consumption gave identical column intervals, and three complete
direct sums at modes0,39,1280 lie in those enclosures. Reusing the
accepted unscaled tail norm gives approximately

$$
E_M=14.1648613043077766231,\qquad
\delta_{\rm up}=298.7040165047722506653,\qquad
d_1=312.8688778090800272884.
$$

The archived endpoints, rather than these rounded displays, specify
the exact upward charges. With $\rho=1$, the existing structured
test on the new complete target certifies1263 positive pivots and
leaves the same18 coordinate modes unresolved. It took54.82 seconds.
The existing validated dense Schur consumer then encloses that new
18-by18 complement in99.48 seconds, without rerunning any supplier
or original target. All18 diagonal lower endpoints are positive,
but this does not establish positivity of their joint matrix.

The full-spectrum enclosure did not isolate eigenvalues. The
classical Sylvester test, using FLINT's existing determinant on
the saved small enclosure, settles the sufficient target without
another solve: its leading two-coordinate principal determinant,
for remaining modes0 and1, satisfies

$$
\det\Sigma_{\{0,1\}}<-3.90918\times10^{-71}<0.
$$

Thus this $L_{\rm new}$ at $\rho=1$ is not positive semidefinite,
despite its positive reduced diagonals. This is a rejection of one
sufficient lower target, not a negative direction of the actual
$S_N$, not an inertia count for the old target, and not a contradiction
to the accepted positive scalar direction. No parameter scan or
higher-precision spectral retry is used. The common column remains
reusable for later joint constructions. All numerical implications
retain the inherited actual domain, comparison and sound-enclosure
premises; no Lean, full actual retained-positivity, cofinal positivity
or RH conclusion is supplied.

#### Reuse the saved good block only after a common monotone gain

The existing [Woodbury interface](fukushima2011dirichlet.md#keep-the-high-constraint-and-the-exact-ground-term)
also specifies which missing data would avoid another complete sign test.
Write the earlier19-channel target, in its saved coordinate order, as

$$
L_* = \begin{pmatrix}P&B_g\\B_g^*&C_c\end{pmatrix},\qquad
X_g=P^{-1}B_g,\qquad \Sigma_*=C_c-B_g^*X_g,
$$

where $P\succ0$ and the complete1263-by18 lift $X_g$ is already
saved. Suppose a later common construction supplies the additional
inequality

$$
S_N\succeq L_*+\mathcal B^*D_*^{-1}\mathcal B,\qquad D_*\succ0.
$$

This monotone-gain premise has not been supplied by the current
Young target: its subtraction of $\rho F_{\rm up}$ cannot be omitted.
For a construction satisfying that premise, put
$\mathcal B_G=\mathcal B[I;0]$ and
$\mathcal B_V=\mathcal B[-X_g;I]$. In the old congruence coordinates,
the exact Schur complement of the updated positive block is

$$
\Sigma_*+\mathcal B_V^*
\left(D_*+\mathcal B_GP^{-1}\mathcal B_G^*\right)^{-1}
\mathcal B_V.
$$

This is the ordinary finite block inverse/Woodbury formula. In
particular, replacing the middle Gram by an upper enclosure
$\overline\Omega\succeq\mathcal B_GP^{-1}\mathcal B_G^*$ gives
a sufficient18-dimensional lower test with denominator
$D_*+\overline\Omega$. Dropping that Gram would leave the good-block
coupling unpaid. The saved lift supplies only $P^{-1}B_g$; it is
not an inverse action on arbitrary new right sides. The remaining
interfaces are a common gain with its actual cross-tail control,
$\mathcal B_V$, and this good-block inverse-metric upper enclosure.
The new finite column is reusable input to such a construction,
not a substitute for those missing objects. No numerical sign or
full retained-positivity conclusion is asserted for this alternative.

#### The saved nineteen-channel base has one negative direction

The [cached lift, cross-row and inertia applications](https://github.com/the-omega-institute/trureturing-experiments/tree/906abfc541483203fde48ffb29ef4486c616e618/docs/reports/weil-c27)
archive the following new thin data and their consumers. All large
actions, scientific suppliers and original inverse actions are reused.

The saved18-by18 complement can be classified without another
retained solve or eigenvalue isolation. Jacobi's signature criterion
uses the signs of its leading determinants $\Delta_k$, with
$\Delta_0=1$: nonzero leading determinants give pivot signs
$\operatorname{sgn}(\Delta_k/\Delta_{k-1})$.
The cached consumer `small_schur_rank_floor.py` finds all18 determinant
intervals strictly negative, using degree-dependent export grids
$640k+64$. Thus its first pivot is negative and the next17 are
positive. Under the inherited exact-complement/enclosure premises,
this OLD nineteen-channel complement has inertia17 positive,
1 negative,0 zero; its full target has1280 positive and1 negative
direction after adding the1263 positive prefix.

The18 small determinants took0.25 seconds and were independently
checked against the same saved core. This is a different object
from both the original $L_0$ complement and the failed new
$\rho=1$ target. Negative diagonals alone had not counted its
negative directions. A positive update of rank one is not excluded
by this inertia: its direction, strength and coupling still matter.
No inertia statement about actual $S_N$ follows.

#### A common inverse majorant and a denominator already in the cache

Keep the original comparison $T$, support $E$, residual $R$ and
finite-input action $M$. Under the existing common form/domain
and inverse identifications, write

$$
B_0=E^*TE,\quad F=E^*HE=B_0+D,\quad D\succ0,\qquad
G=O^*TE,\quad H_c=O^*HE,
$$

where $O$ includes the exterior outside $E$. The effective action
has the inherited block expression

$$
M=T_{OO}-H_cF^{-1}H_c^*
 +(H_c-G)D^{-1}(H_c-G)^*.
$$

The ordinary weighted square completion, with
$H_c=G+(H_c-G)$ and $F=B_0+D$, gives
$M\succeq T_{OO}-GB_0^{-1}G^*$. Consequently
$M^{-1}\preceq O^*T^{-1}O$. These are applications on the admitted
forms and finite inputs; the notation does not supply missing
domain or inverse-existence premises.
Positivity of $H-T$ also gives
$H_{OO}-T_{OO}\succeq(H_c-G)D^{-1}(H_c-G)^*$. The actual exterior
Schur form after eliminating $E$ therefore dominates $M$, yielding
$S_N\succeq Q-R^*M^{-1}R$ on these same forms.

For the SAME old nineteen channels, let

$$
A_\rho=I+A_0+(1+\rho^{-1})\delta_{\rm ch}I,\qquad \rho=1/32,
$$

$$
\overline W=
(W_J-W_JU_JA_\rho^{-1}U_J^*W_J)
\oplus(1+\rho)W_{\rm far}.
$$

Here $A_0$ includes all middle rows, including $E$;
$\delta_{\rm ch}$ is the original channel-tail charge, not
$\delta_{\rm up}$. The earlier common channel trial and Young
bound give $\overline W\succeq O^*T^{-1}O$ and
$Q-R^*\overline W R\succeq L_*$. With $u=Mw$, set

$$
F_\phi=u_J^*W_JU_J,\qquad
\mathcal B=u^*\overline W R-w^*R,\qquad
\mathcal K=u^*\overline W u-h.
$$

The same inverse-residual square completion gives
$\mathcal K\ge0$. In particular

$$
\mathcal K=\delta+\rho\|u_{\rm far}\|_W^2
-F_\phi A_\rho^{-1}F_\phi^*
\le D_*:=\delta_{\rm up}+\rho E_M,
$$

where the accepted common data give $D_*<299.146668420532$.
Choosing the common scalar trial
$\alpha(v)=\mathcal Bv/D_*$, without division by $\mathcal K$, gives

$$
S_N\succeq Q-R^*\overline W R
+\mathcal B^*\mathcal B/D_*
\succeq L_*+\mathcal B^*\mathcal B/D_*.
$$

This conditional application supplies the common-gain inequality;
the actual row and the good-block inverse metric must still be
enclosed tightly enough for its full coupled sign test. The
denominator belongs to this full row, including its far cross;
it cannot be paired with $b_{\rm fin}$ alone.

#### The scalar defect encloses the missing common row without new channels

The cached exact lift $V=[-X_g;I]$ supplies the missing thin data

$$
c=b_{\rm fin}^*V,\qquad \Beta_V=\Beta_0V,\qquad
G_V=(P_{\rm far}^*V)^*\mathcal K_{\rm far}(P_{\rm far}^*V)
+\varepsilon V^*V.
$$

The signed112-feature core and every allowance cross term are
retained. The exact rational $\varepsilon$ is the upper endpoint
of the base's640-bit transported allowance, checked against the
original512-bit metadata. The1024-bit cached products took1.44
seconds; independent1536-bit consumption gave exactly the same3024
matrix interval pairs. No old inverse, target, channel or moment
producer ran.

Put $Z=A_\rho^{-1}\Beta_V$ and
$t_V=u_{\rm far}^*W_{\rm far}R_{\rm far}V$. The full row is
$\mathcal B_V=c-F_\phi Z+(1+\rho)t_V$. The cached Gram $A_0$
majorizes the J-only channel Gram, so weighted Cauchy pays the
finite correction by $\sqrt{e_J(Z^*A_0Z)_{jj}}$, where
$e_J=\|u_J\|_W^2$. The far correction costs
$(1+\rho)\sqrt{E_M(G_V)_{jj}}$. Even these bounds exclude zero
in every coordinate, but do not decide a matrix sign.

There is stronger shared information already available. Let $v_0$
be the accepted exact dyadic retained direction, and reuse its
exact $\vartheta$ and certified finite residual defect

$$
e=R_Jv_0-\vartheta u_J,\qquad e^*W_Je\le E_e.
$$

The saved all-coordinate channel map then gives

$$
F_\phi=(\Beta_0v_0)^*/\vartheta-e^*W_JU_J/\vartheta.
$$

Thus the computable center and error for the FULL common row are

$$
\widehat{\mathcal B}_V=c-(\Beta_0v_0)^*Z/\vartheta,\qquad
|(\mathcal B_V-\widehat{\mathcal B}_V)_j|
\le\frac{\sqrt{E_e(Z^*A_0Z)_{jj}}}{|\vartheta|}
+(1+\rho)\sqrt{E_M(G_V)_{jj}}.
$$

No raw $U_J$ values need to be regenerated for this enclosure.
Relative to the first finite Cauchy radius, the certified defect
factor is less than $0.109095699$. The
`full_gamma_defect_cross.py` consumer takes0.41 seconds and gives,
in the first old-lift coordinate (mode0),

$$
5.99690490660\times10^{-15}
< (\mathcal B_V)_0
<9.65492947706\times10^{-15}.
$$

All18 row intervals exclude zero. Combining their magnitude lower
bounds with the old diagonal enclosures gives
$(\Sigma_*)_{jj}+|(\mathcal B_V)_j|^2/D_*>0$ for every $j$;
the mode0 lower is above $2.44652\times10^{-33}$. These are
restrictions to the OLD lift. They omit the good-block response
and are not the updated Schur complement.

For the scalar common row, a certified
$\Omega\ge\mathcal B_GP^{-1}\mathcal B_G^*\ge0$ must still be
paid in the denominator. A common upper $\Omega<6.21431056$
would preserve all18 positive updated diagonal bounds just
obtained. No such inverse-metric upper has been supplied, and
even positive updated diagonals would leave the off-diagonal
positivity test open. The needed data are the common row's
correlations and a sufficient inverse-metric bound, not another
scalar energy or channel supplier. These are applications of
existing inverse, Cauchy and inertia methods, with no generic
novelty or Lean-verification claim. Full retained and cofinal
positivity, the original Robin tail estimate and RH remain open.

### A shared-error contraction for the full rank-one sign

The same OLD eighteen-coordinate core has exactly one negative
direction. Standard bordered-matrix inertia, equivalently the
rank-one inverse identity, reduces the coupled sign to one scalar:
for $b=\mathcal B_V$, $s>0$ and $q=b\Sigma_*^{-1}b^*$,

$$
\Sigma_*+b^*b/s\succ0\iff s+q<0.
$$

PSD corresponds to $s+q\le0$, with one zero eigenvalue at exact
equality. The exact updated lower-core denominator is
$s=D_*+\Gamma$, where
$\Gamma=\mathcal B_GP^{-1}\mathcal B_G^*\ge0$.
An upper $\Omega\ge\Gamma$ supplies the sufficient test
$D_*+\Omega+q<0$; failure of that test need not exclude the
exact update. This is an application of existing block inertia
and Woodbury algebra, not a new general theorem.

Partition at the negative first pivot:

$$
\Sigma_*=\begin{pmatrix}a&r^*\\r&H\end{pmatrix},\quad
P_+=H-rr^*/a\succ0,\quad
T_+=\binom{-r^*/a}{I_{17}}.
$$

The accepted inertia supplies $P_+\succ0$, and

$$
q=|b_0|^2/a+(bT_+)P_+^{-1}(bT_+)^*.
$$

The scalar-defect transport gives shared information stronger
than independent coordinate radii. For the same actual full row,
$b=\widehat{\mathcal B}_V+f+t$ and

$$
f^*f\preceq C_f=E_e\vartheta^{-2}Z^*A_0Z,\qquad
t^*t\preceq C_t=(1+\rho)^2E_MG_V.
$$

All-middle $A_0$, the signed far core and its entire allowance
remain included. Under the inherited common-form/domain,
inverse/comparison and sound-cache premises, weighted positive
trace bounds the two transported error norms. Let

$$
n_c^2=(\widehat{\mathcal B}_VT_+)P_+^{-1}
(\widehat{\mathcal B}_VT_+)^*,\qquad
n_j^2=\operatorname{tr}(P_+^{-1}T_+^*C_jT_+),\quad j=f,t.
$$

Then the positive term in $q$ lies between
$\max(0,n_c-n_f-n_t)^2$ and $(n_c+n_f+n_t)^2$.
These are conservative simultaneous bounds; they do not assert
joint attainment of separate error extrema.

The [cached correlated-sign application](https://github.com/the-omega-institute/trureturing-experiments/tree/27a634d7fe09e9c20b28215d18e2bd6c051e71b4/docs/reports/weil-c27)
supplies both shared Grams and uses one
validated seventeen-dimensional FLINT solve with thirty-five
right-hand sides. Its1024-bit consumption takes0.40 seconds.
The resulting outer bounds are

$$
-792<q<1.043\times10^{25},\qquad
-493<D_*+q<1.043\times10^{25}.
$$

They determine neither sign and certify no positive good-metric
budget or exclusion of the exact lower update. Independent1536-bit
consumption overlaps all648 Gram intervals and all four intervals
for actual scalar quantities. Among all17 scalar exports,9 overlap
and6 are identical; the eight disjoint exports represent different
computed bound values. The center-energy width ratio is
$0.999999997454$, with the same inconclusive verdict.

The center-only contraction is already broad before adding the
error radii. These data do not distinguish input uncertainty,
conditioning, loss of joint cancellations and validated-solve
overestimation; no condition number or spectral floor was measured.
The exact-reference certificate below supplies useful enclosures of
this center metric and both error traces from the accepted packets.
Their joint full-row sign and the good-block metric remain separate
obligations. Repeating the same interval-box solve supplies no new
source information. Full retained and cofinal positivity, the Robin
tail estimate and RH remain open; this numerical application is not
Lean verification.

### An exact reference and directional residual certificate

The [exact-reference, trace and joint signed applications](https://github.com/the-omega-institute/trureturing-experiments/tree/f5a4f57a7a549684510c928f28042d7d40e4dcfb/docs/reports/weil-c27)
use the existing inverse-residual identity and Neumann comparison on
the same actual $P=P_+\succ0$ and $h=\widehat{\mathcal B}_VT_+$.
From exact rational midpoints of the mirrored core and saved finite
centers, construct $P_0,h_0$, then the small exact FLINT inverse
$R=P_0^{-1}$ and reference profile $x=Rh_0^*$. Exact products check
$RP_0=I$ and $P_0x=h_0^*$. No midpoint positivity is assumed.

Let $\Delta P=P-P_0$, $\delta h=h-h_0$ and
$r=\delta h^*-\Delta Px$. With $E\ge|\Delta P|$ entrywise and
a directed upper $\eta\ge\||R|E\|_\infty$ strictly below one,

$$
hP^{-1}h^*=h_0x+2\operatorname{Re}(\delta h\,x)
-x^*\Delta Px+r^*P^{-1}r,
$$

$$
0\le r^*P^{-1}r\le
\frac{\|r\|_1\|Rr\|_\infty}{1-\eta}.
$$

The exact reference energy avoids evaluating large cancelling terms
as independent intervals. Source uncertainty in the pivot, $T_+$,
center and matrix remains enclosed in the signed corrections.
Under the inherited actual common-form/domain, inverse/comparison
and sound-cache premises, the numerical certificate gives

$$
\eta<3.976\times10^{-28},\quad
|2\operatorname{Re}(\delta h\,x)|<4.39\times10^{-79},
$$

$$
|x^*\Delta Px|<3.30\times10^{-28},\quad
r^*P^{-1}r<1.309\times10^{-55}.
$$

Consequently

$$
391.85784253565945840673491942575
<hP^{-1}h^*<
391.85784253565945840673491942642.
$$

The1024-bit consumption takes0.104 seconds. Independent1536-bit
consumption takes0.092 seconds; all324 exact reference fields match,
the actual correction/energy intervals overlap, and both directed
center widths are below $6.584\times10^{-28}$. These bounds do not
identify the sole cause of the earlier broad interval or measure
an actual condition number or intrinsic uncertainty floor.

The same reference permits a thin error-trace contraction without
another inverse or solve. The Hermitian path $P_0+t\Delta P$ is
nonsingular for $0\le t\le1$ by Neumann. Actual $P\succ0$ therefore
implies $P_0\succ0$ by constant inertia along that path. Since
$R\Delta P$ is similar to a Hermitian matrix and has spectral
radius at most $\eta$, standard congruence/inversion gives

$$
\frac{R}{1+\eta}\preceq P^{-1}\preceq\frac{R}{1-\eta}.
$$

For each same actual PSD $C_j^+=T_+^*C_jT_+$, $j=f,t$,

$$
\frac{\operatorname{tr}(RC_j^+)}{1+\eta}
\le\operatorname{tr}(P^{-1}C_j^+)
\le\frac{\operatorname{tr}(RC_j^+)}{1-\eta}.
$$

The1024-bit thin products take0.030 seconds, retaining every trace
cross term, actual $T_+$ uncertainty and the full far allowance.
The finite/far traces are approximately $8.869400460878844$ and
$6.026200142006464$, with directed actual-trace interval widths
below $8.423\times10^{-27}$ and $5.210\times10^{-27}$ respectively.
The same triangle bounds with the certified center and full-row
$b_0$ now give

$$
-586<q<388,\qquad -287<D_*+q<688.
$$

These marginal bounds leave the sign undecided. The triangle estimate does
not consume every correlation between the negative coordinate and
the positive-subspace errors already recorded in $C_f,C_t$.
A joint signed estimate below uses these correlations to exclude
the $D_*$-based sufficient update. A sufficiently sharper common gain
charge and the good-block inverse metric remain missing. These are
existing exact-rational, inverse-residual and
Loewner methods applied to the saved common object, not new generic
algorithms or Lean proofs. Actual full retained/cofinal positivity,
the original Robin tail estimate and RH remain open.

### A joint signed bound excludes the coarse common charge

The same error Grams retain correlations between the negative
coordinate and positive-subspace errors. Let
$q_c=\widehat{\mathcal B}_V\Sigma_*^{-1}\widehat{\mathcal B}_V^*$
and $g=\Sigma_*^{-1}\widehat{\mathcal B}_V^*$. The accepted reference
profile $x$ and center residual $r_c=h^*-Px$ give

$$
g=g_x+TP^{-1}r_c,\qquad
g_x=(\widehat{\mathcal B}_{V,0}/a)e_0+Tx.
$$

Trace domination of each actual PSD error Gram yields

$$
\|C_j^{1/2}TP^{-1}r_c\|^2\le\tau_jQ_c,\qquad
L_j=\sqrt{(g_x^*C_jg_x)_{\rm up}}
+\sqrt{\tau_{j,\rm up}Q_{c,\rm up}},\quad j=f,t.
$$

Here $Q_c\ge r_c^*P^{-1}r_c$, and $L_j$ bounds the corresponding
linear error. For the full row $b=\widehat{\mathcal B}_V+e$,
$e=f+t$, quadratic expansion gives

$$
q(b)=q_c+2\operatorname{Re}(eg)+e\Sigma_*^{-1}e^*,
$$

$$
-\frac{(\sqrt{(C_f)_{00}}+\sqrt{(C_t)_{00}})^2}{-a}
\le e\Sigma_*^{-1}e^*
\le(\sqrt{\tau_f}+\sqrt{\tau_t})^2.
$$

The1024-bit thin products take0.021 seconds, with no inverse or
solve. Under the inherited actual common-form/domain,
inverse/comparison and sound-cache premises, directed bounds give

$$
-219.39<q<-35.85,\qquad 79.76<D_*+q<263.30.
$$

Independent1536-bit consumption takes0.017 seconds; all17 scalar
interval pairs and the final $q$ interval are endpoint-identical.

Thus the particular $D_*$-based sufficient lower update is not PSD
for any good-block metric $\Gamma\ge0$. This is an exclusion of
that lower construction, not a negative direction for actual
$S_N$ or an exclusion of every rank-one refinement.

The negative upper for $q$ supplies the full coupled sufficient
budget $D_\sharp+\Omega<35.85$, if positive
$D_\sharp\ge\mathcal K$ and $\Omega\ge\Gamma$ are independently
certified for this same common object. No pair meeting this budget
is supplied.
The available identity for $\mathcal K$ implies only

$$
\mathcal K\le D_*-F_\phi A_\rho^{-1}F_\phi^*,
$$

since $D_*$ already bounds
$\delta+\rho\|u_{\rm far}\|_W^2$ upward. A sufficiently strong joint
bound for the common charge and $q$, together with the good-block
inverse metric, remains missing; the ceiling cannot replace the exact
charge in an equality. These are existing quadratic/Cauchy/trace methods applied
to the saved common source, without generic novelty or Lean
verification. Actual full retained/cofinal positivity, the Robin
tail estimate and RH remain unresolved.

### The scalar defect supplies a sharper channel charge

The [experimental source and scalar packet](https://github.com/the-omega-institute/trureturing-experiments/tree/c974ba572b29b33dfc066c7d3ff37267c30c85e5/docs/reports/weil-c27)
retain the consumer and its directed result.

The same original weights, exact $v_0,\vartheta$, saved channel inverse
and accepted scalar defect supply one additional scalar contraction.
Write

$$
F_0=(\Beta_0v_0)^*/\vartheta,\qquad
\eta=e^*W_JU_J/\vartheta,\qquad F_\phi=F_0-\eta,\qquad
k=E_e/\vartheta^2.
$$

Since $U_J^*W_JU_J\preceq A_0\prec A_\rho$, the operator norm of
$W_J^{1/2}U_JA_\rho^{-1/2}$ is at most1. Weighted Cauchy gives
$\eta A_\rho^{-1}\eta^*\le k$, without a channel-count factor.
For $E_0=F_0A_\rho^{-1}F_0^*$, the norm triangle inequalities yield

$$
(\max(0,\sqrt{E_0}-\sqrt{k}))^2
\le F_\phi A_\rho^{-1}F_\phi^*
\le(\sqrt{E_0}+\sqrt{k})^2.
$$

Under the inherited actual common-form/domain, inverse/comparison
and sound-cache premises, the new1024-bit contraction takes0.413
seconds including packet loading. It encloses $E_0$ near
106.3370533152211 and $\sqrt{k}<4.023460$, giving

$$
39.545559<F_\phi A_\rho^{-1}F_\phi^*<205.505007,\qquad
0\le\mathcal K\le D_\sharp<259.601110.
$$

Here $D_\sharp$ is the positive outward ceiling $D_*-L_F$, with
$L_F$ the certified lower endpoint of the squared reverse-triangle
bound. It is not an identity for $\mathcal K$. Combining this
ceiling with the accepted $q$ upper gives a sufficient good-block
metric budget near-223.750468, so the separate bounds provide no
positive allowance for $\Gamma$.

This inconclusive sufficient budget does not exclude a joint
estimate of $\mathcal K+\Gamma+q$. The finite row error and the
channel-energy term contain the same $\eta$; estimating them
separately loses correlations. The good-block inverse metric also
remains missing. The experimental consumer retains $F_0^*$ and
$A_\rho^{-1}F_0^*$ for subsequent common-source contractions.
It reuses the saved inverse and signed bound, with no new inverse,
solve or scientific supplier. This is an application of existing
weighted Cauchy and norm inequalities, without generic novelty or
Lean verification. Actual full retained/cofinal positivity, the
Robin tail estimate and RH remain unresolved.

### Actual source excludes the fixed old-base rank-one lower update

The [experimental consumers and directed packets](https://github.com/the-omega-institute/trureturing-experiments/tree/f9473a5b68a55eac2e3b3239939189d2fae36b24/docs/reports/weil-c27)
separate an information obstruction from an actual-source exclusion.
The error upper envelopes alone admit $\eta=t=0$. At that relaxed
point, the cached finite energy gives
$m_J-h-E_0+q_c>50.028372$, even with zero far action energy.
Thus optimizing those unchanged envelopes cannot force a uniform
negative upper. This relaxed point is not asserted to be realized by
the original source.

The actual nineteen-channel projection instead uses the cached
$u_J=Mw$ and original weights to supply

$$
F_\phi=u_J^*W_JU_J,\qquad
b_J=c-F_\phi A_\rho^{-1}\Beta_V.
$$

Only this missing functional evaluates the original channel shapes;
the effective action, residuals, channel Gram/map and inverse actions
are reused. The1024-bit projection takes15.924 seconds and gives
$E_\phi=F_\phi A_\rho^{-1}F_\phi^*$ near115.345991300848898.
All eighteen finite-row coordinates overlap the original transported
expression $\widehat b+\eta Z$. Independent1536-bit projection
has all79 exported intervals endpoint-identical.

Let $\kappa=1+\rho=33/32$, $s=\|u_{\rm far}\|_W^2\ge0$ and
$t=\kappa u_{\rm far}^*W_{\rm far}R_{\rm far}V$. For this SAME
actual common source,

$$
\mathcal K=m_J-h+\kappa s-E_\phi,\qquad
b=b_J+t,\qquad m_J=\|u_J\|_W^2.
$$

Put $q_J=b_J\Sigma_*^{-1}b_J^*$ and
$g=\Sigma_*^{-1}b_J^*$. The full far Gram $G$, including its
signed core and entire allowance, gives

$$
|t_0|^2\le\kappa^2sG_{00},\qquad
|tg|^2\le\kappa^2s\,g^*Gg.
$$

Using the same one-negative decomposition of $\Sigma_*^{-1}$,
retaining the negative far square and discarding only the
nonnegative positive-complement square, yields

$$
\mathcal K+\Gamma+q
\ge m_J-h-E_\phi+q_J+A s-2B\sqrt{s},
$$

$$
A=\kappa-\kappa^2G_{00}/(-a)>0.7772979,\qquad
B=\kappa\sqrt{g^*Gg}.
$$

The saved exact seventeen-dimensional inverse supplies a new profile
for $b_J$, with residual-energy ceiling below $1.316\cdot10^{-55}$.
It encloses $q_J$ in $(-120.742435,-120.742434)$. The accepted
far trace pays the new gradient remainder, without a new inverse,
solve or trace calculation. Writing the same saved error Gram as
$C_t=\kappa^2E_M^0G$ and using the saved positive lower for $E_M^0$
gives $B^2/A<10.153002$.

Completing the square in $\sqrt{s}$, and using $\Gamma\ge0$, gives
under the inherited actual common-form/domain, inverse/comparison
and sound-cache premises

$$
m_J-h-E_\phi+q_J>48.450729,\qquad
\boxed{\mathcal K+\Gamma+q>38.297727.}
$$

The new1024-bit joint contractions take0.108 seconds. For every
positive $D\ge\mathcal K$, the scalar $D+\Gamma+q$ is consequently
strictly positive. The accepted one-negative-core criterion excludes
PSD of $L_*+\mathcal B^*\mathcal B/D$ for this fixed OLD base $L_*$
and fixed saved dyadic dual $w$. This exclusion uses only
nonnegativity of the good-block inverse metric.

The stronger base $Q-R^*\overline W R$ is not tested by that calculation
alone. Other dual directions and other lower constructions are outside
this exclusion. Actual $S_N$
can dominate this non-PSD lower bound and remain positive. The
calculation supplies no actual $S_N$ negativity or RH counterexample.
Actual full retained/cofinal positivity, the Robin tail and RH remain
unresolved. These are applications of existing residual certification,
weighted Cauchy and square completion, without generic novelty or
Lean verification.

### The paid far-enclosure gap cannot rescue the same fixed dual

The [changed-compression consumer and directed packet](https://github.com/the-omega-institute/trureturing-experiments/tree/a8235067c4a19e422f1ea061876a44b53fb70835/docs/reports/weil-c27)
test $\overline L=Q-R^*\overline W R$ with the same old nineteen
channels, $A_\rho^{-1}$, $\rho=1/32$ and saved fixed dual. The
baseline builders identify the discarded gain without another
inverse or scientific supplier.

Let $\widehat F$ be the signed far approximation, $F_{\rm act}$ the
actual far residual Gram, $\epsilon_0$ the original complete padding,
$\epsilon_1$ the later $\rho$-update padding and $\epsilon$ the exact
rational upper already saved with the lift. The inherited two-sided
far enclosure gives

$$
\|\widehat F-F_{\rm act}\|\le\epsilon_0\le\epsilon_1\le\epsilon.
$$

Writing $C_J=Q-R_J^*W_JR_J+\Beta^*A_\rho^{-1}\Beta$, the actual
source-defined bases satisfy

$$
L_*=C_J-\kappa\widehat F-(\epsilon_0+\rho\epsilon_1)I,
\qquad \overline L=C_J-\kappa F_{\rm act}.
$$

Thus $0\preceq\overline L-L_*\preceq2\kappa\epsilon I$.
The paddings are bounded, not identified as equal. Their original
512-bit metadata grid and transported640-bit grid remain distinct.
This is the same $\overline W$, rather than the different ideal
$W_{\rm G}$ majorant.

Put $H_V=V^*V$, $\delta=2\kappa\epsilon$ and
$\Sigma_{\max}=\Sigma_*+\delta H_V$. Then
$V^*\overline LV\preceq\Sigma_{\max}$. The PSD addition preserves
at least seventeen positive directions; a strictly negative first
pivot leaves exactly one negative direction and no zero direction.
Let $a_{\max}<0$, $P_{\max}\succ0$ and $T_{\max}$ denote its
negative-pivot decomposition.

Reuse the saved exact seventeen-vector $x_J$ only as a variational
trial for this changed complement. With the same actual finite row
$b_J$, define

$$
q_{J,\rm trial}=|b_{J,0}|^2/a_{\max}
+2\Re(b_JT_{\max}x_J)-x_J^*P_{\max}x_J,
\qquad
g_x=(\overline{b_{J,0}}/a_{\max})e_0+T_{\max}x_J.
$$

For $b=b_J+t$ and $q_{\max}=b\Sigma_{\max}^{-1}b^*$, the existing
variational inverse identity gives

$$
q_{\max}\ge q_{J,\rm trial}+2\Re(tg_x)+|t_0|^2/a_{\max}.
$$

The same-source far row and energy obey the preceding weighted
Cauchy bounds with the full $G$. Hence, for $A_{\max}>0$,

$$
\mathcal K+q_{\max}
\ge m_J-h-E_\phi+q_{J,\rm trial}-B_{\max}^2/A_{\max},
$$

$$
A_{\max}=\kappa-\kappa^2G_{00}/(-a_{\max}),\qquad
B_{\max}^2=\kappa^2g_x^*Gg_x.
$$

The new1024-bit contractions take0.467 seconds. Reusing the accepted
finite charge floor, directed endpoints give

$$
\delta<4.285\cdot10^{-135},\qquad
q_{J,\rm trial}>-122.995465,\qquad
B_{\max}^2/A_{\max}<10.153002,
$$

$$
\boxed{\mathcal K+q_{\max}>36.044697.}
$$

Under the inherited actual common-form/domain, inverse/comparison,
two-sided far-enclosure and sound-cache premises, every positive
$D\ge\mathcal K$ therefore has $D+q_{\max}>0$. The existing
one-negative-core criterion excludes PSD of
$\Sigma_{\max}+b^*b/D$, which dominates the compression of
$\overline L+\mathcal B^*\mathcal B/D$. The full specified
stronger-base update is consequently not PSD. No good-block inverse
metric, new inverse or solve is required.

This extends the exclusion only to the same $\overline W$, saved
fixed dual and admissible positive denominators. Other majorants,
new or combined directions and other constructions remain outside
its scope. Actual $S_N$ may dominate the rejected lower bound and
be positive. The calculation gives no actual $S_N$ negativity,
full retained/cofinal positivity, Robin-tail or RH result. It reuses
standard variational inversion, inertia, weighted Cauchy and square
completion, without a generic novelty or Lean claim.

### A coupled two-source space is also excluded

Keep the same nineteen channels, $\rho=1/32$, $\overline W$,
stronger base $\overline L$ and upper compression $\Sigma_{\max}$.
The common actual form/domain and inverse/comparison premises now
apply on the entire span of two finite sources. In particular both
effective actions have finite weighted far energy. The same two-sided
far-error and sound-cache premises remain necessary.

Retain the saved exact $w_0$ and propose $w_1$ from $W_JR_JVe_0$,
where $e_0$ selects the negative first lift coordinate. Normalize by
one power of two, round once to512-bit dyadics, and freeze the exact
list. This is an arbitrary trial, not the exact residual or an
optimizer. A nonzero exact two-coordinate minor makes the sources
independent; both have support $J=2049{:}32768$.

The new [source and action packet](https://github.com/the-omega-institute/trureturing-experiments/tree/c1a313ca2dda77ffbafe389e254396706b9c6313/docs/reports/weil-c27)
reuse the old action and all scalar, channel, lift and far data.
Only $w_1$ needs new actual mixed right sides, their two certified
768-dimensional inverse actions, $u_1=Mw_1$, a1281-coordinate common
row and a19-channel functional. The existing Cauchy projection and
FLINT Toeplitz/Hankel adapter supply these quantities. Every old
scientific supplier and old inverse action is reused unchanged.

Write $U=[u_0,u_1]$, $W_{\rm src}=[w_0,w_1]$ and
$\Phi=U_J^*W_JU_{{\rm ch},J}$. The new complete joint charge and row are

$$
K_J=U_J^*W_JU_J-W_{{\rm src},J}^*U_J-\Phi A_\rho^{-1}\Phi^*,
$$

$$
B=(U_J^*W_J-W_{{\rm src},J}^*)R_JV
-\Phi A_\rho^{-1}\Beta_V.
$$

No source cross term is dropped. With the same negative pivot $a$,
positive complement $P$, elimination map $T$ and complete far Gram
$G$, let $H=BT$, $B_0=Be_0$ and choose one exact17-by2 rational
trial $X$ using the saved reference inverse. Put

$$
Q_X=B_0B_0^*/a+HX+X^*H^*-X^*PX,\qquad
g=e_0B_0^*/a+TX,
$$

$$
A=\kappa-\kappa^2G_{00}/(-a)>0,\qquad
C=K_J+Q_X-\frac{\kappa^2}{A}g^*Gg.
$$

The existing variational inverse bound holds as a matrix inequality
for this fixed $X$. For each coefficient vector $c$, its far row
and far energy come from the same actual source $W_{\rm src}c$.
The preceding weighted Cauchy and square completion therefore give
the uniform bound

$$
K_{\rm actual}+B_{\rm actual}\Sigma_{\max}^{-1}B_{\rm actual}^*
\succeq C.
$$

This pays the full far covariance without requiring a numerical far
profile for $u_1$. It does not add separately optimized scalar gains.
The new1024-bit application takes77.55 seconds. Its directed matrix
enclosure certifies

$$
C_{00}>36.044697,\qquad
C_{11}-|C_{01}|^2/C_{00}>0.0139933305,
$$

so $C\succ0$. For every positive-definite2-by2 denominator
$D\succeq K_{\rm actual}$, ordinary bordered-block inertia leaves one
negative direction in
$\Sigma_{\max}+B_{\rm actual}^*D^{-1}B_{\rm actual}$.
This matrix dominates the compression of the specified full
$\overline L+\mathcal B^*D^{-1}\mathcal B$; that full update is
therefore not PSD. The uniform bound also excludes every individual
source combination from this span with its own admissible positive
scalar denominator.

This extends the numerical exclusion to this specified two-dimensional
space, under the stated common-domain and comparison premises. It
does not exclude other source spaces, majorants or constructions,
and establishes no negativity of actual $S_N$. Full retained/cofinal
positivity, Robin tail and RH remain unresolved. The general inertia,
variational, Cauchy and convolution results are reused; the new
contribution is actual coupled source data and their application,
without a new general theorem, algorithm or Lean claim.


### Calibrate the source quadratic before selecting a new direction

A whole-J source proposal can use the preceding variational formula
with a fixed linear rule $X=R_{\rm ref}T^*B^*$, where $R_{\rm ref}$ is
the saved exact symmetric seventeen-dimensional reference. Define

$$
L=e_0e_0^*/a+TR_{\rm ref}T^*,\qquad
Q=e_0e_0^*/a+T(2R_{\rm ref}-R_{\rm ref}PR_{\rm ref})T^*
-\frac{\kappa^2}{A}L^*GL.
$$

Then the new linear-trial expression is $K_J+BQB^*$. It is a
different trial rule from the preceding archived fixed rational $X$.
The [calibration consumer](https://github.com/the-omega-institute/trureturing-experiments/tree/0310c167ce6d254c09fcf7faec5d23a2b06d15d7/docs/reports/weil-c27)
checks the expanded/factored identity by exact rational arithmetic on
one consistent midpoint model, before any source eigensolver is built.
It consumes the cached two-source rows and parameters without new
source actions, inverses, scalar/channel rows or an old production.

The midpoint reference matrix has maximum entry approximately36.04.
The preselected ordinary-double tolerance is
$10^{-8}\max(1,\|C_{\rm ref}\|_{\max})$. Even rounding the exact $Q$
entries before floating contraction produces a maximum absolute error
approximately $5.1006\times10^{89}$. Factored floating evaluation,
and floating evaluation using rounded exact reference trial entries,
also fail this gate. No eigensolver or new source selection follows.
These are implementation measurements in the recorded NumPy
environment, not a condition number or a universal instability theorem.

On the inherited640-bit input grid with1024 working bits, the naive
variable-trial interval evaluation has maximum width approximately
$1.7499\times10^{25}$; expansion through $Q$ gives
$2.7353\times10^{79}$. Freezing the exact rational reference $X$ first
instead gives width $1.4388\times10^{-27}$. This last computation is
a different admissible fixed-trial rule sharing the midpoint value;
it does not certify the variable-trial source operator. These widths
measure the chosen evaluation, rather than intrinsic uncertainty.

The failed gate rejects this specified shortcut before a new large
source search. It neither excludes new source spaces nor guarantees
that another source-selection method succeeds. No accepted exclusion
is changed, and no actual Weil/cofinal positivity, Robin-tail, RH,
new general theorem, algorithm or Lean result is supplied.



### Reduce the finite source sign to one common eighteen-column inverse

The same-object channel identity changes the finite source-selection
task. This is an application of the existing finite Schur, inverse
comparison and inertia formulas, including the classical
[Haynsworth formula](https://doi.org/10.1016/0024-3795(68)90050-5).
It supplies a parameter correspondence for this comparison, rather
than a new general representer theorem or inverse algorithm.

In this subsection only, let $M=M_J$, $W=W_J$,
$U=U_{{\rm ch},J}$ and $R=R_JV$, where $V$ is the SAME exact
eighteen-column lift. Thus $M$ is a finite30720-dimensional matrix
and $R$ has eighteen columns. The inverse $M^{-1}$ is this finite
matrix inverse, not the compression of an infinite inverse. Put
$A=A_\rho$ and $\Beta=\Beta_0V$. The selected residual rows on $E$
vanish exactly, and the cached channel projection uses the same
middle residual. Consequently

$$
\Beta=U^*WR,\qquad
W_c=W-WUA^{-1}U^*W,\qquad N=W_c-M^{-1}.
$$

The preceding finite block construction proves $N\succeq0$ with
its full channel information. Indeed its block matrix
$\mathscr T$ has Schur complement $M$ and satisfies

$$
\mathscr T\succeq T_{E\cup J}
\succeq\operatorname{diag}(\Lambda_E,\Lambda_J)
+\binom{U_E}{U}\begin{pmatrix}U_E^*&U^*\end{pmatrix}.
$$

With $A_0=U_E^*W_EU_E+U^*WU$, inverse comparison, the $JJ$
inverse block and the ordinary Woodbury identity give

$$
M^{-1}\preceq W-WU(I+A_0)^{-1}U^*W\preceq W_c,
\qquad A_\rho\succeq I+A_0.
$$

The weaker statement $M\succeq W^{-1}$ alone would not justify
subtracting the channel term. This argument retains the original
same-channel domination; it proves semidefiniteness, without a
strict spectral gap for $N$.

For any one fixed Hermitian eighteen-dimensional coefficient
$Q_{\rm s}$, define the finite source row map and coefficient by

$$
B=R^*(WM-I)-\Beta^*A^{-1}U^*WM=R^*NM,
$$

$$
C=M(N+NRQ_{\rm s}R^*N)M,\qquad
\Theta=R^*NR\succeq0.
$$

The sign and negative inertia of this entire finite source operator
are determined by

$$
\boxed{n_-(C)=n_-(\Theta+\Theta Q_{\rm s}\Theta).}
$$

For completeness, for any source $w$ set
$v=R^*NMw$, $a=\Theta^\dagger v$ and $e=Mw-Ra$.
Since $\ker\Theta=\ker(N^{1/2}R)$, $v$ belongs to
$\operatorname{ran}\Theta$ and $R^*Ne=0$. Hence

$$
w^*Cw=a^*(\Theta+\Theta Q_{\rm s}\Theta)a+e^*Ne.
$$

Conversely, taking $w=M^{-1}Ra$ realizes the first term exactly.
The map to $a$ is injective on every negative definite source
subspace, so this decomposition gives both inequalities for negative
inertia. It also handles singular $N$ and $\Theta$. In particular
$C\succeq0$ iff the small matrix is PSD, and any strict negative
witness can be chosen in $M^{-1}\operatorname{ran}R$. This preserves
quadratic sign and negative inertia; it neither identifies an
Euclidean minimum eigenvector nor asserts existence of an optimizer.
Eighteen coordinates refer to this fixed lift, not the complete
1281-dimensional retained positivity problem.

#### Keep the common far Gram before taking the inverse

Let $\Sigma=\Sigma_{\max}$, $\kappa=33/32$ and let $G$ be the
SAME signed far Gram with its complete paid allowance. For a source
with actual finite weighted far energy, write

$$
z=W_{\rm far}^{1/2}u_{\rm far},\quad
F_\infty=W_{\rm far}^{1/2}R_{\rm far}V,\quad
F_\infty^*F_\infty\preceq G,
$$

$$
k_{\rm actual}=k_J+\kappa\|z\|^2,\quad
b_{\rm actual}=b+\kappa F_\infty^*z,\quad
k_J=w^*MNMw,\quad b=Bw.
$$

Here $b$ and $b_{\rm actual}$ are columns. Let $a_\Sigma<0$ be
the negative first pivot of $\Sigma$. The condition
$a_\Sigma+\kappa G_{00}<0$ is already supplied by the accepted
$A_{\max}=\kappa-\kappa^2G_{00}/(-a_\Sigma)>0.7772979$;
no new scalar evaluation is needed. Thus
$\Xi=\Sigma+\kappa G$ has seventeen positive and one negative
eigenvalues.

To retain all far covariances, augment $F_\infty$ by a factor of
$G-F_\infty^*F_\infty$ to obtain
$\widetilde F^*\widetilde F=G$. The negative-pivot decomposition
of $\Sigma^{-1}$ gives

$$
I+\kappa\widetilde F\Sigma^{-1}\widetilde F^*
\succeq\left(1-\frac{\kappa G_{00}}{-a_\Sigma}\right)I\succ0.
$$

Completing the square over the augmented far variable and using
Woodbury therefore yields the common lower bound

$$
\boxed{
k_{\rm actual}+b_{\rm actual}^*\Sigma^{-1}b_{\rm actual}
\ge k_J+b^*\Xi^{-1}b.}
$$

The minimization enlarges the possible far responses. Its minimizer
need not come from an actual source. This construction uses the
exact inverse of $\Xi$; it is distinct from both the archived fixed
trials and the calibrated fixed-linear trial rule.

For $Q_{\rm s}=\Xi^{-1}$, set $S=N^{1/2}R$. The two Schur
complements of
$\left(\begin{smallmatrix}I&S\\S^*&-\Xi\end{smallmatrix}\right)$
and the positive identity on $\ker N$ give

$$
\boxed{n_-(C_{\rm sharp})=n_+(\Xi+\Theta)-17.}
$$

Thus this lower source operator has a negative direction exactly
when $\Xi+\Theta\succ0$. A strictly negative quadratic value for
$\Xi+\Theta$ instead excludes negative directions of
$C_{\rm sharp}$. Exact zero thresholds still require their own
analysis; absence of a strict negative source is not by itself an
exclusion of every semidefinite endpoint update.

#### The missing numerical interface is a common inverse Gram

The finite task is $MX=R$ and the joint eighteen-dimensional Gram
$\Theta=R^*W_cR-R^*M^{-1}R$. For an exact rational trial matrix
$X_0$, put $E_0=R-MX_0$ and
$L_X=R^*X_0+X_0^*R-X_0^*MX_0$. The existing inverse-residual
certificate gives

$$
R^*W_cR-L_X-E_0^*WE_0
\preceq\Theta\preceq R^*W_cR-L_X.
$$

It requires the entire common residual Gram, including every cross
term. The old two sources and the original scalar inverse optimum
do not supply it. The saved lift/channel/far packets also do not
archive $R^*WR$ on this lift. The common inverse certificate remains missing;
no block solve or numerical sign for $\Xi+\Theta$ is supplied here.
The threshold does not require computing $\Xi^{-1}$ explicitly.
The dependence on $\Theta$ is Loewner monotone, whereas $\Theta+\Theta Q_{\rm s}\Theta$ is generally not.

The [finite-lift consumer and packet](https://github.com/the-omega-institute/trureturing-experiments/tree/cd81daec08450f7154e12744dc5012cf062ac69c/docs/reports/weil-c27)
supply the first missing interface, with $Y=R_JV$:

$$
G_J=Y^*W_JY,\qquad
S_J=G_J-\Beta_V^*A_\rho^{-1}\Beta_V=Y^*W_cY.
$$

All30720 finite rows and every cross term are retained. The existing
certified disjoint Cauchy action uses a fixed512-term expansion with its
absolute remainder. The original residual generators, positive weights,
exact implicit lift, nineteen-channel map and channel inverse are reused.
No selected inverse, old source action, scalar/channel supplier or full
1281-dimensional target is regenerated.

The1024-bit application takes88.26 seconds, with maximum exported
$S_J$ entry width below $4.132\times10^{-178}$. An independent1536-bit
execution of the same consumer takes132.23 seconds: all1620 pairs of
actual matrix-entry intervals overlap, with972 endpoint-identical;
all45 guarded files remain unchanged. The six direct generator-row
checks pass in both executions. Width diagnostics describe the chosen
evaluation and are not intrinsic uncertainty or condition numbers.

The five archived matrices include $\Xi+S_J$, an entry enclosure of
one exact Loewner upper matrix for $\Xi+\Theta$. Its scalar endpoints
are not Loewner matrix endpoints, and a positive upper matrix would
not establish positivity of the actual threshold. No threshold sign is
tested. This supplies $S_J$, while the common $MX=R$ action and complete
inverse-residual Gram remain missing. It is a numerical application of
the existing Cauchy and matrix identities, without a new general theorem,
algorithm or Lean verification.

The [cached upper selector](https://github.com/the-omega-institute/trureturing-experiments/tree/5e12e20859da48eeeb070616f1ae0b01fae4d211/docs/reports/weil-c27)
consumes only the archived $U_{\rm th}=\Xi+S_J$. The accepted
seventeen-positive-direction bound and $S_J\succeq0$ reduce this
upper matrix's inertia test to its determinant sign. One1024-bit
Arb determinant takes0.53 seconds and encloses
$\det U_{\rm th}\simeq1.06742140729487513\times10^{-1359}>0$.
Thus this exact upper is positive definite under the inherited premises.
The1536-bit execution gives an overlapping positive interval with
nonidentical endpoints; all40 guarded files remain unchanged. The
existing degree-based export rule uses11584 absolute determinant bits
while retaining the640-bit entry grid. No Gram, source action, inverse,
solve or scientific supplier is replayed.

This positive upper does not decide $\Xi+\Theta$ or certify a negative
source. The inexpensive exclusion selector is therefore insufficient;
this route still needs a sharper common inverse/residual bound or
another sufficient ordered estimate. No actual retained/cofinal
positivity, Robin-tail, RH or Lean result is supplied.

The [two-source projection upper](https://github.com/the-omega-institute/trureturing-experiments/tree/06656aef3fb215e0331c4a9496fe669185a87043/docs/reports/weil-c27)
uses the archived exact $Z=[w_0,w_1]$ and $M_JZ$ to supply

$$
A_Z=Z^*M_JZ,\quad B_Z=Z^*Y,\quad
K_Z=B_Z^*A_Z^{-1}B_Z\preceq Y^*M_J^{-1}Y,
\qquad H=\Xi+\Theta\preceq U_2=\Xi+S_J-K_Z.
$$

Only $B_Z$ and an unexported $A_Z$ diagonal are newly contracted.
The first diagonal and both directed cross enclosures are reused.
One existing two-column adjoint Cauchy projection uses unweighted exact
sources, then the same implicit $V$; six raw generator-column checks
cover both sources and modes0,39,1280. A native two-by-two solve with
eighteen right sides forms every cross term of $K_Z$. No old source
action, forward lift profile, finite Gram, scalar/channel supplier or
F/D solve is regenerated.

The fixed1024-bit application takes9.17 seconds and encloses
$\det U_2\simeq-2.2564304658181403\times10^{-1361}<0$.
The1536-bit execution takes10.55 seconds: all724 matrix-entry interval
pairs have identical endpoints, while the two strictly negative
determinant intervals overlap with nonidentical endpoints. The same
algorithm is used; all40 guarded files remain unchanged.
Under the inherited same-object channel-aware inverse comparison and
seventeen positive directions of $\Xi$, both $U_2$ and $H$ therefore
have seventeen positive and one negative direction. The accepted inertia
identity gives $n_-(C_{\rm sharp})=0$ for this whole finite-$J$,
fixed-eighteen-lift lower source comparison, including sources outside
$\operatorname{span}Z$. Its strict-negative-source criterion is
excluded without supplying the complete common inverse. This does not
exclude actual sufficient updates generally or settle semidefinite
endpoint updates. Actual common-domain/far-energy identification,
good-block/far certification, retained/cofinal positivity, Robin tail
and RH remain open. This is a numerical application of existing
projection and inertia results, without generic novelty or Lean
verification.

Even a certified negative $C_{\rm sharp}$ would only identify a
direction for further actual certification. A sufficient full update
still needs an upper bound for the SAME source on
$d+\Gamma+b_{\rm lift}^*\Sigma_L^{-1}b_{\rm lift}<0$, including
the good-block inverse cost $\Gamma$, actual far cost and actual
Schur complement $\Sigma_L$. The exclusion upper compression
$\Sigma_{\max}$ cannot substitute for $\Sigma_L$ there. The
inherited common-form/domain and inverse/comparison premises remain.
No accepted calculation is repeated, and no actual retained/cofinal
positivity, Robin-tail, RH, generic novelty or Lean result is claimed.


#### The same finite comparison also controls positive-denominator endpoints

Keep the SAME finite $J$, eighteen-column lift, nineteen channels,
$\rho=1/32$, $\overline W$, $\overline L$ and upper compression
$\Sigma=\Sigma_{\max}$. The actual common-form/domain and inverse
identifications, finite far energy, channel comparison and two-sided
far enclosure remain premises. The negative projection upper supplies
$H=\Xi+\Theta$ with inertia17 positive,1 negative,0 zero, the same as
$\Xi$. The following is an application of the preceding block inertia
and square completion, with no new numerical evaluation.

Put $S=N^{1/2}R$ and $P_s=I+S\Xi^{-1}S^*$. The two Schur complements
of $\left(\begin{smallmatrix}I&S\\S^*&-\Xi\end{smallmatrix}\right)$,
using the identical nonsingular inertias of $\Xi$ and $H$, give
$P_s\succ0$. Consequently

$$
C_{\rm sharp}=MN^{1/2}P_sN^{1/2}M\succeq0,
\qquad \ker C_{\rm sharp}=\ker(NM).
$$

This kernel statement needs no strict spectral gap for $N$.
For one eligible source $w$, write $b=R^*NMw$ and
$k_J=w^*MNMw$. Use the same augmented far map
$\widetilde F^*\widetilde F=G$ and embed its actual far response as
$\widetilde z=(z,0)$. The accepted strict far coefficient gives

$$
P_f=I+\kappa\widetilde F\Sigma^{-1}\widetilde F^*\succeq\alpha I,
\qquad\alpha=1-\kappa G_{00}/(-a_\Sigma)>0.
$$

The square completion is an exact identity on these common objects:

$$
\begin{aligned}
\mathcal K+b_{\rm actual}^*\Sigma^{-1}b_{\rm actual}
={}&w^*C_{\rm sharp}w\\
&+\kappa\left\langle
\widetilde z+\widetilde F\Xi^{-1}b,
P_f(\widetilde z+\widetilde F\Xi^{-1}b)
\right\rangle,
\end{aligned}
$$

where $\mathcal K=k_J+\kappa\|z\|^2$ and
$b_{\rm actual}=b+\kappa\widetilde F^*\widetilde z$.
Both terms on the right are nonnegative. Equality forces $NMw=0$,
then $b=k_J=0$, then $z=0$. In particular

$$
\mathcal K+b_{\rm actual}^*\Sigma^{-1}b_{\rm actual}=0
\quad\Longrightarrow\quad
\mathcal K=0,\ b_{\rm actual}=0.
$$

Thus for every positive $d\ge\mathcal K$, the strict inequality
$d+b_{\rm actual}^*\Sigma^{-1}b_{\rm actual}>0$ holds. A zero
one-negative-core threshold with positive denominator is excluded.

The conclusion extends to any finite jointly eligible source block
$W_{\rm src}$ on this same $J$, without requiring independent columns.
Let $K_{\rm actual}$ and $B_{\rm actual}=\mathcal BV$ be its common
charge Gram and row map. Apply the preceding scalar statement to every
coefficient vector and its actual linear-combination source. It gives

$$
D+B_{\rm actual}\Sigma^{-1}B_{\rm actual}^*\succ0
\qquad(D\succ0,\ D\succeq K_{\rm actual}).
$$

Bordered inertia therefore leaves exactly one negative direction in
$\Sigma+B_{\rm actual}^*D^{-1}B_{\rm actual}$. Since
$V^*\overline LV\preceq\Sigma$, this matrix dominates the compression
of $\overline L+\mathcal B^*D^{-1}\mathcal B$. The specified full lower
update is not PSD, including its positive-denominator semidefinite
endpoint cases. The common source/action/far law is required on the
whole source span; unrelated scalar charges cannot be substituted.

Nonsingularity of $H$ is material. For the finite-matrix example
$M=N=1$, $W_c=2$, $R=e_0^*$, $G=0$ and
$\Sigma=\Xi=\operatorname{diag}(-1,I_{17})$, one has
$H=\operatorname{diag}(0,I_{17})$ and $C_{\rm sharp}=0$.
Taking $w=d=1$ and $z=0$ gives $\mathcal K=1$, $b_{\rm actual}=e_0$
and $\Sigma+b_{\rm actual}b_{\rm actual}^*/d\succeq0$.
Thus nonnegativity of $C_{\rm sharp}$ alone would not exclude the
endpoint. The strict projection certificate supplies the extra
nonsingularity for the present data.

This excludes only this fixed-majorant lower-update family with
positive-definite denominator and finite-$J$ sources. Other majorants,
bases and source supports, actual $S_N$ positivity, retained/cofinal
positivity, Robin tail and RH remain undecided. The argument uses the
compression order directly; it does not replace an actual sufficient
Schur complement by $\Sigma_{\max}$. It is a conditional application
of existing matrix identities, without a generic novelty or
Lean-verification claim.


#### The projection also excludes the same complete-Gamma comparison

The same two-source projection supplies a stronger conditional
application than the fixed finite-source exclusion. Keep the actual
exterior operator $H_{\rm ext}$, selected support $E=1281{:}2048$,
diagonal $\Lambda$, complete comparison $T=\Lambda+B_{\rm GP}$,
and the original retained residual map $R_{\rm res}$. The common
form/domain, inverse and sound enclosure premises remain in force.
Here $B_{\rm GP}$ includes the complete Gamma boundary and even pole;
this $T$ is not the nineteen-channel surrogate used in $\overline W$.

For arbitrary retained $v$, use the SAME actual selected trial
$x_0(v)=F^{-1}B_{\rm ret}v$, and write

$$
Q(v)=v^*A_{\rm ret}v-x_0(v)^*Fx_0(v),\quad
r(v)=R_{\rm res}v=Cv-H_{\rm ext}E x_0(v),\quad E^*r(v)=0.
$$

For every $E$-supported correction $t$, the full-comparison margin is

$$
m_T(v,t)=Q(v)+t^*Ft
 -(r(v)-H_{\rm ext}Et)^*T^{-1}(r(v)-H_{\rm ext}Et).
$$

Apply the earlier finite inverse-variational restriction to
$X=[E,Z]$, with the archived $Z=[w_0,w_1]$. The same block completion
as in the scalar dual formula, with two columns instead of one, gives

$$
\sup_t m_T(v,t)\le Q(v)
 -(Z^*r(v))^*A_Z^{-1}(Z^*r(v)),\qquad A_Z=Z^*\mathcal M Z,
$$

where $\mathcal M$ is the complete-$T$ effective action defined above.
The archived $A_Z=Z^*M_JZ$ is exactly this finite energy, and
$B_Z=Z^*R_{\rm res}V=Z^*R_JV$. This application uses positive
$B_0=E^*TE$, $D_0=F-B_0$ and the common finite restriction of $T$.
It neither assumes a full-space optimizer nor identifies $M_J^{-1}$
with a compression of an infinite inverse. The source programs'
complete boundary and periodic diagonal, together with their mixed
$F^{-1}$ and $D_0^{-1}$ action terms, supply this correspondence;
finite proposal channels do not replace $T$ in those actions.

Set $Q_V=V^*QV$, $Y=R_JV$ and
$F_V=(R_{\rm far}V)^*W_{\rm far}(R_{\rm far}V)$. The already
identified common objects satisfy

$$
V^*\overline LV=Q_V-S_J-\kappa F_V\preceq\Sigma_{\max},
\qquad F_V\preceq G,\qquad
\Xi=\Sigma_{\max}+\kappa G.
$$

Consequently the SAME exact matrices obey

$$
Q_V-K_Z\preceq\Sigma_{\max}+S_J+\kappa G-K_Z=U_2.
$$

Choose $a\ne0$ with $a^*U_2a<0$ from the accepted strict projection
certificate. The implicit lift $V$ is injective, so $v=Va\ne0$.
Fix this $v$ once. Then

$$
\sup_t m_T(v,t)\le a^*(Q_V-K_Z)a\le a^*U_2a<0.
$$

For every admitted channel comparison $T_U=\Lambda+UU^*$ with
$UU^*\preceq B_{\rm GP}$ and common inverse-form domains,
$T_U\preceq T$ gives $m_{T_U}(v,t)\le m_T(v,t)$. Thus the same
nonzero retained direction prevents whole-retained positivity
certification by any such channel refinement, for all corrections on
this selected $E$. Adding dual test rows, completing a dual inverse,
or changing a numerical cutoff while representing this SAME
$T,E,\Lambda$ cannot alter the negative exact comparison margin.
The finite $J$ here supplies dual tests, not a truncated exterior.

This is a failure of the specified inverse-residual lower comparison,
not a negative direction of the actual Weil operator. Other selected
supports, a changed diagonal or prime comparison, and estimates using
actual information beyond this $T$ remain distinct routes. No new
numerical contraction is needed. The actual form/domain and inverse
identifications, source/lift/far correspondence and sound-cache
premises have not been discharged by this application. Actual retained
or cofinal positivity, Robin tail and RH remain unresolved; no new
generic theorem, algorithm or Lean verification is claimed.


#### A cached norm bound admits a small actual-surplus shift

The unchanged complete comparison is excluded above. A distinct
conditional construction uses the actual positive difference from it.
Keep the SAME actual $H_{\rm ext}$, $T$, $E$, exterior complement $O$,
effective action $\mathcal M$, residual and lift. Put

$$
D_0=E^*(H_{\rm ext}-T)E,\qquad
C_0=O^*(H_{\rm ext}-T)E,\qquad
\Pi=(H_{\rm ext}-T)_{OO}-C_0D_0^{-1}C_0^*.
$$

Under the inherited common form/domain and inverse identifications,
the actual selected exterior Schur form is
$\mathcal A=\mathcal M+\Pi$. The existing GLOBAL prime/diagonal
slack supplies $H_{\rm ext}-T\succeq I/632$: the earlier weighted row
has $q(59/10-r_q)>1/400$, $q\le79/50$, and
$\Lambda\preceq A_\Gamma-(59/10)I$. This uses the complete cancellation
$H_{\rm ext}-T=A_\Gamma-\Lambda-C_{\rm p}$ on the common form domain;
a bound only on its selected block would not suffice.
Minimizing that global quadratic form over the finite $E$ coordinate
gives $\Pi\succeq I/632$ on $O$.

Fix the archived exact384-bit $w_0$, with SAME full
$u=\mathcal Mw_0$ and $h=w_0^*u>0$. The accepted common-column packet already contains an enclosure of
$E_J$ and an upper bound for $E_F$, where

$$
E_J=\sum_{m=2049}^{32768}W_m|u_m|^2,\qquad
E_F=D_{\rm far}\|u_{\rm far}\|_2^2.
$$

Here $W_{\rm far}=D_{\rm far}I$ is the original positive CONSTANT
far weight. Thus this particular weighted far energy does control the
unweighted norm. The existing pilot contains that exact constant and
all positive middle weights; their $J$ slice starts at array index768.
With $w_{\min,J}=\min_{m\in J}W_m$ and directed cached upper bounds,

$$
\|u\|_2^2\le U_u:=\frac{E_J^{\rm up}}{w_{\min,J}}
 +\frac{E_F^{\rm up}}{D_{\rm far}},\qquad
uu^*\preceq U_uI\preceq p_{\rm up}\Pi,\qquad
p_{\rm up}=632U_u.
$$

For any directed $0<h_{\rm low}\le h$, put

$$
t_{\rm cap}=\frac{h_{\rm low}}{h_{\rm low}+p_{\rm up}}.
$$

Every fixed rational $0<t\le t_{\rm cap}<1$ satisfies
$p_{\rm up}\le h(1-t)/t$. Consequently the existing rank-one shift
is admissible under these premises:

$$
\mathcal M_t=\mathcal M+\frac{t}{h(1-t)}uu^*
\preceq\mathcal A,\qquad
\mathcal M_t((1-t)w_0)=u.
$$

The associated charge and row change by
$\mathcal K_t=\mathcal K+th$ and
$\mathcal B_t=\mathcal B+t\,w_0^*R_{\rm res}$.
The full $u$, including its far action, remains unchanged.
This construction changes the comparison using actual surplus and is
not excluded by the preceding obstruction for unchanged $T$.

The [cached scalar application](https://github.com/the-omega-institute/trureturing-experiments/tree/923ab4a9acaa9aa66d52df450a30145239b32479/docs/reports/weil-c27)
uses only exact rational arithmetic on
the accepted energies, positive weights and $h$ enclosure. It does not
recompute an action, energy, inverse, source, channel or far bound.
Its exact rational output gives, approximately,
$U_u=4541.41733$, $p_{\rm up}=2870175.75239$ and
$t_{\rm cap}=0.000374611014$. Under the stated premises the stored
$t=2^{-13}=1/8192$ is an eligible interior example. This cap is a
sufficient eligibility bound, not the largest admissible shift. The constant-weight identification and all actual
form/domain/source correspondences remain explicit premises.

This supplies no sign of the necessary quadratic
$\ell(t)=k_J+th+(b_J+t r_V)\Xi^{-1}(b_J+t r_V)^*$.
The earlier sole direct evaluation remains inconclusive. Actual
success also requires a joint sufficient upper with the new good-block
charge, the SAME actual complement and full far response. An admissible
parameter alone does not establish that upper. No actual retained or
cofinal positivity, Robin-tail or RH conclusion, generic novelty or
Lean verification is claimed.


#### The cached fixed trial excludes that entire sufficient shift interval

The small shift is eligible but does not rescue this specified lower
update. Reuse the stronger-base compression $\Sigma_{\max}$, its
negative pivot $a=a_{\max}<0$, positive complement, saved exact
seventeen-vector $x_J$ and full paid PSD far Gram $G$ from the
far-enclosure-gap calculation. These are the SAME objects; $\Xi$ is
not substituted for $\Sigma_{\max}$.

Use $\tau$ for the shift parameter, keeping the far row distinct, and set

$$
r=w_0^*R_{\rm res}V=w_0^*R_JV,\qquad
g_0=T_{\max}x_J+(\overline{b_{J,0}}/a)e_0,\qquad
g_\tau=g_0+\tau(\overline{r_0}/a)e_0.
$$

For the SAME fixed trial, changing the finite row from $b_J$ to
$b_J+\tau r$ changes its signed variational value by exactly

$$
2\tau\Re(rg_0)+\tau^2|r_0|^2/a.
$$

The full $u$ and its far action remain unscaled. Reuse verbatim the
cached $A_{\rm low}>0$, completed-square penalty $P_0$, and lower
$L_0>36.044697$ for $\mathcal K+q_{\max}$. Choose a directed upper

$$
P_1\ge\frac{\kappa^2|r_0/a|^2G_{00}}{A_{\rm low}}.
$$

The metric triangle inequality in the SAME PSD $G$ bounds the shifted
far penalty by $(\sqrt{P_0}+\tau\sqrt{P_1})^2$ for $\tau\ge0$.
Combining this with $\mathcal K_\tau=\mathcal K+\tau h$ gives

$$
\mathcal K_\tau+
q_{\max}(\mathcal B_\tau V)
\ge L_0+c_1\tau+c_2\tau^2,
$$

where all coefficients are rounded downward, with

$$
c_1\le h_{\rm low}+2\Re(rg_0)
-2\sqrt{P_0P_1},\qquad
c_2\le |r_0|^2/a-P_1.
$$

The [thin scalar consumer and exact rational packet](https://github.com/the-omega-institute/trureturing-experiments/tree/726ed4d08f4d7b37ae15079d78a0f29bf6c48f75/docs/reports/weil-c27)
reuse the old lower, completion constants, trial and budget. Only the
new mixed scalar and shifted penalty are evaluated; no old action,
inverse, solve, Gram, far production or reference profile is rerun.
The new coefficients are approximately $c_1=-1404.30017560541$ and
$c_2=-32507.0069794674$. Exact rational minimization of the outward
lower polynomial over $[0,t_{\rm cap}]$, without a parameter scan,
has its minimum at $t_{\rm cap}$ and gives, under the inherited
actual common-form/domain, inverse/comparison, far-enclosure and
sound-cache premises,

$$
\boxed{\mathcal K_\tau+q_{\max}(\mathcal B_\tau V)
>35.514069\quad(0\le\tau\le t_{\rm cap}).}
$$

For every eligible rational $0<\tau\le t_{\rm cap}$ and every
positive $D\ge\mathcal K_\tau$, the existing one-negative-core
criterion therefore excludes PSD of
$\Sigma_{\max}+(\mathcal B_\tau V)^*(\mathcal B_\tau V)/D$.
This matrix upper-bounds the compression of
$\overline L+\mathcal B_\tau^*\mathcal B_\tau/D$, excluding that
specified stronger-base lower update. No good-block inverse upper
is needed for this exclusion. The zero endpoint is the old construction.

The sole new1024-bit scalar application takes0.0113 seconds and exports
640-bit outward enclosures and exact rational coefficients. This
does not decide the earlier inconclusive $\ell$ packet. The interval
endpoint is only a sufficient budget bound; larger truly eligible
shifts, different sources, bases and majorants remain unexcluded.
Failure of this lower update is not actual Weil negativity. Actual
retained/cofinal positivity, Robin tail and RH remain unresolved;
no generic novelty or Lean verification is claimed.


## A proved high-energy law and its four-component characteristic geometry

Taira–Willems–Wrochna, *Large eigenvalues of the Connes–Moscovici
operator*, [arXiv:2609.32639v1](https://arxiv.org/pdf/2609.32639v1),
26 September 2026, proves the logarithmic Weyl law previously predicted
for a specified Connes–Moscovici operator. The inspected primary has
45 pages and PDF SHA-256
`49cf5e3863459148b249c9ae721c2297024f1f1055025ba8ef9ed87c8893ffbb`.
The interfaces used here are Theorem 1.1 and Corollary 1.2 on p.2,
the explicit spectral-scope statement on p.5, §§2.1–2.4 on pp.7–10,
the counting argument in §5.3 on p.36, and Theorem A.11 on p.41.
This is a primary-source
application, not an independent audit of the microlocal proof,
numerical reproduction, new spectral theorem or Lean verification.

### The proved operator and its parameters

The differential expression and its distinguished selfadjoint extension
are

$$
P=-\partial_x(x^2-1)\partial_x-4\pi^2x^2,
\qquad P_{\rm sa}:D(P_{\rm sa})\subset L^2(\mathbb R)\to L^2(\mathbb R).
$$

Section 2.4 fixes the domain: the logarithmic terms at $x=\pm1$
are excluded, and the even and odd parts have respectively the
specified sine-type and cosine-type boundary conditions at infinity.
The differential expression alone does not specify this extension.
The spectrum is discrete and unbounded in both directions. The older
Connes–Moscovici notation uses $W_{\rm sa}=-P_{\rm sa}$ and calls the
relevant eigenvalues negative; its parameter called $E$ is the square
root of the present eigenvalue parameter, as Remark 1.6 explains.

With

$$
I(a)=\int_1^\infty\left(
\sqrt{\frac{x^2+a-1}{x^2-1}}-1\right)dx\qquad(a>0),
$$

Theorem 1.1 gives some $E_*>0$ and a smooth remainder such that

$$
R(E)=-\frac{\log E}{16\pi\sqrt E}+O(E^{-1/2}),
\qquad R'(E)=O(E^{-3/2}\log E).
$$

All sufficiently large positive eigenvalues are simple and are
characterized, with $n\in\tfrac12\mathbb Z$ sufficiently large, by

$$
2I\left(1+\frac{E_n}{4\pi^2}\right)+\frac14+R(E_n)
=n+O(E_n^{-\infty}).
\tag{W1}
$$

No numerical value of $E_*$ or explicit constants for these remainder
symbols are supplied by this application. Corollary 1.2 proves

$$
N_+(E)=\frac{4\sqrt E}{2\pi}
\left(\log\frac{\sqrt E}{2\pi}-1+2\log2\right)+O(1).
\tag{W2}
$$

Thus setting $T=4\sqrt E$ gives exactly the main counting function
$T\log(T/(2\pi e))/(2\pi)$ of the classical Riemann–von Mangoldt
formula. This is a parameter match for the main term, not an
identification of individual eigenvalues or of the oscillating zero
count. The primary explicitly preserves that distinction on p.5.
High-energy simplicity in (W1) is also a statement about $P_{\rm sa}$;
it is not the missing simplicity of the actual Weil ground state in
the preceding spectral-triple discussion.

### A literal four-phase symmetry after the scale is recorded

The source uses $E=h^{-2}$ and the global $h$-dependent real symbol

$$
p_h(x,\xi)=(x^2-1)\xi^2-4\pi^2h^2x^2-1,
\qquad h>0.
$$

Put $a_h=2\pi h$ and $y=\xi/a_h$. Then its characteristic equation
becomes the symmetric relation

$$
p_h(x,a_hy)=0
\quad\Longleftrightarrow\quad
(x^2-1)(y^2-1)=1+a_h^{-2}.
\tag{W3}
$$

Both $|x|$ and $|y|$ exceed one on this curve. There are four
components labeled by their two signs, and

$$
C(x,y)=(-y,x),\qquad C^2=-I,\quad C^4=I
$$

preserves (W3), cycling the labels as
$(\sigma_1,\sigma_2)\mapsto(-\sigma_2,\sigma_1)$.
In the original symbol coordinates this is

$$
B_h=\begin{pmatrix}1&0\\0&a_h\end{pmatrix},\qquad
\mathcal C_h=B_hCB_h^{-1}
=\begin{pmatrix}0&-a_h^{-1}\\a_h&0\end{pmatrix},
\qquad p_h(\mathcal C_h(x,\xi))=p_h(x,\xi).
\tag{W4}
$$

The last identity follows by substitution, and
$\det\mathcal C_h=1$ preserves the two-dimensional symplectic form.
This action exchanges the ends approaching $x=\pm1$, $|\xi|=\infty$
with the ends approaching spatial infinity and $\xi=\pm a_h$.
It is a scale-dependent transport of position and momentum boundaries.
Using the unscaled quarter-turn on $(x,\xi)$ instead would give

$$
p_h(C(x,\xi))-p_h(x,\xi)
=(a_h^2-1)(x^2-\xi^2),
$$

which is not identically zero at general $h$. The scale factor in
(W4) therefore cannot be dropped.

The matrix $C$ in normalized coordinates is the same algebraic matrix
as the existing FIB composition operation $C=MJ$ in the
[FIB volume, §149](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
This supplies a concrete common four-phase action after the coordinate
normalization is specified. It does not identify the integer composition
carrier with this continuous characteristic curve. Symbol invariance
alone does not establish a unitary action on the chosen operator domain
or compatibility with the full boundary conditions and quantization
remainder in (W1).

There is, independently, an existing operator-level Fourier symmetry
to reuse. Appendix A, Theorem A.11 on p.41, recalls Connes–Moscovici,
*The UV prolate spectrum matches the zeros of zeta*,
[PNAS 119 (2022), e2123174119, Theorem 1.6](https://doi.org/10.1073/pnas.2123174119):
this same $P_{\rm sa}$ commutes with the source's Fourier transform
$\mathcal F$, the interval projection $Q$, and
$\widehat Q=\mathcal FQ\mathcal F^{-1}$. It is the unique selfadjoint
extension of $P_{\min}$ commuting with $Q$ and $\widehat Q$.
Thus the Fourier compatibility of this specified extension is already
established source mathematics, rather than a new obligation to prove
from (W4). The original theorem is used here as recalled in the inspected
primary; no new audit of the 2022 proof is claimed. It does not identify
the functional Fourier action with a transformation of legal FIB sources.

A FIB-to-spectral bridge would still need a map from legal recursive
sources to this operator's admitted data, an intertwining of the actual
recursion and observations, and the quantization and arithmetic
correspondence. Counting four components or sharing the matrix $C$
does not construct that map. In particular the five-window address
rules are not boundary conditions for $P_{\rm sa}$.

The high-energy theorem should be reused in its own spectral model.
It neither settles the actual Weil ground-state comparison nor bounds
the complete signed $I_\psi(\log N)$ at the selected Robin source.
Those arithmetic estimates and RH remain unproved.

## The exact height clock fails to reproduce the zero-count fluctuations

The main-term match in (W2) has a quantitative boundary supplied by a
classical theorem, rather than a new spectral calculation. Kai-Man Tsang,
*Some Ω-theorems for the Riemann zeta-function*,
Acta Arithmetica **46** (1986), 369–395,
[DOI:10.4064/aa-46-4-369-395](https://doi.org/10.4064/aa-46-4-369-395),
states the unconditional result

$$
S(t)=\Omega_\pm\!\left(
\left(\frac{\log t}{\log\log t}\right)^{1/3}\right)
\tag{T1}
$$

in Theorem 1, equation (1.4), printed p.369. The adjacent stronger
estimate (1.3) assumes RH and is not used. Theorem 2, printed p.370,
gives a dyadic version: for some $c>0$ and all sufficiently large $T$,

$$
\sup_{t\in[T,2T]}\,\pm S(1/2,t)
\ge c\left(\frac{\log T}{\log\log T}\right)^{1/3}.
\tag{T2}
$$

Here the source's allowed range of $\sigma$ includes $\sigma=1/2$.
The inspected [publisher PDF](https://www.impan.pl/shop/publication/transaction/download/product/105022?download.pdf)
has SHA-256
`c6f9404e6e1b29202dd11adbefab220903d2400ef05345922795431f3ee2ad6f`.
These theorem statements and equation (1.1) were read from the scanned
printed pages 369–370; no audit of Tsang's proof is claimed.

### Counts of the same height, with all zero multiplicities

Write

$$
m(t)=\frac{t}{2\pi}\log\frac{t}{2\pi e},\qquad
Q(t)=\left(\frac{\log t}{\log\log t}\right)^{1/3}.
$$

Let $N_\zeta(t)$ count every nontrivial zero with $0<\gamma<t$,
including multiplicity and without imposing $\beta=1/2$. At heights
away from zero ordinates, the source's equation (1.1) is

$$
N_\zeta(t)=m(t)+\frac78+S(t)+O(t^{-1}).
$$

Using (W2) with its already fixed clock $E=t^2/16$ gives

$$
D(t):=N_\zeta(t)-N_+(t^2/16)
=S(t)+\frac78+O(1).
\tag{T3}
$$

The bounded remainder here is a consequence of the two cited counting
laws; no explicit numerical constant is asserted. In particular,
$D(t)=\Omega_\pm(Q(t))$. A version keeping a specified height window
is: for some $c_1>0,C_1$ and every sufficiently large $T$, there are
heights $t_T^+,t_T^-\in[T,4T]$, away from zero ordinates, with

$$
D(t_T^+)\ge c_1Q(T)-C_1,\qquad
D(t_T^-)\le-c_1Q(T)+C_1.
\tag{T4}
$$

To handle endpoints, apply (T2) on $[3T/2,3T]$, inside $[T,4T]$.
At a zero ordinate use the appropriate one-sided value and move to a
nearby height. The source records the jump as the total multiplicity;
this argument neither deletes repeated zeros nor assumes their
simplicity. Either endpoint convention for the high positive spectrum
changes its count by at most one, by the eventual simplicity in (W1).

Thus the multiset of all sufficiently large zero ordinates cannot
equal the transformed positive spectrum $\{4\sqrt{E_n}\}$ under this
exact clock. Finite changes to the head and a fixed index offset alter
the discrepancy only by $O(1)$ and cannot remove (T4).

### A correction bounded in units of mean spacing is also insufficient

Let $r(t)=t+\delta(t)$ be any height clock with
$\delta(t)=O(1/\log t)$. Since

$$
m'(t)=\frac{1}{2\pi}\log\frac{t}{2\pi},
$$

the mean value theorem gives $m(r(t))-m(t)=O(1)$. The spectral counting
law holds uniformly at sufficiently large arguments, hence

$$
N_\zeta(t)-N_+(r(t)^2/16)
=S(t)+\frac78+O(1).
\tag{T5}
$$

The constants may depend on the fixed bound on
$|\delta(t)|\log t$. Consequently even this corrected clock cannot
identify the eventual counts up to a uniformly bounded correction.
The scale $1/\log t$ is the scale of the mean zero spacing, up to the
constant $2\pi$; no assumption about actual consecutive spacings is
used.

More generally, if $r(t)/t\to1$ and an eventual count identification
with bounded error were achieved, (T3) would require
$m(r(t))-m(t)=S(t)+O(1)$. Another application of the mean value theorem
and (T1) would force

$$
(r(t)-t)\log t=\Omega_\pm(Q(t)).
\tag{T6}
$$

This is a necessary condition on a proposed arithmetic correction,
not a construction of one and not a sufficient spectral correspondence.
It excludes only the stated clocks for this specified operator; a
different spectral model or a larger arithmetic reparameterization
has not been excluded. A FIB address or four-phase relabeling does not
by itself supply the fluctuations required in (T6). The deduction is an
application of existing counting and oscillation theorems, with no
originality or Lean-verification claim. It supplies no signed estimate
for the original full Robin tail and leaves RH unproved.

## A reciprocal prime-potential budget and its saved step-weight obstruction

Keep the SAME actual exterior, finite $E$ block, complement $O$,
$u=\mathcal Mw_0$ and $h=w_0^*u>0$ from the surplus-shift application.
The [weighted Schur formula](liu2026tailcompensation.md) and the
complete global cancellation already used there give, on the inherited
common closed form domain,

$$
H_{\rm ext}-T\succeq\operatorname{mult}(v),\qquad
v=59/10-r_q\ge1/632.
$$

For every admitted $f=e+y$, with $e\in E$, $y\in O$, the original
unitary even cosine identification gives $\langle u,f\rangle=
\langle u,y\rangle$. Weighted Cauchy yields

$$
|\langle u,y\rangle|^2\le p_v(H_{\rm ext}-T)[e+y],\qquad
p_v=\int_I\frac{|u(x)|^2}{v(x)}\,dx.
$$

Taking the infimum over legal finite $E$ coordinates proves
$uu^*\preceq p_v\Pi$ for the SAME closed short $\Pi$.
Multiplication by $v$ need not preserve $E$ or $O$; the inequality
is a form restriction. The common form/domain closure, admitted $E$
shifts, original mass/phase and the displayed short identification
remain conditions. This is an application of standard weighted
Cauchy and the existing short variational definition, not a new
general theorem. A directed $p_v\le47h$ would suffice for the fixed
shift $t=1/48$, independently of its still separate actual positivity
score.

### Reuse the existing26cell margins without rebuilding the prime bound

For a saved cell $C\subset[0,1]$, the existing rational minimum
$\mu_C$ bounds $qv$, with $q(Ls)=1+(29/50)s^2$. Define

$$
v_C=\frac{\mu_C}{1+(29/50)(\sup C)^2},\qquad
W(Ls)=W(-Ls)=v_C^{-1}\quad(s\in C),\qquad
m=\max_Cv_C^{-1}.
$$

These disjoint outward cells cover the uncertain support strips too.
Thus $W\ge1/v$ almost everywhere and $p_v\le\int W|u|^2$.
Keep the original full source split $u=u_J+u_F$, $J=2049{:}32768$,
and the accepted complete unweighted far cap $\|u_F\|^2\le U_F$.
For $a_1=\int W|u_J|^2$, the weighted triangle gives

$$
\int W|u|^2\le(\sqrt{a_1}+\sqrt{mU_F})^2.
$$

The [source-specific application](https://github.com/the-omega-institute/trureturing-experiments/tree/96a31ada/docs/reports/weil-c27)
reuses the original640-bit coefficient enclosures, cell minima and far
cap. Only the missing finite weighted energy is computed. It retains
both cosine sum and difference frequencies and interval errors;
no old prime/source/action, inverse, solve, Gram matrix or far supplier
is repeated. Approximately,

$$
\min_Cv_C=0.00174356661223,\quad
a_1=656214.527747263,\quad mU_F=26846.3715529475,
$$

and the forward upper is $948518.835933079$, while
$47h=50553.3119129287$. That upper does not certify the fixed shift.
The numerical application is conditional on the same actual
identifications and sound archives; it is not a Lean result.

### The same step weight fails even with the most favorable far phase

The saved cell-energy lower endpoints give $a_-\le a_1$.
Exact rational postprocessing and integer square roots certify

$$
\sqrt{a_-}\ge810,\qquad \sqrt{mU_F}\le164.
$$

The standard reverse weighted triangle now gives for the SAME full
source, including every far phase satisfying its complete cap,

$$
\boxed{\int_IW|u|^2\ge(810-164)^2=417316>47h.}
$$

The strict comparison uses the archived upper endpoint for $h$.
It requires no further Fourier calculation. Therefore this exact
saved26-cell step majorant cannot supply the proposed multiplication-
weight budget at $1/48$; improving integration precision or the cross
estimate with the same $W$ cannot fix it.

This lower bound concerns $\int W|u|^2$, which is an upper majorant
of $p_v$. It is not a lower bound for $p_v$ or the optimal directional
constant relative to $\Pi$. The exact reciprocal potential, another
majorant, additional actual nonlocal surplus and other eligible shifts
remain unexcluded. No actual Weil negativity, retained/cofinal
positivity, Robin tail, RH or originality claim follows.

## A refined source budget from the same saved potential

Keep the actual forms, source, short, normalization and full far premises
of the preceding reciprocal-potential application. The old step-weight
obstruction concerns its precise26-cell function. A different majorant
can use the already accepted pointwise polynomial information within a
cell.

Let $\beta=29/50$, $q(s)=1+\beta s^2$, and let $P(s)$ be the saved
rational quadratic lower envelope for $q(s)v(Ls)$ on the last original
cell $[l,1]$, where $l=261826231978/274653072167$. Restore its coefficients
from the saved logarithm intervals, square-root bounds and possible-active
lists. Divide this cell into128 equal rational subcells, fixed before
evaluating any new integral. On a subcell $[a,b]$, put

$$
\widetilde W|_{[a,b]}=
\frac{1+\beta b^2}{\min_{[a,b]}P}.
$$

Keep the old weights on the other25 cells and reflect evenly to $I$.
Exact quadratic minima give $1/v\le\widetilde W\le W$ almost everywhere.
The outward support-switch strips remain included. Thus the old lower
bound for $\int W|u|^2$ supplies no lower bound for the new functional.

### Reuse the masses and integrate only the missing subcells

The saved finite source uses $J=2049{:}32768$ and the original unphased
cosine basis. Its physical reflected density is

$$
g(s)=2\left|\sum_{n\in J}u_n\cos(\pi ns)\right|^2,
\qquad \int_0^1g=a_0=\|u_J\|^2.
$$

Keep the cached $a_0$, first25 cell masses and last-cell total
$E_{\rm last}$. If $F$ is the zero-constant sine primitive of the
nonconstant harmonics of $g$, then

$$
F(l)=a_0(1-l)-E_{\rm last},\qquad F(1)=0.
$$

The squared-harmonic intermediate was not archived, so it is restored
once with the existing FLINT convolution/autocorrelation helper. Only
127 missing interior primitives are evaluated; the old26 cell integrals,
source/action, logarithm/Gamma comparison, inverse, solve, Gram and far
suppliers are reused. Both sum and difference frequencies, all coefficient
intervals and the accepted1024/640-bit arithmetic remain in force.

For the SAME $\widetilde W$, the saved153 masses give approximately

$$
a_1=\int\widetilde W|u_J|^2=10681.5778952432,
\qquad a_2=\int\widetilde W^2|u_J|^2=1164563.05493539,
$$

$$
m=\|\widetilde W\|_\infty=554.477544320329,
\qquad mU_F=25954.2272562998.
$$

Unweighted orthogonality $u_F\perp u_J$ allows the standard centered
Cauchy bound

$$
\int\widetilde W|u|^2\le
 a_1+2\sqrt{U_F}\sqrt{a_2-a_1^2/a_0}+mU_F.
$$

Its directed upper is $50854.0911649295$, above $47h=50553.3119129287$.
This upper is inconclusive for the fixed shift; it does not exclude the
new weight or actual eligibility.

### Charge the full orthogonal response with one Cauchy bound

Fix an auxiliary price $\lambda=640$, above the inherited uniform
weight bound632, independently of any new resolvent-moment evaluation.
It leaves the actual shift at $t=1/48$. Define

$$
R_\lambda=\int_I\frac{|u_J|^2}{\lambda-\widetilde W}
 =\sum_{C}\frac{E_C}{\lambda-\widetilde W_C}.
$$

The positive bounded multiplication operator $\lambda-\widetilde W$
and $\langle u_J,u_J+u_F\rangle=a_0$ give by weighted Cauchy

$$
a_0^2\le R_\lambda
 \left(\lambda\|u_J+u_F\|^2-\int\widetilde W|u_J+u_F|^2\right).
$$

Consequently the SAME complete far cap supplies

$$
p_v\le\int\widetilde W|u|^2
 \le\lambda(a_0+U_F)-\frac{a_0^2}{R_\lambda}.
$$

For directed enclosures, use
$\lambda(a_0^{\rm up}+U_F)-(a_0^{\rm low})^2/R_\lambda^{\rm up}$.
All terms describe one common source and weight; no separately attained
far or cross extremum is assumed. Only one scalar sum over the already
saved153 masses is new here.

The [cached-source application](https://github.com/the-omega-institute/trureturing-experiments/tree/ffa984aef314a03470e24cfb0c32f510b0081327/docs/reports/weil-c27)
gives $R_{640}\approx2.14857834484827$ and a directed complete upper
$U_{\rm res}\approx48941.0175472545$. Its exact exported endpoints certify

$$
\boxed{p_v\le U_{\rm res}<47h_{\rm low}\le47h,}
$$

where $47h_{\rm low}\approx50553.3119129287$. Thus the conditional
SAME-source directional budget is admitted at the preselected $1/48$.
The refinement takes5.797seconds; the subsequent cached-mass scalar
application takes0.0144seconds. No auxiliary price, shift, cell count or
precision scan is used.

These are source-specific applications of existing quadratic, finite
Fourier and weighted-Cauchy facts, with no new generic theorem or Lean
verification claimed. The actual common forms/domains, legal $E$ shifts,
unitary mass/phase identification, SAME closed short and sound full
source/far archives remain conditions. The actual sufficient score and
its good-block contribution, retained/cofinal positivity, the Robin tail
and RH remain unresolved.

### Transport the inverse majorant with the actual-surplus shift

The fixed-majorant shifted row above does not exhaust the eligible
construction. Retain the SAME positive effective action $\mathcal M$,
full $u=\mathcal Mw_0$, $h=w_0^*u>0$, and inverse majorant
$\overline W\succeq\mathcal M^{-1}$. The majorant is not identified
with the exact inverse. For an admitted $0<\tau<1$, the existing
rank-one inverse/Woodbury identity gives

$$
\mathcal M_\tau^{-1}
=\mathcal M^{-1}-\frac{\tau}{h}w_0w_0^*,\qquad
\overline W_\tau
=\overline W-\frac{\tau}{h}w_0w_0^*
\succeq\mathcal M_\tau^{-1}\succ0.
$$

This is an application on the inherited common inverse forms and
finite-rank actions, not a claim that an arbitrary subtraction
preserves a positive majorant. The admissibility premise remains
$\mathcal M_\tau\preceq\mathcal A$ for the actual exterior short;
the common domains and inverse identifications remain required.

Put $w_\tau=(1-\tau)w_0$, $h_\tau=(1-\tau)h$, and
$r=w_0^*R_{\rm res}$. Simultaneously transporting the base,
observer and charge gives the exact cancellations

$$
u^*\overline W_\tau R_{\rm res}-w_\tau^*R_{\rm res}
=\mathcal B,\qquad
u^*\overline W_\tau u-h_\tau=\mathcal K,
$$

$$
\overline L_\tau
=Q-R_{\rm res}^*\overline W_\tau R_{\rm res}
=\overline L+\frac{\tau}{h}r^*r.
$$

Consequently the SAME inverse-residual variational argument, for
every fixed $D>0$ with $D\ge\mathcal K$, supplies the conditional
lower construction

$$
S_N\succeq
\overline L+\frac{\tau}{h}r^*r
+\frac{\mathcal B^*\mathcal B}{D}.
$$

It retains a gain discarded by the held-$\overline W$ shifted
construction. The ordinary weighted-square identity is

$$
\frac{\tau}{h}r^*r+\frac{\mathcal B^*\mathcal B}{D}
-\frac{(\mathcal B+\tau r)^*(\mathcal B+\tau r)}{D+\tau h}
=\frac{\tau(h\mathcal B-Dr)^*(h\mathcal B-Dr)}
 {Dh(D+\tau h)}\succeq0.
$$

The archived exclusions for the held-majorant family remain valid
with their original scope. They do not exclude this larger lower
construction, which uses actual surplus beyond the unchanged
comparison $T$.

On the accepted exact lift, its stronger-base compression is
upper-bounded by

$$
\Sigma_\tau=\Sigma_{\max}+\frac{\tau}{h}r_V^*r_V,
\qquad r_V=w_0^*R_{\rm res}V.
$$

The cached finite row $b_J$, actual complete far row, full paid
Gram $G$, and charge floor remain unchanged. A compression exclusion
must test this NEW matrix, with its actual negative first pivot and
new positive complement; the old inverse or far-completion constant
cannot be substituted. There is no additional $\tau h$ charge and
no replacement of $b_J$ by $b_J+\tau r_V$ in this transported
construction. A positive compression lower would exclude only this
specified sufficient construction. A nonpositive lower would leave
its sign undecided. Neither outcome alone determines the actual
retained form, its good-block contribution, cofinal positivity,
the Robin tail or RH. No new general theorem or Lean verification
is asserted.

### The transported projection ceiling excludes the fixed shifted comparison

The archived two-source ceiling also transports, before any new
positive-complement or good-block solve. On the SAME inherited positive
inverse forms, finite inverse-variational restriction gives

$$
V^*(Q-R_{\rm res}^*\mathcal M^{-1}R_{\rm res})V
\preceq Q_V-K_Z\preceq U_2.
$$

Apply the preceding rank-one inverse identity with the SAME actual
$w_0$, full $u$, $h$ and residual map. Then

$$
\boxed{
V^*(Q-R_{\rm res}^*\mathcal M_\tau^{-1}R_{\rm res})V
\preceq U_{2,\tau}:=U_2+\frac{\tau}{h}r_V^*r_V.}
$$

Every admitted inverse-majorant/residual-trial lower construction
for $\mathcal M_\tau$, including the fully transported majorant
above, is dominated by the exact comparison on the left. A negative
direction of $U_{2,\tau}$ therefore prevents whole-retained positivity
certification by that fixed comparison. This upper ceiling concerns
the full exterior comparison; its two finite sources are inverse
trials, not a truncation of that exterior.

The [source-specific cached application](https://github.com/the-omega-institute/trureturing-experiments/tree/95cba44473164287deeb484d4483f4cc4ff1b255/docs/reports/weil-c27)
uses only the archived $U_2$,
$r_V$, BOTH directed endpoints of the true $h$, and the accepted
conditional $\tau=1/48$ budget. One new FLINT18 determinant gives

$$
\boxed{\det U_{2,1/48}<-4.93328\times10^{-1362}<0.}
$$

The original $U_2$ has at least seventeen positive directions, and
the exact rank-one addition is PSD; thus this new ceiling has
seventeen positive and one negative direction. The same nonzero
lifted retained direction rules out positivity certification by
any of the specified lower constructions for this $\mathcal M_{1/48}$.
This includes both the held-majorant and fully transported families,
for every admitted positive denominator and residual trial. It does
not give a negative direction of the actual Weil form.

The new determinant takes0.0286seconds. No source/action, energy,
projection, inverse, solve, Gram or complete-far supplier is repeated.
The planned seventeen-dimensional trial is unnecessary for this
fixed comparison and is not executed. These are applications of the
existing inverse-projection, rank-one inverse and inertia interfaces;
no generic novelty or Lean verification is claimed.

For the SAME source, an additional uniform test needs only exact
scalar arithmetic. If $U_{\rm res}$ is the saved complete upper for
$p_v$, then

$$
\tau_{\rm cap}=\frac{h_{\rm low}}{h_{\rm low}+U_{\rm res}}
$$

is a sufficient eligibility endpoint, because the saved complete
resolvent upper bounds the SAME $p_v$ independently of $\tau$.
The function $d(\tau)=\det(U_2+\tau r_V^*r_V/h)$ is affine, so

$$
d(\tau_{\rm cap})=(1-48\tau_{\rm cap})d(0)
 +48\tau_{\rm cap}d(1/48).
$$

Here $\tau_{\rm cap}>1/48$: a directed upper uses the LOWER
endpoint for $d(0)$, whose coefficient is negative, and the UPPER
endpoint for $d(1/48)$. The exact rational cached application gives

$$
\tau_{\rm cap}\approx0.0215048994247574,\qquad
\boxed{\sup_{0\le\tau\le\tau_{\rm cap}}d(\tau)
 <-4.36494\times10^{-1362}<0.}
$$

Thus this fixed-source comparison cannot certify whole-retained
positivity anywhere in the supplied sufficient eligibility interval.
The scalar application takes0.0145seconds and uses no new determinant
or matrix solve. Refining a residual trial or its numerical solver
inside this comparison cannot overcome that upper ceiling.

This interval is not the maximal actual capacity: an upper bound for
$p_v$ cannot exclude all larger actually eligible shifts. Additional
actual-surplus information permitting a larger shift, other positive
update directions, or a changed comparison/support remain distinct
routes. The actual common forms/domains, legal $E$ elimination,
unitary/SAME-short/inverse identifications and sound common
source/lift/full-far archives remain premises. Actual retained or
cofinal positivity, the Robin tail and RH remain unresolved.

### Use the complete band to tighten the same-source surplus budget

Keep the SAME actual common forms/domains, legal $E$ elimination,
closed short, unitary unphased cosine identification, exact384-bit
$w_0$, full $u=\mathcal Mw_0$, true $h$, complete far cap $U_F$ and
reflected153-cell weight $\widetilde W\ge1/v$. The far source is
orthogonal to EVERY cosine mode0 through $N=32768$, beyond the
single relation $u_F\perp u_J$ used in the centered bound. This full
band identification is a source/domain premise, not a consequence
of the scalar cache alone.

Let $P_N$ project onto those modes, and put

$$
\beta_k=\langle e_k,\widetilde W u_J\rangle,\quad
E_N=\sum_{k=0}^N|\beta_k|^2,\quad
b^2=\|(I-P_N)\widetilde W u_J\|^2=a_2-E_N.
$$

The ordinary Bessel/orthogonal projection and Cauchy inequalities give

$$
\boxed{p_v\le a_1+2\sqrt{U_F}\,b+mU_F.}
$$

For interval evaluation subtract a certified LOWER for $E_N$ from
the saved UPPER for $a_2$, retain a nonnegative residual, and use
UPPER endpoints in the final budget. The full far self-energy remains
$mU_F$; no far mode or cross term is discarded.

Only the missing multiplication projection needs production. In the
reflected coordinate $s\in[0,1]$, write $c_l=\int_0^1\widetilde W(s)
\cos(\pi ls)\,ds$. The same rational cell boundaries and weights give
$c_0$ by weighted length and $c_l$, $l\ge1$, by the finite sum of
internal jumps times $\sin(\pi lt)/(\pi l)$. For the saved positive
input modes $J=2049{:}32768$,

$$
\beta_0=\sqrt2\sum_{n\in J}u_nc_n,\qquad
\beta_k=\sum_{n\in J}u_n(c_{|n-k|}+c_{n+k}),\quad1\le k\le N.
$$

This is the standard Toeplitz plus Hankel multiplication formula:
see Olver–Townsend, [arXiv:1202.1347v2](https://arxiv.org/pdf/1202.1347v2),
§2.2, (2.7), crediting Baszenski–Tasche. The substitution
$x=\cos(\pi s)$ gives the Chebyshev correspondence. Only the exact
multiplication identity is used; the subsequent continuous-coefficient
uniform approximation argument is not transferred to this step weight.
Coefficients through $2N$ suffice EXACTLY for the requested matrix
elements, without truncating the weight or its full squared norm.
One symmetric Laurent polynomial convolution supplies all $\beta_k$,
using FLINT's existing ball product rather than a new FFT implementation;
see Johansson, [arXiv:1611.02831v1](https://arxiv.org/pdf/1611.02831v1),
§6.1, and the [FLINT polynomial multiplication interface](https://flintlib.org/doc/arb_poly.html#c.arb_poly_mul).

The [same-source experimental application](https://github.com/the-omega-institute/trureturing-experiments/tree/d5345c96/docs/reports/weil-c27)
reuses the source/action, all153 source-cell masses, $a_1,a_2$, far
allowance and old determinants. It supplies

$$
E_N\approx1147558.75453915,\qquad
b^2<17004.300397,\qquad
\boxed{p_v<38420.120.}
$$

The complete cross upper is approximately1784.31468695. The new
budget improves the saved48941.0175473 resolvent upper, using the
same source and weight. The sole1024-bit computation takes9.17seconds;
all65537 weight coefficients and32769 projection coefficients are
archived for reuse. There is no new determinant, operator-source
action, inverse, solve, old source-cell integral or far supplier.

The two saved determinant enclosures also locate the zero of the
SAME affine ceiling $d(\tau)$, without a new matrix calculation:

$$
\tau_*\approx0.0266626470290776,\qquad
C_*:=h\frac{1-\tau_*}{\tau_*}\approx39265.5677943.
$$

Use the LOWER endpoint of the induced $C_*$ enclosure for the strict
budget test. The new complete upper passes it and supplies

$$
\tau_{\rm band}=\frac{h_{\rm low}}{h_{\rm low}+U_{\rm band}}
\approx0.0272333893565792,
\qquad
d(\tau_{\rm band})\approx4.83012948603\times10^{-1363}>0.
$$

Thus this stronger information supplies eligible parameters beyond the
previous negative-ceiling interval. The previous exclusion on its OLD
supplied interval remains valid. A positive ceiling at the new endpoint
does not prove a lower construction positive, identify maximal actual
capacity, or settle the good-block/sufficient score. Those are separate
remaining estimates.

There is no need to expand the fixed-price640 resolvent test space.
For any allowed test $q$, weighted Cauchy with
$A_\lambda=\lambda-\widetilde W>0$ gives

$$
\frac{|\langle q,u_J\rangle|^2}
 {\langle q,A_\lambda^{-1}q\rangle}
\le\lambda a_0-a_1.
$$

Consequently every upper-bound recipe of the form
$\lambda(a_0+U_F)-|\langle q,u_J\rangle|^2/
\langle q,A_\lambda^{-1}q\rangle$ is at least $a_1+\lambda U_F$.
At640 this recipe floor exceeds the required $C_*$ even if its test
space is enlarged. This is an obstruction to that upper-bound recipe,
not a lower bound for actual $p_v$; no further resolvent producer is run.

These are applications of existing Fourier multiplication, ball
arithmetic and projection inequalities to one common source, not new
general theorems or Lean verification. All stated actual form/domain,
short, unitary, full-band, source and sound complete-far/cache premises
remain conditions. Actual retained/cofinal positivity, the Robin tail
and RH remain unresolved.

### Transport the archived trial before another matrix solve

Use the supplied $\tau_{\rm band}$ above and BOTH true-$h$ endpoints.
The archived exact17trial $x$ and scalar enclosures already describe
the SAME $\Sigma_0=\Sigma_*+\delta H_{\rm lift}$, unchanged finite row
$b_J$, source row $r=r_V$ and complete paid PSD far Gram $G$.
Write $\Sigma_0=\left(\begin{smallmatrix}a_0&c\\c^*&F_0\end{smallmatrix}\right)$,
$a_0<0$, and

$$
g_0=\bigl((b_0-cx)/a_0,x\bigr),\quad m_0=rg_0,\quad
z_0=g_0^*Gg_0,\quad \mu=\tau/h,\quad
\eta=1+\mu r_0^2/a_0.
$$

For this real fixed trial, the standard rank-one update gives

$$
a_\tau=a_0+\mu r_0^2=a_0\eta,\quad
\theta=\frac{\mu r_0m_0}{a_\tau},\quad
g_\tau=g_0-\theta e_0,
$$

$$
q_\tau(x)=q_0(x)-\frac{\mu m_0^2}{\eta},\qquad
z_\tau=z_0-2\theta(e_0^*Gg_0)+\theta^2G_{00}.
$$

Indeed, the first gradient coordinate is
$(b_0-cx-\mu r_0r_+x)/(a_0+\mu r_0^2)$; subtracting its old
value gives $-\theta$. Expanding
$q_0(x)=(b_0-cx)^2/a_0+2b_+x-x^*F_0x$ under the SAME rank-one
update gives the displayed decrement. The Gram identity then follows
by expanding $g_\tau^*Gg_\tau$.

The cached $q_0$ is only a LOWER and is used in that direction.
Only the missing18term mixed scalar $e_0^*Gg_0$ needs a new contraction.
Recompute, rather than transfer the old far coefficient,

$$
A_\tau=\kappa-\frac{\kappa^2G_{00}}{-a_\tau}>0,
\qquad \kappa=33/32.
$$

The same-source far square completion supplies the directed lower

$$
\mathcal K+q_\tau(\mathcal BV)
\ge\ell_\tau:=(\mathrm{charge})_{\rm lo}+q_{0,\rm lo}
 -\left(\frac{\mu m_0^2}{\eta}\right)_{\rm up}
 -\left(\frac{\kappa^2z_\tau}{A_\tau}\right)_{\rm up}.
$$

The [saved scalar application](https://github.com/the-omega-institute/trureturing-experiments/tree/a2283cc01569193283e2a0ee12139cc66909e35b/docs/reports/weil-c27)
reuses all old trial, source, energy and Gram calculations. Its sole
fixed1024/640-bit run takes0.09882seconds and encloses

$$
\eta\simeq0.379630426033288183,\quad
a_\tau\simeq-4.47097042972572520\times10^{-32},\quad
A_\tau\simeq0.362304559585549403,
$$

$$
z_\tau\simeq55.6410065569858228,\qquad
(\kappa^2z_\tau/A_\tau)_{\rm up}\simeq163.323659119699822,
\qquad \boxed{\ell_\tau\simeq-177.935387035771641.}
$$

The strict pivot and coefficient guards pass, but this negative LOWER
is inconclusive about the exact score and about positivity. A positive
$\ell_\tau$ would exclude every $D>0,D\ge\mathcal K$ at the endpoint;
the fixed-$D$ order

$$
\overline L_{\tau_2}+\mathcal B^*\mathcal B/D
 -\overline L_{\tau_1}-\mathcal B^*\mathcal B/D
=\frac{\tau_2-\tau_1}{h}r^*r\succeq0
$$

would then extend that exclusion down the supplied interval. Its
antecedent is not established here. The old smaller-interval ceiling
exclusion and the enlarged conditional eligibility budget keep their
stated scopes.

No new inverse, solve, trial, matrix/determinant, source/action,
Fourier/potential or old energy/far supplier is run, and this fixed
recipe stops without scanning. A sufficient positivity certificate
still needs the SAME actual Schur complement and good-block inverse
cost; the projected18row and exclusion upper $\Sigma_{\max}$ cannot
replace them. All inherited actual inverse-form/domain, legal $E$,
SAME-short, unitary/source/lift and sound complete-far/cache conditions
remain premises. This is a numerical application of established
rank-one and square-completion identities, without a generic novelty,
Lean, actual retained/cofinal positivity, Robin-tail or RH claim.


### Reuse complete cached finite coordinates before a good-block metric

The common-column, finite-channel and actual-channel packets already
supply all inputs for a finite row on the complete retained space.
Keep the original real, unphased384-bit row0 source, residual map,
weights and mode order. With retained modes $0,\ldots,1280$, write

$$
c\in\mathbb R^{1281\times1},\quad
\Beta\in\mathbb R^{19\times1281},\quad
\chi=A_\rho^{-1}F_\phi^*\in\mathbb R^{19\times1}.
$$

Here $c$ is `common.column`, $\Beta$ is `boundary.finite_beta`, and
$\chi$ is `actual.channel_inverse_actual_column`. These are the saved
complete arrays; no new source or channel action is needed. Their
same-source finite common row is

$$
\boxed{b_J=c^*-\chi^*\Beta.}
$$

The new consumer assembles its1281 coefficients with one thin channel
product. Its consistency check uses the SAME implicit exact lift
$V=[-X;I]$, $X=P^{-1}C$, with the archived positive/remaining coordinate
order. Thus

$$
b_JV=(b_J)_\ell-(b_J)_gX
=c^*V-\chi^*\Beta V.
$$

Source identity, normalization and distributivity identify this with
`actual.actual_finite_row_on_lift`; interval overlap checks the numerical
implementation, rather than proving equality from overlap. The saved
1263-by18 inverse action is used only for this lift, never as an inverse
on an arbitrary new good-block row.

The sole fixed1024-working/640-export-bit application takes0.22688seconds, exports all1281 finite ordered coefficient intervals,
and overlaps the archived lift row in all18 check coordinates. The
[saved source and data](https://github.com/the-omega-institute/trureturing-experiments/tree/85ba706c298d2f13651941d06c3b5c8a8cd652c9/docs/reports/weil-c27) preserve
the six input pins, twelve invoked source/helper hashes, original
source identity, retained partition and inherited conditions. The packet
SHA256 is
`479b8da2bb1d490d0f4adf285a67797d733ec05d4dab33d88b6175946a89f28a`.
No old supplier, source/adjoint/channel projection, inverse, solve,
Gram, far or Fourier production runs; no scan or precision retry follows.

The export contains every retained coordinate of the FINITE source
contribution. The actual complete row $b=\mathcal B$ still includes the
SAME-source far mixed row. The unweighted full $r=w^*R$ and a usable
1263-dimensional inverse-metric bound are also not supplied by this
assembly. Completeness in retained coordinates does not remove the
finite-source cutoff.

### A sufficient joint border on the same old core

Apply the existing Schur and Haynsworth inertia formulas to a weaker
SAME-object retained lower form $L_*\preceq\overline L$. This is an
application interface, with its missing inputs stated explicitly, not
a new general theorem or a computed positivity certificate. In the
archived coordinate order let

$$
L_*=\begin{pmatrix}P&C\\C^*&A_0\end{pmatrix},\quad
P\succ0,\quad X=P^{-1}C,\quad
\Sigma_0=A_0-C^*X,
$$

where $P$ has dimension1263 and the nondegenerate18-dimensional
$\Sigma_0$ has inertia$(17+,1-)$. For the original COMPLETE source
rows $r,b$, choose an admitted $0<t\le\tau/h$ and $D>0,D\ge\mathcal K$.
The lower target is

$$
T=L_*+t r^*r+b^*b/D.
$$

Define

$$
\rho=r_\ell-r_gX,\quad \beta_0=b_\ell-b_gX,\quad
U=\begin{pmatrix}\rho\\\beta_0\end{pmatrix},\qquad
G_2=\begin{pmatrix}r_g\\b_g\end{pmatrix}
P^{-1}\begin{pmatrix}r_g^*&b_g^*\end{pmatrix}.
$$

Eliminating the good block and then the rank-two border gives

$$
J=\operatorname{diag}(t^{-1},D),\qquad
N_2=J+G_2+U\Sigma_0^{-1}U^*,\qquad
T\succ0\ \Longleftrightarrow\ \det N_2<0.
$$

Indeed the good-block Schur complement is
$\Sigma_0+U^*(J+G_2)^{-1}U$. Its border with lower block
$-(J+G_2)$ has two congruent block eliminations. Since $J+G_2\succ0$
and $\Sigma_0$ has exactly one negative direction, $N_2$ has at least
one positive direction; strict positivity of the updated core is
therefore equivalent to one negative direction of $N_2$. A strictly
negative quadratic value $e^*N_2e$ for one fixed exact nonzero $e$
already suffices. This sufficient border uses the actual old core and
complete same-source rows; it is distinct from the archived two-source
UPPER ceiling.

The joint metric is essential. For the algebraic example
$P=1,C=0,\Sigma_0=-1$, $r=(1,1)$, $b=(\pm1,1)$ and $t=D=1$,
the reduced rows and both marginal inverse energies are equal in the
two cases. The cross energy changes sign, giving border Schur scores
$1$ and$-3$. Consequently those marginal and reduced data alone do
not determine even the sufficient score's sign. This is an interface
counterexample, not a sign calculation for the retained source.

If no applicable old factorization is available, the standard scalar
Schur test offers an alternative for one COMPLETE fixed combination row
$s=\overline e_1r+\overline e_2b$ and a proposed $\Omega>0$:

$$
P-s_g^*s_g/\Omega\succ0
\quad\Longleftrightarrow\quad s_gP^{-1}s_g^*<\Omega.
$$

A new structured positivity test of this changed target could certify
that metric bound using the existing displacement elimination; no
inverse need be formed. With full-row uncertainty $s=s_J+f$ and a sound
joint bound $f^*f\preceq C_{\rm far}$, Young's inequality gives, for
$\eta>0$,

$$
s^*s\preceq(1+\eta)s_J^*s_J+(1+\eta^{-1})C_{\rm far}.
$$

The same full uncertainty must also control the reduced-core term.
No combination, metric bound, far majorant, numerical parameter scan
or new structured positivity run is supplied here. The choice
$e=(0,1)$, and at $t=\tau/h$ the choice $e=(\tau,1)$, return
previously studied recipes and do not create new targets by renaming
them. Pivot lists and saved actions
against18 particular right sides do not constitute general1263-block
factors; the cached17-dimensional inverse acts only inside the18-core.

This leaves a precise next input: the complete rows and their joint
good-block inverse metric, or a sound bound for one fixed combination.
The finite1281-row assembly supplies one missing finite component only.
All actual common-form/domain, legal elimination, SAME-short,
unitary/source/lift, comparison and sound complete-far/cache premises
remain conditions. No Lean result, actual retained/cofinal positivity,
Robin-tail bound or RH conclusion is obtained.

### Stop a fixed-charge old-base recipe before filling the joint metric

The true old-core trial and its lower value are already cached. Apply
the existing fixed-trial transport and bordered-inertia identities to
that core, rather than rerunning the inconclusive transport on the
compression UPPER $\Sigma_{\max}$. Keep the original real, unphased
384-bit row0 source, $\rho=rV$, $\beta_J=b_JV$ and exact17-column $x$.
The cached lower $q_{0,\mathrm{lo}}$ is a lower for this SAME trial:
the saved positive variational lower is strictly positive, so the
producer's `max(0,trial)` clipping was inactive.

Write the TRUE old core as
$\Sigma_0=\left(\begin{smallmatrix}a&c\\c^*&F\end{smallmatrix}\right)$,
with $a<0$ and the saved inertia$(17+,1-)$. Choose exact rational values

$$
t_+=\frac{\tau_{\rm cap}}{h_{\rm lower}},\qquad
\overline D=\operatorname{up}
  (\texttt{actual.refined_common_charge_upper}).
$$

This $t_+$ is only an UPPER COMPARISON; its own eligibility is not
asserted. Every supplied $0\le\tau\le\tau_{\rm cap}$ and actual
$h\ge h_{\rm lower}>0$ gives $t=\tau/h\le t_+$.
Two short contractions restore the true-core gradient and mixed scalar:

$$
g_0=\binom{(\beta_{J0}-cx)/a}{x},\quad m=\rho g_0,\quad
\eta=1+t_+\rho_0^2/a,\quad a_+=a+t_+\rho_0^2.
$$

The fixed-trial identity on $\Sigma_0+t_+\rho^*\rho$ gives

$$
q_{\mathrm{trial},t_+}
=q_{\mathrm{trial},0}-t_+m^2/\eta
\ge q_{0,\mathrm{lo}}-\operatorname{up}(t_+m^2/\eta).
$$

The sole1024-working/640-export-bit application takes0.10488seconds.
It certifies $a_+<0$ and $\eta>0$, with approximate values

$$
\begin{gathered}
t_+\simeq2.5319197720691323970\cdot10^{-5},\qquad
a_+\simeq-4.47097042972572520\cdot10^{-32},\qquad
\eta\simeq0.379630426033288183,\\
q_{0,\mathrm{lo}}\simeq-120.742434607587509,\qquad
\operatorname{up}(t_+m^2/\eta)\simeq60.8094277285621680,\\
q_{t_+,\mathrm{lo}}\simeq-181.551862336149677,\qquad
\overline D\simeq183.800677119682971,\\
\boxed{\overline D+q_{t_+,\mathrm{lo}}>2.24881478>0.}
\end{gathered}
$$

The updated core retains17 positive directions and has a negative
first diagonal, hence exactly one negative direction. The center
border's first pivot is positive, and its second Schur pivot is at
least the displayed strict margin. Thus the center border is PD.
Adding any actual PSD $G_2$ cannot make $N_2$ indefinite. The preceding
inertia application therefore gives one negative direction of the
auxiliary target with ZERO projected far response, without computing
the missing1263-good-block inverse metric. Loewner order extends this
exclusion throughout $0\le t\le t_+$ and $D\ge\overline D$ for the
same zero-response recipe.

The [source and directed data](https://github.com/the-omega-institute/trureturing-experiments/tree/a6747eec1610f0d473fda635a1160ddb0d98b181/docs/reports/weil-c27)
pin the seven cached inputs and source identities; packet SHA256 is
`685d3535cfbc21f6ad3d03b04126d5250ff76570265fbf7f315ca741a6b45af3`.
Only17 first-gradient and18 mixed-contraction terms are new. No
supplier, inverse, solve, profile, old trial quadratic, Gram, source
action, far action or parameter/precision scan is run.

Consequently an explicitly enlarged energy/Gram upper-only uncertainty
relaxation containing zero PROJECTED far response cannot certify this
fixed-$\overline D$ recipe uniformly. That relaxed response is not an
actual $u_F=Mw$ realization. A smaller source-dependent valid $D$, a
signed/correlated far-charge constraint excluding this relaxed point,
or a stronger TRUE baseline remains outside the obstruction. Merely
tightening upper envelopes while retaining that point cannot remove it.
The older unshifted actual-source exclusion is reused, not republished
as new. All common-form/domain/inverse/legal-elimination/SAME-short,
unitary/source/lift/comparison and sound full-far/cache premises remain
conditions. The actual full far completion, actual retained/cofinal
positivity, Robin tail, RH and Lean verification remain unresolved.

### Retain signed source correlations in the infinite principal tail

The previous fixed-charge exclusion does not cover a smaller legal,
source-dependent fee. Estimate that fee from the SAME actual far action

$$
u_F=G_{FJ}w-G_{FE}q+H_{FE}(q-p),
\quad E=\{1281,\ldots,2048\},\quad
J=\{2049,\ldots,32768\}.
$$

Keep the original constant $W_F=D_{\rm far}I$ and the saved inverse
profiles. The existing disjoint smooth kernel has principal term
$(-1)^{m+n}/[2(m+n)]$. Write $M=32768$, $L=1281$ and combine its two
source blocks BEFORE taking a norm:

$$
z_n=\begin{cases}-(-1)^nq_n,&n\in E,\\
(-1)^nw_n,&n\in J.\end{cases}
\qquad v_m=\frac{(-1)^m}{2}\sum_{n=L}^{M}\frac{z_n}{m+n}.
$$

This is a classical tail-Gram application. Partial fractions and the
[digamma recurrence](https://dlmf.nist.gov/5.5.E2) give, for $n\ne k$,

$$
S_{nk}=\sum_{m>M}\frac1{(m+n)(m+k)}
=\frac{H_{M+k}-H_{M+n}}{k-n}.
$$

On the diagonal the [trigamma series](https://dlmf.nist.gov/5.15.E1)
and the integral test give $S_{nn}\le1/(M+n)$. Define

$$
h_L=0,\qquad h_{n+1}=h_n+\frac1{M+n+1},\qquad
(Kz)_n=\sum_{k\ne n}\frac{z_k}{n-k}.
$$

Pairing the off-diagonal terms yields the directed quadratic upper

$$
Q_{\rm pad}=\sum_{n=L}^M\frac{z_n^2}{M+n}
+2\sum_{n=L}^M h_nz_n(Kz)_n
\ \ge\ \sum_{m>M}\left(\sum_{n=L}^M\frac{z_n}{m+n}\right)^2.
$$

Only positive diagonal padding is added to the exact Gram. Thus the
bound holds for signed real sources, with their E/J cross terms intact.
It does not follow from an entrywise matrix upper being a Loewner upper.
One linear Toeplitz convolution computes $Kz$ through the existing FLINT
ball polynomial product; the kernel orientation is $1/(n-k)$.
The saved finite $w^*Jw$ convolution is a different quadratic and is
reused as its own result, not recomputed here.

Let $R_w,R_q$ be the saved UNWEIGHTED smooth remainder norm uppers,
already including $\gamma$, and let $H_{\rm mix}$ be the saved WEIGHTED
bound for $H_{FE}(q-p)$. The complete actual-source estimate is

$$
N_{\rm new}=\frac{\sqrt{D_{\rm far}}}{2}
 \sqrt{\operatorname{up}(Q_{\rm pad})}
+\sqrt{D_{\rm far}}(R_w+R_q)+H_{\rm mix},\qquad
s=\|u_F\|_{W_F}^2\le E_{F,\rm new}:=\operatorname{up}(N_{\rm new}^2).
$$

All mixed-H and smooth remainder allowances, including the norm cross
terms, remain paid. A negative interval lower for $Q_{\rm pad}$ causes
no problem when its finite upper is nonnegative; a negative upper or
nonfinite result stops the prescribed computation.

Rebuild the independent charge constant with the required directions,

$$
K_{0,\rm up}=\operatorname{up}(m_J)
-\operatorname{lo}(h)-\operatorname{lo}(E_\phi),\qquad
D_{\rm new}=\operatorname{up}(K_{0,\rm up}+\tfrac{33}{32}E_{F,\rm new}).
$$

Then $D_{\rm new}\ge\mathcal K$ for the same actual source, and its
strict positivity is checked before using it as a legal denominator.
Subtracting an old far-energy UPPER from an arbitrary old charge UPPER
would not justify this conclusion.

The saved full-band Bessel projection and reflected potential remain
unchanged. With their saved $a_1,B^2,m_{\max}$, the existing budget
identity gives

$$
U_{F,\rm new}=E_{F,\rm new}/D_{\rm far},\quad
p_{\rm up}=\operatorname{up}
 (a_{1,\rm up}+2\sqrt{U_{F,\rm new}B^2_{\rm up}}
       +m_{\max}U_{F,\rm new}),\quad
\tau_{\rm new}=\frac{h_{\rm lower}}{h_{\rm lower}+p_{\rm up}}.
$$

This cap asserts sufficient conditional eligibility only. The prior
full-band budget already met its conservative capacity target; no new
determinant or capacity-sign claim is needed.

The sole fixed1024-working/640-export-bit application takes0.52936
seconds. Its directed endpoints have the following approximate values:

| Quantity | Previous upper | New upper |
|---|---:|---:|
| Complete weighted far energy |14.1648613043077766|9.16483973939069465|
| Positive source-valid fee |183.800677119682971|178.644404880862230|
| Supplied sufficient parameter cap |0.0272333893565792018|0.0358711862066475850|

The saved diagonal padding is approximately0.0310968581461585082,
the signed cross contribution85.8252958041207774, and
$Q_{\rm pad}\simeq85.8563926622669359$. The new principal weighted norm
upper is2.54859258899100702; the retained smooth remainder contributes
at most approximately$1.37047745623703291\cdot10^{-12}$ and the mixed-H
norm upper remains0.478756042961116999. Their complete norm upper is
3.02734863195349449. The rebuilt independent charge constant upper is
169.193163899615576 and the complete reflected weighted budget upper
is28909.5331794819506.

The [source and directed data](https://github.com/the-omega-institute/trureturing-experiments/tree/348943da339e0eb3eaf8b6d49a67e64a24c0b439/docs/reports/weil-c27)
pin nine accepted inputs, nine invoked source/helper files and nine
cached producer sources. Packet SHA256 is
`d09a5ab254d164cfd40982b31e1a155e31d6288b705d916bf248236a0d527606`.
Only one new length31488 signed-source linear convolution and its
quadratic reduction are performed. The original w, q and p, symbol
remainder certificates, weighted mixed-H bound, channel subtraction,
full-band projection and moment are reused. No old producer,
inverse/solve, far-mode array, new potential projection, determinant,
or parameter/source/precision scan is run.

This supplies a smaller positive legal fee and a larger sufficient
eligibility cap under the inherited actual common-form/domain,
inverse/legal-elimination/SAME-short, unitary/source/lift/comparison
and sound complete-far/cache premises. It does not give a negative
FULL border margin. In particular the earlier fixed-$\overline D$
auxiliary exclusion does not apply to this smaller fee; leaving that
exclusion's scope is not a positivity certificate. The actual signed
mixed far response, the relevant joint good-block inverse metric,
actual retained/cofinal positivity, Robin tail, RH and Lean
verification remain unresolved. The tail identity and numerical
algorithms are classical results reused in a source-specific
application, not new generic mathematics.

### A fixed negative-channel envelope before a signed far functional

Keep the SAME true old18-core and write

$$
\Sigma_0=\begin{pmatrix}a&c\\c^*&F\end{pmatrix},\quad a<0,
\quad S=F-c^*c/a\succ0,\quad
T=\binom{-c/a}{I},\quad \delta=-a.
$$

The existing block inverse identity gives

$$
Q=\Sigma_0^{-1}=Q_+-\frac{e_0e_0^*}{\delta},\qquad
Q_+=TS^{-1}T^*\succeq0.
$$

The negative channel is thus the first coordinate; no new eigenvector
or inverse is required. The saved exact17-reference $R$ and certified
$0\le\eta<1$ already give $S^{-1}\preceq R/(1-\eta)$ for this SAME
positive complement. The reference is not identified with the actual
inverse.

Use the signed-tail packet's energy cap $\overline E$, positive fee
$D$ and supplied cap $\tau_{\rm cap}$, all frozen at their outward
exported endpoints. Freeze the legal coefficient

$$
t_0=\tau_{\rm cap}/h_{\rm upper}>0.
$$

Since actual $h\le h_{\rm upper}$, this satisfies
$t_0\le\tau_{\rm cap}/h$. The comparison coefficient formed with
$h_{\rm lower}$ does not supply this legality statement.
The cached rows remain $\rho=rV$ and $\beta_J=b_JV$, with actual
$\beta=\beta_J+f$ and $f=\kappa u_F^*W_FR_FV$, $\kappa=33/32$.
For a fixed real $e=(\alpha,1)$ set

$$
y=\alpha\rho+\beta_J,\qquad \lambda=y_0,\qquad \xi=f_0.
$$

Select $\alpha$ once from the finite reference steering entries

$$
H_{11}^{\rm ref}=t_0^{-1}+\rho_0^2/a+(\rho T)R(\rho T)^*,\qquad
H_{12}^{\rm ref}=\rho_0\beta_{J0}/a+(\rho T)R(\beta_JT)^*.
$$

Require a positive steering denominator. Take the exact midpoints of
their outward640-grid exports, form their negative ratio, and floor it
to a64-bit dyadic. This fixes a direction independently of the actual
signed tail. It asserts neither actual-center equality nor optimality.

Let $G$ be the original full paid far Gram on the SAME lift, including
all allowance. The existing reference-trace bound $\tau_F$ applies to
$C_t=\kappa^2E_0G$, where $E_0$ is the OLD chosen energy-cap constant.
With its positive cached lower endpoint $E_{0,\rm lo}$,

$$
\operatorname{tr}(Q_+G)\le
\mathcal T:=\frac{\tau_{F,\rm up}}{\kappa^2E_{0,\rm lo}}.
$$

This denominator is a lower for a cap constant, not a lower for actual
$\|u_F\|_W^2$. No new trace or Gram contraction is needed. Put

$$
p_\alpha=\operatorname{up}
 \frac{(yT)R(yT)^*}{1-\eta},\quad
c_+=\operatorname{up}(\kappa\sqrt{\overline E\mathcal T}),\quad
C_-=\operatorname{up}(\kappa\sqrt{\overline E G_{00,\rm up}}).
$$

PSD trace and the seminorm triangle inequality give
$|\xi|\le C_-$ and an exact frozen exported upper

$$
\overline T=\operatorname{up}
 \left(\alpha^2/t_0+D+(\sqrt{p_\alpha}+c_+)^2\right).
$$

For the full center border, before its additional good-block metric,

$$
\boxed{e^*H_{\rm full}e
\le \overline T-\frac{(\lambda+\xi)^2}{\delta}.}
$$

Let $L_\lambda$ be a directed upper for $|\lambda|$. A cheap capacity
floor for this fixed UPPER-envelope package is

$$
F_{\rm pkg}=\operatorname{down}
 \left(\overline T-\frac{(L_\lambda+C_-)^2}{\delta_{\rm lower}}\right).
$$

If $F_{\rm pkg}\ge0$, no allowed $\xi$ makes this package strictly
negative. This excludes only the fixed $\alpha$ and positive-channel
pricing envelope. Separate favorable endpoints are not asserted to
have a common realization. If $F_{\rm pkg}<0$, the package is merely
not excluded; a negative lower proves no actual sign.

For a subsequent SAME-source interval $I_\xi$, the sufficient center
test would instead use the opposite denominator endpoint:

$$
U_{\rm ctr}=\operatorname{up}
 \left(\overline T-
 \frac{\operatorname{dist}(0,I_\lambda+I_\xi)^2}
      {\delta_{\rm upper}}\right)<0.
$$

A zero-crossing response interval earns no negative-channel credit.
Even a negative center bound still needs
$e^*G_2e<-U_{\rm ctr}$ for the additional PSD good-block metric before
the sufficient retained positivity criterion applies.

The sole fixed1024-working/640-export-bit application takes0.04108
seconds and gives the following approximate directed values:

| Quantity | Directed value |
|---|---:|
| Fixed dyadic $\alpha$ |0.0379872985139444681|
| Legal $t_0$ |0.0000333498575645498988|
| Positive-channel finite energy upper $p_\alpha$ |589.902516599596736|
| Positive far-channel norm upper $c_+$ |1.97459507735731611|
| Frozen $\overline T$ |911.633113280467383|
| Finite response $\lambda$ |$9.64684697797322708\cdot10^{-15}$|
| Far-response radius $C_-$ |$5.23550628472335536\cdot10^{-16}$|
| Sufficient response magnitude upper |$1.03616862656981840\cdot10^{-14}$|
| Package floor lower $F_{\rm pkg}$ |33.3488964810889399|

Even the most favorable allowed magnitude of the negative-channel
response is at most approximately$1.01703976064455626\cdot10^{-14}$.
Its largest permitted negative credit is approximately878.284216799378443,
below the frozen positive envelope. The strict positive floor excludes
this fixed package for every allowed signed far response. Computing
its actual $\xi$ alone cannot make this envelope certify a negative
center, so this package's prospective signed-tail supplier is not run.

At the same direction, fee, legal coefficient and response radius, any
replacement positive-channel envelope would have to remove at least
a gap greater than33.3488 before strict negativity could
become possible. This is a necessary package-capacity requirement only;
separate favorable endpoints need not be attained together, and passing
it would supply neither an actual negative center nor the additional
good-block metric. Tighter coherent positive-channel pricing or another
legal direction/recipe is not excluded. The actual FULL border can
have a sign that this conservative envelope does not certify.

The [source and directed packet](https://github.com/the-omega-institute/trureturing-experiments/tree/a98a4b1e8a85b4830d6aebe526cda7ba4566ddf6/docs/reports/weil-c27)
pin ten accepted inputs and ten cached producer sources, with invoked
local helper and input bytes guarded at entry and exit. Packet SHA256
is `1487736c15e524c3b86859c3e427c85ccf3512659990597bb8199e882688b21e`.
Only three new17-dimensional reference quadratic/bilinear forms are
evaluated. The exact reference identities, Neumann/inertia tests, old
trace and Gram, original source/finite action and signed-tail energy
result are reused. No old producer or passed suite, new inverse/solve,
trace/Gram/source/far supplier, determinant or parameter/source/precision
scan is executed.

This is a source-specific cached-data application of the established
block inverse decomposition, certified Loewner comparison, PSD trace
and norm triangle/Cauchy bounds; no new generic theorem or algorithm is
claimed. All inherited actual-form/domain, inverse/legal-elimination/
SAME-short, unitary/source/lift/comparison and sound complete-far/cache
premises remain conditions. The actual signed far functional, full-border
sign, joint good-block metric, retained/cofinal positivity, Robin tail,
RH and Lean verification remain unresolved.

### Price a coherent full-inverse tail direction

The isolated negative-channel envelope is excluded only with its
fixed triangle pricing of the positive channel. Keep the SAME legal
coefficient, fee, source-energy cap and exact dyadic direction from
that packet. Let $\mathcal H_{\rm ctr}(e)$ denote the center scalar
before the additional PSD good-block metric. All rows retain the
original real, unphased convention. Write $y=\alpha\rho+\beta_J$ and
$f=\kappa u_F^*W_FR_FV$, without changing the original source row
$\rho$. With the same true old-core decomposition, define

$$
Q_R=TRT^*-\frac{e_0e_0^*}{\delta},\qquad
v_R=Q_Ry^*,\qquad \vartheta=fv_R.
$$

This direction is determined by finite data before evaluating the
actual signed far response. $Q_R$ is a reference, not the true inverse.
The one signed functional $\vartheta$ combines the positive and negative
cross terms before taking absolute values. It differs from the
previous isolated response $\xi=f_0$.

Reuse the saved finite reference energy $r=(yT)R(yT)^*$, the
relative comparison $R/(1+\eta)\preceq S^{-1}\preceq R/(1-\eta)$
and the complete-far trace bound $fQ_+f^*\le c_+^2$. Set

$$
A=\operatorname{up}((1+\eta)c_+^2),\quad
\epsilon_R=\frac{\eta}{1-\eta},\quad
\Delta=\operatorname{up}\left[
\epsilon_R(\sqrt{r_{\rm up}}+\sqrt A)^2\right].
$$

The lower comparison gives $R\preceq(1+\eta)S^{-1}$, so
$fTRT^*f^*\le A$. The upper comparison gives
$S^{-1}-R\preceq\epsilon_R R$. Consequently the reference error
on the SAME combined row $y+f$ is at most $\Delta$.

Expanding through $Q_R$ and discarding only the nonpositive tail
self-term $-f_0^2/\delta$ yields

$$
\mathcal H_{\rm ctr}(e)
\le\frac{\alpha^2}{t_0}+D+r+A+\Delta
-\frac{\lambda^2}{\delta}+2\vartheta,
\qquad \lambda=y_0.
$$

Freeze the exact outward exported upper

$$
C_{\rm lin}=\operatorname{up}_{640}\left[
\frac{\alpha^2}{t_0}+D+r_{\rm up}+A+\Delta
-\frac{\lvert\lambda\rvert_{\rm lo}^2}{\delta_{\rm up}}
\right].
$$

Then $\mathcal H_{\rm ctr}(e)\le C_{\rm lin}+2\vartheta$.
Using an upper magnitude for the subtracted finite response, or a
lower denominator, would not justify this upper bound.

Before supplying an actual signed tail interval, the SAME full paid
far Gram $G$ gives

$$
\lvert\vartheta\rvert\le C_\vartheta:=\operatorname{up}
\left[\kappa\sqrt{\overline E\,
\operatorname{up}(v_R^*Gv_R)}\right].
$$

Only one new reference matrix-vector action and one full far-Gram
quadratic are needed; the inverse, trace, finite reference energy and
norm cap are reused. Enclosing the one exact $v_R$ by interval
coefficients preserves this capacity statement when the complete
quadratic interval is propagated. Selecting an unrelated center would
instead require paying a separate direction-error term.

A nonnegative directed floor

$$
\operatorname{down}(C_{\rm lin}-2C_\vartheta)\ge0
$$

excludes only this frozen linear upper-envelope recipe. A negative
floor means only that the recipe is not excluded. Its supplier would
have to enclose the actual SAME-source $\vartheta$ in an interval
$I_\vartheta$ with

$$
\operatorname{up}(C_{\rm lin}+2I_\vartheta)<0.
$$

Separate favorable endpoints need not be jointly attained. The
discarded negative self-square can also make the linear recipe fail
when a more precise nonlinear estimate could pass. Even a negative
actual center certificate still needs the additional PSD good-block
metric payment before the sufficient retained criterion applies.

The sole fixed1024-working/640-export-bit application freezes
$C_{\rm lin}\simeq25.528336100647874028$ and the exact sufficient
threshold $-C_{\rm lin}/2\simeq-12.764168050323937014$. The reference
tail-energy upper is $A\simeq3.899025719523745176$ and the combined
reference-error payment is $\Delta\simeq2.741896657461350714\cdot10^{-25}$.
The direct interval for the full Gram quadratic is approximately
$[-4.498124461691914\cdot10^{24},4.498124461691913\cdot10^{24}]$.
Its positive endpoint gives only
$C_\vartheta\simeq6.621282736104631330\cdot10^{12}$; the resulting
negative package floor supplies no actual sign or favorable realization.
It does not establish a large actual norm. The retained coefficient
intervals enclose the one analytic direction; their endpoints must not
be selected independently to define another source.

### Bound the same direction using the cached positive trace

The existing complete-far PSD trace certificate gives a second
bound without another vector, Gram or trace contraction. Let
$\mathsf B=R_FV$ and keep the SAME paid PSD majorant
$\mathsf B^*W_F\mathsf B\preceq G$, including all allowance. Put

$$
g=yT,\quad H=T^*GT,\quad
M_R=R^{1/2}HR^{1/2}\succeq0,\quad x=R^{1/2}g^*.
$$

The classical PSD operator/trace inequality, trace cyclicity and
$R\preceq(1+\eta)S^{-1}$ give

$$
\begin{aligned}
\|G^{1/2}TRg^*\|^2
&=x^*M_Rx\le\|x\|^2\operatorname{tr}M_R\\
&=r\operatorname{tr}(TRT^*G)\\
&\le r(1+\eta)\operatorname{tr}(Q_+G)
\le r(1+\eta)\mathcal T.
\end{aligned}
$$

No commutation of the PSD factors is assumed. Since
$v_R=TRg^*-(\lambda/\delta)e_0$, the SAME majorant seminorm obeys

$$
\boxed{
\|\mathsf Bv_R\|_{W_F}\le\sqrt{v_R^*Gv_R}
\le N_{\rm split}:=\operatorname{up}\left[
\sqrt{r_{\rm up}(1+\eta_{\rm up})\mathcal T_{\rm up}}
+\frac{|\lambda|_{\rm up}}{\delta_{\rm lo}}
 \sqrt{G_{00,\rm up}}\right].}
$$

Here $\mathcal T$ is the already-normalized positive-channel trace
bound from the fixed negative-channel packet. Dividing it by another
energy or cap factor would not preserve the certificate. For this norm
upper, the response magnitude uses its UPPER endpoint and the positive
pivot magnitude uses its LOWER endpoint, opposite to the subtracted
finite credit in $C_{\rm lin}$.

The direct quadratic upper supplies
$N_{\rm direct}=\operatorname{up}\sqrt{(v_R^*Gv_R)_{\rm up}}$.
Freeze the minimum of these two exact outward bounds on the SAME
seminorm and its resulting radius:

$$
N_{\rm cap}=\min(N_{\rm split},N_{\rm direct}),\qquad
C_{\vartheta,\rm new}
=\operatorname{up}_{640}(\kappa\sqrt{\overline E}N_{\rm cap}).
$$

This is a uniform operator-norm derivation. Dividing a bound on a
particular source's $|\vartheta|$ by its source-energy cap would not
prove a direction-norm bound. Taking the minimum does not assert
that separate extremizers are jointly attained. $N_{\rm cap}$ controls
the one analytic direction, not all vectors in its coefficient box.
Any future source-specific functional must preserve that relation
through its factored or short-lift interface and pay coefficient and
remainder errors; replacing the direction by a free midpoint is invalid.

One scalar-only1024-working/640-export-bit consumption of the saved
packets takes0.01185seconds and gives:

| Quantity | Approximate directed value |
|---|---:|
| Positive-direction norm upper |15.361788283107843110|
| Negative-direction norm upper |13.736525306317097479|
| Selected norm upper $N_{\rm cap}$ |29.098313589424940590|
| Response radius $C_{\vartheta,\rm new}$ |90.843575457008727073|
| Unchanged $C_{\rm lin}$ |25.528336100647874028|
| Package floor lower |−156.158814813369580117|
| Uniform center upper |207.215487014665328174|
| Unchanged strict signed threshold |−12.764168050323937014|

The new radius is smaller than the direct entrywise interval bound.
The negative package floor still supplies no actual signed functional,
favorable realization, negative center or full-border sign. Even an
actual response below the frozen threshold would only open the
additional PSD good-block metric test. In particular zero remains
allowed by this radius alone. No expensive tail supplier is run on
capacity nonexclusion alone; a complete source-specific factored or
short-lift evaluation and its error contract remain missing.

The coherent packet SHA256 is
`b082eaad102c5f7ca38d1c49c19970952288ce630198a4ea76b48b96d8d23b65`;
the scalar-only packet SHA256 is
`6e4232d6079a4279511a67c13c6501d51a3b4fdaf410ccfee957adce29e1d7bc`.
Both sources and directed data are retained in the
[experiment package](https://github.com/the-omega-institute/trureturing-experiments/tree/053d16a54d6eb05c634867b271922e7d994ca9d5/docs/reports/weil-c27).
The scalar adapter parses only the two accepted packets' scalars and
metadata and guards inherited data/producer/helper bytes at entry and
exit. It does not extract matrices or vectors, repeat a scientific
contraction or replay an old producer or passed suite. There is no
inverse/solve, source/far supplier, determinant or parameter/source/
precision scan. The fixed direction, fee, legal coefficient, source
energy cap, exact center envelope and signed threshold are unchanged.

This is a source-specific application of the existing block inverse,
relative Loewner, PSD operator/trace and Cauchy inequalities, not new
generic mathematics. All inherited actual-form/domain, inverse/legal
elimination/SAME-short, source/unitary/lift/comparison and complete
paid-far/cache premises remain conditions. Actual signed tail response,
full-border sign, good-block metric, retained/cofinal positivity,
Robin tail, RH and Lean verification remain unresolved.

### Use the full short residual jet for one signed functional

The forward geometric-jet bounds in the existing infinite-coupling
section also supply a function-error interface for the SAME coherent
direction. A Gram-error estimate alone would not supply one: replacing
an operator by its negative preserves its Gram and changes its action.
Here the original construction separately bounds the forward geometric
error and the error in the exact midpoint features.

Let $C_{\rm phys}$ be the original coupling from modes0 through2048 to
$m>32768$, and let $\mathcal D=\binom I{-Y}$ be the SAME exact physical
residual map, with $Y=F_E^{-1}B_E$ on $E=\{1281,\ldots,2048\}$.
Keep the exact implicit retained lift $V$ and direction $v_R$. Thus
$\mathsf B=R_FV=C_{\rm phys}\mathcal D V$. The complete56-term jet is
$\mathcal L P$, with exact synthesis prefactor $2/\pi$, actual far
symbol $s_m$ and the original unphased parity factors. $P_0$ is the
original fixed midpoint feature matrix, including its midpoint for
$1/\sqrt2$. The cached lift features enclose $P_0\mathcal D V$.

Write $w_F>0$ for the original constant far weight and
$\alpha_J=4/(\pi^2M)$. Here $r_2$ is the original unweighted squared Frobenius bound;
$w_Fr_2$ bounds its weighted square. The previously established
component bounds give

$$
\|C_{\rm phys}-\mathcal LP\|_{W_F}^2\le w_Fr_2,
\qquad
\|\mathcal L(P-P_0)\|_{W_F}^2
\le w_F\alpha_J H_*e_P^2.
$$

The existing allowance construction has nonnegative components with
$\eta_{\rm geom}\ge r_2$ and
$\eta_{\rm round}\ge\alpha_JH_*e_P^2$. It retains the physical
residual amplification $K_{\rm phys}\ge\|\mathcal D\|^2$, so the
saved exact complete allowance satisfies

$$
\epsilon_{\rm complete}\ge
w_F(\eta_{\rm geom}+\eta_{\rm core}+\eta_{\rm round})K_{\rm phys}.
$$

The triangle inequality and $(a+b)^2\le2(a^2+b^2)$ therefore imply

$$
\boxed{
\|\mathsf Bv_R-j_h\|_{W_F}
\le\sqrt{2\epsilon_{\rm complete}}\,\|Vv_R\|,
\qquad h=P_0\mathcal D Vv_R.}
$$

This uses the forward component bounds, not Gram closeness alone.
The genuine full moment Gram controls $\|\mathcal L\|$; the sparse
masked core is not assumed PSD. No higher moment production or use
of that sparse core as a whole-jet norm is needed.

The exact midpoint feature order is $A_0,\ldots,A_{55},B_0,\ldots,B_{55}$,
and its actual synthesis is

$$
j_h(m)=\frac{2(-1)^m}{\pi m}
\sum_{k=0}^{55}(M/m)^{2k}
\bigl[(M/m)h_{B_k}-s_mh_{A_k}\bigr],\qquad M=32768.
$$

One new cached112-by18 feature action encloses $h$. The existing
lift Gram supplies a cheap diagonal-only norm bound

$$
L_V=\operatorname{up}\sum_{j=1}^{18}
|(v_R)_j|_{\rm up}\sqrt{(V^*V)_{jj,\rm up}},\qquad
\epsilon_b=\operatorname{up}_{640}
 \bigl(\sqrt{2\epsilon_{\rm complete}}L_V\bigr).
$$

No physical-vector reconstruction or new Gram contraction is required.
The target's matrix entries use640-bit units, while its original
allowance metadata retains512-bit units; the already-checked lift
metadata records that distinction. The source coefficient intervals
are propagated through the new feature action. A separately selected
midpoint is not identified with the exact common direction.

For the original principal proxy from the signed Hankel-tail estimate,
retain

$$
u_m^{(0)}=\frac{(-1)^m}{2}
\left[-\sum_{n\in E}\frac{(-1)^nq_n}{m+n}
+\sum_{n\in J}\frac{(-1)^nw_n}{m+n}\right],
\quad J=\{2049,\ldots,32768\}.
$$

Its independently bounded norm is $\|u^{(0)}\|_{W_F}\le P_{\rm up}$.
The SAME smooth and mixed-$H$ residual bounds give
$\|u_F-u^{(0)}\|_{W_F}\le\epsilon_u$. The original $q$ remainder
is retained; it is not relabeled as a remainder for $p$.
For $\mu=\kappa\langle u^{(0)},j_h\rangle_{W_F}$, telescope as

$$
\vartheta-\mu=\kappa\left[
\langle u_F-u^{(0)},\mathsf Bv_R\rangle_{W_F}
+\langle u^{(0)},\mathsf Bv_R-j_h\rangle_{W_F}\right].
$$

The existing direction norm cap consequently gives the scalar payment

$$
\boxed{
|\vartheta-\mu|\le E_\mu:=\operatorname{up}_{640}
\bigl[\kappa(\epsilon_uN_{\rm cap}+P_{\rm up}\epsilon_b)\bigr].}
$$

This uses the independent principal-proxy norm cap for the same fixed
source. A future SAME-source interval $I_\mu$ would have to satisfy the
sufficient directed test

$$
\operatorname{up}\bigl(C_{\rm lin}+2(I_\mu+E_\mu)\bigr)<0.
$$

The corresponding exact arithmetic threshold is
$\sup I_\mu<-C_{\rm lin}/2-E_\mu$. Supplying a priced threshold alone supplies
no actual signed moment or center sign. The additional PSD good-block
metric remains a separate obligation even after that condition holds.

The sole fixed1024-working/640-export-bit application takes0.28065seconds.
It reads the saved112-by18 features once and consumes18 diagonal
lift-norm entries. Its directed scalar results are:

| Quantity | Approximate directed value |
|---|---:|
| Diagonal triangle bound $L_V$ |$4.487671887147054866\cdot10^{67}$|
| Inherited complete allowance |$2.077324851584678042\cdot10^{-135}$|
| Jet forward error $\epsilon_b$ |2.892599471220086626|
| Same-source proxy error $\epsilon_u$ |0.478756042962487477|
| Signed-functional error $E_\mu$ |21.968771391420024702|
| Unchanged exact direction norm upper |29.098313589424940590|
| Unchanged $C_{\rm lin}$ |25.528336100647874028|
| Sufficient proxy threshold $-C_{\rm lin}/2-E_\mu$ |−34.732939441743961716|

All thresholds use the saved exact rationals; the displayed decimals
are approximate. The112 exported coefficient intervals have maximum
absolute endpoint approximately1038.04984493700085 and maximum absolute
width approximately$5.11418\cdot10^{-25}$. These are enclosures of the
ONE shared direction, not independently selectable coefficients.

The small original operator allowance does not itself establish a small
vector error: it must be multiplied by the direction's lift-norm bound.
The resulting error payment is finite, and the missing signed supplier
now has an explicit numerical obligation. No value or sign of $\mu$ or
$\vartheta$ is supplied. In particular this threshold does not establish
a negative center or justify an expensive supplier on nonexclusion alone.

The packet SHA256 is
`154949d8ab3e1f2875de531aa63a9c5a3c3d7d133640a5ce8b1d23c98d67565a`.
The [source and directed data](https://github.com/the-omega-institute/trureturing-experiments/tree/d649640d58161392ae8382a4e64662b9165ec944/docs/reports/weil-c27)
are a source-specific application of the existing geometric-jet,
triangle and Cauchy bounds. All earlier producers, passed suites,
reference/Gram/trace/inverse/solve and source/far suppliers are reused.
The adapter guards its current source and inherited inputs, helpers and
producers at entry and exit, and writes one exclusive fresh archive.
There is no source, parameter or precision scan, new generic algorithm
or Lean theorem. Actual-form/domain, full physical support, common
source/short/lift, original weight, genuine symbol and component-bound
conditions remain inherited. Actual signed response, good-block metric,
full-border sign, retained/cofinal positivity, Robin tail and RH remain
unresolved.

### Enclose the same-source signed proxy with an Abel tail allowance

The saved forward interface reduces the missing signed response to
$\mu=\kappa\langle u^{(0)},j_h\rangle_{W_F}$. Keep all112 coefficient
intervals for the SAME full56 jet, the original384-bit source and the
original constant far weight $D_F$. Write $n_0=1281$, $M=32768$ and

$$
z_n=\begin{cases}
-(-1)^nq_n,&1281\le n\le2048,\\
(-1)^nw_n,&2049\le n\le M,
\end{cases}
\qquad
S_m=\sum_{n=n_0}^{M}\frac{z_n}{m+n}.
$$

Here $q$ is the saved `D_inverse_difference`, not the other inverse
profile $p$. Put
$A(t)=\sum_{k<56}h_{A_k}t^k$ and
$B(t)=\sum_{k<56}h_{B_k}t^k$. The principal factor $1/2$ and jet
factor $2/\pi$ combine, and their two parity factors cancel:

$$
\boxed{
\mu=\frac{\kappa D_F}{\pi}\sum_{m>M}\frac{S_m}{m}
\left[\frac M m B((M/m)^2)-s_mA((M/m)^2)\right].}
$$

The adjacent finite block $M+1\le m\le2M$ is evaluated with one
existing FLINT polynomial product. With $s=M-n_0+1$, set

$$
Z_{\rm rev}(t)=\sum_{n=n_0}^{M}z_nt^{M-n},\qquad
K(t)=\sum_{a=0}^{M+s-2}\frac{t^a}{M+1+n_0+a}.
$$

Then
$[t^{s-1+i}]Z_{\rm rev}K=S_{M+1+i}$ for $0\le i<M$.
This is a reciprocal-sum kernel, distinct from the already-consumed
signed energy convolution's difference kernel. Its32768 new outputs are saved in an exclusive Cauchy checkpoint
before finite-symbol evaluation. The finite approximate jet outputs
are saved in a second checkpoint before infinite-tail work. The final
interval packet references the two checkpoints by SHA256; it does not
duplicate either array. Existing
FLINT vector polynomial evaluation in its iterative Horner mode
evaluates both full jet polynomials and the saved smooth symbol.
No multiplication or multipoint algorithm is reimplemented.

The original symbol certificate gives

$$
\widehat s_m=C(M/m)-\sum_u a_u\operatorname{Im}(\xi_u^m),
\qquad |s_m-\widehat s_m|\le\sigma.
$$

Reuse all64 coefficients of $C$ and the832-grid uniform error; its
polynomial entries use640-grid units. The seed records exact prime
powers and the number of folded phases, not their coefficient values.
Only the14 elementary prime-power weights and13 folded phases are
initialized, using the existing exact phase-alias function. The
original polynomial producer is not invoked. For each folded rational
phase, use $\tau_u=2\log u/\log27$ and evaluate
$\operatorname{Im}\xi_u^m=\sin(\pi m\tau_u)$ directly with
FLINT real `sin_pi`, retaining its full angle/weight uncertainty.
This avoids rectangular-interval wrapping across a long rotation
recurrence; the exact signed Fourier samples are unchanged.

Only the separated tail $m\ge T:=2M+1$ uses the source expansion

$$
a_r(x)=\sum_{\ell<r}d_\ell x^\ell,
\qquad d_\ell=\sum_nz_n(-n/M)^\ell,
\qquad S_m\simeq m^{-1}a_r(M/m).
$$

The cached unweighted principal terms from the original primal
estimate equal $\|w\|_1/(2\sqrt M)$ and
$\|q\|_1/(2\sqrt M)$. Their upward sum, multiplied by $2\sqrt M$,
therefore supplies $Z\ge\sum_n|z_n|$ without another source norm scan.
The exact reciprocal remainder and an integral from $T-1=2M$ give

$$
\left|\frac1{m+n}-\frac1m\sum_{\ell<r}(-n/m)^\ell\right|
=\frac{(n/m)^r}{m(1+n/m)},
\qquad
\delta_r:=\operatorname{up}_{640}
\frac{\sqrt{D_F}Z\,2^{-r}}{2\sqrt{(2r+1)2M}}.
$$

Thus $\|u^{(0)}-\widetilde u^{(0)}\|_{W_F}\le\delta_r$ when
$\widetilde u^{(0)}$ agrees with the true principal source on the
finite block and uses this approximation only on the tail. The
factor $1/2$ is already included in $\delta_r$. The order is chosen
once by an exact bit-length upper bound, with the prescribed scalar
geometric budget $\eta=1/64$, to ensure
$\kappa J_{\rm cap}\delta_r\le\eta$;
$J_{\rm cap}=N_{\rm cap}+\epsilon_b$ bounds the actual full jet.
There is no order, cutoff, source or precision scan.

Contract the short polynomials before evaluating any infinite kernels:

$$
F_0(x)=a_r(x)\left[xB(x^2)-C(x)A(x^2)\right],
\qquad F_1(x)=a_r(x)A(x^2).
$$

For the smooth contribution, reuse FLINT's real Hurwitz implementation:

$$
K_q(T,1)=M^{q-1}\zeta(q,T),\qquad q\ge2,
\qquad
\widehat\mu_{\rm smooth}=\frac{\kappa D_F}{\pi M}
\sum_p(F_0)_pK_{p+2}(T,1).
$$

The normalization remains $M=32768$, with endpoint $T=65537$.
Every order is at least2. The existing sparse moments at endpoint
$M+1$ are not a complete dense bank at $T$; this application records
its new real kernel intervals for reuse.

No complex infinite phase kernel is needed. For an exact unit phase
$\xi\ne1$, the geometric partial sums have modulus at most
$2/|1-\xi|$. Abel summation with decreasing positive $m^{-q}$ gives

$$
\left|\sum_{m\ge T}\frac{\xi^m}{m^q}\right|
\le\frac{2}{|1-\xi|T^q},\qquad
|K_q(T,\xi)|\le\frac{2M^{q-1}}{|1-\xi|T^q}.
$$

For each exact folded phase, the interval computation certifies a
strictly positive lower bound for $|1-\xi_u|$. Omitting the
oscillatory part of the SAME approximate-source tail costs at most

$$
\boxed{
R_{\rm osc}=\operatorname{up}_{640}\left[
\frac{2\kappa D_F}{\pi T^2}
\left(\sum_p |(F_1)_p|_{\rm up}(M/T)^p\right)
\left(\sum_u\frac{|a_u|_{\rm up}}{|1-\xi_u|_{\rm lo}}\right)
\right].}
$$

This applies to $F_1=a_rA(x^2)$, not to a separately optimized source.
The source and symbol telescope below therefore retains its original
terms. Coefficient intervals crossing zero are retained throughout;
only a provably exact zero may be discarded. These are standard
geometric-sum and Abel estimates, not a new tail algorithm or theorem.

With $\rho_0=M/(M+1)$, the global symbol payment is

$$
\beta_s=\operatorname{up}_{640}
\frac{2\sqrt{D_F}\sigma}{\pi\sqrt M}
\sum_{k<56}|h_{A_k}|_{\rm up}\rho_0^{2k},
\qquad \|j_h-\widehat j_h\|_{W_F}\le\beta_s.
$$

The SAME independent principal cap gives
$\|\widetilde u^{(0)}\|_{W_F}\le P_{\rm up}+\delta_r$.
Pair the source error with the actual jet and the symbol error with
the approximate source. This gives the complete analytic allowance

$$
\boxed{
R_\mu=\operatorname{up}_{640}\left[
\kappa\left(J_{\rm cap}\delta_r+(P_{\rm up}+\delta_r)\beta_s\right)
\right].}
$$

If $I_{\rm alg}$ encloses the finite block plus smooth tail with
all input intervals and arithmetic rounding, then
$\mu\in I_{\rm alg}+[-(R_\mu+R_{\rm osc}),R_\mu+R_{\rm osc}]$ and
$\vartheta\in I_{\rm alg}+[-(R_\mu+R_{\rm osc}+E_\mu),R_\mu+R_{\rm osc}+E_\mu]$.
The existing sufficient test before the additional PSD good-block
metric is

$$
\operatorname{up}\left(C_{\rm lin}
+2(I_{\rm alg}+R_\mu+R_{\rm osc}+E_\mu)\right)<0.
$$

A negative upper only opens that remaining metric test. A positive
value of this sufficient upper expression does not establish a
positive actual center. All actual-form/domain, same source/short/lift,
genuine symbol, original weight and previous component conditions
remain inherited; this application supplies no generic algorithm or
Lean result and no full-border, cofinal, Robin or RH conclusion.

The saved direct-real-sine/Abel application uses1024 working bits and
640-bit exports and takes6.96478seconds. The fixed order is$r=13$;
there is one new reciprocal-sum convolution,186 real Hurwitz kernels,
13 certified positive phase gaps and425984 direct real sine samples.
The final packet saves both checkpoint references and the new real
kernel intervals. No source/lift, inverse/solve, reference, Gram or
trace producer is regenerated.

| Quantity | Approximate directed result |
|---|---:|
| Finite approximate functional |−2.266706962449528562|
| Smooth tail center |−2.242939503220959819|
| Algorithmic center |−4.509646465670488381|
| Source/symbol allowance $R_\mu$ |0.001800203553588446|
| Omitted oscillatory allowance $R_{\rm osc}$ |0.000869186655284127|
| Complete analytic allowance |0.002669390208872574|
| Exported proxy interval $I_\mu$ |[−4.512315855885066397,−4.506977075455910365]|
| Exported $\vartheta$ interval |[−26.48108725775422862,17.46179432641325185]|
| Exported $C_{\rm lin}+2\vartheta$ interval |[−27.43383853406987275,60.45192487268366729]|

All decimals are approximate. The saved exact640-bit grid intervals
and exact rational allowances supply the tests; Arb radius conversion
adds conservative inflation to the exported intervals. The proxy
interval does not satisfy the unchanged sufficient threshold
$-C_{\rm lin}/2-E_\mu\simeq-34.732939441743961716$.

A stronger boundary for this particular estimate follows without
another source calculation. Exact endpoint arithmetic gives

$$
C_{\rm lin}+2I_\mu>\frac{33}{2}.
$$

The approximate endpoints are16.50370438887774123 and
16.51438194973605330. Therefore
reducing the nonnegative norm-only transfer allowance$E_\mu$, even to
zero, cannot make this principal-proxy sufficient upper test negative.
This is a limitation of that sufficient estimate; it establishes
neither a positive actual center nor a negative Weil test.

Keep the actual signed correction
$\Delta_\vartheta=\vartheta-\mu$ instead. The pre-good-metric test would
follow from a new SAME-source upper bound satisfying

$$
\sup\Delta_\vartheta<
-\frac{C_{\rm lin}}2-\sup I_\mu
\simeq-8.25719097486802665.
$$

The inherited absolute estimate
$|\Delta_\vartheta|\le E_\mu\simeq21.96877$ does not supply this negative
upper. The numerical target is for the full signed correction, not a
separately selectable source or coefficient. The additional PSD
good-block metric remains separate even if that new signed condition
is met. Neither smaller oscillatory-tail payment alone nor a sharper
nonnegative transfer allowance alone closes this proxy's deficit.

The final interval packet SHA256 is
`6475e5f63dba423b2f1ee7e488581f15ef8d53de83a22ea064ac2e393b124d55`.
The Cauchy checkpoint SHA256 is
`dbfedf8f55f74b4fa1659ff02e57559fea52e3250379c8f99ed1807ee91245f9`,
and the finite-jet checkpoint SHA256 is
`43a29c6710cae4b4b7ad2fce9433ebba4ca0bdec9dfea968d668b13d3a469bc8`.
The [source and directed data](https://github.com/the-omega-institute/trureturing-experiments/tree/905f8cf4c9705e32075280ae4c5741f1199a873d/docs/reports/weil-c27)
are retained in the existing experimental packet. This application reuses standard FLINT suppliers, Abel
summation and the prior error contracts; it introduces no generic
algorithm, literature-novelty or Lean claim. All actual-form/domain,
common source/short/lift, original-weight and component premises remain
conditions. Actual-center sign, the good-block metric, full-border
sign, retained/cofinal positivity, Robin tail and RH remain unresolved.

### Recover the signed mixed correction with the saved physical Gram

Keep the SAME original384-bit source, physical residual, retained lift,
direction and original constant far weight $W_F=w_FI$. Put
$E=\{1281,\ldots,2048\}$, $q=D^{-1}(z-b)$ and $p=F^{-1}z$,
using the saved `D_inverse_difference` and `F_inverse_z` profiles,
respectively. Embed $\lambda=q-p$ as $\ell$ on physical modes0 through2048,
with zero entries outside $E$. The original full-Gamma action satisfies

$$
u_F=u^{(0)}+r_{\rm sm}+C_{\rm phys}\ell.
$$

Here $u^{(0)}$ is the already-enclosed principal proxy, and the previous
smooth-remainder certificate supplies
$\|r_{\rm sm}\|_{W_F}\le\epsilon_{\rm sm}$.
For the SAME exact direction write
$t=\mathcal D Vv_R$, $\mathcal D=\binom I{-Y}$,
$\mathsf Bv_R=C_{\rm phys}t$ and $h=P_0t$.
The saved full112-component vector encloses this exact $h$.
Retain the existing upper bounds

$$
\|t\|\le\sqrt{K_{\rm phys}}L_V,\qquad
\|\mathsf Bv_R\|_{W_F}\le N_{\rm cap},\qquad
\|u^{(0)}\|_{W_F}\le P.
$$

The original target already saves the112-by112 kernel
$K_0=\alpha_0w_FH_0$ and the physical operator-error certificate

$$
\|C_{\rm phys}^*W_FC_{\rm phys}-P_0^TK_0P_0\|
\le\epsilon_{\rm far}.
$$

The kernel includes the original fixed-midpoint prefactor and masked
moment core. No PSD assumption on $H_0$ is used. Its masking, moment,
feature and prefactor errors are already covered by the physical
certificate. The target's `far_matrix_error` and
`trial_operator_norm_sq_upper` retain512-bit metadata units; the
kernel arrays use640-bit units. The amplified complete allowance is
not substituted for this physical error.

Set

$$
a=P_0\ell,\qquad
\nu=\kappa\langle C_{\rm phys}\ell,C_{\rm phys}t\rangle_{W_F},
\qquad \nu_0=\kappa a^TK_0h.
$$

Then the operator-error certificate gives

$$
|\nu-\nu_0|\le
\kappa\epsilon_{\rm far}Z_\lambda\sqrt{K_{\rm phys}}L_V,
\qquad Z_\lambda\ge\|\lambda\|_1\ge\|\ell\|.
$$

Only the left features are new. On $E$ they are

$$
a_{A_k}=\sum_{n\in E}(-1)^n\lambda_n(n/M)^{2k},\qquad
a_{B_k}=\sum_{n\in E}(-1)^ns_n^0\lambda_n(n/M)^{2k+1},
$$

where $s_n^0$ is the SAME exact midpoint of the saved scalar interval.
The existing signed source-power reduction supplies both families:
even coefficients of the source $(-1)^n\lambda_n$, and odd coefficients
of $-(-1)^ns_n^0\lambda_n$, because its power ratio is $-n/M$.
The original short jet and kernel are read directly. No new moments,
physical lift, long source, proxy, inverse or far-output samples are needed.

The previous primal producer also supplies a norm bound without another
absolute source reduction. Its `actual_mixed_tail_norm_upper` encloses

$$
\frac{2\sqrt{w_F}B}{\pi\sqrt{M-2048}}\,\|\lambda\|_1,
$$

where the SAME exact symbol budget $B$ is enclosed by its saved
`actual_symbol_budget`. If $B_{\rm lo}>0$ and $H_{\rm mix}$ is the saved
mixed upper, define

$$
c_{\rm lo}\le\frac{2\sqrt{w_F}B_{\rm lo}}{\pi\sqrt{M-2048}},
\qquad
Z_\lambda=\operatorname{up}_{640}(H_{\rm mix}/c_{\rm lo}).
$$

This divides the established bound on the coefficient-times-norm by a
positive coefficient lower bound; it does not invert an operator upper
bound to obtain a norm estimate.

For the remaining proxy-forward error, use the already established
separate forward components directly. With $N_p=2048$, $R=56$,
$M=32768$, $\eta=N_p/M$ and $k_p=1-N_p/(M+1)$, put

$$
r_2=\frac{4B_{\rm up}^2N_p}{\pi^2k_p^2M(4R+1)}\eta^{4R},
\qquad
e_P^2=e_0^2+\rho_s^2\frac{N_p\eta^2}{1-\eta^4},
\qquad \alpha_J=\frac4{\pi^2M}.
$$

Here $e_0$ is half the width of the original saved zero-feature interval.
All2049 physical symbol intervals have width at most one640-bit grid
unit, so the conservative choice $\rho_s=2^{-640}$ covers their
midpoint radii. The saved true full moment norm upper $H_*$ uses628-bit
units and is independent of the physical support size; it is not the
masked kernel's PSD norm. The forward component bounds imply

$$
\epsilon_b^\sharp=
\operatorname{up}_{640}\left[
\sqrt{w_FK_{\rm phys}}
\left(\sqrt{r_2}+\sqrt{\alpha_JH_*}\,e_P\right)L_V\right].
$$

The squared remainder $r_2$ is below the640-bit grid. Its square root is
taken at1024 working bits before640-bit upward rounding; its saved
squared interval uses a separate1024-bit grid.

Finally the SAME-object decomposition is

$$
\vartheta=\mu+\nu
+\kappa\langle r_{\rm sm},\mathsf Bv_R\rangle_{W_F}
+\kappa\langle u^{(0)},\mathsf Bv_R-j_h\rangle_{W_F}.
$$

Consequently the new complete transfer allowance is

$$
R_\vartheta=
\kappa\bigl(\epsilon_{\rm sm}N_{\rm cap}+P\epsilon_b^\sharp\bigr)
+\kappa\epsilon_{\rm far}Z_\lambda\sqrt{K_{\rm phys}}L_V,
\qquad
\vartheta\in I_\mu+\nu_0+[-R_\vartheta,R_\vartheta].
$$

This replaces the earlier norm-only transfer allowance $E_\mu$.
The already-saved $I_\mu$ retains its source, symbol and Abel allowances;
they are not charged again. The unchanged pre-good-metric sufficient
expression is $C_{\rm lin}+2\vartheta$.

The sole fixed1024-working/640-export-bit application completes in
1.30498seconds. It makes two short source-power reductions on768
entries and one112-by112 signed cross. The original inverse profiles,
full jet, Gram kernel, proxy interval, symbols and moment bounds are
reused; no old scientific producer or parameter/source scan is replayed.
The resulting directed values are:

| Quantity | Approximate enclosure or upper |
|---|---:|
| $Z_\lambda$ |18.61447623568004556|
| Signed kernel cross $\nu_0$ |+0.181002566603288306|
| Sharp forward allowance $\epsilon_b^\sharp$ |5.304632297062084e−69|
| Gram cross allowance |1.669239650964427e−66|
| Complete transfer allowance $R_\vartheta$ |4.112478850097329e−11|
| Actual correction $\vartheta-\mu$ |[0.18100256656216351,0.18100256664441310]|
| Actual $\vartheta$ |[−4.331313289332710,−4.325974508801690]|
| Frozen $C_{\rm lin}+2\vartheta$ |[16.865709521960626,16.876387083066322]|

Displayed interval endpoints round outwards. The saved640-bit integer
endpoints and exact rational allowances determine the strict tests.
Reopening the saved proxy interval as an Arb ball introduces
conservative radius inflation, which is also retained in these
exports. The proxy's analytic allowance is unchanged. Its width now
dominates the final interval width; the remaining transfer allowance
is approximately $4.11248\cdot10^{-11}$ and is dominated by the smooth
remainder payment.

Under the inherited certificates, the actual signed correction is
positive. It therefore does not meet the negative correction upper
required by the unchanged sufficient test. Moreover exact saved
endpoint arithmetic gives

$$
C_{\rm lin}+2(I_\mu+I_{\nu_0})>16.86.
$$

This holds even before adding a nonnegative transfer allowance.
Further reduction of that allowance cannot make this fixed sufficient
upper expression negative. This establishes a limitation of the frozen
linear envelope, not positivity of the actual center that it bounds.
A next sufficient estimate must recover additional signed credit or
derive a tighter linear upper with its own justification. The
previous value of $C_{\rm lin}$ and its certificate remain intact.
The additional good-block metric remains a separate obligation.

The packet saves the new112 left features, cross enclosure, fine
1024-bit squared remainder and exact scalar allowances for reuse. Its
SHA256 is
`d527c5217314bdd5b21e0f1080ef17b1e29b880954a1bafe77a711a1102dc6bd`;
the [source and directed data](https://github.com/the-omega-institute/trureturing-experiments/tree/1c83b683b465264fb2dc1e1ccdee28f56087ec4c/docs/reports/weil-c27)
are retained in the existing experimental packet. The separate
forward estimate uses Arb's arbitrary exponent range through the
small squared feature terms, taking square roots before final-grid
rounding. At physical mode0 the geometric remainder is exactly zero:
the original coupling column and exact jet both equal
$-\sqrt2(-1)^ms_m/(\pi m)$. Its midpoint feature error is paid by $e_0$.

This is a source-specific numerical application of the existing
physical Gram and forward component estimates. It supplies no new
generic algorithm, literature novelty or Lean theorem. Actual-form,
domain, common source/short/lift, original-weight and component-bound
premises remain conditions. Actual-center and full-border signs,
retained/cofinal positivity, Robin tail and RH remain unresolved.


### Test all steering coefficients before a new signed supplier

Keep the SAME source, old core, lift, far row $f$, frozen positive
fee $D_*$ and legal coefficient $t_0$. Only the real coefficient
$\alpha$ in $y(\alpha)=\alpha\rho+\beta_J$ varies. The common source
and its effective far action stay fixed as this row coefficient varies;
no new dual source is selected.
Define the fixed-fee comparison expression

$$
\mathcal E_*(\alpha)=\frac{\alpha^2}{t_0}+D_*
+(y(\alpha)+f)Q_{\rm true}(y(\alpha)+f)^*,
\qquad
Q_{\rm true}=TS^{-1}T^*-\frac{e_0e_0^*}{\delta}.
$$

This is a sufficient comparison family with its specified frozen fee.
A lower bound for it is not a lower bound for an actual center using a
smaller charge. The existing proof route needs a negative comparison;
a positive floor would exclude this recipe for every real $\alpha$,
without determining the sign of the actual full border. The algebraic
family is defined for all real coefficients; this does not assert that
every coefficient is an admissible physical test. Any legal subset
with the same fixed data is covered by an all-real exclusion.

Let $\alpha_0$ be the saved dyadic steering origin and
$y_0=\alpha_0\rho+\beta_J$. All the following quantities already have
saved enclosures for the SAME exact reference:

$$
\begin{aligned}
Q_R&=TRT^*-e_0e_0^*/\delta,&
\vartheta_0&=fQ_Ry_0^*,\\
r_0&=y_0TRT^*y_0^*,&
r_\rho&=\rho TRT^*\rho^*,\\
h_{11}&=t_0^{-1}+\rho Q_R\rho^*,&
h_{12}&=\rho Q_R\beta_J^*.
\end{aligned}
$$

The new signed-correction packet supplies $\vartheta_0$; the finite
steering packet supplies the remaining coefficients. Retain its
$|f_0|\le C_-$, $\delta\ge\delta_{\rm lo}>0$, and the coherent
packet's $fTRT^*f^*\le A$. No new direction, matrix action, norm
reduction, source, inverse or far sample is needed.

The exact curvature identity gives

$$
\frac{\rho_0^2}{\delta}=t_0^{-1}+r_\rho-h_{11}.
$$

Thus one may use upward bounds

$$
N_\rho=\operatorname{up}
(t_0^{-1}+r_{\rho,\rm up}-h_{11,\rm lo}),
\qquad
F_- =\operatorname{up}(C_-^2/\delta_{\rm lo}).
$$

Cauchy on the positive reference form and the scalar negative channel
then supply the previously unevaluated derivative's capacity:

$$
\left|fQ_R\rho^*\right|
\le\Phi:=\operatorname{up}
\left(\sqrt{A r_{\rho,\rm up}}+\sqrt{F_-N_\rho}\right).
$$

This is a uniform bound for one common realization. Separate maxima
are not asserted to be jointly attainable. Put

$$
d_0=h_{11}\alpha_0+h_{12},\qquad
B=\operatorname{up}(|d_0|_{\rm up}+\Phi).
$$

Enclose the finite reference value directly from saved scalar data:

$$
q_0=\frac{\alpha_0^2}{t_0}+D_*+r_0-\frac{(y_0)_0^2}{\delta}.
$$

In particular, a finite lower is not obtained by subtracting upper
allowances from $C_{\rm lin}$. The old inverse comparison yields

$$
Q_{\rm true}\succeq Q_R-\epsilon_-TRT^*,
\qquad \epsilon_- =\frac{\eta}{1+\eta}.
$$

For every real $s=\alpha-\alpha_0$, the positive-form triangle bound gives

$$
\|(y_0+s\rho+f)T\|_R^2
\le4r_{0,\rm up}+4s^2r_{\rho,\rm up}+2A.
$$

Expanding the reference quadratic and retaining
$fQ_Rf^*\ge-F_-$ therefore gives

$$
\mathcal E_*(\alpha_0+s)\ge K+Hs^2-2B|s|,
$$

where downward $K,H$ may be chosen as

$$
\begin{aligned}
K&=q_{0,\rm lo}+2\vartheta_{0,\rm lo}-F_-
-\operatorname{up}\bigl[\epsilon_-(4r_{0,\rm up}+2A)\bigr],\\
H&=h_{11,\rm lo}
-\operatorname{up}(4\epsilon_-r_{\rho,\rm up}).
\end{aligned}
$$

If $H>0$, scalar square completion covers all real coefficients:

$$
\boxed{\mathcal E_*(\alpha)\ge K-\operatorname{up}(B^2/H)
\quad\text{for every }\alpha\in\mathbb R.}
$$

The calculation tests the maximum possible gain before supplying the
actual derivative. A nonpositive lower leaves this capacity test
unsettled; it supplies neither a realizable favorable derivative nor
a negative comparison. A positive lower excludes this fixed-fee and
fixed-$t_0$ family. A smaller justified fee, another legal coefficient,
source or comparison is a different recipe.


The fixed1024-working/640-export-bit scalar application uses three
accepted packets and finishes in0.61818seconds, including serialization.
Its60 source/input byte bindings agree at entry and prewrite. There
are no new source, matrix, norm, feature, derivative or tail calls and
no replay of an old scientific producer. The source applies existing
Schur comparison, Cauchy and scalar square completion; no new generic
theorem, algorithm, literature novelty or Lean proof is claimed.

| Quantity | Approximate directed value |
|---|---:|
| Finite reference value $q_0$ |[21.62931038112412885233753,21.62931038112412885233755]|
| Negative-channel credit cap $F_-$ |2.327429771347697837|
| Signed derivative capacity $\Phi$ |515.620424366832531834|
| Comparison curvature lower $H$ |25136.371399957733363764|
| Comparison base lower $K$ |10.639254031103735470|
| Maximal steering gain upper |10.576881515391657423|
| All-real comparison floor lower |0.062372515712078048|

The displayed upper/lower quantities round in the indicated direction;
the saved640-bit integer endpoints and exact rational allowances are
authoritative. In particular, the final lower endpoint is strictly
larger than0.062372515712078048. Hence

$$
\mathcal E_*(\alpha)>0.062372515712078048
\quad\text{for every real }\alpha,
$$

under the inherited common-object and inverse/component certificates.
The unchanged fee and $t_0$ comparison recipe cannot become negative
by changing $\alpha$, even with the most favorable derivative allowed
by these norm caps. Supplying its actual derivative is unnecessary
for this excluded recipe. This does not exclude negativity of an
actual center with a smaller justified fee or another comparison.

At the fixed $\alpha_0$, the separate class of self-term-only
refinements also has a positive floor. With $\vartheta_0$ and all
other frozen terms retained, even removing the positive far-energy
charge $A$, deleting the old nonnegative comparison allowance
$\Delta$, and returning the entire allowed negative square gives

$$
C_{\rm lin}+2\vartheta_{0,\rm lo}-A-\Delta-F_-
>10.639254031103735470.
$$

This diagnostic bounds refinements of that frozen upper expression;
it is not an actual-center lower bound.

The [scalar source and packet](https://github.com/the-omega-institute/trureturing-experiments/tree/673dff6646fb1f41721bb8c891e54c6fca17199f/docs/reports/weil-c27)
retain the exact result under SHA256
`85a52adf97e96def95aaf5abaa307338522a2bae5d7b40c96692ad0366a444fe`.
The source SHA256 is
`dcdb47a55003e4ca745bf33ce81133fd65577facdf6004d38308fb9f1dddc96e`.
All inherited actual-form, domain, common-source/short/lift, weight and
component assumptions remain. The next useful gap must change a
justified fee, coefficient, source or comparison and retain a common
realization; a sharper estimate inside the excluded fixed recipe
cannot supply its missing negative comparison. The good-block metric,
actual-center/full-border signs, retained/cofinal positivity, Robin
tail and RH remain unresolved.


### Reprice the same source from its saved mixed-H features

The actual far source and its physical weight remain fixed. Its
accepted decomposition is

$$
u_F=u^{(0)}+r_{\rm sm}+C_{\rm phys}\ell,\qquad
\|u^{(0)}\|_{W_F}\le P,\quad
\|r_{\rm sm}\|_{W_F}\le\epsilon_{\rm sm}.
$$

The existing signed-correction packet saves $a=P_0\ell$ and a
source norm cap $Z_\lambda\ge\|\ell\|$. Its original physical target
contains $K_0$ and

$$
\|C_{\rm phys}^*W_FC_{\rm phys}-P_0^TK_0P_0\|
\le\epsilon_{\rm far}.
$$

Therefore a single new quadratic suffices:

$$
\|C_{\rm phys}\ell\|_{W_F}^2
\le a^TK_0a+\epsilon_{\rm far}Z_\lambda^2.
$$

This uses the original weighted physical error in512-bit metadata
units; the saved feature and kernel arrays use640-bit units. The
kernel need not be PSD. No source, feature, moment, Gram or inverse
supplier is repeated. With upward rounding define

$$
H_{\rm new}=
\operatorname{up}\sqrt{\operatorname{up}(a^TK_0a)
+\operatorname{up}(\epsilon_{\rm far}Z_\lambda^2)},\qquad
E_{\rm new}=\min\left\{E_{\rm old},
\operatorname{up}\bigl((P+\epsilon_{\rm sm}+H_{\rm new})^2\bigr)\right\}.
$$

All norm cross terms remain in the square. The same actual source
then satisfies $\|u_F\|_{W_F}^2\le E_{\rm new}$.

One energy cap must enter both the fee and eligibility budget.
Reuse the independent charge constant upper $K_{0,\rm up}$ from
the original charge identity. Do not obtain it by subtracting a
far-energy upper from an unrelated fee upper. With $\kappa=33/32$,

$$
D_{\rm new}=K_{0,\rm up}+\kappa E_{\rm new}>0.
$$

For the SAME reflected potential and Bessel certificate, reuse
$a_{1,\rm up}, B_{\rm band}^2,m_{\max}$ and $W_F=w_FI$:

$$
p_{\rm new}=\operatorname{up}
\left(a_{1,\rm up}
+2\sqrt{\frac{E_{\rm new}}{w_F}B_{\rm band}^2}
+m_{\max}\frac{E_{\rm new}}{w_F}\right),\qquad
\tau_{\rm new}=\frac{h_{\rm lo}}{h_{\rm lo}+p_{\rm new}},\qquad
t_{\rm new}=\frac{\tau_{\rm new}}{h_{\rm hi}}.
$$

The lower endpoint supplies the numerator in the eligibility cap;
the upper endpoint supplies the denominator defining the legal
coefficient. These directions are retained even if the displayed
values of $h_{\rm lo},h_{\rm hi}$ coincide.

Changing $t$ changes the reference steering curvature as well as
the finite value. Keep the original source, rows, lift, $R,T$ and
$Q_R$ fixed. Then

$$
h_{11,\rm new}=h_{11,\rm old}+t_{\rm new}^{-1}-t_{\rm old}^{-1},
\qquad h_{12,\rm new}=h_{12,\rm old}.
$$

The same $y_0=\alpha_0\rho+\beta_J$, $r_0,r_\rho,\lambda_0,\delta$
and previously supplied $\vartheta_0=fQ_Ry_0^*$ remain unchanged.
The old all-real comparison exclusion concerns its specified old
fee and coefficient; it is not an exclusion for this repriced family.

The original positive and negative Cauchy bounds are homogeneous
in the common source energy cap. Hence one may use

$$
A_{\rm new}=\operatorname{up}\left(A_{\rm old}
\frac{E_{\rm new}}{E_{\rm old}}\right),\qquad
C_{-,\rm new}=\operatorname{up}\left(C_{-,\rm old}
\sqrt{\frac{E_{\rm new}}{E_{\rm old}}}\right).
$$

No favorable component endpoints are asserted jointly attainable.
For the fixed saved coefficient $\alpha_0$ directly enclose

$$
q_{\rm new}=\frac{\alpha_0^2}{t_{\rm new}}+D_{\rm new}
+r_0-\frac{\lambda_0^2}{\delta},\qquad
\Delta_{\rm new}=\operatorname{up}
\left[\frac{\eta}{1-\eta}
\left(\sqrt{r_{0,\rm up}}+\sqrt{A_{\rm new}}\right)^2\right].
$$

A new sufficient upper before the additional good-block metric is

$$
C_{\rm lin,new}=
\operatorname{up}(q_{\rm new,up}+A_{\rm new}+\Delta_{\rm new}),
\qquad C_{\rm lin,new}+2\vartheta_0.
$$

The negative far self-square has been dropped in this upper.
The existing all-real scalar capacity formula also applies, with
$h_{11,\rm new},t_{\rm new},D_{\rm new},A_{\rm new},C_{-,\rm new}$.
In particular its slope uses the shifted curvature, rather than
the old nearly stationary finite derivative.

A positive sufficient upper or a nonpositive lower capacity
does not determine an actual-center sign or furnish a favorable
actual derivative. A negative upper would still leave the
good-block metric and full-border/cofinal obligations to be paid.
The fee remains an upper defining this comparison, never a lower
bound on an actual smaller charge. This is one common-source
energy enclosure and linked application, not a certificate for
an independently optimized continuum of energy bounds.

This is a numerical application of the existing physical Gram operator
error, triangle inequality, source-charge identity, Bessel budget and
Schur/Cauchy estimates. It supplies no new generic theorem, algorithm,
literature novelty or Lean proof. All inherited actual-form/domain,
common-source/short/lift, original weight and component premises remain.
Actual-center/full-border signs, the good-block metric, retained/cofinal
positivity, Robin tail and RH remain unresolved.

The single fixed1024-working/640-export-bit application finishes in
0.55967seconds including serialization. It makes one112-by112
mixed quadratic from saved arrays. Its62 source/input bindings agree
at entry and prewrite; no source, feature, inverse, reference, trace,
Gram, signed-response or tail supplier is replayed.

| Quantity | Previous value | Repriced value |
|---|---:|---:|
| Weighted mixed-H norm upper |0.478756042961117000|0.052637674256435558|
| Weighted far-energy upper |9.164839739390695|6.766398882441490|
| Positive source-valid fee |178.644404880862231|176.171012747133362|
| Sufficient eligibility cap |0.035871186206647585|0.042365798558350576|
| Legal coefficient |0.000033349857564549898|0.000039387973940699242|
| Fixed-point sufficient expression |[16.865709521960626,16.876387083066322]|[6.738778327421815964,6.749455888527510587]|

The displayed energy/norm/fee quantities round upward and legal
caps/coefficients downward; the interval endpoints round outward.
Saved640-bit integer endpoints and exact rational parameters are
authoritative. The mixed Gram quadratic is approximately
0.00277072475112661857, and the paid physical error upper is
approximately$6.26272\cdot10^{-133}$. No extra$\kappa$ or far weight
is inserted into that already weighted mixed norm.

At the retained$\alpha_0$, the new reference finite value is
approximately12.52275519466849333. The finite derivative is now
approximately$-174.6152875359602151$, and the adjusted comparison
curvature lower is approximately20539.69581714781024. These are
changes in the legal-coefficient contribution, not a newly supplied
far derivative. The previously near-stationary finite coefficient
must not be treated as stationary in the new recipe.

The same all-real capacity estimate now gives a lower floor near
$-16.43212445437972714$. It therefore does not exclude the repriced
family. This is not a favorable derivative or negative comparison
certificate: the fixed-point sufficient upper still has positive
upper endpoint6.749455888527510587. At this fixed coefficient, even
the separate self-term-only refinement class has a positive floor
above2.141787799175894749. That diagnostic concerns refinements of
the specified frozen upper expression, not an actual-center lower.

The useful new information is the tighter shared energy cap and its
joint effect on fee and eligibility. The next signed quantity for
steering is$fQ_R\rho^*$, with the shifted finite slope above. Before
supplying a new long pairing, the saved full physical Gram and known
$\vartheta_0$ can be used to assess its conditional capacity; that
additional capacity has not been computed here. Repeating the old
source, mixed norm or signed$\vartheta_0$ suppliers is unnecessary.

The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/a24e55cb1c5686534d786330e0a8bdd7a8801975/docs/reports/weil-c27)
retain packet SHA256
`66360516946c571c187b5a4eb35aeed1487eef9eff28bee26d5f8fb3211f1a59`
and source SHA256
`92d38517ef0e724cc819ae26e934f492273d93a2a8634c89b573f98c3154b518`.
The saved old recipe and its exclusion remain intact. All actual-form,
domain, source/short/lift, weight, homogeneous-cap and component
premises remain conditions; actual-center/full-border signs,
good-block payment, retained/cofinal positivity, Robin and RH are
unresolved.

### Couple the saved signed response through the single negative direction

The independent derivative and self-term caps do not preserve all relations
already present in the saved signed response. Reuse the classical
negative-index-one Schur estimate on the SAME reference row instead.
Keep the actual source, old core, lift, rows, reference inverse and signed
response fixed. Set

$$
P=TRT^*\succeq0,\quad Q_R=P-\frac{e_0e_0^*}{\delta},\quad
\varepsilon=\frac{\eta}{1+\eta},\quad
Q_\varepsilon=(1-\varepsilon)P-\frac{e_0e_0^*}{\delta}
\preceq Q_{\rm true}.
$$

Here the chosen $\eta$ is the already certified upper bound. The inverse
comparison and common-form/domain interfaces remain hypotheses. For
$y_0=\alpha_0\rho+\beta_J$, use the saved full intervals for

$$
q_0=\frac{\alpha_0^2}{t_{\rm old}}+D_{\rm old}+y_0Q_Ry_0^*,\quad
r_0=y_0Py_0^*,\quad r_\rho=\rho P\rho^*,\quad
\vartheta_0=fQ_Ry_0^*,\quad
d_0=h_{11,\rm old}\alpha_0+h_{12,\rm old}.
$$

In particular $d_0=\alpha_0/t_{\rm old}+\rho Q_Ry_0^*$. The three
joint quantities needed below obey

$$
\begin{aligned}
b&=-y_0Q_\varepsilon y_0^*
=D_{\rm old}+\alpha_0^2/t_{\rm old}-q_0+\varepsilon r_0,\\
g&=\rho Q_\varepsilon y_0^*
=d_0-\alpha_0/t_{\rm old}-\varepsilon\rho Py_0^*,\\
c&=(\beta_J+f)Q_\varepsilon y_0^*
=q_0-D_{\rm old}+\vartheta_0-\alpha_0d_0
-\varepsilon(\beta_J+f)Py_0^*.
\end{aligned}
$$

These identities retain the cancellations before interval enclosure. A
lower bound on $b$ uses the upper endpoint of $q_0$; its previously
available lower endpoint alone would not suffice. Freeze the far-row
seminorm bound at the accepted new energy UPPER,

$$
fPf^*\le A_*,\qquad A_*=A_{\rm new,up}.
$$

With $R_*=\sqrt{r_{\rho,\rm up}r_{0,\rm up}}$, outward bounds are

$$
\begin{aligned}
0<B&\le b,\\
G&\ge|d_0-\alpha_0/t_{\rm old}|+\varepsilon R_*,\\
M&\ge|q_0-D_{\rm old}+\vartheta_0-\alpha_0d_0|\\
 &\quad+\varepsilon\left(r_{0,\rm up}+|\alpha_0|R_*
 +\sqrt{A_*r_{0,\rm up}}\right).
\end{aligned}
$$

$Q_\varepsilon$ has at most one negative direction. When $b>0$, its
orthogonal complement to $y_0$ is nonnegative; completing along $y_0$
gives $xQ_\varepsilon x^*\ge-|xQ_\varepsilon y_0^*|^2/b$. This standard
inertia/Schur argument also allows a singular positive part $P$.
Consequently the SAME paid comparison satisfies, for every real $\alpha$,

$$
\mathcal E_{D,k}(\alpha)
=k\alpha^2+D+(\alpha\rho+\beta_J+f)Q_{\rm true}
 (\alpha\rho+\beta_J+f)^*
\ge k\alpha^2+D-\frac{(G|\alpha|+M)^2}{B}.
$$

If $L=Bk-G^2>0$, ordinary square completion gives

$$
\mathcal E_{D,k}(\alpha)\ge D-\frac{kM^2}{Bk-G^2}.
$$

A positive floor excludes a negative value of this paid comparison for
all real steering coefficients, including any legal subset. It is not
a lower bound for a center whose actual charge is smaller than $D$.
A nonpositive floor or denominator supplies no sign conclusion.

#### Cover the fixed source-energy-only pricing rule

The saved signed Hankel cross lower can supply an actual energy lower
without a new Hankel calculation. The exact omitted principal diagonal
is nonnegative, and its weighted normalization is $w_F/4$. Thus

$$
E_{\rm true}=\|u_F\|_{W_F}^2\ge E_H
=\left[\sqrt{\max\{w_F\operatorname{cross}_{\rm lo}/4,0\}}
-\epsilon_{\rm sm,up}-H_{\rm new,up}\right]_+^2.
$$

The right side is rounded downward. Its principal, smooth and mixed terms
must use the same source and weighted norm. $E_H$ remains a LOWER bound;
it never replaces the fixed far-row UPPER $A_*$ in $G,M$.

Fix the independent charge upper, original Bessel coefficients and $h$
endpoints. For an energy-upper parameter $E\ge E_{\rm true}$, the pricing
rule is

$$
D(E)=K_{\rm const,up}+\kappa E,\qquad
k(E)=h_{\rm hi}\left(1+\frac{p_{\rm up}(E)}{h_{\rm lo}}\right),
$$

where $p_{\rm up}$ is the upward-rounded original complete budget
$a_{1,\rm up}+2\sqrt{(E/w_F)b_{2,\rm up}}+m_{\max}E/w_F$.
Both functions are nondecreasing. Evaluate the unrounded budget at $E_H$
and round the resulting reciprocal coefficient DOWN to $k_{\min}$;
then $k(E)\ge k_{\min}$. Also set
$D_{\min}=K_{\rm const,up}+\kappa E_H$.

For $Bk-G^2>0$, $k/(Bk-G^2)$ is nonincreasing in $k$. Hence

$$
Bk_{\min}-G^2>0,\qquad
D_{\min}-\frac{k_{\min}M^2}{Bk_{\min}-G^2}>0
$$

would exclude all real-$\alpha$ comparisons obtained only by further
improving the source-energy cap in this fixed pricing rule. This family
keeps the actual far row and $A_*$ fixed; it does not cover better
independent charge terms, different Bessel estimates, sources or lifts.
The formal lower endpoint need not itself be a legal source energy cap.

This is a saved-data application of classical matrix inertia, Schur
complements, seminorm Cauchy bounds, reverse triangle inequality and
scalar square completion. It introduces no new generic theorem,
algorithm, literature novelty or Lean proof. The actual-center sign,
good-block payment, full-border/cofinal positivity, Robin and RH remain
unresolved under the inherited premises.

The single fixed1024-working/640-export application uses no new matrix,
norm, source, feature, derivative, signed-response, inverse, trace or
tail supplier. Its64 source/input bindings agree at entry and prewrite;
18 scalar intervals and14 exact rationals are retained. Stored assembly
time is0.15059seconds; total time including serialization is0.18470seconds.

| Bound or comparison | Directed value |
|---|---:|
| Timelike lower $B$ |>200.284690047319663558|
| Pairing upper $G$ |<1139.054295521911259039|
| Pairing upper $M$ |<161.346407789081724764|
| Source-energy lower $E_H$ |>6.227486948459329823|
| Fixed repriced rank denominator |>3787475.149285169293|
| Fixed repriced all-real floor |>1.667100663167811801|
| Energy-endpoint rank denominator |>3579664.592067604194|
| Energy-endpoint all-real floor |>-1.473501281813134057|

The current repriced fee/coefficient comparison is therefore strictly
positive for EVERY real steering coefficient under its inherited
interfaces. Computing a favorable derivative cannot make that specified
paid comparison negative. This strengthens the preceding independent-cap
test, whose negative lower floor left the same family unexcluded.
It still supplies no lower bound for an actual smaller-fee center.

The energy endpoint has a positive rank denominator, but its saved floor
is negative. The sufficient endpoint test therefore does NOT exclude the
whole fixed-budget energy-cap-only family. That negative lower bound is
neither a realizable negative value nor a negative upper. The accepted
actual energy now lies between the certified lower6.227486948459329823
and upper6.766398882441490; a sharper SAME-source energy enclosure or a
change to another charge/budget component can escape the scope of the
fixed-recipe exclusion. No such escape or successful negative recipe is
certified here. In particular independent triangle bounds do not supply
the signed principal/mixed correlation needed to sharpen that enclosure.

The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/27f0bf5ec9560f7d34aab6eabddc598644a97dd8/docs/reports/weil-c27)
retain packet SHA256
`a7df6338b629e9dd791ac2914c8efc7f3ef3c69c20e562da0aa18067aa40728d`
and source SHA256
`9c84ee8891ccc7d9af9aeaa79b162e3c0854bf714badd9366607890aa8e345c3`.
The exact packet endpoints and rational comparisons are authoritative.
The two scalar applications use one common realization and frozen far-row
upper; they are not a parameter scan. The actual good-block metric,
full-border/cofinal positivity, Robin and RH remain unresolved. No Lean
verification or new generic theorem is claimed.

### Retain two saved projections in the source-energy estimate

The physical mixed correction and principal proxy already have signed
projections on the SAME saved direction. Consume these projections before
requesting another principal/mixed pairing. The estimate is the classical
three-vector Gram inequality, as recorded in Dragomir,
[*Improving Schwarz Inequality in Inner Product Spaces*](https://arxiv.org/abs/1709.02029v1),
equation (1.5), applied through its Schur-complement form. It is not a new
generic inequality or algorithm.

Use the original real weighted Hilbert space with $W_F=w_FI$ and write

$$
u_F=v+r+c,\qquad c=C_{\rm phys}\ell,\qquad
b=C_{\rm phys}t,\qquad t=\mathcal D Vv_R,\qquad h=P_0t.
$$

All of these are the SAME source, lift and direction as in the signed
mixed-correction section. Let $\|r\|_{W_F}\le\epsilon_{\rm sm}$.
The saved signed proxy encloses $\mu=\kappa\langle v,j_h\rangle_{W_F}$.
The saved sharp forward and physical mixed-cross allowances give

$$
\begin{aligned}
s:=\langle v,b\rangle_{W_F}
&\in I_\mu/\kappa+[-R_{\rm forward}/\kappa,R_{\rm forward}/\kappa],\\
z:=\langle c,b\rangle_{W_F}
&\in I_{\nu_0}/\kappa+[-R_{\rm mixed}/\kappa,R_{\rm mixed}/\kappa].
\end{aligned}
$$

Here $R_{\rm forward}=\kappa P\epsilon_b^\sharp$ and
$R_{\rm mixed}=\kappa\epsilon_{\rm far}Z_\lambda\sqrt{K_{\rm phys}}L_V$
are reused separately. The smooth remainder is not part of $z$.
The proxy's already paid source, symbol and Abel allowances are retained.

Only one numerical supplier is missing: the norm of this common direction.
The existing physical certificate, $h=P_0t$ and
$\|t\|\le\sqrt{K_{\rm phys}}L_V$ supply

$$
\|b\|_{W_F}^2
\le h^TK_0h+\epsilon_{\rm far}K_{\rm phys}L_V^2.
$$

Evaluate one112-component feature quadratic and take the minimum of its
outward upper and the old $N_{\rm cap}^2$. The kernel already includes the
original far weight; neither another $w_F$ nor $\kappa$ is inserted.
Its arrays use640-bit units, while the original physical error and
$K_{\rm phys}$ metadata use512-bit units. No PSD property of $K_0$ is
required. This computation preserves the shared short features instead
of reopening the broadly enclosed eighteen-channel quadratic.

Let $N^2\ge\|b\|_{W_F}^2$ denote the resulting cap. For $N>0$, the
Schur-complement inequality is

$$
\left|\langle v,c\rangle_{W_F}-\frac{sz}{N^2}\right|
\le
\sqrt{\left(\|v\|_{W_F}^2-\frac{s^2}{N^2}\right)
       \left(\|c\|_{W_F}^2-\frac{z^2}{N^2}\right)}.
$$

A norm UPPER is sufficient: increasing the bottom diagonal of the true
three-vector Gram to $N^2$ preserves positive semidefiniteness. No norm
lower or equality with the true norm is assumed.

Use the already saved principal squared-norm lower
$P^2_{\rm lo}=\max\{w_F\operatorname{cross}_{\rm lo}/4,0\}$ and upper
$P^2_{\rm up}$, and the mixed-energy bounds $C^2_{\rm lo},C^2_{\rm up}$.
The mixed lower is the saved physical quadratic lower minus its paid
error, truncated at zero. Let $s_*,z_*$ be lower bounds on the absolute
values of the two signed projections. Outward interval evaluation gives

$$
R=\sqrt{\left(P^2_{\rm up}-s_*^2/N^2\right)
          \left(C^2_{\rm up}-z_*^2/N^2\right)},\qquad
\langle v,c\rangle_{W_F}\in I_sI_z/N^2+[-R,R].
$$

Intersect this with ordinary Cauchy. Negative residual caps or
inconsistent domains stop the application. If $N=0$, both projection
intervals must contain zero and the application uses ordinary Cauchy
without division. The resulting cross interval $[X_{\rm lo},X_{\rm up}]$
gives

$$
J_{\rm lo}=\max\{0,P^2_{\rm lo}+C^2_{\rm lo}+2X_{\rm lo}\}
\le\|v+c\|_{W_F}^2
\le P^2_{\rm up}+C^2_{\rm up}+2X_{\rm up}=J_{\rm up}.
$$

All bounds hold uniformly for one common realization. Independent
interval endpoints need not be jointly attainable. Apply the existing
pricing map to the valid decomposition $(v+c)+r+0$:

$$
[\sqrt{J_{\rm lo}}-\epsilon_{\rm sm}]_+^2
\le E_{\rm true}\le
(\sqrt{J_{\rm up}}+\epsilon_{\rm sm})^2.
$$

Retain the stronger previous energy lower and smaller previous upper.
The zero third component belongs to this regrouped decomposition; it
does not assert that the original mixed vector vanishes. A single new
upper prices both the fee and the complete original Bessel budget.
The energy-lower endpoint uses the same regrouping and the fixed charge
constant and $h$ endpoints. Both all-real comparison tests reuse the
saved $B,G,M$ and their fixed far-row UPPER $A_*$; the energy lower is
never substituted for that upper.

The single fixed1024-working/640-export application retains66 runtime
bindings, unchanged at entry and prewrite. Stored assembly time
is0.61203seconds; time including serialization is0.72872seconds.
Its physical quadratic is approximately11.172943110390517642,
and the complete physical representer-energy upper is below
15.356508960841880022. The resulting norm upper is below
3.918738184778600392, compared with the saved broad cap near29.0983.

| Quantity | Directed value |
|---|---:|
| Principal/mixed cross interval |[−0.113379023101042651,0.013416593112150290]|
| Source-energy lower |>6.268984281541914933|
| Source-energy upper |<6.524928095642312689|
| Source-valid positive fee |<175.921995998246711018|
| Legal coefficient |>0.000040122278284528281535|
| Fixed repriced all-real floor |>0.296481006612169882|
| Energy-endpoint all-real floor |>−1.220854294197841680|

Displayed intervals round outwards; exact rationals and640-bit integer
endpoints are authoritative. Both ends improve the previous source-energy
bracket [6.227486948459329823,6.766398882441490]. The new fixed paid
comparison remains positive for every real steering coefficient, so
computing a favorable derivative cannot make that recipe negative.
This supplies no lower bound for an actual center with a smaller charge.
The energy-endpoint lower is negative and remains inconclusive for the
whole fixed-budget energy-cap-only family. It is neither a negative
upper nor a realizable negative comparison. The principal/mixed cross
interval still contains positive numbers: opposite signs of the two
saved projections alone have not certified a negative cross.


The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/3253bccd35cab40a5ed3140a892f27e572ee7d1a/docs/reports/weil-c27)
retain packet SHA256 `59374362635382b3b180aff21584a5a1e32d603b19ccaa5db3ea693086b5f89c` and source SHA256 `ba5ea56e4a30c3afcaf52d428bbd060f19ca18a29464f6dc15e8055837329735`.
The fixed1024-working/640-export application makes one new physical
direction quadratic and reuses the saved signed projections. No old
scientific producer, signed pairing, source, feature, inverse, trace,
moment or long-tail supplier is replayed; there is no source, parameter,
precision or cutoff scan.

This is a numerical application of existing Gram/Schur, physical-error
and pricing certificates, with no new generic theorem, literature
novelty or Lean proof. The actual-form/domain, common-source/short/lift,
original-weight, component-bound and inverse-comparison premises remain.
Actual-center/full-border signs, the good-block metric, retained/cofinal
positivity, Robin tail and RH remain unresolved.

### Pay omitted jet moments on the saved feature direction

The complete physical operator-error payment in the preceding estimate
contributes about4.18357 to the representer squared-norm cap. The existing
exact full-jet Gram supplies another route on the SAME saved feature
direction, without repeating its quadratic. Retain
$h=(A_0,\ldots,A_{55},B_0,\ldots,B_{55})$, physical representer $b$,
midpoint-feature jet $j_h$, original weight $w_F$, and the certificates

$$
\|j_h\|_{W_F}^2=\alpha w_Fh^THh,\qquad
K_0=\alpha_0w_FH_0,\qquad
\alpha=\frac4{\pi^2M},\qquad
\|b-j_h\|_{W_F}\le\epsilon_b^\sharp.
$$

Here $M=32768$, $R=d=56$. The full moment matrix $H$ is independent
of the physical low-support size: the saved far packet's support1280
and the current representer's support2048 use the same $H$.
$H^{(d)}$ keeps $k+l<d$ in each block, and $H_0$ is its one exact
midpoint approximation. The saved $Q_{\rm up}$ encloses the SAME
$h^TK_0h$, including its exported-array uncertainty; it is reused.

Group signed feature products before bounding omitted moments. For
$d\le n\le2R-2$, form the complete ordered sums

$$
a_n=\sum_{k+l=n}A_kA_l,\qquad
g_n=\sum_{k+l=n}A_kB_l,\qquad
b_n=\sum_{k+l=n}B_kB_l.
$$

Then the omitted quadratic is exactly

$$
h^T(H-H^{(d)})h
=\sum_{n=d}^{2R-2}
(a_nU_{2n+2}-2g_nT_{2n+3}+b_nV_{2n+4}).
$$

Ordered sums count the AA and BB off-diagonal terms, and the single
factor2 counts AB and BA. The existing actual-symbol budget $B_*$ and
moment integral bounds give the one-sided upper

$$
e_{{\rm box},n}=
\frac{B_*^2(a_n)_+}{2n+1}
+\frac{2B_*|g_n|}{2n+2}
+\frac{(b_n)_+}{2n+3}.
$$

True $U,V$ are nonnegative. Thus a negative AA or BB coefficient need
not be charged as its absolute value. Interval evaluation preserves
uncertainty in the saved features and any resulting cancellation.

Three already retained moments supply another bound. Put

$$
S_*=
\begin{pmatrix}U_{112}&T_{113}\\T_{113}&V_{114}\end{pmatrix},
\qquad q=\frac{M}{M+1}.
$$

For the true moments, with $x_m=M/m$ and $m>M$,

$$
S_n=\frac1M\sum_{m>M}x_m^{2n+2}
\binom{s_m}{x_m}(s_m,x_m),\qquad
0\preceq S_n\preceq q^{2(n-55)}S_*.
$$

This follows termwise from $0<x_m\le q$. It is a relation between
true Gram matrices; their rounded centers need not be PSD. For
$G_n=\left(\begin{smallmatrix}a_n&-g_n\\-g_n&b_n\end{smallmatrix}\right)$,
the support function of $0\preceq X\preceq cS_*$ is
$c\operatorname{Tr}[(S_*^{1/2}G_nS_*^{1/2})_+]$, including singular
$S_*$. In dimension2, define

$$
\tau_n=a_nU_{112}-2g_nT_{113}+b_nV_{114},\qquad
\delta_n=(a_nb_n-g_n^2)(U_{112}V_{114}-T_{113}^2).
$$

The positive-part trace equals

$$
\Phi_n=\frac{\tau_n+\sqrt{\tau_n^2+4\max\{-\delta_n,0\}}}{2}.
$$

This expression is monotone in $\tau_n$ and $\max\{-\delta_n,0\}$.
Outward upper/lower bounds for $\tau_n,\delta_n$ therefore yield
$\Phi_n^{\rm up}$ without a matrix square root. Select the smaller of
the two uniform bounds for each SAME antidiagonal:

$$
E_h=\sum_{n=56}^{110}
\min\{e_{{\rm box},n}^{\rm up},q^{2(n-55)}\Phi_n^{\rm up}\},
\qquad h^T(H-H^{(d)})h\le E_h.
$$

No high moment or signed-moment supplier is evaluated. The three anchor
intervals are the original640-grid enclosures, not new estimates.
Neither the retained mask nor the omitted block is assumed PSD.

Retained moment widths are at most two640-grid units, giving
$\|H^{(d)}-H_0\|\le e_H=112\,2^{-640}$.
The saved `moment_gram_norm` field is the original explicit TRACE upper
$H_*$. Since true $H\succeq0$ and masking decreases Frobenius norm,

$$
\|H_0\|\le\|H^{(d)}\|_F+e_H
\le\operatorname{Tr}H+e_H\le H_*+e_H.
$$

An arbitrary operator-norm cap alone would not justify this masked
bound. Let $A_h$ be the sum of squared upward absolute feature caps.
Reuse the original prefactor interval to obtain $\alpha_{\rm up}$ and
$|\alpha-\alpha_0|\le e_\alpha$. The accepted outer certificate gives

$$
\|j_h\|_{W_F}^2\le J_h:=Q_{\rm up}
+w_F\left[\alpha_{\rm up}E_h
+A_h\left(\alpha_{\rm up}e_H+e_\alpha(H_*+e_H)\right)\right],
\qquad
\|b\|_{W_F}^2\le(\sqrt{J_h}+\epsilon_b^\sharp)^2.
$$

This pays omission, moment midpoint error and prefactor error. The
original512-grid physical allowance is not reinterpreted as a640-grid
moment error. The sharp weighted forward allowance already pays the
actual representer to this SAME full jet; no duplicate physical-source
payment, extra $w_F$ or $\kappa$ is inserted. A negative final $J_h$
is inconsistent and stops the application.

Only a strictly smaller representer cap enters the existing projection
and pricing maps. The valid regrouping remains $(v+c)+r+0$; stronger
old source-energy endpoints are retained, and unchanged comparison
parameters reuse their saved rank outputs. The SAME $B,G,M$ and frozen
far-row energy UPPER remain throughout.

The single fixed1024-working/640-export application retains68 runtime
bindings, unchanged at entry and prewrite. The saved quadratic is reused.
The omitted-block payment is below$1.43015\cdot10^{-130}$ and the
separate rounding payment below$1.25068\cdot10^{-185}$. Adding the
original sharp forward allowance gives the following outward bounds.

| Quantity | Directed value |
|---|---:|
| Representer squared-norm upper |<11.172943110390517643|
| Representer norm upper |<3.342595265716523695|
| Principal/mixed cross interval |[−0.076771255960990555,−0.060620829249211873]|
| Source-energy lower |>6.342199815821979165|
| Source-energy upper |<6.376853250919508462|
| Source-valid positive fee |<175.769293814626319160|
| Legal coefficient |>0.000040586603433261736126|
| Fixed repriced all-real floor |>−0.572919445838071768|
| Energy-endpoint all-real floor |>−0.779703303246544574|

The norm cap improves from3.918738184778600392, and both ends of the
preceding energy bracket [6.268984281541914933,6.524928095642312689]
tighten. The principal/mixed cross is now strictly negative under the
retained common-source premises. This follows from the sharper common
direction norm, with no new signed pairing supplier.

The preceding paid-recipe exclusion applies to its original fee and
coefficient. The newly repriced pair has a negative all-real LOWER,
so that lower-bound test leaves the new recipe unexcluded. Its negative
lower neither realizes a negative comparison nor supplies a negative
upper. The energy-endpoint test also remains inconclusive for the whole
fixed-budget energy-cap-only family. Actual smaller-fee center sign is
not determined. Displayed endpoints round outwards; exact rationals
and640-bit packet endpoints are authoritative.

The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/a89093fb3d7165a48c71f57374f218fa5c757f88/docs/reports/weil-c27)
retain packet SHA256 `9ccd6494c0520f9f53efe0b44bcae879566157c7e7ffb698165f9d02c258fd41` and source SHA256 `d9cbc7f94640ec60a885dfce018fc626726fe77caaaa87aef63c912c0f70abcd`.
There is one new grouped omitted-block contraction, three signed feature
antidiagonal families, three retained anchor reads and one feature
absolute norm. The saved masked quadratic, moment suppliers, signed
projections, physical source, lift, inverse, trace and long-tail
suppliers are reused, with no source/parameter/precision/cutoff scan.

This is a numerical application of existing moment, semidefinite
support-function, midpoint and jet certificates. It claims no new
generic theorem, literature novelty or Lean proof. The actual-form/domain,
common-source/short/lift, original-weight, component and
inverse-comparison premises remain. Actual-center/full-border signs,
good-block payment, retained/cofinal positivity, Robin tail and RH
remain unresolved.

### Test an equality row inside the signed-response and energy relaxation

A negative lower bound does not establish that its relaxation permits a
negative value. Test one explicitly constructed row before replacing the
accepted timelike estimate by a larger constrained optimization. This is
an application of classical timelike Schur equality on the SAME finite
reference form, with no new generic inequality or optimality claim.

Retain $P=TRT^*\succeq0$, $Q_R=P-e_0e_0^*/\delta$, and
$y_0=\alpha_0\rho+\beta_J$. The existing scalar packet already encloses

$$
r_0=y_0Py_0^*,\quad r_\rho=\rho P\rho^*,\quad
r_{\rho\beta}=\rho P\beta_J^*,\quad
\lambda=y_0[0],\quad g=\rho Q_Ry_0^*.
$$

Use the saved finite cross, rather than supplying another Gram:

$$
p=\alpha_0r_\rho+r_{\rho\beta}=\rho Py_0^*,\qquad
b=\lambda^2/\delta-r_0=-y_0Q_Ry_0^*>0.
$$

Both the coefficient $\lambda$ and the finite parameters retain their
interval uncertainty. No rounded center is declared the true form.
Choose the one rational steering value $\alpha_*=101/2000$, and an
exact interior value $\theta_*$ of the saved signed-response interval.
The chosen value is not asserted to equal the actual signed response.
Define, for the true common finite parameters,

$$
s=\alpha_*-\alpha_0,\qquad
\tau=-\frac{\theta_*+sg}{b},\qquad
f_{\rm rel}=\tau y_0-s\rho.
$$

Then, exactly,

$$
f_{\rm rel}Q_Ry_0^*=\theta_*,\qquad
\alpha_*\rho+\beta_J+f_{\rm rel}=(1+\tau)y_0.
$$

This is a row in a selected scalar relaxation. Its generation by the
original physical source/coupling, and membership of $\alpha_*$ in a
physical legal subset, are not supplied. The construction defines a row
for each actual finite reference form covered by the common intervals.

Its two norm/cap checks use

$$
f_{\rm rel}Pf_{\rm rel}^*=
\tau^2r_0-2\tau sp+s^2r_\rho,\qquad
f_{\rm rel}[0]=\tau\lambda-s\delta\frac{p-g}{\lambda}.
$$

The second identity uses $\lambda\ne0$ and
$\rho[0]=\delta(p-g)/\lambda$. The original far-row positive-energy
and negative-coordinate bounds are homogeneous in the source-energy
UPPER. From the saved mixed-norm recipe's $E_0,A_0,C_0$ and the latest
source-energy upper $E$, the accepted interface gives outward caps

$$
A=A_0E/E_0,\qquad C=C_0\sqrt{E/E_0}.
$$

These are bounds in different units: $E$ is source energy, $A$ bounds
$fPf^*$, and $C$ bounds $|f[0]|$. No source-energy lower is substituted
for a far-row upper. Check the constructed row against BOTH caps.

The already certified upper inverse comparison gives
$Q_{\rm true}\preceq Q_R+\eta(1-\eta)^{-1}P$. Thus this constructed
row's paid comparison has the sufficient UPPER

$$
\mathcal E_{D,k}^{\rm rel}(\alpha_*)
\le k\alpha_*^2+D
+(1+\tau)^2\left(-b+\frac{\eta}{1-\eta}r_0\right).
$$

It is an upper on this particular constructed row, rather than the
previous all-real lower bound. All scalar intervals propagate, and no
matrix, inverse, physical far row or actual derivative is regenerated.

The single application satisfies both caps and has a strictly negative
UPPER for this constructed row:

| Quantity | Directed value |
|---|---:|
| Constructed positive-energy upper |<0.583108075508182745|
| Allowed positive-energy cap |>2.712924125459587053|
| Constructed absolute first-coordinate upper |<2.228217728848581443e-16|
| Allowed absolute first-coordinate cap |>4.367163575891468984e-16|
| Constructed paid-comparison upper |<−0.567072019035610609|

All three checks, and their conjunction, pass. Consequently these
selected scalar constraints do permit a negative paid comparison under
the retained finite-form and inverse-comparison premises. No uniform
nonnegative bound follows from this relaxation alone. This is a
feasible row in the relaxation, not just a negative lower bound and not
an attained value of the original physical source. The chosen response
lies inside the measured interval but is not identified with its true
value. Displayed values round outwards; exact rational caps and640-bit
interval endpoints are authoritative.

The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/06d399b169a01deeeef13c2480ec60acde04eaca/docs/reports/weil-c27)
retain packet SHA256 `1879f4b0653e762ca0d7bb1e1933a59afc79fb10851d155f1c16c87055872992` and source SHA256 `218946086714e3408a4837a98e211622a10e7361eb0789427b1d3c9f24245340`.
The single fixed1024-working/640-export application uses one literal
$\alpha_*$ and one interior target, with no parameter/source/precision/
cutoff scan or retry. Earlier producers and passed fixtures are reused.

The constructed row lies in the span of $\rho,y_0$, so a new payment
confined to the perpendicular residual would vanish on this row.

The selected relaxation keeps the finite form, inverse comparison,
signed-response interval and two homogeneous far-row caps. It omits the
full original source-to-row image constraint and other physical
observations. A row admitted by this relaxation is not automatically
admitted by the original source model. Determining the actual-source
sign requires its response or an additional relation that distinguishes
it from the constructed row; this test does not establish which single
additional scalar would suffice.

This is a numerical application of existing equality and inverse
comparison identities, with no new generic theorem, novelty or Lean
proof. Actual-center/full-border signs, good-block payment,
retained/cofinal positivity, Robin tail and RH remain unresolved.


### Retain the source relation on a zero-first-coordinate direction

The preceding negative row belongs to a scalar relaxation. Add a
relation supplied by the original common source before seeking another
nonnegative certificate. Reuse $P=TRT^*\succeq0$,
$Q_R=P-e_0e_0^*/\delta$, $y_0=\alpha_0\rho+\beta_J$ and
$\lambda=y_0[0]\ne0$. Set

$$
c=\frac{\rho[0]}\lambda,\qquad w=\rho-cy_0.
$$

Then $w[0]=0$ exactly, so

$$
Q_Rw^*=Pw^*,\qquad
fQ_R\rho^*=fPw^*+c\theta,\qquad \theta=fQ_Ry_0^*.
$$

This is a positive-metric slice of the SAME finite reference form;
it does not change the actual row. Since the first row of $T$ is the
negative-pivot elimination row and its other rows form the identity,
$wT=w_{\rm tail}$. Thus one cached reference-vector action supplies

$$
v_d=Pw^*=TRw_{\rm tail}^*.
$$

No new inverse, solve or old reference quadratic is required. The
coefficient $c$ and every finite row retain their interval uncertainty;
$w[0]=0$ is imposed using the exact common-parameter identity, not a
subtraction of rounded coordinates.

The original source relation is
$f=\kappa u_F^*W_F\mathsf B$, where $\mathsf B=R_FV$ and
$\kappa=33/32$. Define

$$
v_b=Q_Ry_0^*,\qquad b=\mathsf Bv_b,\qquad d=\mathsf Bv_d.
$$

The saved signed observation and the desired new pairing are therefore

$$
\theta=\kappa\langle u_F,b\rangle_{W_F},\qquad
\zeta=fPw^*=\kappa\langle u_F,d\rangle_{W_F}.
$$

The entire signed $\theta$ interval is retained, together with the SAME
source-energy UPPER $E\ge\|u_F\|_{W_F}^2$. No interior response is
substituted for the actual one. The tighter saved cap
$J_b\ge\|b\|_{W_F}^2$ is reused without replaying its quadratic.

For any direction $v$ in this common lift, the original physical
interface supplies $t_v=D_{\rm phys}Vv$, $h_v=P_0t_v$, and
$\|t_v\|\le\sqrt{K_{\rm phys}}L_v$, where

$$
L_v=\sum_j|v_j|\sqrt{(V^*V)_{jj}}.
$$

Use the cached112-by18 feature map once to obtain $h_d$; $h_b$ is
already saved. The original operator-norm Gram certificate gives

$$
\begin{aligned}
\|d\|_{W_F}^2&\le J_d:=
\operatorname{up}\left(h_d^TK_0h_d+
\epsilon_{\rm far}K_{\rm phys}L_d^2\right),\\
\langle b,d\rangle_{W_F}&\in h_b^TK_0h_d+
[-e_{bd},e_{bd}],\qquad
 e_{bd}=\operatorname{up}
 (\epsilon_{\rm far}K_{\rm phys}L_bL_d).
\end{aligned}
$$

The complete interval evaluation also pays uncertainty in both feature
vectors and the saved kernel. This is a bilinear Gram error; it does
not infer a vector error by taking the square root of a Gram error.
Neither rounded kernel centers nor the masked kernel are assumed PSD.
The physical allowance retains its original512-grid interpretation;
weighted kernel and Hilbert norms already contain the original far
weight, with no extra weight or $\kappa$ inserted.

Apply the existing `projected_energy` common-representer bound to the
SAME three real vectors $(u_F,d,b)$, using squared-norm uppers
$(E,J_d,J_b)$ and signed pairings
$s=\theta/\kappa$, $t=\langle b,d\rangle$. At each exact realization,

$$
\left|\langle u_F,d\rangle-\frac{st}{J_b}\right|
\le
\sqrt{\left(E-\frac{s^2}{J_b}\right)
      \left(J_d-\frac{t^2}{J_b}\right)}.
$$

The formula remains valid when $J_b$ is only an upper: extend $b$ by
one orthogonal coordinate to give it squared norm $J_b$, and extend
$u_F,d$ by zero. The existing interval implementation bounds both
residual factors and the signed product uniformly. Multiplication by
$\kappa$ supplies a conditional interval for $\zeta$ and then for
$fQ_R\rho^*=\zeta+c\theta$.

Retain the earlier scalar-only bound too. With
$p=\rho Py_0^*$, $r_0=y_0Py_0^*$, $r_\rho=\rho P\rho^*$ and the
SAME far-row energy cap $A\ge fPf^*$,

$$
|\zeta|\le\sqrt{A(r_\rho-2cp+c^2r_0)}.
$$

Here $A$ and source energy $E$ have different meanings and units. The
two valid intervals are intersected; an empty intersection is an
inconsistency and stops the application.

For the previously constructed row, reuse its own saved $\tau$ and
$s=\alpha_*-\alpha_0$ to obtain

$$
f_{\rm rel}Pw^*=\tau(p-cr_0)-s(r_\rho-cp).
$$

Its target remains chosen inside the observed interval, not identified
with the actual $\theta$. Disjoint intervals would exclude this
particular row under the added source-energy/Gram relation; this test
neither excludes all negative rows nor decides the actual paid
comparison.

The uniform physical Gram estimate has new-direction quadratic
$h_d^TK_0h_d\simeq13.75086838$, but its norm-error payment exceeds2984.69.
It therefore retains the scalar-only interval and leaves the constructed
row unexcluded. This identifies the cost of that uniform certificate,
not an attained physical norm or a source counterexample.

Reuse the preceding directional full-jet estimate on the SAVED new
features and quadratic. No direction, feature, quadratic or cross is
recomputed. In the original sharp forward formula, all factors except
$L_v$ form one uniform coefficient $C_{\rm forw}$. Since
$\epsilon_b^\sharp\ge C_{\rm forw}L_b$ and $L_b>0$,

$$
\epsilon_d^\sharp:=\operatorname{up}
\left(\epsilon_b^\sharp\frac{L_d}{L_b}\right)
\ge C_{\rm forw}L_d.
$$

This transfers a uniform forward-error coefficient, not an arbitrary
norm of the old realization. The original three retained moments and
existing omitted-block/midpoint payments give $J_{h_d}$ for the full
new jet. Thus

$$
\|d\|_{W_F}^2\le J_d^{\rm jet}:=
\operatorname{up}\left((\sqrt{J_{h_d}}+\epsilon_d^\sharp)^2\right).
$$

Select the smaller of this cap and the valid uniform physical cap,
then apply the SAME common-projection bound with the saved old/new
cross. Intersect the resulting interval with the saved coarse interval.
The actual signed response and common source stay fixed throughout.

The directional certificate gives the following outward displayed
bounds. Exact rational caps and640-bit endpoints remain authoritative;
the actual-pairing rows below also enclose the exported Arb balls.

| Quantity | Enclosure or directed cap |
|---|---:|
| Uniform physical squared-norm upper |<2998.447008|
| Directional full-jet squared-norm upper |<13.750868382|
| Transferred sharp forward-error upper |<1.416877e-67|
| Retained scalar-only zero-pairing interval |contained in[−66.425463,66.425463]|
| Refined actual $\zeta$ interval |contained in[−9.656778,9.656778]|
| Constructed row's $f_{\rm rel}Pw^*$ |contained in[−20.900041,−20.900040]|
| Refined actual $fQ_R\rho^*$ interval |contained in[−33.775533,−14.432247]|

The norm cap strictly improves and the actual zero-pairing interval
strictly narrows. It is disjoint from the particular constructed row's
pairing. Thus the additional source-energy/norm relation excludes that
row under the retained original-source premises. The symmetric new
$\zeta$ bound does not supply its sign. The reference-$\rho$ pairing
is strictly negative within the same conditional model, but this is
one far-row pairing, not the paid expression or a full-border sign.

The [sources, exact packets and README](https://github.com/the-omega-institute/trureturing-experiments/tree/64fb7bfb67e4acfe00418f03047e1c860f733d59/docs/reports/weil-c27)
retain the coarse packet SHA256
`c4cbbead777f652812c0aa0bd238bf08053daa52be7afbedfa1321da19847a9b`
and source SHA256
`612ba841171f1a040c90f376c85cbc326f3e46c2a9ef94e0257094720c0460bb`;
the directional refinement packet SHA256 is
`ee401d13ef503a44089c33e958b8f90dab09aefa843050f09713ee6a33729861`
and its source SHA256 is
`4c07a0a9a55dd9d87c1f1b741960f29c495246a9a868ecd3b2341bf0b11c07d0`.
There is one cached-reference vector action, one cached-feature action,
one new physical-feature quadratic and one old/new feature cross. The
old direction quadratic, source, sine, moment, tail, inverse, solve and
trace suppliers are reused. Each consumer has one fixed1024-working/
640-export application. The refinement only applies the homogeneous
forward, existing directional norm and common-projection bounds to
saved outputs; it repeats none of those four finite actions. There is
no parameter/source/precision/cutoff scan or retry.

This is a numerical application of existing linear, physical-Gram and
common-projection results. It claims no generic theorem, novelty or
Lean proof. The actual-form/domain, common-source/lift and original
physical error premises remain. An interval for an actual far-row
pairing is not an exact derivative or an actual paid-comparison sign.
Actual-center/full-border signs, good-block payment, retained/cofinal
positivity, Robin tail and RH remain unresolved.

### Retain the old/new directional Gram before pricing the family

The uniform physical cross payment above is greater than111.74,
although the saved masked cross is about10.64041669 and both individual
directional norm certificates have small errors. Retain that SAME
masked cross and the two saved feature arrays. A two-sided application
of the original moment and forward-vector estimates can pay their
cross without repeating either feature action or contraction.

Use the ACTUAL-symbol full jets $j_b,j_d$ from the existing synthesis
interface, with $x_m=M/m$, $M=32768$, $R=56$:

$$
j_v(m)=\frac{2(-1)^m}{\pi m}
\left[x_mB_v(x_m^2)-s_mA_v(x_m^2)\right].
$$

Here $s_m$ is the true far symbol. The original moments, symbol budget
$|s_m|\le S$, weight $w_F$, and sharp bounds
$\|b-j_b\|_{W_F}\le\epsilon_b^\sharp$,
$\|d-j_d\|_{W_F}\le\epsilon_d^\sharp$ all refer to this actual
synthesis. The approximate-symbol finite samples in the signed-proxy
calculation are not used in this application. In particular no new
symbol-error identification is required. Both forward bounds are
copied from accepted packets, without rescaling them again.

For each omitted antidiagonal $R\le n\le2R-2$, form the ordered
bilinear coefficients

$$
\begin{aligned}
a_n&=\sum_{k+l=n}(h_b)_{A_k}(h_d)_{A_l},\\
g_n&=\sum_{k+l=n}
\left[(h_b)_{A_k}(h_d)_{B_l}+(h_b)_{B_k}(h_d)_{A_l}\right],\\
b_n&=\sum_{k+l=n}(h_b)_{B_k}(h_d)_{B_l}.
\end{aligned}
$$

The omitted jet cross is exactly

$$
w_F\alpha\sum_{n=R}^{2R-2}
\left(a_nU_{2n+2}-g_nT_{2n+3}+b_nV_{2n+4}\right),
\qquad \alpha=\frac4{\pi^2M}.
$$

The two mixed orientations are included in $g_n$; no additional
factor2 is inserted. The original decreasing-tail moment bounds give

$$
U_p\le\frac{S^2}{p-1},\qquad
|T_p|\le\frac S{p-1},\qquad
V_p\le\frac1{p-1}.
$$

Consequently the absolute masking payment is bounded upward by

$$
e_{\rm mask}=\operatorname{up}\left[
w_F\alpha_{\rm up}\sum_{n=R}^{2R-2}
\left(\frac{S^2|a_n|}{2n+1}
+\frac{S|g_n|}{2n+2}+\frac{|b_n|}{2n+3}\right)\right].
$$

Absolute AA and BB coefficients pay BOTH signs; the earlier one-sided
norm estimate cannot simply be negated to supply a cross lower.
Feature uncertainty is propagated before taking absolute uppers.
No omitted moment is produced or reconstructed.

Reuse the original moment-matrix error $e_H=112\,2^{-640}$,
full moment TRACE upper $H_*$, prefactor halfwidth $r_\alpha$,
and saved squared feature-norm uppers $H_b,H_d$. The same midpoint
interface, now bilinear, supplies

$$
e_{\rm mid}=\operatorname{up}\left[
w_F\sqrt{H_bH_d}
\left(\alpha_{\rm up}e_H+r_\alpha(H_*+e_H)\right)\right].
$$

The retained entry intervals have width at most two640-grid units,
so midpoint errors remain at most $2^{-640}$ entrywise after masking.
Thus $e_H$ controls the SAME masked matrix; it is not inferred by
assuming that masking contracts operator norm. The full true moment
Gram is PSD and masking contracts its Frobenius norm, giving the
previous bound $\|H_0\|\le H_*+e_H$. The masked moment matrix
and its rounded center need not be PSD.
For the saved full-jet norm uppers $J_{j_b},J_{j_d}$, the separate
forward-vector certificates and Cauchy give

$$
e_{\rm forw}=\operatorname{up}\left[
\epsilon_b^\sharp\sqrt{J_{j_d}}
+\epsilon_d^\sharp\sqrt{J_{j_b}}
+\epsilon_b^\sharp\epsilon_d^\sharp\right].
$$

This is a payment using actual vector errors, not a square root of
the old Gram error. With the SAVED masked cross interval $I_0$,

$$
\langle b,d\rangle_{W_F}\in
\left(I_0+[-e,e]\right)\cap I_{\rm coarse},\qquad
e=e_{\rm mask}+e_{\rm mid}+e_{\rm forw}.
$$

An empty intersection stops the application. The existing
`projected_energy` estimate uses this signed interval on the SAME
$(u_F,d,b)$, with the saved $(E,J_d,J_b)$ and entire
$\theta/\kappa$ interval. Intersect its resulting $\zeta$ interval
with the accepted one, then retain the corresponding interval for
$\phi=fQ_R\rho^*=\zeta+c\theta$. All intersections preserve the
same actual row and parameter uncertainty.

#### Apply the existing paid square completion to the new response

Use the saved old reference values, with $k_0=t_0^{-1}$:

$$
q_0=k_0\alpha_0^2+D_0+y_0Q_Ry_0^*,\qquad
d_0=k_0\alpha_0+\rho Q_Ry_0^*,\qquad
h_{11}=k_0+\rho Q_R\rho^*.
$$

Keep the earlier SAME-row negative-square upper $F_-$ and inverse-loss
payments $C_0+C_2s^2$, $s=\alpha-\alpha_0$. They are valid uppers
from the earlier source certificate; a new source-energy lower is
never substituted for any of these far-row uppers. For any one fixed
new reciprocal coefficient $k>0$ and fee $D>0$, the existing expansion
gives the all-real lower

$$
\mathcal E_{D,k}(\alpha_0+s)
\ge K+Hs^2-2B|s|,
$$

where directed choices are

$$
\begin{aligned}
K&=\operatorname{down}\left[q_{0,\rm lo}+D-D_0
+(k-k_0)\alpha_0^2+2\theta_{\rm lo}-F_--C_0\right],\\
H&=\operatorname{down}\left[h_{11,\rm lo}+k-k_0-C_2\right],\\
B&=\operatorname{up}|d_0+(k-k_0)\alpha_0+\phi|.
\end{aligned}
$$

These translations preserve the old reference definitions while
changing the paid recipe. If $H>0$, scalar square completion gives

$$
\mathcal E_{D,k}(\alpha)\ge
K-\operatorname{up}(B^2/H)\qquad(\alpha\in\mathbb R).
$$

A nonpositive floor is inconclusive and supplies neither a feasible
negative row nor an actual-source upper. No restriction on physically
legal $\alpha$ is invented. The consumer evaluates the fixed current
$(k,D)$ and the already saved energy LOWER-endpoint $(k_{\min},D_{\min})$.
Monotonicity of the existing fixed pricing rule makes a strictly
positive endpoint floor an exclusion for every recipe obtained solely
by improving its source-energy upper. That exclusion would still give
no lower bound for an actual center with a smaller justified charge.

The following displays enclose the exported balls, or round scalar
upper/lower certificates in the indicated direction. Exact rational
caps and640-bit packet endpoints remain authoritative.

| Quantity | Enclosure or directed bound |
|---|---:|
| Bilinear omitted-moment masking payment |<1.055086e-128|
| Bilinear moment/prefactor rounding payment |<2.575728e-185|
| Total additional bilinear cross-error payment |<4.932753e-67|
| Actual physical $\langle b,d\rangle_{W_F}$ |contained in[10.6404166919614235901773440,10.6404166919614235901773441]|
| Refined actual $\zeta$ |contained in[−8.423007,0.178344]|
| Refined actual $fQ_R\rho^*$ |contained in[−32.541761,−23.910682]|
| New fixed-recipe all-real lower, rounded down |−2.756762331|
| New energy-endpoint all-real lower, rounded down |−2.959238524|
| Retained stronger fixed-recipe lower, rounded down |−0.572919446|
| Retained stronger energy-endpoint lower, rounded down |−0.779703304|

The small additional payment does not remove the saved masked-cross
uncertainty: the final physical-cross interval still has width about
$5.56\times10^{-27}$, rather than $4.94\times10^{-67}$. Both the
physical cross and $\zeta$ strictly narrow. The $\zeta$ interval still
contains zero; the strictly negative reference-$\rho$ pairing is not
the sign of the paid expression.

Both new paid-floor exclusion flags are false. These two square-completion
lowers are weaker than the preceding timelike joint floors, so retain
the preceding stronger floors for the SAME fixed and energy-endpoint
recipes. No old valid lower is replaced. Improved marginal pairing
intervals alone have not improved the paid positivity certificate;
the source response and its self-term must retain enough joint
information to control that comparison. Neither negative lower
constructs a feasible negative row or supplies an actual negative upper.


The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/a4bc1a53695fd8ec65150026e1cc3271dfad061b/docs/reports/weil-c27)
retain packet SHA256 `5cfba16d5428c1c61618a861a8167ca6828f46142d7bd7993d4d84b20de6e980` and source SHA256
`a35c3222a788508622b92adc6525bc73a26cdc2070c26eb5a701a62015e991a5`. There is one new bilinear error application,
one application of the existing common projection and two scalar paid
floor applications, at fixed1024 working/640 export bits. No finite
direction, feature, quadratic or cross is repeated, and no source,
sine, moment, tail, inverse, solve or trace producer is invoked. There
is no parameter/source/precision/cutoff scan or retry.

This is a conditional application of the original jet/moment/forward
certificates, Cauchy, existing common projection and scalar square
completion. It asserts no generic theorem, novelty or Lean proof.
The actual-form/domain, common-source/lift and physical error premises
remain. Actual-center/full-border/good-block/cofinal positivity,
Robin and RH remain unresolved.

### Retain both source responses in the same indefinite plane

The single-timelike lower and marginal derivative completion discard
part of the joint self-term relation. Reuse the classical block Schur
and inertia argument on the SAME two-dimensional span, keeping the
positive square instead of dropping it. This is an application of the
existing matrix theory and saved source certificates, not a new
generic inequality or an RH claim.

Write

$$
Q_\varepsilon=\gamma P-e_0e_0^*/\delta\preceq Q_{\rm true},
\quad \gamma=1-\varepsilon=\frac1{1+\eta},
\quad \varepsilon=\frac\eta{1+\eta},\quad 0\le\eta<1.
$$

Keep the same real rows $y_0=\alpha_0\rho+\beta_J$, actual $f$,
$c=\rho[0]/y_0[0]$ and $w=\rho-cy_0$ with $w[0]=0$. Define

$$
\begin{aligned}
b&=-y_0Q_\varepsilon y_0^*>0,&
g&=\rho Q_\varepsilon y_0^*,&
h&=\rho Q_\varepsilon\rho^*,\\
t&=wQ_\varepsilon w^*=\gamma wPw^*\ge0,&
\omega&=c+g/b,&
a&=t+b\omega^2=h+g^2/b.
\end{aligned}
$$

The common identities come from the original reference rows and
operators. Overlap of two scalar interval evaluations is only an
inconsistency test; it cannot establish a common realization.
For $a>0$, the row $v=\rho+(g/b)y_0$ is $Q_\varepsilon$-orthogonal
to $y_0$ and has energy $a$. The span has one negative and one positive
direction. Since $Q_\varepsilon$ has at most one negative direction,
its orthogonal remainder is nonnegative, even when $P$ is singular.
Consequently

$$
fQ_\varepsilon f^*\ge
-\frac{\theta_\varepsilon^2}{b}
+\frac{(\gamma\zeta+\omega\theta_\varepsilon)^2}{a},
\qquad
\theta_\varepsilon=fQ_\varepsilon y_0^*,\quad \zeta=fPw^*.
$$

Transport the whole original signed-response interval by

$$
\theta_\varepsilon=\theta-\varepsilon fPy_0^*,\qquad
|\theta_\varepsilon-\theta|\le
\varepsilon\sqrt{A\,r_{0,\rm up}}.
$$

Here $A\ge fPf^*$ is the SAVED upper for the same actual row, while
$r_0=y_0Py_0^*$. Keep $A$ fixed in both paid recipes, including the
source-energy lower-endpoint recipe. No source-energy lower replaces a
far-row upper. The other exact response identity is

$$
fQ_\varepsilon\rho^*=\gamma\zeta+c\theta_\varepsilon.
$$

For one fixed saved $k,D>0$, put $H=k+h$. Expanding the SAME paid
comparison and minimizing over every real $s=\alpha-\alpha_0$, when
$H>0$, gives

$$
\begin{aligned}
\mathcal E_{D,k}(\alpha)&\ge
F(\theta_\varepsilon,\zeta),\\
F(\theta_\varepsilon,z)&=
k\alpha_0^2+D-b+2\theta_\varepsilon
-\frac{\theta_\varepsilon^2}{b}
+\frac{(\gamma z+\omega\theta_\varepsilon)^2}{a}
-\frac{(k\alpha_0+g+c\theta_\varepsilon+\gamma z)^2}{H}.
\end{aligned}
$$

This is a lower for the specified paid comparison. It is not a lower
for an actual center with a smaller justified charge, and an all-real
bound does not assert physical admissibility of every $\alpha$.

The coefficient of $\theta_\varepsilon^2$ is

$$
-\frac1b+\frac{\omega^2}{a}-\frac{c^2}{H}
=-\frac{t}{ab}-\frac{c^2}{H}\le0.
$$

Thus its minimum over the certified $\theta_\varepsilon$ interval,
for each $z$, occurs at one of its two endpoints. If in addition
$k-g^2/b>0$, the $z^2$ coefficient is positive:

$$
A_z=\gamma^2\left(\frac1a-\frac1H\right)>0,
\qquad H-a=k-g^2/b.
$$

Each endpoint leaves one convex quadratic
$A_z z^2+2B_z z+C_z$ on the saved $[z_{\rm lo},z_{\rm hi}]$.
Take directed rational $0<A_{\rm lo}\le A_z$, $C_{\rm lo}\le C_z$
and $B_z\in[B_{\rm lo},B_{\rm hi}]$. Put

$$
B_m=(B_{\rm lo}+B_{\rm hi})/2,\quad
B_r=(B_{\rm hi}-B_{\rm lo})/2,\quad
Z=\max\{|z_{\rm lo}|,|z_{\rm hi}|\}.
$$

For every allowed $z$, a common lower is

$$
A_{\rm lo}z^2+2B_mz+C_{\rm lo}-2B_rZ.
$$

Its minimum occurs at the exact rational

$$
z_* = \max\{z_{\rm lo},\min\{z_{\rm hi},-B_m/A_{\rm lo}\}\}.
$$

Evaluate this lower at $z_*$ and take the smaller result from the two
$\theta_\varepsilon$ endpoints. All finite-parameter errors remain
included. No endpoints are asserted simultaneously attainable, and
$z_*$ belongs only to a bounding quadratic, not a constructed actual
source or physically legal steering parameter. If the required
positive denominators or curvature cannot be certified, this consumer
supplies no new floor.

The fixed1024-working/640-export application gives the following
outward displays. Exact rational lower certificates and640-bit
endpoints remain authoritative.

| Quantity | Enclosure or directed bound |
|---|---:|
| Transported $\theta_\varepsilon$ |contained in[−4.331314,−4.325974]|
| Saved $\zeta$ |contained in[−8.423007,0.178344]|
| Theta transport error upper |<1.590332e-26|
| Positive-plane energy $a$ |>1629.238166139474|
| Fixed comparison curvature $H$ |>19789.907603158162|
| Fixed rank gap $k-g^2/b$ |>18160.669437018688|
| Previous fixed all-real lower, rounded down |−0.572919446|
| New fixed all-real lower, rounded down |−0.484608778|
| Previous energy-endpoint all-real lower, rounded down |−0.779703304|
| New energy-endpoint all-real lower, rounded down |−0.687084970|

Both lower certificates strictly improve, while both exclusion flags
remain false. The four scalar bounding quadratics, one per theta
endpoint and recipe, select the saved lower zeta endpoint. This
identifies the worst endpoint of these bounding polynomials; it
constructs no source realizing that endpoint or a negative paid value.

The improvement comes from retaining the positive plane and its common
response relations, with the original working precision and saved
suppliers. It does not determine the actual paid sign. It leaves open whether further source-image or residual information
can settle that sign. No claim is made that any one new scalar
necessarily suffices.

The single application binds12 invoked and66 inherited paths and
performs two joint-plane applications, each with two analytic theta
endpoints. Stored assembly time is<0.133236seconds, excluding
serialization. It repeats no old scientific producer or passed
fixture.


The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/82e2d6241886e2c19355ebecfa19c3e261369a78/docs/reports/weil-c27)
retain packet SHA256 `3bdf5f3f81daeeda99c5fa71f2a48ee64c84c09da0f20070b45b0ad781aeec22` and source SHA256
`fb6ae6eb627079e43628481bae7e2b9485077ab22bac7c85b4bcf12994f1b3b9`. The consumer applies this saved-scalar bound
to the fixed current $(k,D)$ and the already saved energy-endpoint
$(k_{\min},D_{\min})$. Every stronger previous floor remains retained.
A strictly positive endpoint floor excludes only the fixed monotone
energy-cap-only pricing family because every one of those comparisons
has $k\ge k_{\min},D\ge D_{\min}$, with the same actual row and other
premises. A nonpositive lower is inconclusive and constructs no
negative row or upper.

No finite direction, feature, Gram, cross, source, derivative, inverse,
solve, sine, moment, tail, trace or pricing supplier is repeated.
There is no source/parameter/precision/cutoff scan or retry. The
original actual-form/domain, common source/lift, reference, inverse,
weight and actual-symbol physical-error certificates remain premises.
This reuses standard indefinite projection, concavity and scalar
quadratic minimization; it claims no generic theorem, novelty or Lean
proof. Actual-center/full-border/good-block/cofinal positivity, Robin
and RH remain unresolved.


### Recover a source response from saved finite outputs

The previous response interval uses common Hilbert norms and a signed
old/new Gram. The original computation also retains the complete finite
Cauchy output and old approximate jet on modes $M+1$ through $2M$,
$M=32768$. These are stronger observations of the same source. Reuse them
before asking for another source, elementary sine or tail-moment supplier.
The new interface applies ordinary algebra and polynomial interpolation;
it asserts no new generic inequality or algorithm.

Keep the original real weighted space $W_F=w_FI$, $\kappa=33/32$, and

$$
u_F=v+r+C_{\rm phys}\ell,\qquad
v_m=\frac{(-1)^m}{2}C(m),\qquad
C(m)=\sum_{n=1281}^{M}\frac{z_n}{m+n},\qquad
\sum_n|z_n|\le Z.
$$

The saved source intervals and the exact384-bit source integers define
these same $z_n$. The smooth remainder has its existing bound
$\|r\|_{W_F}\le\epsilon_{\rm sm}$. Retain the old and zero-coordinate
directions $b=\mathsf Bv_b,d=\mathsf Bv_d$, with complete short features
$h_b,h_d$. Their actual jets are

$$
j_h(m)=\frac{2(-1)^m}{\pi m}
\left[xB_h(x^2)-s_mA_h(x^2)\right],\qquad x=M/m.
$$

The desired response is $\zeta=\kappa\langle u_F,d\rangle_{W_F}$.
The physical source, lift, reference form, weights and errors remain
unchanged. No relation between independently chosen interval endpoints
is asserted.

#### Eliminate the shared approximate symbol

The stored old finite jet $\widetilde j_b(m)$ uses the original
approximate symbol $\widetilde s_m$. It is not the actual physical
operator. All its coefficient and output uncertainty is retained.
For $0\le t\le1$, a coefficient bound supplies

$$
|A_b(t)|\ge
|h_{b,A_0}|-\sum_{k=1}^{55}|h_{b,A_k}|>0.
$$

Consequently each already saved finite jet determines an enclosing
interval for the SAME approximate symbol by

$$
\widetilde s_m=
\frac{xB_b(x^2)-\pi m(-1)^m\widetilde j_b(m)/2}{A_b(x^2)}.
$$

Use it with $h_d$ and the already saved $C(m)$ to evaluate one new
finite functional

$$
\widetilde\mu_{d,\rm fin}
=\frac{\kappa w_F}{\pi}
\sum_{m=M+1}^{2M}\frac{C(m)}m
\left[xB_d(x^2)-\widetilde s_mA_d(x^2)\right].
$$

This is a new contraction of old outputs. It does not repeat their
Cauchy convolution, old jet evaluation or elementary sine evaluations.
Failure to certify the nonzero denominator stops this interface;
there is no midpoint division or precision retry.

#### A tail interpolation from the same saved source outputs

Set $U(x)=\sum_nz_n/(1+(n/M)x)$, so that $C(m)=U(M/m)/m$.
Use exactly13 saved sample modes

$$
m_i=M+1+\left\lfloor\frac{i(M-1)}{12}\right\rfloor,
\quad x_i=M/m_i,\quad U_i=m_iC(m_i),\quad 0\le i\le12.
$$

Their rational nodes satisfy $1/2\le x_i<1$ and are distinct. Let
$P_{12}$ be their explicit Lagrange interpolation polynomial. Every
coefficient retains the saved sample uncertainty, including its
amplification by the interpolation bases.

Apply the classical reciprocal-kernel difference formula in Carl de Boor,
[*Divided Differences*](https://arxiv.org/abs/math/0502036v1),
section7 Example8 equations(38)–(39), together with the interpolation
remainder in section1 Example6 equation(16). With $a_n=n/M\in(0,1]$,

$$
U(x)-P_{12}(x)=
(-1)^{13}\prod_{i=0}^{12}(x-x_i)
\sum_n\frac{z_na_n^{13}}
{(1+a_nx)\prod_{i=0}^{12}(1+a_nx_i)}.
$$

For one kernel $1/(1+ax)$, multiply its interpolation error by
$1+ax$. The resulting degree13 polynomial vanishes at every $x_i$;
evaluation at $x=-1/a$ determines its leading factor as
$(-a)^{13}/\prod_i(1+ax_i)$. Summing over the signed source coefficients
gives the displayed identity. This uses no positivity of those coefficients.

For $0\le x\le1/2$, each $|x-x_i|\le x_i$, and
$a/(1+ax_i)$ increases on $0\le a\le1$. Thus

$$
|U(x)-P_{12}(x)|\le
E_U:=Z\prod_{i=0}^{12}\frac{x_i}{1+x_i}.
$$

This bound uses signed source coefficients through their absolute sum;
it assumes neither positivity nor a fitted empirical remainder.
For $m>2M$, replacing $C(m)$ by $P_{12}(M/m)/m$ therefore has weighted
principal-source error at most

$$
\delta_v=\frac{\sqrt{w_F}E_U}{2\sqrt{2M}},
$$

because $\sum_{m>2M}m^{-2}\le(2M)^{-1}$. The finite band is unchanged.
The old source-power polynomial was not retained and is not regenerated;
this polynomial is obtained directly from the saved outputs.

#### Reuse the saved real kernels and physical errors

Write $L(x)$ for the original approximate smooth symbol polynomial,
and set

$$
F_0=P_{12}\bigl(xB_d(x^2)-L(x)A_d(x^2)\bigr),\qquad
F_1=P_{12}A_d(x^2).
$$

The original archived real kernels use the normalization

$$
K_q=M^{q-1}\sum_{m\ge2M+1}m^{-q}.
$$

Their saved range covers every coefficient used here. The nonoscillatory
tail term is exactly

$$
\widetilde\mu_{d,\rm tail}
=\frac{\kappa w_F}{\pi M}\sum_p(F_0)_pK_{p+2}.
$$

The existing phase-gap cap and Abel estimate bound the omitted oscillatory
part by

$$
R_{\rm osc}=\frac{2\kappa w_F}{\pi(2M+1)^2}
\left[\sum_p|(F_1)_p|\left(\frac M{2M+1}\right)^p\right]
\mathrm{PhaseCap}.
$$

No new phase, logarithm, sine or Hurwitz kernel is supplied.
The global approximate-symbol error still has to be paid. The inherited
uniform symbol allowance gives a jet error $\beta_d$; use the original
Hilbert error contract

$$
R_{\rm fun}=\kappa\left[J_d\delta_v+(P+\delta_v)\beta_d\right],
\quad J_d\ge\|j_d\|_{W_F},\quad P\ge\|v\|_{W_F}.
$$

Here $J_d$ denotes a norm upper, rather than the squared-norm upper used
in the earlier Gram sections. In this application it is bounded by the
saved physical norm plus the saved sharp forward error. Thus the actual
principal pairing is enclosed by the finite and nonoscillatory terms
with radius $R_{\rm fun}+R_{\rm osc}$.

For the mixed source, reuse the saved $a=P_0\ell$ and weighted physical
kernel $K_0$. One new cached action $a^TK_0$, followed by its contraction
with $h_d$, supplies $\kappa a^TK_0h_d$. Its physical Gram error is paid
using the original homogeneous error coefficient and the saved lift
norm. Add the separate smooth and proxy-forward allowances. The kernel
already contains the original far weight and is not assumed PSD.
These operations give an enclosure of the actual $\zeta$; intersect it
with the previous interval and stop on inconsistency.

The fixed1024-working/640-export application gives the following
outward displays; the packet's exact rational bounds and640-bit
interval endpoints remain authoritative.

| Quantity | Enclosure or directed bound |
|---|---:|
| Nonzero old $A_b$ absolute lower |$>1037.446293$|
| Source absolute-sum upper $Z$ |$<2161.865701$|
| Uniform interpolation error $E_U$ |$<0.016074441$|
| Principal-source tail norm error $\delta_v$ |$<0.000017270703$|
| Functional interpolation/symbol error $R_{\rm fun}$ |$<0.000066044862$|
| Oscillatory tail allowance $R_{\rm osc}$ |$<0.000584639478$|
| Physical mixed error allowance |$<4.458569\times10^{-65}$|
| Smooth remainder allowance |$<5.240841\times10^{-12}$|
| Proxy forward allowance |$<3.723887\times10^{-67}$|
| Previous $\zeta$ |contained in$[-8.423006305,0.178343401]$|
| New $\zeta$ |contained in$[-7.591449537,-7.590148168]$|
| Previous fixed all-real lower, rounded down |$-0.484608778$|
| Retained fixed all-real lower, rounded down |$-0.472489776$|
| Previous energy-endpoint all-real lower, rounded down |$-0.687084970$|
| Retained energy-endpoint all-real lower, rounded down |$-0.674685242$|

The actual same-source response interval is strictly narrower, and both
retained paid lower bounds strictly improve. Both exclusion flags remain
false. All four saved bounding quadratics select the new lower zeta
endpoint; this constructs no source realizing that endpoint and supplies
no negative actual paid value. Even after the response is localized to
this narrow negative interval, these particular paid estimates do not
establish positivity. Further sharpening of this scalar alone has not
been shown sufficient.

The application binds16 invoked and66 inherited paths. Stored assembly
time is<1.118949seconds, excluding serialization. The old producers and
accepted fixtures are reused without replay.

The reusable packet retains the recovered approximate finite symbols,
13 interpolation coefficients and nodes, and physical left-kernel
action. They remain observations and enclosures of the same source;
they do not identify arbitrary interval choices with realizable rows.
The [source, exact packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/d4741a6243a16170ee2634c7cb6e9f18fc34fb0c/docs/reports/weil-c27) retain source
SHA256 `da93886e4aa00ef58ab4c446486c671996f6f22eaed8d251b7fa8d6d064d94d2` and packet SHA256 `2f6fa2f46f91dfa0449d5bec2523cdbd91a0e7587284f8e417ccb5bd2068ee03`.

The application uses one fixed13-node interpolation and the original
finite band, at1024 working/640 export bits. It repeats no old producer
or accepted fixture and performs no source/parameter/precision/cutoff
scan. It reuses the previous plane bound with the new response interval
and the same saved transported theta and actual-row positive-energy
upper. Stronger earlier floors remain retained. A positive paid floor
would exclude only the specified recipe or monotone pricing family;
a negative lower remains inconclusive for its actual sign. No claim is
made about an actual smaller-charge center, full-border or cofinal
positivity, Robin or RH. This is an application of known interpolation,
scalar algebra and the existing physical certificates; no generic
theorem, novelty or Lean proof is asserted.


### Bound the value of further response-only refinement

The cached-source response is now localized, but both paid lower
certificates remain negative. Before requesting a narrower response,
keep the same source, finite parameters, transported-theta endpoints,
prices and directed quadratic coefficients. Only a nonempty closed
subinterval $J\subseteq I=[z_-,z_+]$ may change, including a singleton.
This restriction defines the certificate algorithm being tested; it
places no new restriction on the actual source.

For each saved theta endpoint $e$ and each of the two saved recipes,
write its rational coefficient lower model as

$$
q_{e,J}(z)=A_ez^2+2B_ez+C_e-2R_e\sup_{u\in J}|u|,
\qquad A_e>0,\quad R_e\ge0.
$$

Whenever the actual response also satisfies $\zeta\in J$, the
previous derivation gives a valid LOWER certificate

$$
L(J)=\min_e\min_{z\in J}q_{e,J}(z).
$$

The algebraic ceiling below holds for every such subinterval, including
ones that are not established to contain the actual response. Those
unjustified subintervals do not supply actual energy lower bounds.

Removing the nonnegative linear-radius debit gives the more optimistic
polynomial $p_e(z)=A_ez^2+2B_ez+C_e$. For every $z\in I$, write
$z=(1-t)z_-+tz_+$, $0\le t\le1$. Direct expansion yields

$$
p_e(z)=(1-t)p_e(z_-)+tp_e(z_+)
-A_et(1-t)(z_+-z_-)^2
\le U_e:=\max\{p_e(z_-),p_e(z_+)\}.
$$

Thus, for EVERY allowed refinement, without choosing its endpoints,

$$
L(J)\le\min_eU_e.
$$

If $L_0$ is the already retained lower certificate for that recipe,
retaining it after a refinement gives

$$
\boxed{
\max\{L_0,L(J)\}
\le C_{\rm cert}:=\max\{L_0,\min_eU_e\}.
}
$$

The right side bounds the output strength of this unchanged LOWER
certificate algorithm. It is not an upper bound for the actual energy,
a constructed negative row or an exclusion of the paid family itself.
A strictly negative $C_{\rm cert}$ excludes positive certification by
response-only narrowing, even with exact knowledge of the response.
A nonnegative ceiling leaves this diagnostic inconclusive. Recomputing
coefficients, changing theta constraints, prices, projections or joint
source information lies outside this statement.

The exact-rational application gives the following directed displays.
Lower certificates round down; certificate CEILINGS round up. The
saved fractions remain authoritative.

| Quantity | Fixed recipe | Energy-endpoint recipe |
|---|---:|---:|
| Current retained lower, rounded down |$-0.472489776$|$-0.674685242$|
| Optimistic ceiling at lower theta endpoint |$<-0.472470198$|$<-0.674665225$|
| Optimistic ceiling at upper theta endpoint |$<-0.460850945$|$<-0.663035940$|
| Retained scalar-refinement certificate ceiling |$<-0.472470198$|$<-0.674665225$|

Both recipe flags are true: with the specified coefficients and all
other inputs fixed, no response-only interval refinement can make
these lower certificates positive. This includes a hypothetical exact
response and even waives the nonnegative linear-radius debit. The
result does not exclude actual paid positivity or yield a negative
physical source. It gives no restriction on a new bound that changes
the projection, directed coefficients, prices or joint source
constraints.

The single exact-rational application stores assembly time<0.041523
seconds, excluding serialization. Its eight endpoint evaluations and
two retained caps are new; the original plane and source suppliers
are not repeated.

The [source, exact rational packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/b4c455e129b6958ab07493ce78847369b5c56f16/docs/reports/weil-c27)
retain source SHA256 `bc523a5b5392e37f6cbcbb8da27151a39cd3f2e216633e01bb51ff03cd1e1baf` and packet SHA256
`f4e444527b6e471b710734e702d9d31067a73eac59cab985a358900213729f1a`. The new application reads only the accepted response
packet and uses exact rational endpoint arithmetic. It performs eight
new polynomial endpoint evaluations and two recipe caps, with no
plane-floor call, old scientific producer/accepted fixture replay or
parameter/source/precision/cutoff scan. This applies elementary
convexity; no generic theorem, novelty or Lean proof is claimed.

#### A source-dependent complement is a different missing supplier

The preceding ceiling does not constrain an improved projection using
new joint information. To specify one such missing quantity, keep the
SAME actual finite form $Q=Q_\varepsilon$, $b=-Q(y_0,y_0)>0$ and
$v=\rho+(g/b)y_0$, with $a=Q(v,v)>0$. In this subsection write
$\theta:=Q_\varepsilon(f,y_0)=\theta_\varepsilon$ for the transported
response, rather than the earlier $Q_R$ response. Set

$$
s=Q(f,v)=\gamma\zeta+\omega\theta,\qquad
f_\perp=f+(\theta/b)y_0-(s/a)v.
$$

Then $f_\perp$ is $Q$-orthogonal to $y_0,v$. Under the inherited
negative-index-one contract its complement is nonnegative, and

$$
Q(f,f)=-\theta^2/b+s^2/a+R,\qquad
R=Q(f_\perp,f_\perp)\ge0.
$$

Reuse the full comparison before projection, not merely its weaker
lower bound $\mathcal E_{D,k}\ge F$. For $u=\alpha-\alpha_0$ and
$x=y_0+f+u\rho$, the existing actual-form comparison is

$$
\mathcal E_{D,k}(\alpha)\ge k\alpha^2+D+Q(x,x).
$$

Keep $H=k+h>0$ and $A_0=k\alpha_0+g+c\theta+\gamma\zeta$.
The exact square completion is

$$
k\alpha^2+D+Q(x,x)
=H\left(u+\frac{A_0}{H}\right)^2+F(\theta,\zeta)+R.
$$

The old projection discards $R$. Since steering by $\rho$ stays in
the retained plane, the same residual remains after minimizing the
real steering coefficient, so

$$
\mathcal E_{D,k}(\alpha)\ge F(\theta,\zeta)+R.
$$

Consequently an independently certified common-source lower
$R\ge r>0$ with $L(I)+r>0$ would make that paid comparison positive
for every real steering coefficient. This condition is sufficient;
no positive $r$ is supplied here, and it is not a necessary condition
for positivity of the actual comparison. Here $L(I)$ must lower this
same $F$; the residual cannot be added to a separate earlier bound
whose derivation did not retain this decomposition.

For a concrete further real reference row $e$ in this controlled form
domain, remove its SAME-plane
components:

$$
e_\perp=e+\frac{Q(e,y_0)}b y_0-\frac{Q(e,v)}a v,
\qquad T=Q(e_\perp,e_\perp)>0.
$$

On the nonnegative complement, the standard Cauchy inequality gives

$$
R\ge\frac{|Q(f,e_\perp)|^2}{T},
$$

with the common-source cross

$$
Q(f,e_\perp)=Q(f,e)+\frac{\theta}bQ(y_0,e)
-\frac{s}aQ(v,e).
$$

Thus a common-realization enclosure $\ell\in[\ell_-,\ell_+]$ for
this cross and a positive upper $T\le T_{\rm up}$ would supply
$r=\operatorname{dist}(0,[\ell_-,\ell_+])^2/T_{\rm up}$, provided
the actual $T>0$ and all original form/source/physical conditions hold.
If the cross interval contains zero this route supplies only $r=0$.
The additional signed source response and the nondegenerate complement
row are missing; assigning independent interval endpoints or naming a
nonnegative residual does not supply either. A counterexample row from
the older scalar relaxation lay in the retained plane and had $R=0$;
its already documented exclusion does not prove a positive lower for
the actual source's residual.

This is the existing negative-index-one projection and Cauchy argument
applied to a stated missing interface. It neither constructs a new
physical row nor proves actual paid/center/full-border/good-block or
cofinal positivity, Robin or RH.


#### Use the saved raw-coordinate cap as a complement response

The existing absolute-coordinate certificate can be tested against the
same projection without supplying a new physical far row. Keep the real
finite form and all common-source/domain assumptions above. In the
original block factorization, the tail of $T$ is the identity and its
first row is $-\Sigma_{0,\mathrm{tail}}/\Sigma_{00}$. Therefore the real row

$$
n=(1,\Sigma_{0,\mathrm{tail}}/\Sigma_{00})
$$

satisfies $Pn^*=0$ and $n[0]=1$. With $\delta=-\Sigma_{00}>0$, define
$\xi=-\delta n$. Since $Q=\gamma P-e_0e_0^*/\delta$,

$$
Q\xi^*=e_0,\qquad Q(\xi,\xi)=-\delta,\qquad Q(f,\xi)=f[0].
$$

This is a reference row in the same full finite real form domain; it is
not asserted to be a new source-generated far row. Write
$\lambda=y_0[0]$ in the RAW original coordinate, so $v[0]=\lambda\omega$.
Removing the same $y_0,v$ components gives

$$
\begin{aligned}
T_\xi&=Q(\xi_\perp,\xi_\perp)
=-\delta+\frac{\lambda^2}{b}-\frac{\lambda^2\omega^2}{a}
=-\delta+\frac{\lambda^2t}{ba},\\
\ell_\xi&=Q(f,\xi_\perp)
=f[0]+\lambda\left(\frac{t\theta}{ba}
-\frac{\gamma\omega\zeta}{a}\right).
\end{aligned}
$$

Here $\theta=\theta_\varepsilon$ is still the transported response.
The accepted cap $C\ge|f[0]|$ and $\lambda$ use the same raw units,
with no division by $\sqrt\delta$. This follows from the saved
$\lambda=\alpha_0\rho[0]+\beta_J[0]$ definition and the original
homogeneous coordinate-cap derivation. A cap for source energy would
not be interchangeable with $C$.

Let $I_d$ enclose the second term of $\ell_\xi$ using the saved
common-source responses and shared finite parameters. Then
$I_\ell=[-C,C]+I_d$ encloses the actual $\ell_\xi$. Under a certified
$0<T_\xi\le T_{\xi,\mathrm{up}}$, the preceding PSD Cauchy estimate gives

$$
r_\xi=\frac{\operatorname{dist}(0,I_\ell)^2}{T_{\xi,\mathrm{up}}}
\le R.
$$

The implementation requires a strictly positive directed lower for
$T_\xi$ before division. A zero-containing cross gives $r_\xi=0$;
an unresolved norm sign also supplies no positive gain. Algebraic
identities come from the same reference form, not overlap of separately
evaluated scalar intervals.

For each paid recipe let $L_F$ be the saved lower for precisely the
$F$ in the full $F+R$ decomposition. The augmented lower is $L_F+r_\xi$;
only afterward take its maximum with the previously retained lower.
Adding $r_\xi$ directly to an unrelated older lower would not follow
from that decomposition.


The single saved-scalar application certifies that this projected
coordinate direction is nondegenerate, but its cross interval contains
zero:

| Quantity | Outward range or exact result |
|---|---|
| $T_\xi$ | $[3.460702373153308560,3.460702373153308561]\cdot10^{-31}$ |
| $I_d$ | contained in $[-2.135953295,-2.133377122]\cdot10^{-16}$ |
| $I_\ell$ | contained in $[-6.503116871,2.233786454]\cdot10^{-16}$; exact saved interval contains0 |
| Certified $r_\xi$ | $0$ |
| Fixed retained lower | unchanged, $-0.472489775052793370265\ldots$ |
| Energy-endpoint retained lower | unchanged, $-0.674685241069653953208\ldots$ |

Thus this use of the saved absolute coordinate cap supplies no positive
residual gain. It does not show that the actual residual is zero or
that an actual paid energy is negative.

The entire saved $I_d$ is inside $[-C,C]$, where the accepted cap is
$C>4.367163575891468984\cdot10^{-16}$. To see the resulting limitation
of these particular observations, use the exact common plane row

$$
f_H=-\frac{\theta}{b}y_0+
\frac{\gamma\zeta+\omega\theta}{a}v.
$$

It satisfies $Q(f_H,y_0)=\theta$ and $P(f_H,w)=\zeta$; the latter
follows from $w=v-\omega y_0$ and $w[0]=0$. It also has
$f_H[0]=-d$ and $R(f_H)=0$. Consequently the two responses and this
absolute-coordinate cap ALONE permit zero residual for every common
realization covered by these enclosures. This does not assert that
$f_H$ satisfies every earlier scalar constraint, a paid sign or the
original source-to-row image condition. A positive residual lower for
the actual source still needs a noncancellation relation for
$f[0]+d=f_\perp[0]$, or another residual direction.

The [source, directed interval packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/d7497eef7232569ed88113c4d1cdc7e2ec7342ef/docs/reports/weil-c27)
retain source SHA256
`47f34f89cfddfecb581fe626415d303df64de0b5c5004935ebfb0c42285c0a19`
and packet SHA256
`7f6c5d4dc3175e4cd508aadef54d65588bf4c003fddfd01f1c22f8b1748198bb`.
The one1024-working/640-export application stores assembly time<0.580244
seconds, excluding serialization. It reads four accepted scalar
packets, makes one coordinate-complement application and two lower
additions, with no old plane-floor/source/matrix/inverse/solve/tail
supplier or accepted scientific fixture replay and no parameter,
source, precision or cutoff scan/retry.

This applies the existing projection and PSD Cauchy inequality. No new
generic theorem, literature novelty or Lean proof is claimed. All
original common-form, source-energy and physical-error premises remain;
actual paid/center/full-border/good-block/cofinal positivity, Robin and
RH remain unresolved.


#### Supply a signed raw coordinate from the same cached source

The missing observation can be supplied without regenerating the source.
Keep the original physical map $f=\kappa u_F^*W_FB$ with $B=R_FV$ and
$\kappa=33/32$. Let $e_0$ be the first coordinate of the same18-column
lift, $b_0=Be_0$, and $h_0=(P_0D_{\rm phys}V)e_0$. Then

$$
f[0]=\kappa\langle u_F,b_0\rangle_{W_F}.
$$

This is the raw coordinate used above, with no division by $\sqrt\delta$.
The saved full physical Gram bound supplies
$N_0=\sqrt{G_{00,\mathrm{up}}}\ge\|b_0\|_{W_F}$; its original weight
already belongs to $W_F$ and it contains no $\kappa$ factor. The lift
cap is $L_0=\sqrt{(V^*V)_{00}}$. The accepted forward and mixed-error
certificates are uniform coefficients times a lift norm cap. Their
transport by $L_0/L_b$ therefore applies to this new direction;
it is not an empirical scaling of an error measured on one vector.

Use the stored approximate symbols, source interpolation polynomial
and left physical-kernel action on the first feature column. The
finite principal pairing and analytic tail are evaluated only for
this new column. The mixed term is one new112-component dot product
of the stored left-kernel row with $h_0$, multiplied once by $\kappa$.
No kernel positivity is assumed.

Write $N_{\mathrm{pr}}$ for the saved principal-source norm cap, $\Delta$ for the
saved source-tail interpolation error, $\epsilon_0$ for the transported
physical forward error and $\epsilon_{\rm sm}$ for the saved smooth
source remainder. If $A_{0,k}$ are the new first-column
jet coefficients and $\sigma$ is the original uniform symbol error,
the new symbol-jet allowance is

$$
\beta_0=\operatorname{UP}\frac{2\sqrt w\,\sigma}{\pi\sqrt M}
\sum_{k=0}^{55}|A_{0,k}|\left(\frac M{M+1}\right)^{2k},
\qquad M=32768.
$$

The actual-symbol jet norm is at most $N_0+\epsilon_0$. Consequently
the source/symbol allowance is

$$
\kappa\bigl((N_0+\epsilon_0)\Delta+(N_{\mathrm{pr}}+\Delta)\beta_0\bigr).
$$

Pay the new analytic-tail Abel allowance and transported two-sided
physical mixed error separately, together with
$\kappa\epsilon_{\rm sm}N_0$ and $\kappa N_{\mathrm{pr}}\epsilon_0$.
The approximate symbols are not substituted for actual symbols
without this allowance. The smooth polynomial uses its640-bit export
grid; the uniform symbol error uses its832-bit analytic grid.

Intersect the resulting signed interval $I_0$ with the original
$[-C,C]$. The same-source residual observation is now
$I_{\ell,\mathrm{new}}=(I_0+I_d)\cap I_\ell$, using the SAVED plane
offset and complement norm. An empty intersection stops the application.
With the inherited positive norm certificate, reuse

$$
R\ge r_{\xi,\mathrm{new}}=
\frac{\operatorname{dist}(0,I_{\ell,\mathrm{new}})^2}
{T_{\xi,\mathrm{up}}}.
$$

As before, add this only to the lower of the SAME $F$, then take the
maximum with the previously retained lower. Signed-coordinate
separation, residual gain and paid positivity are separate tests.


The single1024-working/640-export application gives these outward
results; exact saved fractions remain authoritative:

| Quantity | Directed range or lower certificate |
|---|---|
| Raw $f[0]$ | $[2.200218370,2.201145838]\cdot10^{-16}$ |
| New $f_\perp[0]$ enclosure | $[6.426507665,6.776871553]\cdot10^{-18}$ |
| Residual lower $r_{\xi,\mathrm{new}}$ | $\ge0.0001193399383345589672>0$ |
| Fixed retained lower | $\ge-0.472370436$; exact saved lower is still negative |
| Energy-endpoint retained lower | $\ge-0.674565902$; exact saved lower is still negative |

Both paid recipes improve by the same saved residual lower, but neither
certificate is positive. Under the inherited common-source/form and
physical-error premises, this additional signed observation rules out
zero residual for the actual row in this direction. It does not assert
that every row satisfying the older observations has positive residual;
the older zero-residual plane construction remains valid for those
older observations alone. A negative retained lower does not establish
negative actual paid energy.

The source and packet retain SHA256
`a8f9133a4dd8a574fc9a3b7db27cfc1e2d9722764b444fc31cdd636fcd653a12`
and
`12cd1ff9de20ab9083d27ddae812d415ec37c95520de619a6f9813304c2081a5`.
Assembly time is<1.073261seconds, excluding serialization. The consumer
reads ten accepted packets, makes one new finite principal functional,
one new cached analytic-tail application and one new short mixed dot.
It makes no source recovery/interpolation, physical left-kernel action,
quadratic/matrix/inverse/solve/moment/sine/phase supplier or plane-floor
call. No old producer or accepted scientific fixture is replayed;
there is no parameter/source/precision/cutoff scan or retry.

This is a new source-specific application of the existing projection,
error transport and PSD Cauchy argument, with no new generic theorem,
literature novelty or Lean claim. Actual paid/center/full-border/good-block
and cofinal positivity, Robin and RH remain unresolved.

The [source, directed interval packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/3366fa48c777581c99fdb0d5c132b1615285cfd0/docs/reports/weil-c27) retain this application and its original input bindings.


#### Replace one coordinate by the complete same-source far row

Further precision on a single coordinate cannot supply arbitrary
residual gain. Keep the saved cross interval $I_\chi$ and positive
norm interval $[T_{\xi,\mathrm{lo}},T_{\xi,\mathrm{up}}]$. Set
$U_\chi=\max_{x\in I_\chi}|x|$. For any justified refinement $J$ and
norm upper $T_{\mathrm{up,new}}$ enclosing the SAME actual quantities,

$$
\frac{\operatorname{dist}(0,J)^2}{T_{\mathrm{up,new}}}
\le C_\xi:=\frac{U_\chi^2}{T_{\xi,\mathrm{lo}}}.
$$

Indeed $\operatorname{dist}(0,J)\le|f_\perp[0]|\le U_\chi$ and
$T_{\mathrm{up,new}}\ge T_\xi\ge T_{\xi,\mathrm{lo}}>0$.
With the SAME saved plane lower $L_F$ and all other inputs fixed,
the retained LOWER certificate can therefore be no greater than
$\max\{L_{\mathrm{previous}},L_F+C_\xi\}$. This bounds the strength
of this one-coordinate certificate; it is not an upper bound on the
actual residual or paid energy. A negative ceiling rules out positive
certification by that refinement alone, including exact knowledge of
the coordinate and its dual norm.

The full fixed row is a different observation. Keep
$f=\kappa u_F^*W_F B$ in its original18-coordinate lift. The first
coordinate is already saved. Each remaining original basis column is
now supplied once from the SAME accepted source caches, yielding a
joint containing box for $f$. Completeness here means all18entries in
this fixed reduced lift; the unbounded support/source family remains
separate. This constructs no new source and makes
no assertion that independently chosen box endpoints are jointly
attainable. Shared source and error terms do not invalidate a containing
box; evaluating the finite expressions on that box remains conservative.

For each $j=1,\ldots,17$, use the saved feature column $h_j$, lift norm
cap $L_j=\sqrt{(V^*V)_{jj}}$, and physical norm cap

$$
N_j=\sqrt{(G_{\mathrm{far,up}})_{jj}}\ge\|Be_j\|_{W_F}.
$$

The accepted FULL physical Gram Loewner majorant supplies each diagonal
bound. Its original weight is already included, with no factor of
$\kappa$. Reuse the established symbol/source/forward/smooth/mixed
allowances on the new columns, including each new Abel allowance.
The uniform physical errors scale by the SAME $L_j/L_b$ contract.
The stored left-kernel row supplies all17 mixed centers in one matrix
product. The masked kernel is not assumed PSD. Coordinate0 is reused
without another finite or analytic-tail evaluation.

Let $R_{\mathrm{ref}}$ be the saved positive reference inverse and use
the original elimination map $T$, whose first row is
$-\Sigma_{0,\mathrm{tail}}/\Sigma_{00}$ and whose tail is the identity.
Keep

$$
P=TR_{\mathrm{ref}}T^*,\quad
\delta=-\Sigma_{00}>0,\quad
Q=Q_\varepsilon=\gamma P-e_0e_0^*/\delta\le Q_{\mathrm{true}}.
$$

This is the SAME lower comparison form, rather than a newly computed
inverse. The finite rows $\rho,\beta_J$, reference $\alpha_0$ and
$y_0=\alpha_0\rho+\beta_J$ remain unchanged. With $z=fT$, one new
reference action $R_{\mathrm{ref}}z^*$ supplies three contractions:

$$
\begin{aligned}
p_{ff}&=zR_{\mathrm{ref}}z^*,\\
p_{fy}&=(y_0T)R_{\mathrm{ref}}z^*,\\
p_{f\rho}&=(\rho T)R_{\mathrm{ref}}z^*.
\end{aligned}
$$

They give the joint same-source observations

$$
\begin{aligned}
q_{ff}&=Q(f,f)=\gamma p_{ff}-f[0]^2/\delta,\\
\theta_*&=Q(f,y_0)=\gamma p_{fy}-f[0]y_0[0]/\delta,\\
r_*&=Q(f,\rho)=\gamma p_{f\rho}-f[0]\rho[0]/\delta.
\end{aligned}
$$

These use the raw coordinate with its original $\kappa$ factor.
The new $\theta_*$ encloses the SAME actual transported response;
it is supplied directly from the full row and comparison form.
Saved-interval overlap checks detect inconsistencies. The shared
source/form construction supplies the identities; overlap alone does
not establish them.

Reuse $b=-Q(y_0,y_0)>0$, $g=Q(\rho,y_0)$, $h=Q(\rho,\rho)$ and
$a=h+g^2/b>0$. With $s_*=r_*+(g/b)\theta_*$, the complete positive
orthogonal residual is

$$
R_{\mathrm{full}}=q_{ff}+\theta_*^2/b-s_*^2/a\ge0.
$$

Its directed lower is combined with the saved coordinate residual
lower by a MAXIMUM, since both bound the SAME residual. Only afterward
is it added to the cached SAME-$F$ plane lower. The two residual
lower bounds are never added to each other.

There is also a direct route retaining the joint row throughout the
all-real steering completion. For $u=\alpha-\alpha_0$, the SAME
comparison quadratic is

$$
\begin{aligned}
k\alpha^2+D+Q(y_0+f+u\rho,y_0+f+u\rho)
={}&(k+h)u^2+2A_*u+C_*,\\
A_*={}&k\alpha_0+g+r_*,\\
C_*={}&k\alpha_0^2+D-b+2\theta_*+q_{ff}.
\end{aligned}
$$

Under $k+h>0$, its minimum over all real steering coefficients is
$C_*-A_*^2/(k+h)$. A directed interval lower gives another valid
lower for the original paid comparison. Keep the maximum of this
new direct lower, the complete-residual plane lower and the previous
retained lower. They are alternative lower estimates, not summands.
An upper endpoint for the minimum of this LOWER comparison form is
not an upper bound for the actual paid energy.

The single1024-working/640-export application separates three outcomes:
the saved-coordinate ceiling is negative for both retained recipes,
the complete fixed row is supplied, and this rectangular row enclosure
does not improve either paid lower. Exact saved fractions are
authoritative; the following displayed intervals are outward.

| Quantity | Directed range or lower certificate |
|---|---|
| Coordinate-only residual-certificate ceiling $C_\xi$ | $[0.000132707130189352722726116,\ 0.000132707130189352722726117]$ |
| Fixed coordinate-only retained-certificate ceiling | $[-0.472357067922604017542290,\ -0.472357067922604017542289]$ |
| Energy-endpoint coordinate-only retained-certificate ceiling | $[-0.674552533939464600486126,\ -0.674552533939464600486125]$ |
| Complete-row residual interval | contained in $[-7.352650,\ 7.352650]\cdot10^{194}$ |
| Retained residual lower | unchanged, $\ge0.0001193399383345589672$ |
| Fixed direct all-real lower | exact saved lower lies in $[-1.393700,\ -1.393699]\cdot10^{193}$ |
| Energy-endpoint direct all-real lower | exact saved lower lies in $[-1.398417,\ -1.398416]\cdot10^{193}$ |
| Fixed retained paid lower | unchanged; exact lower lies in $[-0.472370435114458811297816,\ -0.472370435114458811297815]$ |
| Energy-endpoint retained paid lower | unchanged; exact lower lies in $[-0.674565901131319394241652,\ -0.674565901131319394241651]$ |

Thus exact refinement of this one coordinate and its dual norm cannot
certify a positive paid lower while the other saved inputs are fixed.
This conclusion concerns the specified lower algorithm, not the actual
residual or paid energy. It does not exclude another joint observation
or a stronger plane lower.

The rectangular joint row remains a valid containing set, but it loses
useful accuracy under the reference contractions. All17 new raw
coordinate widths are at most $1.281033\cdot10^{-19}$. Their stored
finite-evaluation widths are below $2.490399\cdot10^{-43}$, whereas the
separately paid source and Abel allowances are on the $10^{-22}$ to
$10^{-20}$ scales. The resulting positive-reference quadratic interval
is contained in $[-5.871461,\ 5.871461]\cdot10^{96}$; even its sign is
not resolved by interval evaluation. The exact quadratic is nonnegative
under the inherited reference-form premises. Its wide interval does not
contradict that fact.

This diagnoses failure of the present rectangular error transport, not
negative actual energy or failure of the common source. Merely reducing
arithmetic roundoff while keeping these analytic error allowances and
the same rectangular contraction does not remove those allowances.
A stronger use of the row would need a justified estimate preserving
shared-source relations through the reference metric, or another
independently stronger bound. No such improvement is certified here,
and no retry or direction/precision/parameter scan is performed.

The source and packet retain SHA256
`74e900b9d40834c07bc2dc4fd7b37e1bb025542933a1c48073d08a8265bffc41`
and
`00b9e4bdd8a99da4d6fdafc696d313bd43e4060e1ba7d8cec316f7cc5bcb7707`.
The packet is42121bytes; assembly time is<9.746238seconds, excluding
serialization. It reads16 immediate accepted packets, reuses coordinate0,
and makes17 new finite functionals,17 new cached analytic-tail
applications, one17-output mixed product, one reference action, three
reference contractions and two direct minima. It makes no source
recovery/interpolation, physical left-kernel action, old reference
quadratic, inverse, solve or old plane-floor call. Accepted producers,
scientific helpers' tests and fixtures are not replayed.

This is a source-specific application of existing interval enclosure,
projection and scalar square completion, with no generic theorem,
literature novelty or Lean proof claim. All inherited common-source,
physical-error, reference-form and paid-comparison premises remain.
Actual paid/center/full-border/good-block and cofinal positivity, Robin
and RH remain unresolved.


The [source, directed interval packet and README](https://github.com/the-omega-institute/trureturing-experiments/tree/7f62b16b30d65c182492885e6f78bed549ffce06/docs/reports/weil-c27) retain the full fixed-row application and the original input bindings.


#### Bound the complete residual before another source query

The full-row rectangular enclosure does not require another source query
to obtain a sharper residual UPPER. Reuse the SAME real comparison form,
raw coordinate, accurate transported response and positive-plane response:

$$
Q=\gamma P-e_0e_0^*/\delta,\quad
R=\gamma P(f,f)-f[0]^2/\delta+\theta^2/b-s^2/a,\quad
s=\gamma\zeta+\omega\theta,\quad \omega=\chi+g/b.
$$

Here $\chi$ denotes the saved coordinate ratio, $b,a,\delta>0$, and the saved scalar
$A_{\rm up}$ bounds precisely $P(f,f)$ for the same fixed18-coordinate
row. The original raw $\kappa=33/32$ normalization is already in $f$;
no additional $\kappa$ or pivot normalization is inserted.
Let $I_0,I_\theta,I_s$ enclose $f[0],\theta,s$ for one common realization.
Set $d_0=\operatorname{dist}(0,I_0)$,
$d_s=\operatorname{dist}(0,I_s)$ and
$m_\theta=\max_{x\in I_\theta}|x|$. Directed denominator bounds give

$$
0\le R\le U_R:=
\gamma A_{\rm up}
-\frac{d_0^2}{\delta_{\rm up}}
+\frac{m_\theta^2}{b_{\rm lo}}
-\frac{d_s^2}{a_{\rm up}}.
$$

Every termwise inequality holds for the actual common realization.
Correlations need not be discarded from the model or asserted to attain
separate interval endpoints. A negative $U_R$, or an upper below the
accepted positive residual lower, is inconsistent and stops the
application. The smaller of $U_R$ and the saved full-row upper remains
an upper for that SAME residual.

This upper can screen a different question from actual paid-energy
sign. Keep a saved lower $L_F$ of the SAME $F$, and an already retained
paid lower $L_{\rm previous}$, fixed. Any valid future lower $r$ of
this residual satisfies $r\le R\le U_R$. Therefore

$$
\max\{L_{\rm previous},L_F+r\}
\le C_R:=\max\{L_{\rm previous},L_F+U_R\}.
$$

A negative $C_R$ prevents positive certification by refining this
residual alone, even with exact knowledge of $R$. A nonnegative $C_R$
is inconclusive. The statement does not bound actual paid energy from
above and does not exclude a stronger joint $F$ estimate or changed
recipe. In particular, $L_F$ is a LOWER for $F$, so substituting it
into an actual-energy upper would reverse the role of the available
information.


The saved-scalar application gives the outward enclosure

$$
0.0001193399383345589672\le R\le
2.364814143855336105831392.
$$

The upper replaces the previous rectangular upper of approximately
$7.35265\cdot10^{194}$. This is an upper-enclosure improvement, not
an improvement of a residual or paid LOWER certificate. With the SAME
saved $L_F$ and previous paid lower, the resulting fixed and
energy-endpoint certificate ceilings respectively lie in

$$
\begin{aligned}
C_{R,\rm fixed}&\in
[1.892324368802542735566375,\ 1.892324368802542735566376],\\
C_{R,\rm endpoint}&\in
[1.690128902785682152622539,\ 1.690128902785682152622541].
\end{aligned}
$$

Both are positive, so this diagnostic does not rule out further
residual estimation. It also certifies no positive paid lower. It uses
only saved scalars; no physical source, feature, matrix, reference,
inverse, solve, analytic tail or previous producer is reevaluated.

#### One common-source covector before bounding errors

Fix exactly one trial by a prescribed rule. Let $e$ be the exact
dyadic midpoint of the saved complete18-coordinate row. Let
$\Sigma_0$ be the exact symmetric midpoint of the original saved core,
and construct $T_0,\delta_0$ from it. Keep the same exact positive
$R_{\rm ref}$ and exact $\gamma$. Define

$$
Q_0=\gamma T_0R_{\rm ref}T_0^*-e_0e_0^*/\delta_0,
\qquad c=Q_0e^*,\qquad z=eT_0.
$$

One exact reference action constructs $c$. This uses $Q_0$ only to
choose a fixed exact covector. It neither replaces the actual $Q$ by
$Q_0$ nor asserts $Q_0\preceq Q_{\rm true}$.
There is no inverse or solve, alternative direction, parameter scan,
precision scan or cutoff change.

The abstract actual-$Q$ Riesz representer of $x\mapsto xc$ is
$u=(Q^{-1}c)^*$. It is used in the proof, not computed. The original
form has inertia one negative and17positive directions, since

$$
Q(x,x)=\gamma(x_{\rm tail}+x[0]t)R_{\rm ref}
(x_{\rm tail}+x[0]t)^*-x[0]^2/\delta,
$$

where $t$ is the first row of $T$. Removing the timelike $y_0$ and
orthogonal spacelike $v=\rho+(g/b)y_0$ leaves a positive definite
space. Define

$$
\begin{aligned}
d_y&=y_0c,& d_v&=\rho c+(g/b)d_y,\\
L_c&=fc+(\theta/b)d_y-(s/a)d_v,\\
D_c&=c^*Q^{-1}c+d_y^2/b-d_v^2/a\ge0.
\end{aligned}
$$

These are the cross and squared norm of the representer projected
to the SAME positive residual space. The Hilbert variational identity
therefore gives, for every real $\tau$,

$$
R\ge2\tau L_c-\tau^2D_c.
$$

Thus an enclosure $L_c\in I_c$ and positive upper $D_c\le U_D$
supply

$$
R\ge r_c:=\frac{\operatorname{dist}(0,I_c)^2}{U_D}.
$$

No positive numerical LOWER for $D_c$ is required. If $U_D<0$, the
inputs contradict structural nonnegativity and the application stops.
If $U_D=0$, then $D_c=L_c=0$ and there is no gain, so no physical
functional need be queried. An interval $I_c$ containing0 gives
$r_c=0$.

The actual-core dependence in the dual norm has an explicit block
formula. Because $c_{\rm tail}=\gamma R_{\rm ref}z^*$,

$$
c^*Q^{-1}c=\gamma zR_{\rm ref}z^*
-\delta(c[0]-t c_{\rm tail})^2.
$$

This supplies no new inverse. Anchor its cancellation exactly at

$$
q_{\rm inv,0}=ec,\qquad
k_0=c[0]-t_0c_{\rm tail}=-e[0]/\delta_0,\qquad
\Delta k=-(t-t_0)c_{\rm tail}.
$$

Then the interval implementation uses

$$
c^*Q^{-1}c=q_{\rm inv,0}
-(\delta-\delta_0)k_0^2
-\delta\bigl(2k_0\Delta k+(\Delta k)^2\bigr).
$$

Finite row actions are also anchored at exact midpoint products, with
all original interval variations retained. The actual $g/b$ remains
in $d_v$; neither the plane nor its readouts are replaced by midpoint
values. The projected cross reuses the saved accurate $\theta$ and $s$;
the fixed $c$ and finite row actions retain their inherited same-source
bindings.

For the one new physical quantity $fc$, use linearity to form $Hc$
from the saved112-by18feature map BEFORE estimating any errors.
The complete physical contract is applied to this one aggregate.
A safe lift cap is

$$
L_c^{\rm lift}=\sum_{j=0}^{17}|c_j|
\sqrt{(V^*V)_{jj,\rm up}}\ge\|Vc\|.
$$

The existing uniform sharp-forward and raw mixed allowances scale
by this SAME lift cap divided by their saved positive reference cap;
the raw mixed allowance already includes $\kappa$. One new masked
physical quadratic is evaluated in the original weighted kernel.
Its broad Gram-error cap and its full directional-jet cap are both
paid; take their minimum. The latter retains the omitted signed
antidiagonal moments, anchor bound, moment and prefactor rounding,
and actual-symbol forward allowance. The full high-support moment
Gram does not depend on whether low physical support ends at1280or2048.
No extra $\kappa$ or weight is inserted in this physical norm.

The existing finite functional, cached analytic tail and saved
physical left-kernel action then evaluate this aggregate once.
Original source, approximate-symbol, forward, smooth, raw-mixed and
new Abel allowances all remain. Common source permits this direct
linear functional; it does not authorize guessing correlations from
the previously saved marginal coordinate boxes or discarding any
error payment. Accepted original-coordinate suppliers and their
fixtures are not rerun.

Retain $\max\{r_{\rm old},r_c\}$, check it does not exceed the
saved $U_R$, and add it only to each saved SAME-$F$ lower before taking
the maximum with the previous paid certificate. The two lower bounds
for the SAME residual are never added. A positive output, if obtained,
would concern only the fixed-source paid comparisons under their
inherited premises. It would not settle actual-center/full-border,
cofinal, Robin or RH positivity.


The variational identity is literature-attested: Kurz, Pauly,
Praetorius, Repin and Sebastian, *Functional a posteriori error estimates
for boundary element methods*, Theorem4 proof, lower-bound paragraph,
[DOI10.1007/s00211-021-01188-6](https://doi.org/10.1007/s00211-021-01188-6).
Only its stated Hilbert-space identity is used; no PDE-specific
regularity, approximation or divergence-free conclusion is imported.
The block elimination, Riesz projection and Cauchy steps are standard.
The result here is their source-specific application with the original
physical-error contracts, without a new generic theorem, originality
or Lean-proof claim.


The single fixed1024-working/640-export application supplies the
following outward enclosures. Saved exact fractions and grid endpoints
are authoritative.

| Quantity | Directed range or lower certificate |
|---|---|
| Projected dual norm $D_c$ | $[0.000473029422163194849593401045,\ 0.000473029422163194849593401047]$ |
| New actual aggregate $fc$ | $[-0.062357225190587662283111460115,\ -0.062321776681492458365870736146]$ |
| Projected cross $L_c$ | $[0.000393412340550746747861519848,\ 0.000552651839094430769431308305]$ |
| New retained residual lower $r_c$ | exact lower in $[0.000327195862341560763228991826,\ 0.000327195862341560763228991827]$ |
| Previous retained residual lower | exact lower in $[0.000119339938334558967200315853,\ 0.000119339938334558967200315854]$ |
| Fixed retained paid lower | exact lower in $[-0.472162579190451809501787039320,\ -0.472162579190451809501787039319]$ |
| Energy-endpoint retained paid lower | exact lower in $[-0.674358045207312392445622899610,\ -0.674358045207312392445622899609]$ |

The residual lower increases by more than
$0.000207855924007001796028675973$; both retained paid lower
certificates improve by the same amount. They remain below0, so
neither recipe is certified positive. This does not establish a
negative actual paid energy.

The aggregate physical-norm-squared upper is at most
$0.003645779633808749843771299565$, using the fully paid directional
jet bound instead of the broad Gram cap, which exceeds
$0.089001135794317123782524109570$. These are physical norm bounds,
not $D_c$ or bounds on the source residual $R$.
The new functional's complete explicit allowance is at most
$0.000017724254513063006656728984$; its new Abel part alone is at most
$0.000016648856539851024265837724$.
The projected cross additionally retains the saved plane-response
uncertainties. The successful aggregation therefore resolves part of
the rectangular transport loss while retaining finite, nonzero
analytic payments.

The new source and packet have SHA256
`2379245eacc259969067e7940fa8c1a9b9f7050b0ca901f204fad3d3af1b8cef`
and
`c0aa04f3fbf6d523d0846003a8d2b8385a3d6d3fc891a882d14953a9e88f27c7`.
The packet is48397bytes and assembly takes<0.921542seconds, excluding
serialization. It makes one exact reference action, one core-variation
profile, one aggregated feature column, one masked physical quadratic,
one directional-norm application, one finite functional, one cached
tail and one mixed dot. Original-coordinate queries, new inverse or
solve, old scientific producers and fixture replays are all0.
There is no alternative direction, source, precision, parameter,
cutoff scan or retry.

The saved-scalar envelope source and packet separately retain SHA256
`c9430f825ffa6cb5a745d22e971e2c16c5a53894ee5a4f894a177c7e31180ece`
and
`7ca0ccd8a23dee5a0a60b793d21c07d287652d017afa387e28eb3a6243122d94`.
That packet is13420bytes and assembly takes<0.251660seconds,
excluding serialization. It supplies one upper and two certificate
ceilings without any physical response or old scientific replay.

These are conditional, fixed-source applications of existing methods.
All inherited source, physical-error, reference-form and paid-comparison
premises remain. Actual paid/center/full-border/good-block and cofinal
positivity, Robin and RH remain unresolved.


The [two application sources, directed packets and README](https://github.com/the-omega-institute/trureturing-experiments/tree/1c806b85586413d33d44e75865907ff683478220/docs/reports/weil-c27) retain the scalar envelope and the single common-source trial with their original bindings.

#### The saved common covector cannot pay either fixed comparison

The common-trial packet also permits a stopping test without another
source query. Keep its exact covector $c$, actual form, plane and both
saved SAME-$F$ lower certificates fixed. Write

$$
I_c=[\ell_-,\ell_+],\qquad
D_c\in[d_-,d_+],\qquad d_->0,
\qquad
C_c=\frac{\max\{|\ell_-|,|\ell_+|\}^2}{d_-}.
$$

For any nonempty closed refinement $J\subseteq I_c$ and any valid
upper $U$ from a refined dual-norm interval contained in
$[d_-,d_+]$, one has $U\ge d_-$ and hence

$$
\frac{\operatorname{dist}(0,J)^2}{U}\le C_c.
$$

This includes singleton refinements, so eliminating the interval width
in this same observation cannot exceed $C_c$. Equivalently, the
existing convex-endpoint helper is applied to $z^2/d_-$ on $I_c$;
no original response, trial construction, physical error, inverse,
reference action or old experiment is recomputed.

For each unchanged SAME-$F$ lower $L_F$ and previous retained paid
lower $L_{\rm old}$, the most optimistic retained lower from this
one-direction recipe is bounded by

$$
\max\{L_{\rm old},L_F+C_c\}.
$$

The one exact-rational saved-data application gives outward ranges:

| Quantity | Range containing the exact certificate ceiling |
|---|---|
| One-direction residual-certificate capacity $C_c$ | $[0.000645676655497943832123311,\ 0.000645676655497943832123312]$ |
| Fixed retained-certificate ceiling | $[-0.471844098397295426432892720,\ -0.471844098397295426432892719]$ |
| Energy-endpoint retained-certificate ceiling | $[-0.674039564414156009376728580,\ -0.674039564414156009376728579]$ |

The capacity is less than0.14%of the required $-L_F$ in either
unchanged recipe. The source has SHA256
`8bcf41f185202bac5eb189720e62e19b437a1c978cd5605e2443e273c2d31d59`;
the7656-byte packet has SHA256
`914ec78b2be3b1ba1ebed01fb0a205802f9258786fbf02318c0fe7ba3cb971f0`.
Assembly takes<0.009150seconds, excluding serialization.


Both ceilings are negative. This rules out positive certification by
refining this same covector's saved intervals while holding the
SAME-$F$ certificates fixed. The positive lower for $D_c$ is needed
for this stopping test; it was not needed for the original residual
lower. The calculation reuses the accepted exact convex-endpoint
helper, without replaying its fixtures or any scientific producer.

The geometric missing part can be stated independently. In the
positive residual space, let $u_c$ be the projected actual-$Q$ Riesz
representer and $f_\perp$ the residual of $f$ after the original
indefinite plane. Since $D_c>0$, orthogonal decomposition gives

$$
R=\frac{L_c^2}{D_c}+R_{\perp c},\qquad
R_{\perp c}=\left\|f_\perp-\frac{L_c}{D_c}u_c\right\|_Q^2\ge0.
$$

The observed one-dimensional contribution is at most $C_c$; the
unobserved orthogonal contribution has no new upper or positive
lower here. Any extension which keeps $L_F$ and certifies positivity
by adding separate lower bounds for these two orthogonal terms must
supply an independent remainder lower strictly exceeding
$-L_F-C_c$. Merely renaming the previous total-residual lower as a
remainder would not justify adding it to the common-trial lower.
A joint bound which also improves $F$ is outside this fixed-recipe
test and requires its own common-source estimate.

Thus the stopping result limits a particular lower-certificate
algorithm and its observed component. It is not an upper for total
$R$, actual paid energy, the actual finite border or the full Weil
form. The two actual comparison signs, actual-center/full-border,
good-block/cofinal positivity, Robin and RH remain unresolved.
This is a source-specific application of the existing projection and
convexity results, without a generic novelty or Lean-proof claim.

The [fixed-trial source, exact packet and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/fbfefa527018d4388fd9c2cb4dd5c0d2130f7043/docs/reports/weil-c27) preserve this conditional stopping result; the common-trial supplier is reused without replay.


### The complete unweighted row and the finite joint good-block metric

The archived $1263$-by-$18$ action $P^{-1}C$ serves the old lift,
not arbitrary new rows. A different query supplies the missing
unweighted row and two inverse actions on the SAME positive principal
block of the rho32-v2 lower target. The accepted original target,
residual generators, source, lift and positive-pivot evidence are
reused; no old target supplier or old lift solve is replayed.

The original exact384-bit row0 source $w$ has support
$2049\le m\le32768$. Put its coefficients, without $W$, $Mw$ or
rescaling, into the accepted residual-generator Cauchy product. This
gives every retained coefficient of

$$
r_n=\sum_{m=2049}^{32768}w_mR_{mn},\qquad0\le n\le1280.
$$

The scalar $\kappa$ enters only through the reused product.
Because $w$ itself is finitely supported, this $r=w^*R$ is complete
for the original source; it requires no omitted $w$-source tail.
The source and exact-lift formulas identify $rV$ with the archived
unweighted projection. The overlap check tests the new implementation
and does not establish source equality from overlap.

Use the saved full finite row $b_J$ and restrict both rows to the
accepted1263 positive coordinates. With

$$
B_J=\begin{pmatrix}r_g\\b_{J,g}\end{pmatrix},\qquad
PX_J=B_J^*,\qquad G_{JJ}=B_JX_J,
$$

one new validated two-right-side solve encloses $X_J$ and $G_{JJ}$.
The two off-diagonal evaluations enclose the same real cross entry;
their average remains enclosing. For every real $e\in\mathbb R^2$,

$$
e^*G_{JJ}e=(e^*B_J)P^{-1}(B_J^*e)\ge0.
$$

This retains the common-realization cross energy, rather than
combining separately optimized marginal bounds. $P$ is the certified
principal block of the saved lower target, not a new certification of
the whole actual center.

| Metric entry | Outward enclosure |
|---|---|
| $r_gP^{-1}r_g^*$ | $[4787.103066499741053563,\ 4787.103066499741053564]$ |
| $r_gP^{-1}b_{J,g}^*$ | $[663.225066385094668430,\ 663.225066385094668431]$ |
| $b_{J,g}P^{-1}b_{J,g}^*$ | $[92.167958630498818052,\ 92.167958630498818053]$ |

The row packet is144087bytes, SHA256
`566cb68530f31dd6e26af076055bb368e2b2e82fdcc0857abb7b2b475a036f48`;
its assembly takes<8.573037seconds. The joint metric packet is303335bytes,
SHA256
`9ba53b70a0f1cad25b9e92894eff93f1340dc31d1a9bf945c560b6dc6940d072`.
It includes all1263-by2 inverse-action intervals. Its preparation and
target reconstruction take<14.334747seconds, the one two-right-side
solve takes<118.573775seconds, and total assembly takes<133.114112seconds,
excluding serialization.

The working precision is fixed1024bits and export precision640bits;
the Cauchy product uses the fixed accepted order512. There is one
new unweighted product and one new solve with two new right sides.
The target reconstruction supplies that new solve's input; it is not
an old scientific-producer replay. No general inverse, source,
direction, parameter, precision or cutoff scan is performed.

The complete row remains $b=b_J+b_{\rm far}$. Writing
$f_g=b_{{\rm far},g}$, the complete metric from the earlier joint
border is

$$
G_2=G_{JJ}+
\begin{pmatrix}
0&r_gP^{-1}f_g^*\\
f_gP^{-1}r_g^*&
b_{J,g}P^{-1}f_g^*+f_gP^{-1}b_{J,g}^*+f_gP^{-1}f_g^*
\end{pmatrix}.
$$

Thus $G_{JJ,11}$ already concerns the complete original $r$, whereas
the other entries do not yet supply the complete $b$ metric.
The exported1263-by2 inverse actions can be reused for the two mixed
far terms; the remaining far energy and the reduced-core far row
still require a sound common-source estimate. No arbitrary finite
$b_J$ energy can replace the complete $b$ energy, and the correction
matrix is not asserted to have either Loewner sign.

All inherited actual form, residual-map/domain, source/lift and
comparison premises remain. These are conditional numerical
applications of the existing Cauchy-product, interval-solve and
Schur mechanisms, without a generic-method novelty or Lean-proof
claim. The actual-center/full-border/cofinal positivity, Robin and
RH questions remain open.

The [two new consumers, complete retained row, finite joint metric and inverse actions](https://github.com/the-omega-institute/trureturing-experiments/tree/f9610d3a5a732abaf68e733e50a7e34e66148ced/docs/reports/weil-c27) preserve the source and target bindings and reproduction entry.


### Two new far pairings on the saved good-block inverse actions

The complete18-coordinate far row on the old lift is already saved
above. It is reused, rather than queried again. The new finite joint
metric also saves two different directions,
$Y_1=P^{-1}r_g^*$ and $Y_2=P^{-1}b_{J,g}^*$, on the SAME1263-positive
principal block. The missing observations are now the two actual
same-source contractions

$$
u=f_gY_1,\qquad v=f_gY_2,\qquad
f=\kappa u_F^*W_FR_F,\quad\kappa=33/32.
$$

These profiles are not columns of the old18-dimensional lift, and
their inverse actions are already supplied. No new solve, general
inverse or target reconstruction is needed.

Let $H$ be the existing1281-by112 far feature map and let
$\iota_g$ embed the positive coordinates with zeros on the remaining
18 coordinates. Aggregate

$$
h_i=H^*\iota_gY_i,\qquad L_i\ge\|\iota_gY_i\|_2
$$

before source functionals or error estimates. The norm caps are
computed directly on the full embedded retained vectors. The signed
masked kernel $K$ is not assumed PSD. The full paid Gram comparison
and the accepted directional jet estimate give two independently
valid bounds on the same physical profile:

$$
\|R_F\iota_gY_i\|_{W_F}^2
\le \min\left\{\operatorname{up}(h_i^*Kh_i)+\varepsilon L_i^2,\
N_{i,\mathrm{jet}}^2\right\}.
$$

Here $\varepsilon$ is the already transported COMPLETE far allowance,
at least the original512-grid allowance. Matrix arrays use640bits.
The directional bound retains its omitted moments, masking,
rounding and actual-symbol forward payment. The original physical
weight is already present; this norm bound adds no $\kappa$ factor.

The existing cached finite and analytic-tail maps are applied once
to each new aggregated profile. The raw mixed part uses the saved
left-kernel row on the same two-column feature matrix. All source,
symbol, smooth, actual-symbol forward, raw mixed and Abel allowances
are retained. Uniform forward and raw mixed errors scale by $L_i$
through the existing homogeneous contract. Approximate cached symbols
are not identified with the actual symbol.

| New observation | Outward enclosure |
|---|---|
| $u=f_gP^{-1}r_g^*$ | $[20.231424206590496643,\ 20.240043090713776357]$ |
| $v=f_gP^{-1}b_{J,g}^*$ | $[2.786887993197035236,\ 2.788073520641284838]$ |
| Complete $G_{2,12}=c+u$ | $[683.456490591670613158,\ 683.465109475822996702]$ |
| $G_{2,22}-z=d+2v$ | $[97.741734616883793577,\ 97.744105671790482675]$ |

The single1024-working/640-export application takes<4.991544seconds,
excluding serialization. Its30181-byte packet has SHA256
`39ddee410fa83bf4d35cb97f33bc9e63568dff8d9404dee331b0b3925336a858`;
the source has SHA256
`62c0da60931ae22580a8e1f16b79180ef9f26c40bae4aaf08b047e2006b09d2b`.
It makes two new feature, norm, finite-functional and cached-tail
applications, with one two-column raw mixed product. Old source
recovery, old lift queries, target reconstruction, inverse/solve,
scientific producer and fixture replays are all0. No scan or retry
follows.

For these two profiles the directional jet caps are selected; their
improvement over the full paid Gram caps is below the displayed precision.
The physical norm-squared uppers are at most241.529430992648325580 and
4.573192066649095956. The total explicit functional allowances are
at most0.004309442047589309 and0.000592763720310256, including
the respective Abel allowances0.004032646541103321 and
0.000554676109821741. The positive signs do not result from dropping
these nonzero analytic payments.

Write the previously saved finite metric as
$G_{JJ}=\left(\begin{smallmatrix}a&c\\c&d\end{smallmatrix}\right)$.
The actual complete joint metric is enclosed through

$$
G_2=
\begin{pmatrix}a&c+u\\c+u&d+2v\end{pmatrix}
+\begin{pmatrix}0&0\\0&z\end{pmatrix},
\qquad z=f_gP^{-1}f_g^*\ge0.
$$

The unknown $z$ still has no new upper bound. The matrix before the
$z$ term need not be PSD and is not substituted for $G_2$.
The two response intervals contain functionals of ONE actual source;
their endpoints are not asserted independently attainable.
The saved old18-coordinate far row also retains its earlier broad
error-transport limitation. These observations alone do not certify
the complete joint border or remove the cofinal obligation.

All inherited common-form/domain, residual-map, source, normalization
and comparison premises remain. This is a new source-specific
application of accepted functional and error-estimation methods,
without a generic-method novelty or Lean-proof claim. Actual-center,
full-border/cofinal positivity, Robin and RH remain open.

The [new two-profile source, directed cross terms, partial complete metric and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/d90d6869c73e1fbcdb4321e0879b55902b4abd81/docs/reports/weil-c27) preserve this same-source application and all explicit payments.


### Price the remaining far inverse energy from the saved correlations

Reuse the two paid far pairings and the finite joint metric on the SAME
positive block. Write
$G_{JJ}=\left(\begin{smallmatrix}a&c\\c&d\end{smallmatrix}\right)$,
$m=(u,v)$ and $s=d-c^2/a>0$. The classical projection inequality gives

$$
z=f_gP^{-1}f_g^*\ge Q_J,
\qquad
Q_J=\frac{u^2}{a}+\frac{(v-cu/a)^2}{s}.
$$

This is a lower bound, not the missing upper. One saved-data application
returns

$$
\boxed{Q_J\in[0.086276954471713906,\ 0.086630925124381975].}
$$

It reuses every old source query and inverse action. No new source or far
functional, target reconstruction, inverse, solve or parameter scan runs.
The interval is for functionals of one source; its endpoints are not
asserted jointly attainable.

For the earlier joint border use the SAME complete reduced row
$\beta=\beta_J+fV$, with the already saved18-coordinate far row. Choose
only the fixed optimistic comparison
$t_+=\mathrm{cap}/h_{\mathrm{lo}}$ and the saved refined common charge
$D=\overline D$. Eligibility of $t_+$ is not asserted. Let $p=(\Sigma_0)_{00}<0$;
the18-by17 core elimination map $T_\Sigma$ has first row
$-(\Sigma_0)_{0,1:}/p$ and remaining block $I_{17}$. The reference
inverse $R$ of the17-dimensional positive core and its accepted Neumann
constant $\eta<1$ are reused. A single new reference action on
$\beta T_\Sigma$ supplies its energy and its cross with $\rho T_\Sigma$;
the archived $\rho T_\Sigma R T_\Sigma^*\rho^*$ is consumed directly. The relative inverse error
is bounded by $\eta/(1-\eta)$ in the reference metric, with its bilinear
Cauchy allowances retained.

Put

$$
\begin{aligned}
\mathfrak a&=t_+^{-1}+a+\rho\Sigma_0^{-1}\rho^*,\\
\mathfrak c&=c+u+\rho\Sigma_0^{-1}\beta^*,\\
\mathfrak d&=\overline D+d+2v+\beta\Sigma_0^{-1}\beta^*.
\end{aligned}
$$

Then the existing border identity becomes

$$
\det N_2=\mathfrak a z+\mathfrak a\mathfrak d-\mathfrak c^2.
$$

The first entry is enclosed by

$$
\mathfrak a\in[39434.061125466995953787,\
39434.061125466995953788]>0.
$$

Thus this comparison requires

$$
z<z_{\mathrm{crit}}
=\mathfrak c^2/\mathfrak a-\mathfrak d,
\qquad
z-Q_J<\Delta=z_{\mathrm{crit}}-Q_J.
$$

The calculation is inconclusive about that budget. The saved canonical
18-coordinate far-row box, transported through the weak core directions,
produces enclosures for both $z_{\mathrm{crit}}$ and $\Delta$ contained
in $[-7\cdot10^{192},7\cdot10^{192}]$ that cross zero. These are wide
containing intervals, not a claim that either exact quantity varies over
them or that the actual source has intrinsic uncertainty of that size.
The undivided determinant coefficients remain saved. The new projection
floor does not turn an inconclusive budget into a target sign.

Consequently the positive floor does not settle the required joint
inequality $z<z_{\mathrm{crit}}$. The current canonical row box also fails
to provide a useful threshold for that comparison. A useful next input must retain shared
source constraints in the core transport or supply a sufficient joint
comparison directly. Increasing the arithmetic precision of this same
box does not add those constraints. No source or precision retry follows.
Any future exclusion with $t_+$ would apply only to $0<t\le t_+$ and
$D\ge\overline D$ on this SAME lower target, not to every admissible
charge or the actual full center.

The sole1024-working/640-export application takes<0.121972seconds,
excluding serialization. Its11131-byte packet has SHA256
`11ccabd6110436b2b29f1a910c6c36a5fd8479af19d183cf614826ed9ad746c6`;
the source has SHA256
`a478b8d52e52384be98b6f385e65df9a4364d6b882a5fd82a119c9752ca3fd9f`.
It makes one new17-reference action, two new reference bilinears and one
explicit two-dimensional projection calculation. No old scientific
producer or fixture is replayed. All inherited common-form/domain,
residual, source/lift, complete-far, normalization and comparison premises
remain. These are conditional numerical applications of existing
projection, Schur and Neumann methods, without generic-method novelty
or a Lean-proof claim. Actual-center/full-border/cofinal positivity,
Robin and RH remain open.

The [saved-data consumer, directed energy budget and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/3115ead2bc655c55bf3b25435f9d20a979cd3872/docs/reports/weil-c27) preserve the accepted source and its single application.


### Condition the lifted far row on the paid good-block observations

Keep the SAME source, positive block and exact enclosed lift. Let
$Y=P^{-1}[r_g^*,b_{J,g}^*]$ be the two saved actions, put
$A=[\iota_gY,V]$, and write the physical upper Gram as

$$
F=A^*(HKH^*+\varepsilon I)A
=\begin{pmatrix}F_{mm}&F_{my}\\F_{ym}&F_{yy}\end{pmatrix}.
$$

The signed112-dimensional kernel $K$ is not assumed positive.
The inherited physical majorant
$R_F^*W_FR_F\preceq HKH^*+\varepsilon I$ implies positivity of the
exact $F$. No claim is made that every matrix in its entrywise interval
box is positive. The complete original512-metadata allowance is retained.
Reuse the saved $H^*\iota_gY$, $H^*V$, $V^*V$ and $F_{yy}$;
the new contractions supply $Y^*Y$, $-Y^*(P^{-1}C)$, $F_{mm}$ and
$F_{my}$. No old physical block, source functional or inverse action
is recalculated.

For the actual row $y=fV$ and the already paid pair $m=(u,v)$, the
column $\xi=(m,y)^T$ satisfies

$$
\xi\xi^*\preceq\Gamma F,
\qquad \Gamma=\kappa^2E,
\qquad \kappa=33/32,
$$

where $E$ is the accepted upper for the SAME physical source norm
squared. The original weight is already present in $F$ and $E$.
This physical Gram is distinct from the earlier inverse metric $G_{JJ}$.
Its observed energy is not the unknown $z=f_gP^{-1}f_g^*$.

Standard Schur conditioning gives, for this one common realization,

$$
B=F_{mm}^{-1}F_{my},\qquad S_F=F_{yy}-F_{ym}B,
$$

$$
(y-mB)^*(y-mB)
\preceq
\left(\Gamma-mF_{mm}^{-1}m^*\right)S_F.
$$

Only positivity of the observed two-by-two block is required for this
formula; the remaining exact Schur form may be semidefinite. The single
saved-data application verifies its pivots within

$$
(F_{mm})_{00}\in[241.5294309926483,\ 241.5294309926484],
\qquad
s_m\in[2.76928258548446,\ 2.76928258548447]\cdot10^{-6}.
$$

It encloses the observed fraction

$$
\frac{mF_{mm}^{-1}m^*}{\Gamma}
\in[0.19224358456570,\ 0.82455202205468].
$$

This is a containing interval, not an asserted attainable range.
A lower enclosure of the spent energy supplies the remaining-energy
upper used in the coordinate supports. Across all18 original lift
coordinates, the individual physical variance ratios obey

$$
\boxed{
\frac{(S_F)_{jj}}{(F_{yy})_{jj}}
\in[1.8707,\ 1.9304]\cdot10^{-10},\qquad 0\le j<18.
}
$$

These compare conditional and unconditional variances in the SAME
physical Gram. They are not a reduction factor for the old source-query
errors, the core inverse energy, or the Robin deficit. Intersecting the
conditional supports with the original saved640-grid far row leaves
all18 original intervals exactly unchanged. Width accounting uses those
original grid bounds; no round-trip enlargement is credited as progress.
The full joint Gram and conditional Schur form are retained for a
correlated core estimate. Unchanged coordinate intervals alone do not
exclude an improvement of that estimate.

For a subsequent quadratic comparison, existing trust-region results
must keep their hypotheses. [Jeyakumar--Li, Lemma6.3 and
Corollary4.3](https://arxiv.org/abs/1309.3000) distinguish the single
Slater quadratic constraint from extended trust regions with linear
constraints; the latter equivalence requires strict feasibility and
their dimension condition(2.2).
[Wang--Xia, Theorem6](https://arxiv.org/html/1407.0465v2) concerns one
scalar quadratic interval constraint, not this two-observation rectangle.
No exactness of a future multiple-constraint relaxation or successful
quadratic comparison is asserted here.

The sole1024-working/640-export application takes<0.358260seconds,
excluding serialization. Its126523-byte packet has SHA256
`2e1c11ef3807445ce6b157d47232bc6086ac96f8a07786e4b03b7355e61c00ae`;
the source has SHA256
`d081a2d80786ea53deb91896548271e5b63f3adf966922362c0f9d5a6da7e7ab`.
There is no new source/far query, target reconstruction, inverse/solve,
old producer/fixture replay or parameter/precision scan. This is a
conditional numerical application of existing Schur and ellipsoid
methods, without generic-method novelty or a Lean-proof claim.
The indefinite core and joint determinant remain uncertified; no upper
for the unseen far inverse energy is supplied. A sufficient direct joint
comparison remains an alternative. Actual-center/full-border/cofinal
positivity, Robin and RH remain open.

The [twenty-profile consumer, directed conditional Gram and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/f3e667c05bc6bbdce7ef7832f7e368567a7f3969/docs/reports/weil-c27) retain the shared-source application and its original-grid comparison.


### Contract the complete joint budget before taking its upper bound

Keep the SAME finite comparison, source, lift and measured pair. Write
$G=\Sigma_0^{-1}$ as a mathematical symbol, without computing a new
inverse. Let $p=(\Sigma_0)_{00}<0$, $T=[-(\Sigma_0)_{0,1:}/p;I]$, and
reuse the accepted positive reference inverse $R$ with its original
$0\le\eta<1$. Put

$$
\mathcal W=TRT^T,\qquad
\widehat G=p^{-1}e_0e_0^T+\mathcal W,\qquad
\ell=\frac{\eta}{1-\eta}.
$$

For the actual inverse, the inherited relative reference guarantee gives

$$
|v^T(G-\widehat G)w|
\le\ell\sqrt{v^T\mathcal Wv}\sqrt{w^T\mathcal Ww}.
$$

This is the original Neumann payment, not an identification of the
reference and actual inverses. All vectors below use column notation;
the saved regression $B$ still has two rows and eighteen columns.
Let $S=S_F$, $m=(u,v)^T$, $\mu=B^Tm$, and $r=y-\mu$. The retained
conditional geometry gives

$$
rr^T\preceq\overline\Delta S,
$$

where $\overline\Delta$ is the already saved remaining-energy upper.
The exact $S$ is positive semidefinite under the physical-majorant
premise. Its whole entrywise interval box is not asserted positive.
The signed far kernel and original full $\varepsilon/512$-metadata
allowance remain unchanged.

The actual comparison is

$$
z_{\rm crit}-Q_J
=\frac{(c+u+\rho^TGx)^2}{A}
-\overline D-d-2v-x^TGx-Q_J(m),\qquad x=\beta_J+y,
$$

with the SAME positive $A$, finite inverse metric entries $c,d$, fixed
optimistic $t_+$ and charge $\overline D$ from the previous budget.
Choose a positive rational $a_0$ at the midpoint of the saved $A$
enclosure. Define

$$
\begin{aligned}
\widehat h(m)&=c+u+\rho^T\widehat G(\beta_J+B^Tm),\\
\widehat q_c(m)&=\widehat h(m)^2/a_0-\overline D-d-2v
-(\beta_J+B^Tm)^T\widehat G(\beta_J+B^Tm)-Q_J(m),\\
\widehat g(m)&=\widehat G\rho\,\widehat h(m)/a_0
-\widehat G(\beta_J+B^Tm),\\
\widehat H&=\widehat G\rho\rho^T\widehat G/a_0-\widehat G.
\end{aligned}
$$

The complete nominal budget is exactly

$$
\widehat q_c(m)+2\widehat g(m)^Tr+r^T\widehat Hr.
$$

The source assembles $\widehat q_c=\theta^TC_q\theta$ and
$\widehat g=Z\theta$, $\theta=(1,u,v)^T$, BEFORE taking interval
bounds. Thus the square and indefinite core contribution retain their
signed cancellation. New contractions supply

$$
t_1=\operatorname{tr}(S\widehat H),\qquad
t_2=\operatorname{tr}(S\widehat HS\widehat H),\qquad
C_g=Z^TSZ.
$$

[Wolkowicz--Styan, Theorem2.1, Eq(2.3)](https://www.math.uwaterloo.ca/~hwolkowi/henry/reports/bndseigs80.pdf)
gives the real-eigenvalue trace bound. Apply it to the mathematical
symmetric matrix $S^{1/2}\widehat HS^{1/2}$ in dimension18; no numerical
square root, inverse or eigensolver is needed. With directed trace
intervals $[a_1,b_1]$, $[a_2,b_2]$, and
$d_1=\operatorname{dist}(0,[a_1,b_1])$, use

$$
\overline\lambda=
\max\left(0,\frac{b_1}{18}
+\sqrt{17\left(\frac{b_2}{18}-\frac{d_1^2}{18^2}\right)}\right).
$$

A negative upper enclosure for the discriminant contradicts the
inherited domain and stops. The primary paper requires real eigenvalues;
it does not require this nominal curvature to be positive.

The linear term keeps BOTH the conditional Gram and the original raw
640-grid row box. Write the latter as $y\in[\bar y-b,\bar y+b]$.
Two uniform support uppers are obtained from

$$
\sqrt{\overline\Delta\,\theta^TC_g\theta},\qquad
\widehat g(m)^T(\bar y-B^Tm)+\sum_i b_i|\widehat g_i(m)|.
$$

Let $L_+$ be the smaller of their directed uniform uppers, and set

$$
U_{\rm nom}=\operatorname{ub}(\widehat q_c)+2L_+
+\overline\Delta\,\overline\lambda.
$$

All these are upper bounds for one common realization. Endpoints and
component extrema are not asserted jointly attainable. No coordinate
interval has to shrink, and no exact optimization or multi-constraint
S-lemma equivalence is invoked.

The reference error is paid on the ENTIRE budget. A new conditional
reference-energy bound $E_x\ge x^T\mathcal Wx$ follows by PSD trace
monotonicity and Minkowski, using the mean Gram of
$[\beta_J,B^T]$ and $\operatorname{tr}(R T^TST)$. Its finite diagonal
is reused from the paid identity
$gRg-2\alpha\,rRb-\alpha^2rRr$; only the two new regression rows
receive reference vector actions. This $E_x$ is a reference-core norm,
not the unseen far inverse energy $z$.

Reuse $R_\rho\ge\rho^T\mathcal W\rho$, and put

$$
\begin{aligned}
\delta_O&=\ell\sqrt{R_\rho E_x},\\
\overline O&=\operatorname{ub}|\widehat h|
+\sqrt{\overline\Delta\operatorname{ub}(\rho^T\widehat GS\widehat G\rho)},\\
J_A&=\operatorname{ub}|A^{-1}-a_0^{-1}|,\\
\epsilon_R&=\frac{2\overline O\delta_O+\delta_O^2}{A_{\rm lo}}
+\overline O^2J_A+\ell E_x.
\end{aligned}
$$

Expanding the actual offdiagonal as its nominal value plus
$\rho^T(G-\widehat G)x$, and applying the same reference inequality to
$x^T(G-\widehat G)x$, gives the sufficient bound

$$
\boxed{z_{\rm crit}-Q_J\le U_*:=U_{\rm nom}+\epsilon_R.}
$$

The denominator enclosure and all original reference/source payments
are retained. This avoids substituting an unpriced nominal inverse or
independent interval entries for the actual inverse.

The single saved-data application is inconclusive about the complete
comparison. The directed bounds include

| Contribution | Saved enclosure |
|---|---|
| Nominal center $\widehat q_c(m)$ | $[-157.40499,-147.08236]$ |
| Selected linear support upper $L_+$ | $[2.0669461,2.0669462]\cdot10^{68}$ |
| Curvature upper $\overline\lambda$ | $[2.8567554,2.8567555]\cdot10^{28}$ |
| Complete reference/denominator payment $\epsilon_R$ | $[6.5348005,6.5348006]\cdot10^{-15}$ |
| Complete budget upper $U_*$ | $[4.1338923,4.1338924]\cdot10^{68}$ |

The last four rows enclose computed upper-bound values, not attainable
ranges of the target. In particular, the positive $U_*$ supplies no sign
for $z_{\rm crit}-Q_J$. The selected linear support is the dominant
contribution to this sufficient upper. Its gradient-energy enclosure is
contained in $[-5.4265663,5.4265663]\cdot10^{135}$, although the exact
energy is nonnegative under the inherited physical-majorant premise.
This is an unresolved enclosure, not an assertion that the actual source
has that intrinsic uncertainty. This application does not distinguish
inherited entry widths, evaluation dependency and arithmetic loss as
causes of its size. A next comparison needs a better joint-gradient
bound or another correlation-preserving contraction; the small paid
reference perturbation alone does not fix the current upper.

The auxiliary reference-energy calculation does give a strictly tighter
positive-core upper. The old paid original-grid upper lies in
$[8.0136669,8.0136670]\cdot10^{97}$, whereas the new one lies in
$[451.44423,451.44424]$. Their ratio lies in
$[5.6334290,5.6334291]\cdot10^{-96}$. These are bounds on the SAME
positive-core energy, with the original source allowance and Neumann
factor. They do not measure a change in that energy or an improvement
of the Robin deficit. The new reference-energy bound is consumed in
$\epsilon_R$ for the COMPLETE budget; it is not a substitute terminal
claim. A useful norm bound has therefore not yet delivered the required
joint sign.

The sole1024-working/640-export application takes<0.247876seconds,
excluding serialization. Its138122-byte packet has SHA256
`6656a9e9ab05dd090168c93a359eeb8930998b89e855755b062f2493634dd0dd`;
the source has SHA256
`f72c0235bf32f8ded6fefc615f7a7414e7b66d2cd57626002e18b6f1eb437063`.
Only the new regression actions and common-source trace/gradient
contractions are evaluated. No source/far query, target reconstruction,
inverse/solve, accepted producer/fixture replay or source/precision scan
runs. The original raw coordinate intervals and source allowance are
retained.

If a certified $U_*<0$ were obtained, the EXISTING LOWER bound $z\ge Q_J$
would give

$$
\det N_2=A(z-z_{\rm crit})\ge A_{\rm lo}(-U_*)>0.
$$

This would exclude only the fixed optimistic comparison. It would not
pay parameter eligibility or a transfer to the actual full target.
An inconclusive upper is neither a target counterexample nor an
impossibility result for stronger correlated certificates. No independent
$z$ upper, negative determinant, actual-center/full-border/cofinal
positivity, Robin or RH proof is supplied. This is a source-specific
application of existing trace, norm and reference-error methods, without
a generic-method novelty or Lean-proof claim.


The [joint-budget consumer, directed result and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/58635d877caf1fe56e3708faa14394e19d2f9154/docs/reports/weil-c27) retain the single application and its common-source bindings.


### Consume the reference energies as a complete scalar norm bound

Keep the SAME source, lift, conditional mean $\bar x=\beta_J+B^Tm$,
remaining-energy upper $\overline\Delta$, nominal denominator $a_0$,
nominal center $\widehat q_c$ and complete actual-minus-nominal payment
$\epsilon_R$. These quantities are consumed from the preceding packets;
the matrix contractions that produced them are not repeated.

Write $d_p=-1/p>0$, so that
$\widehat G=\mathcal W-d_p e_0e_0^T$. For the exact positive semidefinite
forms $\mathcal W,S$, ordinary PSD trace monotonicity gives

$$
\mathcal W S\mathcal W\preceq
\operatorname{tr}(S\mathcal W)\mathcal W.
$$

It follows by the triangle inequality that

$$
\|S^{1/2}\widehat Gv\|
\le\sqrt{\operatorname{tr}(S\mathcal W)\,v^T\mathcal Wv}
+d_p|v_0|\sqrt{S_{00}}.
$$

Both forms may be singular. These are applications of existing PSD
trace, Cauchy--Schwarz and norm inequalities, without a new generic
theorem or positivity claim for the full interval-entry box.

Reuse uniform saved upper bounds $\tau,R_\mu,R_\rho$ for
$\operatorname{tr}(S\mathcal W)$,
$\bar x^T\mathcal W\bar x$ and $\rho^T\mathcal W\rho$.
With directed scalar enclosures define

$$
\begin{aligned}
K_\mu&=\sqrt{\tau R_\mu}+d_p|\bar x_0|\sqrt{S_{00}},\\
K_\rho&=\sqrt{\tau R_\rho}+d_p|\rho_0|\sqrt{S_{00}},\\
H_+&=|c+u|+d_p|\rho_0|\,|\bar x_0|+\sqrt{R_\rho R_\mu}.
\end{aligned}
$$

Each right side denotes its directed uniform upper. In particular,
$|\widehat h|\le H_+$ and
$\|S^{1/2}\widehat g\|\le H_+K_\rho/a_0+K_\mu$.
The first coordinate $\bar x_0$ is a new scalar combination of the
already saved finite row, observations and regression. No new vector or
matrix action is needed.

For the SAME conditional residual $rr^T\preceq\overline\Delta S$, put

$$
L_N=\sqrt{\overline\Delta}
\left(H_+K_\rho/a_0+K_\mu\right),\qquad
\Lambda_N=K_\rho^2/a_0+d_p S_{00}.
$$

Then $\widehat g^Tr\le L_N$. Moreover,

$$
r^T\widehat Hr
=\frac{(\rho^T\widehat Gr)^2}{a_0}
-r^T\mathcal Wr+d_p r_0^2
\le\overline\Delta\Lambda_N.
$$

The negative $-r^T\mathcal Wr$ is dropped in the upper-bound direction.
This is a sufficient norm majorant, not an assertion that the current
curvature is positive or that component extrema are simultaneously
attainable. Reusing the saved COMPLETE center and inverse/denominator
payment gives another full comparison bound,

$$
\boxed{
z_{\rm crit}-Q_J
\le U_N=\operatorname{ub}(\widehat q_c)
+2L_N+\overline\Delta\Lambda_N+\operatorname{ub}(\epsilon_R).
}
$$

All original source-energy, physical-majorant, source/lift/domain,
positive-reference, normalization, full epsilon/512-metadata and
positive actual-denominator premises remain. The same nominal inverse
and $a_0$ are used, so the original complete perturbation payment applies
without being recalculated.

The single scalar application now certifies a strictly negative complete
upper. Its directed values include

| Sufficient bound | Saved enclosure |
|---|---|
| Linear support upper $L_N$ | $[57.877991,57.877992]$ |
| Curvature upper $\Lambda_N$ | $[0.10457128,0.10457129]$ |
| Complete budget upper $U_N$ | $[-30.503107,-30.503106]$ |

These intervals enclose computed bound values, not attainable target
ranges. Under the stated inherited premises, the existing lower bound
$z\ge Q_J$ and positive actual comparison denominator give

$$
\boxed{
\det N_2=A(z-z_{\rm crit})
\ge A_{\rm lo}(-U_N)
\ge1.2028613\cdot10^6>0.
}
$$

Thus the fixed optimistic comparison is excluded from the desired
negative-determinant route. This conclusion uses no unseen $z$ upper.
It does not establish the admissibility of its optimistic coefficients,
exclude other source/parameter choices, or transfer the sign to the
actual full target. The old positive sufficient upper and new negative
one refer to the SAME comparison; replacing the unresolved gradient
contraction by a scalar majorant is enough to decide this conditional
fixed-case sign. The source itself and its original allowance have not
changed.

The sole1024-working/640-export scalar application takes<0.228457seconds,
excluding serialization. Its8469-byte packet has SHA256
`5e0cbe77aac75340a29b40987bf820efa3272e6b421c40ba769cc38cdd9aef9a`;
the source has SHA256
`e61f59d027c536bdcd8e1761123c502cf865ee46a40b74cd15a5308de5c8ba37`.
There are zero new vector/matrix reference actions or contractions,
source/far queries, target reconstructions, inverse/solves, old scientific
producer/fixture replays or source/precision scans.

This consumes a different sufficient majorant of the SAME unresolved
comparison. It is not a rerun of the source, the previous scientific
producer, its fixtures or a different precision. The new application
uses only saved scalar inputs and scalar inequalities. It does not
assert an unseen far inverse-energy upper, comparison-parameter
eligibility, transfer to the actual target, or actual-center/full-border/
cofinal positivity. Robin and RH remain unresolved; no Lean-proof or
generic-method novelty is claimed.


The [scalar norm consumer, directed fixed-comparison certificate and reproduction entry](https://github.com/the-omega-institute/trureturing-experiments/tree/7e5a0a22485af3938723588bbc78117c81e5caef/docs/reports/weil-c27) retain the source, single application and inherited comparison bindings.

### Extend the old-base exclusion to every valid common charge

Reuse the accepted actual common-charge identity and its saved lower,

$$
\mathcal K=m_J-h+\kappa s-E_\phi\ge D_{\rm lo},\qquad s\ge0,
\qquad D_{\rm lo}>169.193163899615576.
$$

This lower is distinct from the refined common-charge UPPER
$\overline D$. The new norm upper and this floor bind to the SAME
actual finite row, original source and old core through their accepted
packet chains. No new source relation or independent endpoint
attainability is assumed.

At the SAME optimistic $t_+$, changing only the fee gives the exact
identity

$$
z_{\rm crit}(D)-Q_J
=z_{\rm crit}(\overline D)-Q_J+\overline D-D.
$$

Consequently every actual-valid $D\ge\mathcal K\ge D_{\rm lo}$ has

$$
\boxed{z_{\rm crit}(D)-Q_J\le
U_{\rm adm}:=U_N+\overline D-D_{\rm lo}<-15.895593038365393<0.}
$$

The exact-rational saved-data application uses the original endpoints.
The extra debit is below14.607513220067395, so it fits inside the
already certified negative budget. At $D=D_{\rm lo}$ the existing
$z\ge Q_J$ and positive first border entry give

$$
\det N_2\ge A_{\rm lo}(-U_{\rm adm})>626827.787500448>0.
$$

Thus this endpoint border is positive definite. The inherited inertia
identity gives a negative direction of the SAME OLD lower target at
$(t_+,D_{\rm lo})$. For every $0<t\le t_+$ and $D\ge\mathcal K$,

$$
L_*+t r^*r+b^*b/D
\preceq L_*+t_+r^*r+b^*b/D_{\rm lo}.
$$

The negative direction therefore persists throughout that family.
Neither endpoint is asserted physically eligible; this stronger
comparison suffices to exclude the actual eligible subset. In
particular the legal shifts supplied by the saved band cap are included,
since $t\le\tau_{\rm band}/h\le t_+$.

This closes the smaller-charge escape for this old-base, fixed-source,
supplied-shift family. It does not repeat the old projection-ceiling
exclusion: that covered only $\tau\le0.0215048994$, while the band
budget reaches approximately0.0272333894. The earlier norm result
covered only $D\ge\overline D$; this application also includes all
actual-valid smaller fees. Affine dependence, inertia and Loewner
monotonicity are reused, without a generic novelty or Lean-proof claim.

The single exact-rational application takes<0.003954seconds, excluding
serialization. Its3155-byte packet has SHA256
`9ed4c784f0f38cb430d48c527fac4478a41577069c7431428c08bc27a0e06435`;
the120-line source has SHA256
`3ddf2f163e70f9af2c1930f4a726ad337b174419407673cba6f4758a6e6f978a`.
There are zero new source/far queries, matrix/vector contractions,
inverses/solves, accepted producer/fixture replays or parameter scans.
The [consumer and exact packet](https://github.com/the-omega-institute/trureturing-experiments/tree/734afcfef0edc6d958a0a64da55e18b55648095a/docs/reports/weil-c27)
retain the original inputs and their common-source bindings.

All inherited common-form/domain, physical-majorant, source/lift,
positive-reference, normalization, full-far and actual-denominator
premises remain. A stronger TRUE baseline, other sources or shifts
beyond the supplied cap are outside this exclusion. The actual retained
form can dominate the rejected lower target and remain positive.
Actual retained/cofinal positivity, Robin and RH remain unresolved.

### Test one explicit twenty-profile direction on the stronger baseline

The preceding old-target exclusion does not decide the stronger baseline.
The already saved frame $A=[\iota_gY,V]$ supplies a different finite test:

$$
A^*L_*A=\operatorname{diag}(G_{JJ},\Sigma_0),\qquad H_{20}=A^*A,
\qquad 0\preceq\overline L-L_*\preceq\delta I.
$$

All these are the SAME archived forms and profiles. For fixed exact
coefficients $w=(g,z)\in\mathbb Q^2\oplus\mathbb Q^{18}$, retain
$m=(u,v)$ in both the good coordinates and conditional mean. Then

$$
\begin{aligned}
B_w&=g^*G_{JJ}g+z^*\Sigma_0z,\\
\mu_w&=c g_1+d g_2+\beta_Jz+m(g+Bz),\\
|bAw|&\le|\mu_w|+\sqrt{\overline\Delta\,z^*Sz}.
\end{aligned}
$$

Here $G_{JJ}=\left(\begin{smallmatrix}a&c\\c&d\end{smallmatrix}\right)$,
$y=mB+q$ and $qq^*\preceq\overline\Delta S$ are the saved conditional
source relation. Ordinary Cauchy and the baseline order give the full
sufficient upper

$$
U(w)=\operatorname{ub}B_w+\delta\operatorname{ub}(w^*H_{20}w)
+t_+\operatorname{ub}|rAw|^2
+\frac{\left(\operatorname{ub}|\mu_w|
+\sqrt{\overline\Delta\operatorname{ub}(z^*Sz)}\right)^2}{D_{\rm lo}}.
$$

A negative $U(w)$ would certify a negative direction of the SAME stronger
lower construction. The existing monotonicity then covers all
$0<t\le t_+$ and $D\ge\mathcal K\ge D_{\rm lo}$. Reference or midpoint
data can choose $w$; the original enclosures must certify it.

One nominal Woodbury selection, with one new combined17-reference action
and two2x2 selection inverses, does not pass this test. Its fixed dyadic
vector gives

| Quantity | Saved enclosure |
|---|---|
| Old-base quadratic $B_w$ |$[4.2597335,4.2597336]\cdot10^{37}$|
| Euclidean norm squared $w^*H_{20}w$ |$[4.3024170,4.3024171]\cdot10^{171}$|
| Full stronger-target upper $U(w)$ |$[6.5391654,6.5391655]\cdot10^{37}$|

The first row is strictly positive. Since all added terms and the true
baseline gain are nonnegative, this particular vector cannot be a
negative witness even for the old target. A positive sufficient UPPER
alone would be inconclusive; the separate strict base LOWER rules out
this vector. Neither fact decides the stronger form's sign or excludes
another vector. The earlier negative border budget is not the quadratic
value or normalization of this selected vector.

This application does not distinguish selection mismatch, rounding
amplification and loss of common relations as causes of failure. No
source, direction, parameter or precision retry follows. A further
witness-recovery method must retain its actual elimination relations;
the saved vector and all component bounds can be consumed without
rerunning this selection.

The sole1024-working/640-export application takes<0.102317seconds,
excluding serialization. Its9259-byte packet has SHA256
`db3c21bc3ddb8af0784521f27311d6fd75312b7371a68dd3410c66fbd371c3b7`;
the232-line source has SHA256
`ebeabd3114efd0fb109082cc96f7c1ba11fc4a4a010c57202ff55c58b0bf8626`.
The [explicit vector, source and directed budget](https://github.com/the-omega-institute/trureturing-experiments/tree/48619c68429c987a929fbb1ea0af0aba5aa9f973/docs/reports/weil-c27)
retain this fixed test. Every old source, solve, physical/Euclidean Gram
and passed fixture is reused. No new large inverse/solve, source/far query
or scientific-producer replay runs.

All inherited actual common-form/domain, source/lift, normalization,
reference, conditional-ellipsoid, complete-far and true-baseline-order
premises remain. This applies existing block minimization, Rayleigh and
Cauchy methods without a generic novelty or Lean-proof claim. The
stronger-target sign, actual retained/cofinal positivity, Robin and RH
remain unresolved.

### Normalize a coherent source-dependent negative family

The accepted negative border budget supplies an exact source-dependent
family, even though the preceding fixed nominal direction failed. No
second nominal vector is selected. The new calculation bounds the norm
of the exact family before paying the stronger-base allowance.

Write the saved negative pivot as $-d<0$, put
$J=[T,e_0]$ and $\mathcal D=\operatorname{diag}(I_2,J)$. The existing
congruence gives

$$
\mathcal D^*A^*L_*A\mathcal D
=\operatorname{diag}(C_0,-d),\qquad
C_0=\operatorname{diag}(G_{JJ},P_+)\succ0.
$$

For each SAME actual source realization, write its two rows on
$A\mathcal D$ as $[F,k]$ and define

$$
\Lambda=\operatorname{diag}(t_+,D_{\rm lo}^{-1}),\qquad
C=\Lambda^{-1}+FC_0^{-1}F^*,\qquad
p=C^{-1}k,\qquad v=-C_0^{-1}F^*p.
$$

These are exact mathematical objects, not a computation using the
reference inverse. Standard block minimization gives the coefficient
vector $w=\mathcal D(v,1)$ and

$$
\begin{aligned}
(Aw)^*T_0(Aw)&=-d+k^*C^{-1}k,\\
v^*C_0v&=p^*(C-\Lambda^{-1})p\le k^*C^{-1}k,\\
\frac{\det N}{\det C}&=1-\frac{k^*C^{-1}k}{d},
\qquad N=C-kk^*/d.
\end{aligned}
$$

Here $T_0=L_*+t_+r^*r+b^*b/D_{\rm lo}$ is the SAME endpoint
comparison. This family allows its exact vector to depend on the
source; it does not assert one common fixed vector for every source.

The restricted-border identification is essential. Its two good rows
are $(a,c)$ and $(c+u,d_J+v_m)$, where
$G_{JJ}=\left(\begin{smallmatrix}a&c\\c&d_J\end{smallmatrix}\right)$
and the measured pair is $m=(u,v_m)$. Their inverse metric is exactly

$$
\begin{pmatrix}
a&c+u\\c+u&d_J+2v_m+Q_J
\end{pmatrix},\qquad Q_J=mG_{JJ}^{-1}m^*.
$$

Consequently setting the good far energy to $Q_J$ in the accepted
complete budget gives THIS restricted twenty-profile border. It does
not assert that the full good far energy attains its projection lower.
The existing bound $z_{\rm crit}-Q_J\le U_{\rm adm}<0$ therefore
supplies the inherited $\det N\ge\Delta_N>0$ for the restricted
family as well.

Use the saved complete positive-core energy upper $E_b$, reference
source energy upper $E_r$ and reference factor $\eta<1$. Two diagonal
uppers and a determinant upper are

$$
\begin{aligned}
C_{11}&\le c_1=t_+^{-1}+\operatorname{ub}a+E_r/(1-\eta),\\
C_{22}&\le c_2=D_{\rm lo}+\operatorname{ub}d_J
+2\operatorname{ub}v_m+\operatorname{ub}Q_J+E_b,\\
\det C&\le c_1c_2\le\overline\Delta_C.
\end{aligned}
$$

Here $\overline\Delta_C$ rounds the product upwards. The complete $E_b$ already includes the SAME conditional mean and
residual; no separate source extremes are asserted jointly attainable.
With downward $\vartheta=\Delta_N/\overline\Delta_C$, define

$$
\mu=d_{\rm lo}\vartheta>0,\qquad
E_+=d_{\rm up}(1-\vartheta).
$$

Then this exact family has old-target quadratic at most $-\mu$ and
positive-part energy at most $E_+$. Dividing by a determinant UPPER is
what turns the border determinant LOWER into a primal energy gap.

The new Euclidean calculation uses $H=A^*A$ and the existing actual
positive inverse enclosure $P_+^{-1}\preceq R/(1-\eta)$. If
$H_{gg}=Y^*Y$ and $H_{VV}=V^*V$, the trace bound is

$$
\operatorname{tr}(H_+C_0^{-1})\le
\tau:=\operatorname{ub}\operatorname{tr}(H_{gg}G_{JJ}^{-1})
+\frac{\operatorname{ub}\operatorname{tr}(T^*H_{VV}TR)}{1-\eta}.
$$

Here $H_+$ is the full positive-coordinate block of
$\mathcal D^*H\mathcal D$, including its mixed good/core entries.
Those entries contribute zero to its trace against block-diagonal
$C_0^{-1}$; they are not assumed zero in the Gram. The PSD trace
inequality and triangle inequality give

$$
\|Aw\|^2\le
N_{\rm fam}:=\left(\sqrt{\operatorname{ub}(H_{VV})_{00}}
+\sqrt{\tau E_+}\right)^2.
$$

Thus the complete sufficient stronger-target upper is

$$
-\mu+\delta N_{\rm fam},\qquad
\delta=2\kappa\epsilon,
$$

and a certified sufficient coefficient allowance is any
$0\le\delta'<\delta_{\rm cert}$, where
$\delta_{\rm cert}$ is a downward bound for $\mu/N_{\rm fam}$.
This allowance is not a maximal perturbation or an actual generalized
spectral gap. All exact PSD, common-source, reference, normalization,
full original allowance and domain premises remain.

The single directed application gives these outward enclosures of the
computed certificate values. They are not ranges of attainable source
values or actual eigenvalues.

| Certificate quantity | Enclosure of its computed value |
|---|---|
| Joint Euclidean energy trace upper $\tau$ | $[1.0100202,1.0100203]\cdot10^{134}$ |
| Normalized old negative margin lower $\mu$ | $[1.6070745,1.6070746]\cdot10^{-33}$ |
| Family norm squared upper $N_{\rm fam}$ | $[1.1732857,1.1732858]\cdot10^{103}$ |
| Sufficient coefficient threshold lower $\delta_{\rm cert}$ | $[1.3697212,1.3697213]\cdot10^{-136}$ |
| Complete stronger-family quadratic upper | $[4.8662150,4.8662151]\cdot10^{-32}$ |

The original allowance gives
$\delta\in[4.2844825,4.2844826]\cdot10^{-135}$.
Its norm payment upper is contained in
$[5.0269224,5.0269225]\cdot10^{-32}$, exceeding the certified
negative margin in this sufficient bound. Thus the stronger-target test
is inconclusive. Neither the positive sufficient upper nor the smaller
sufficient coefficient threshold establishes a stronger-form sign or an
upper limit on its true tolerance. For a separately justified gain bound
$0\preceq E\preceq\delta'I$ with
$0\le\delta'<1.3697212\cdot10^{-136}$, the same family certificate
would remain strictly negative; no such replacement for the actual
allowance is assumed.

The new information is the correctly normalized exact-family gap and
norm bound. The uniform trace discards directional source geometry;
a further method must preserve that geometry or supply an independently
stronger joint estimate. No direction, parameter, source, precision or
norm-refinement retry follows this inconclusive application.

The sole1024-working/640-export application takes<0.043857seconds,
excluding serialization. Its5733-byte packet has SHA256
`6d81b66716ed241500982bdc3e46cf5b096a1e4922759b1ff26b255f763b2018`;
the225-line source has SHA256
`ccd86c9281ad3ed832659dae760fec62ef97c3d62dce938033e36f945c70fe33`.
One joint Euclidean geometry trace is new. There is no fixed-vector
selection, new reference action, inverse, solve, source/far query or
accepted producer/fixture replay. The original reference, complete
source energies, determinant certificate and all original allowances
are reused.

The complete source and directed result are retained at [the immutable experimental commit](https://github.com/the-omega-institute/trureturing-experiments/tree/2d9951b20841ea1c839db256382ce33b1712e79e/docs/reports/weil-c27).
This is an application of existing block minimization, determinant,
PSD trace and energy inequalities, without generic novelty or a Lean
proof. The actual stronger-target sign, retained/cofinal positivity,
Robin and RH remain unresolved.


### Pay the same family's norm through its source responses

Keep the preceding exact source-dependent minimizer, normalized margin
$\mu$ and energy cap $E_+$. No new nominal vector is chosen. With
$\Lambda=\operatorname{diag}(t_+,D_{\rm lo}^{-1})$ and
$p=C^{-1}k$, the accepted relations imply

$$
p^*\Lambda^{-1}p\le p^*Cp=k^*C^{-1}k\le E_+.
$$

This coefficient ellipse holds for the SAME actual source as $p$, the
measured pair $m$ and the conditional residual. It does not require a
numerical inverse of $C$.

Let $H=A^*A$ be the saved twenty-profile Euclidean Gram. The physical
columns of $A$ are ordered as two good profiles followed by the eighteen
old lifted columns. Write $e_-$ for coordinate $2$ in this order, and
$H_{VV}$ for the eighteen-column Gram. Put

$$
Q=TRT^*,\qquad \gamma_\eta=\frac{\eta}{1-\eta}.
$$

Here $R$ is only the accepted positive inverse REFERENCE. The exact
minimizer and its negative margin continue to use the actual positive
core inverse $P_+^{-1}$.

The good source row is the first row of $G_{JJ}$; the second row is
the second row of $G_{JJ}$ plus the measured $m$. Consequently its
reference responses have exact good coordinates $e_1$ and
$e_2+G_{JJ}^{-1}m^*$. Define five coefficient columns in the original
frame by

$$
\begin{aligned}
z_-&=e_-,&
z_r&=\binom{e_1}{Q\rho^*},&
z_{b0}&=\binom{e_2}{Q\beta_J^*},\\
z_{b1}&=\binom{G_{JJ}^{-1}e_1}{QB_1^*},&
z_{b2}&=\binom{G_{JJ}^{-1}e_2}{QB_2^*}.
\end{aligned}
$$

The rows $B_1,B_2$ belong to the already saved conditional regression.
The measured-source response is
$z_b(m)=z_{b0}+m_1z_{b1}+m_2z_{b2}$. The new Gram is

$$
\mathcal G_5=[z_-,z_r,z_{b0},z_{b1},z_{b2}]^*
H[z_-,z_r,z_{b0},z_{b1},z_{b2}].
$$

The negative-column norm $h_0$ is reused. The two regression reference
actions are reused; only the previously unsaved $\rho$ and $\beta_J$
response products and the new Euclidean contractions are computed.
No inverse, solve or new physical source query is needed.

Let $E(m)$ be the two-response Gram of $z_r,z_b(m)$ in $H$, and
$n(m)=(z_-^*Hz_r,z_-^*Hz_b(m))$. The reference nominal family
$x_0=z_--z_rp_1-z_b(m)p_2$ satisfies

$$
\|Ax_0\|^2\le N_0:=h_0+E_+\ell_2
+2\sqrt{E_+s_0},
$$

where $\ell_2$ bounds the largest eigenvalue of
$\Lambda^{1/2}E(m)\Lambda^{1/2}$ and
$s_0$ bounds $n(m)\Lambda n(m)^*$. This follows by applying the
coefficient ellipse to both the quadratic term and the complete
negative-column cross term. The source $m$ remains shared throughout
these contractions. Interval uppers do not assert simultaneous
attainability of their endpoints.

For the real two-by-two response matrix, diagonal uppers $a,d$ and an
absolute offdiagonal upper $c$ give the elementary Rayleigh upper; choose

$$
\ell_2=\frac{a+d+\sqrt{(a-d)^2+4c^2}}2.
$$

This is a response-space bound. It is not an eigenvalue enclosure for
the original indefinite physical operator.

The SAME conditional residual $q=y-mB$ obeys
$q^*q\preceq\overline\Delta S_F$. Its response cost is controlled by
one new nonnegative trace,

$$
\tau_Q=\operatorname{tr}(H_{VV}QS_FQ),\qquad
\|VQq^*p_2\|\le
\sqrt{E_+\overline\Delta\tau_Q/D_{\rm lo}}.
$$

The trace inequality follows directly from the outer-product order;
$S_F$ need not be invertible. The bound uses this same source's
$p_2$, with $D_{\rm lo}|p_2|^2\le E_+$. Neither an independence
assumption nor an independent selection of $p_2$ and $q$ is used.

Finally, let $f_P$ be the positive-core source column multiplied by the
SAME exact $p$. Its actual inverse energy is at most $E_+$. The accepted
two-sided inverse-reference relation gives

$$
R\preceq(1+\eta)P_+^{-1},\qquad
f_P^*Rf_P\le(1+\eta)E_+.
$$

With the already saved
$\tau_P=\operatorname{tr}(T^*H_{VV}TR)$, relative inverse perturbation
and the PSD trace bound give

$$
\|VT(P_+^{-1}-R)f_P\|
\le\gamma_\eta\sqrt{\tau_P(1+\eta)E_+}.
$$

Thus the full trace enters only the inverse-reference ERROR. The
complete norm bound is

$$
N_{\rm dir}=\left(
\sqrt{N_0}
+\sqrt{E_+\overline\Delta\tau_Q/D_{\rm lo}}
+\gamma_\eta\sqrt{\tau_P(1+\eta)E_+}
\right)^2.
$$

All cross terms between nominal, conditional and inverse-error vectors
are paid by this triangle inequality. The complete sufficient comparison
is still $-\mu+\delta N_{\rm dir}$ with the original $\delta$.
No smaller baseline allowance, replacement source or truncated parameter
range is assumed.

These are applications of existing block minimization, ellipsoid
support, Schur conditioning and relative inverse inequalities. For the
related use of positive metrics on indefinite systems,
[Vecharynski--Knyazev, Definition2.2, Theorem2.3 and Corollary2.4](https://arxiv.org/abs/1104.4530)
assume a nonsingular real symmetric matrix and an SPD preconditioner,
and compare the preconditioned spectrum with that of its absolute
value. Their result does not supply this physical Euclidean norm or
commute absolute value with a general congruence. The response Gram and
error payment above supply the required source-specific metric
comparison; no general-method novelty is claimed.


The sole directed application yields the following outward enclosures of
COMPUTED certificate values. They are not source-attainable ranges or
actual eigenvalues.

| Certificate quantity | Outward enclosure |
|---|---|
| Nominal reference family norm-squared upper $N_0$ | $[8.3700696,8.3700697]\cdot10^{101}$ |
| Conditional response norm upper | $[3.3845050,3.3845051]\cdot10^{50}$ |
| Inverse-reference error norm upper | $[1.3616977,1.3616978]\cdot10^{24}$ |
| Complete family norm-squared upper $N_{\rm dir}$ | $[1.5708394,1.5708395]\cdot10^{102}$ |
| Original gain payment upper | $[6.7302343,6.7302344]\cdot10^{-33}$ |
| Complete sufficient quadratic upper | $[5.1231598,5.1231599]\cdot10^{-33}$ |
| Sufficient coefficient threshold lower | $[1.0230672,1.0230673]\cdot10^{-135}$ |

The original $\delta$ remains in
$[4.2844825,4.2844826]\cdot10^{-135}$, and the preceding normalized
margin lower remains in $[1.6070745,1.6070746]\cdot10^{-33}$.
The new norm upper improves the earlier trace upper by a factor in
$(7.46,7.48)$, but its complete gain payment still exceeds the
certified margin. The coefficient threshold is sufficient only, not
maximal. The positive sufficient upper is inconclusive about the
actual stronger-target sign or the exact family's optimal tolerance.

Even deleting the other two terms from THIS estimator leaves its
nominal-only computed expression

$$
-\mu+\delta N_0>1.97\cdot10^{-33}.
$$

This comparison concerns only fixed computed sufficient bounds.
It is not a lower bound for the exact physical quadratic or family
norm. It shows that sharpening just the conditional or inverse-error
payment, while leaving this nominal upper unchanged, cannot make this
estimator negative. A next estimate must preserve more of the joint
$p,C,m,q$ relation or provide an independent joint comparison. No
source, direction, parameter, precision or present-formula retry
follows.

The single1024-working/640-export application takes<0.046938seconds
excluding serialization. Its263-line source has SHA256
`961c1ab5dd31d8e351cd824df8d25266c9c530060dd74bec9e6fa5901b3e8aac`;
the11399-byte packet has SHA256
`6e12d77e100465978d3a9eb777280de15c1942256cbedf62c337fbe120f1c7d3`.
One five-response Gram, one conditional Euclidean trace and two
previously unsaved reference-vector products are new. The two saved
regression reference actions, previous accepted normalized margin,
full trace and all scientific producers and fixtures are reused without
replay. No new inverse, solve, source/far query or fixed-vector
selection is made.

The [source and directed packet at the immutable experimental commit](https://github.com/the-omega-institute/trureturing-experiments/tree/f5eeb74c8594a9f168a21e6a9da1ff794fbe243d/docs/reports/weil-c27)
retain the sole application. All inherited actual/common-source,
domain, exact-frame, PSD physical and Euclidean, conditional source,
source-energy, two-sided inverse-reference, complete original
512-metadata allowance, endpoint/charge and baseline-order premises
remain. This is a source-specific application of established methods,
without a generic novelty or Lean-proof claim. The stronger-target
sign, actual retained/cofinal positivity, Robin and RH remain unresolved.


### Retain exact first-row stationarity before paying the norm

The preceding free coefficient ellipse discards the first equation of
$Cp=k$. Retain that equation for the SAME exact source-dependent
minimizer. This changes the coefficient set; it does not refine the
stopped nominal-response estimator or select a new fixed vector.
The Schur elimination and quadratic minimization used here are standard:
[Boyd--Vandenberghe, *Convex Optimization*, Appendix A.5.5,
pp.650--651](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
Their source-specific application below is repo-derived, without a
claim of a new general matrix inequality.

All quantities in this section are real, as in the inherited even
finite frame. Write

$$
C=\begin{pmatrix}A&c\\c&b\end{pmatrix},\qquad
k=\binom{k_1}{k_2},\qquad s=b-c^2/A.
$$

The first source is fixed independently of the uncertain second
source, so $A$ and $k_1$ are independent of that uncertainty. The exact
relations are

$$
\begin{aligned}
p_1&=k_1/A-(c/A)p_2,\\
p_2&=(k_2-ck_1/A)/s,\\
p^*Cp&=k_1^2/A+sp_2^2.
\end{aligned}
$$

In the existing positive-source representation,

$$
s=D_{\rm lo}
+f_b(C_0+t_+f_r^*f_r)^{-1}f_b^*\ge D_{\rm lo}.
$$

Hence the inherited $p^*Cp\le E_+$ also gives

$$
D_{\rm lo}p_2^2\le E_+-k_1^2/A.
$$

This constraint is used together with the signed Schur ratio, rather
than permitting $p_1$ and $p_2$ to vary independently in the former
ellipse.

Use the inherited inverse reference $R$, transport $T$, measured pair
$m=(m_1,m_2)$ and conditional core row

$$
b_V=b_{J,V}+m\Gamma+q,\qquad q^*q\preceq\overline\Delta S_F.
$$

The saved trace packet already supplies $R(\Gamma T)^*$, the two
regression reference actions. The only new mixed source quantities are
the two scalar entries

$$
\ell=(r_VT)R(\Gamma T)^*.
$$

No reference vector action is repeated. With the saved reference
energies $E_r=r_VTRT^*r_V^*$, $E_{\rm res}$ and
$E_{\rm complete}$, a reference centre and a complete radius for the
actual cross entry are

$$
\begin{aligned}
c_{\rm ref}
&=G_{12}+m_1+(r_VT)R(b_{J,V}T)^*+\ell m^*,\\
|c-c_{\rm ref}|
&\le\sqrt{E_rE_{\rm res}}
+\frac{\eta}{1-\eta}\sqrt{E_rE_{\rm complete}}.
\end{aligned}
$$

Here the finite reference cross is saved, not recontracted. The
conditional part uses Cauchy in the reference metric. The inverse
part uses the existing two-sided relative certificate. In particular,
$A=t_+^{-1}+G_{11}+r_VTP_+^{-1}T^*r_V^*$ is enclosed using the same
$E_r$ and $\eta$.

The second diagonal also has an available lower bound. Set

$$
B_J=D_{\rm lo}+G_{22}+2m_2+Q_J,
\qquad Q_J=mG^{-1}m^*.
$$

The saved mean reference energy $E_{\rm mean}$ and residual reference
energy upper give, by reverse triangle and the two-sided certificate,

$$
b\ge B_J+
\frac{\bigl(\sqrt{\operatorname{lb}E_{\rm mean}}
-\sqrt{E_{\rm res}}\bigr)_+^2}{1+\eta}.
$$

Its upper is the previously accepted $c_2$. The saved finite negative
coordinate plus the intersected far-coordinate interval enclose
$k_2$. These data enclose $s$ and the Schur ratio for $p_2$. Intersect
that interval with the energy bound above. Denote the resulting
interval by $[p_-,p_+]$. Empty or uncertified positive denominator
intervals stop the application.

Let $K$ be the saved five-response Euclidean Gram in its existing
order. Put

$$
x=k_1/A,\qquad y=c/A,\qquad
h_0=(1,-x,0,0,0)^*,\qquad
h_2=(0,y,-1,-m_1,-m_2)^*.
$$

For each SAME realization, the nominal reference-family norm squared
is exactly

$$
\mathcal N(p_2)=(h_0+p_2h_2)^*K(h_0+p_2h_2).
$$

The exact $K$ is PSD, so this quadratic is convex in real $p_2$.
Consequently

$$
\mathcal N(p_2)\le
\max\{\mathcal N(p_-),\mathcal N(p_+)\}.
$$

Three scalar contractions of the saved Gram enclose the constant,
half-linear and quadratic coefficients. Upward evaluation at both
endpoints gives $N_{\rm stat,0}$. This endpoint comparison holds for
every realization even though $x,y,m,p_2$ are dependent. Interval
hulls need not have jointly attainable corners; no such attainability
or PSD property of a full entry box is used.

Reuse the preceding conditional Euclidean trace $\tau_Q$ and the
complete inverse-reference error bound $e_{\rm inv}$. With
$P_2=\max(|p_-|,|p_+|)$ the complete bound is

$$
\begin{aligned}
e_{\rm cond}&\le
P_2\sqrt{\overline\Delta\tau_Q},\\
N_{\rm stat}&=
\bigl(\sqrt{N_{\rm stat,0}}+e_{\rm cond}+e_{\rm inv}\bigr)^2,\\
U_{\rm stat}&=-\mu+\delta N_{\rm stat}.
\end{aligned}
$$

The SAME family still has positive energy at most $E_+$, so the
accepted inverse-reference norm payment remains applicable.
The margin $\mu$, endpoint parameters and complete original $\delta$
are unchanged. Strict $U_{\rm stat}<0$ would exclude only the SAME
stronger endpoint comparison under all inherited premises. A
nonnegative sufficient upper is inconclusive about its actual sign.

The single directed application gives:

| Computed sufficient quantity | Enclosure |
|---|---:|
| Signed exact second coefficient interval | $[8.6391331,12.4704686]\cdot10^{-18}$ |
| Signed exact first coefficient interval | $[1.6769537,4.3412752]\cdot10^{-19}$ |
| Nominal norm-squared upper $N_{\rm stat,0}$ | $[3.0020727,3.0020728]\cdot10^{101}$ |
| Conditional response norm upper | $[1.6107661,1.6107662]\cdot10^{50}$ |
| Complete norm-squared upper $N_{\rm stat}$ | $[5.0266447,5.0266448]\cdot10^{101}$ |
| Original gain payment upper | $[2.1536571,2.1536572]\cdot10^{-33}$ |
| Complete sufficient quadratic upper | $[5.4658264,5.4658265]\cdot10^{-34}$ |
| Sufficient coefficient threshold lower | $[3.1971117,3.1971118]\cdot10^{-135}$ |

The normalized inherited margin remains in
$[1.6070745,1.6070746]\cdot10^{-33}$ and the original gain coefficient
remains in $[4.2844825,4.2844826]\cdot10^{-135}$. The complete
norm-squared upper is smaller than the preceding response-ellipse
upper by a factor in $(3.12,3.13)$. Its original gain payment still
exceeds the certified margin by a factor in $(1.34,1.35)$.
The complete sufficient upper is positive, so this application is
inconclusive about the SAME stronger comparison's actual sign.
The threshold is sufficient only, not maximal.

The signed coefficient intervals show that the exact first-row
constraint supplies information discarded by the previous ellipse.
They do not establish a jointly attained worst source or determine the
second-row source response. This estimator stops here. No present
formula, precision, source, direction or parameter retry follows.
Further joint information includes
$sp_2=k_2-ck_1/A$ coupled with the SAME residual $q$ that contributes
to both $c,k_2$ and the physical response; separately enclosing these
quantities has not settled the full payment.

The258-line source has SHA256
`e16031be55706d509027664c7bb0132a7a862e0fc1b1c31caeaec57dd0f28972`;
the9170-byte packet has SHA256
`169e858deb9f06ca677098da032849450074f794627eb0174711717abc5ca1b8`.
The one1024-working/640-export application takes<0.038870seconds
excluding serialization. Its only new geometric contractions are the
two mixed scalar dots and three contractions of the saved response
Gram. All accepted reference actions, Grams, traces, energies,
normalized margin, original complete allowance and scientific
producers/fixtures are reused without replay. No new inverse, solve,
reference vector action, source/far query or fixed vector is selected.

The [source and directed packet at the immutable experimental commit](https://github.com/the-omega-institute/trureturing-experiments/tree/54668e4c10f8df1043cb23534502d0ca2bc7dd20/docs/reports/weil-c27)
retain the sole application. All inherited actual/common-source,
domain, exact-frame, physical and Euclidean PSD, conditional-source,
two-sided reference, complete original512metadata allowance and
endpoint/charge/baseline-order premises remain. This is a
source-specific application of established inequalities. No generic
novelty, actual stronger-target sign, actual retained/cofinal
positivity, Robin, RH or Lean proof is claimed.


### Compare the same source's negative energy and physical cost jointly

The preceding scalar norm upper remains valid. A different comparison
retains the source-dependent negative energy until after the physical
cost is added. All saved norm and error bounds are reused unchanged.
This is a source-specific application of standard Schur elimination,
energy completion and quadratic norm expansion; the mathematical
method is not claimed as new. The Schur identities are those already
cited from Boyd--Vandenberghe, Appendix A.5.5.

For each SAME real source realization, reuse the exact minimizer and
write

$$
\alpha=k_1^2/A,\qquad
h=b-c^2/A>0,\qquad
\beta=k_2-ck_1/A,\qquad p_2=\beta/h.
$$

The accepted pointwise energy identity gives

$$
p^*Cp=\alpha+\beta^2/h\le E_+,
\qquad\beta^2\le eh,\quad e=E_+-\alpha\ge0.
$$

Here $E_+$ is the inherited uniform energy cap, whereas $\alpha,h$
and $\beta$ are the SAME realization's exact quantities. The saved
first-row remaining-energy upper already encloses $e$.

Let $n_0,\gamma,\rho_H$ denote the three saved coefficients of the
nominal Euclidean norm quadratic:

$$
\mathcal N_{\rm nom}
=n_0+2p_2\gamma+p_2^2\rho_H,\qquad \rho_H\ge0.
$$

These are coefficients of the SAME nominal reference response, with
the actual source-dependent coefficients retained. The conditional
row and inverse-reference effects are still separate paid errors.
Substituting $p_2=\beta/h$ and using the energy inequality only on
the nonnegative square term gives

$$
\mathcal N_{\rm nom}
\le n_0+\frac{2\beta\gamma+e\rho_H}{h}.
$$

The sign of $\beta\gamma$ is kept. No absolute cross support is
substituted. In particular, $\beta$ in the energy, cross and negative
quadratic belongs to one realization.

The previous nominal norm-squared upper $N_0$ and complete norm-error
uppers $e_{\rm cond},e_{\rm inv}$ are unchanged. Set

$$
\varepsilon=e_{\rm cond}+e_{\rm inv},\qquad
K_{\rm err}=2\sqrt{N_0}\,\varepsilon+\varepsilon^2.
$$

Triangle and $\mathcal N_{\rm nom}\le N_0$ imply

$$
\|Aw\|^2\le\mathcal N_{\rm nom}+K_{\rm err}.
$$

This is the expansion of the existing complete norm payment. It
neither sharpens its components nor drops their cross terms.

The old endpoint's exact quadratic on this family is
$-d+\alpha+\beta^2/h$. The SAME strengthened endpoint lower comparison
adds at most $\delta\|Aw\|^2$ under the inherited baseline ordering.
Consequently its family quadratic satisfies

$$
Q_{\rm str}(w)\le-\Omega/h,
$$

where

$$
\boxed{
\Omega=
\bigl(d-\alpha-\delta(n_0+K_{\rm err})\bigr)h
-\beta^2-2\delta\beta\gamma-\delta e\rho_H.
}
$$

This comparison forms the SAME source's negative energy minus its
physical cost before taking a uniform bound. It uses the original
$\delta$, endpoint $t_+$ and charge floor $D_{\rm lo}$. No new
source, minimizer, reference action, inverse, Gram or trace is needed.

Evaluate the saved scalar enclosures outward, using the accepted
upper for $e$ and the upper for $\rho_H$. The exact $\rho_H$ is
nonnegative, so these substitutions have the required direction.
The interval products enclose every common realization without
asserting that their corners can occur simultaneously. Round the
resulting lower $\underline\Omega$ to the640 grid before normalization.
For the saved $h\in[h_-,h_+]$,

$$
Q_{\rm str}(w)\le
\begin{cases}
-\underline\Omega/h_+,&\underline\Omega>0,\\
-\underline\Omega/h_-,&\underline\Omega\le0.
\end{cases}
$$

Only a strictly negative complete upper excludes this endpoint lower
comparison. Monotonicity then covers the inherited dominated parameter
range $0<t\le t_+$ and $D\ge K\ge D_{\rm lo}$ for each SAME source.
The exact witnessing vector may depend on that source; a common fixed
vector is not asserted. The comparison is the particular sufficient
lower comparison used by this proof route. Its failure does not
determine the actual retained Weil form or its cofinal limit.

The single directed application gives:

| Computed sufficient quantity | Enclosure |
|---|---:|
| Complete squared-error cost upper $K_{\rm err}$ | $[2.0245720,2.0245721]\cdot10^{101}$ |
| Complete coefficient $d-\alpha-\delta(n_0+K_{\rm err})$ | $[7.1552412,7.1552413]\cdot10^{-32}$ |
| Signed cross gain $-2\delta\beta\gamma$ | $[3.5658829,4.0047579]\cdot10^{-31}$ |
| Conditional energy-cost upper $\delta\overline e\,\overline\rho_H$ | $[9.0037697,9.0037698]\cdot10^{-31}$ |
| Rounded sufficient numerator lower $\underline\Omega$ | $[2.0929367,2.0929368]\cdot10^{-30}$ |
| Complete uniform quadratic upper | $[-3.6680036,-3.6680035]\cdot10^{-33}$ |

Thus the rounded numerator lower is strictly positive and the
complete uniform upper is strictly negative. Under ALL inherited
premises, every admissible SAME source has a source-dependent
negative vector for this particular strengthened endpoint LOWER
comparison, throughout its dominated range
$0<t\le t_+$ and $D\ge K\ge D_{\rm lo}$.
This excludes that sufficient comparison route. It does not establish
a common fixed vector, an actual retained/cofinal Weil sign, Robin
or RH. The original allowance and every saved error payment remain.

The positive sufficient upper from the preceding norm estimate was
inconclusive. The new result comes from retaining the SAME source's
negative energy and physical cost in one numerator. It does not
invalidate the older norm bound or sharpen its components.
Under the stated premises, this lower-comparison route now stops;
continued research requires the actual retained form or a different
comparison with an explicitly justified bridge to it.

The170-line source has SHA256
`d64767daa7375eb460e44d7051b5c966c1ed38ec85797dbb86191fb753503d03`;
the7434-byte packet has SHA256
`cdb77c01221bd7289c5c593c928360471075b4d43850aec7bc75c410d9cf09da`.
The sole1024-working/640-export scalar application takes
<0.029441seconds excluding serialization. It performs zero new
geometric contractions, Grams, traces, reference actions, inverses,
solves, source/far queries or fixed-vector selections. All accepted
scientific producers and fixtures are reused without replay; no
source, direction, parameter, precision or present-formula retry is
performed.

The [source and directed packet at the immutable experimental commit](https://github.com/the-omega-institute/trureturing-experiments/tree/d21b88f6c9c4db3a7d16b0668680a33a63b4025e/docs/reports/weil-c27)
retain the single application. This is a numerical certificate for
the specified conditional comparison, not a Lean proof or a generic
novelty claim. All inherited actual/common-source, domain,
exact20frame, physical and Euclidean PSD, conditional-source,
two-sided reference, complete original512metadata allowance,
normalization, endpoint-charge and baseline-order premises remain.

## One propagated positive row for the actual prime slack

Keep the SAME actual $c=27$ clipped prime operator, common form/domain,
global cancellation $H_{\rm ext}-T=A_\Gamma-\Lambda-C_{\rm p}$,
and $\Lambda\preceq A_\Gamma-(59/10)I$. Reuse the
[weighted Schur formula](liu2026tailcompensation.md#a-source-formula-application-to-the-actual-prime-block-at-c9).
The particular old endpoint lower comparison remains excluded.
The application here only sharpens a global bound on the actual
prime operator; it supplies no sign of the actual retained form.

Put $L=\log27/2$ and

$$
q_0(x)=1+\frac{29}{50}(x/L)^2,\qquad
q_1=C_{\rm p}q_0,\qquad
R_1=\mathop{\rm ess\,sup}_{x\in(-L,L)}
\frac{C_{\rm p}^2q_0(x)}{q_1(x)}.
$$

This is one canonical positive-weight propagation, not a new Schur
theorem or a weight optimization. Both $q_0$ and $q_1$ are even.
The shift $-\log2$ is active everywhere on $[0,L]$, so
$q_1\ge(\log2)/\sqrt2>0$ there and, by reflection, on the full
interval. Its upper bound is finite because the prime sum is finite.

### Exact ordered clipping and a finite ratio certificate

For $x\in[0,L]$ use $e=\exp(L-x)\in[1,\sqrt{27}]$.
A signed shift has factor $a=n$ or $1/n$, with weight
$w_n=(\log p)/\sqrt n$ when $n=p^k$. It is active exactly when

$$
a<e<27a.
$$

An ordered two-step path $(a,b)$ contributes to $C_{\rm p}^2q_0$
only when, in addition, $ab<e<27ab$. Thus both its intermediate
and final points must remain in the interval. The possible switches
$a,27a,ab,27ab$ are rational. Group equal factors and sort those in
$(1,\sqrt{27})$ exactly; their membership is decided by rational
squares. This supplies the exact cell order independently of the
uncertain logarithms. A rational sample between consecutive switch
labels only selects the constant active set; it is not sampled
quadrature or a numerical maximum search. Isolated switch points
do not change the operator or its essential bound.

On an exact normalized cell $[l,r]$, write $z=(1-t)l+tr$.
Each term $1+(29/50)(z+s)^2$ has degree-two Bernstein coefficients

$$
1+\frac{29}{50}(l+s)^2,\quad
1+\frac{29}{50}(l+s)(r+s),\quad
1+\frac{29}{50}(r+s)^2.
$$

Let $D_i,N_i$ be the resulting coefficients of $q_1$ and
$C_{\rm p}^2q_0$. All three $D_i$ are certified positive. Since
the Bernstein basis functions $B_i(t)$ are nonnegative,

$$
\frac{\sum_iN_iB_i(t)}{\sum_iD_iB_i(t)}
=\sum_i\frac{D_iB_i(t)}{\sum_jD_jB_j(t)}\frac{N_i}{D_i}
\le\max_i\frac{N_i}{D_i}.
$$

The saved rational logarithm enclosures and outward Arb arithmetic
enclose the exact endpoints, weights and coefficients. Exporting
each cell upper outward to the 640 grid preserves the direction.
The bound below is the maximum of those certified cell uppers,
not a claim that the true essential maximum attains it.

### Global slack and the complete source budget

Weighted Schur gives $C_{\rm p}\preceq\overline R_1 I$ and hence

$$
H_{\rm ext}-T\succeq gI,\qquad
g=59/10-\overline R_1.
$$

When $g>0$, taking the infimum over the SAME legal finite $E$
coordinate gives $\Pi\succeq gI$ on $O$. No preservation of
Fourier bands by $C_{\rm p}$ is assumed. For the SAME archived
full $u=\mathcal Mw_0$, use its accepted complete squared-norm
upper $N$ and $0<h_{\rm lo}\le h=\langle w_0,u\rangle$.
The full far action remains included in $N$. Standard Cauchy gives

$$
uu^*\preceq NI\preceq\frac Ng\Pi,\qquad
\mathcal M+\rho uu^*\preceq\mathcal M+\Pi=\mathcal A,
\quad 0\le\rho\le\frac gN.
$$

The coefficient $\rho$ is distinct from the normalized parameter
$\tau=h\rho$ and the shrink parameter $\tau/(1+\tau)$.
In particular the inherited excluded coefficient endpoint is
$t_+\simeq2.531919772\cdot10^{-5}$; the earlier $0.0272333894$
is a normalized $\tau$ cap, not that coefficient. The directed
comparison below uses $g/N$ and the exact saved $t_+$.

The single directed application supplies:

| Certified sufficient quantity | Directed bound |
|---|---:|
| Row upper $\overline R_1$ | $<5.53914888029651$ |
| Actual slack lower $g$ | $>0.36085111970349$ |
| Complete-source directional budget upper $N/g$ | $<12585.2937174196$ |
| One eligible rank-one coefficient $\rho_{\rm cert}=g/N$ | $>7.9457819773874\cdot10^{-5}$ |
| Its normalized parameter lower $h_{\rm lo}\rho_{\rm cert}$ | $>0.08546502014787$ |

In particular, under the stated premises,

$$
\boxed{H_{\rm ext}-T\succeq\frac9{25}I,\qquad
\Pi\succeq\frac9{25}I.}
$$

This strengthens the inherited $1/632$ floor using the actual
nonlocal prime operator. The complete-source norm and far bound
are unchanged. The supplied coefficient satisfies
$\rho_{\rm cert}>3t_+$, beyond the range of the stopped endpoint
exclusion. This comparison of scales is an eligibility result;
the missing actual joint retained-sign estimate is separate.
It does not evaluate or revive the excluded lower construction.
The value is one certified sufficient coefficient, not a maximum
of all eligible coefficients.

All original actual common-form/domain, SAME-source, unitary mass,
finite-short and sound-cache premises remain. This is a conditional
numerical application of established weighted Schur, Bernstein and
rank-one inequalities, without a Lean or generic novelty claim.
An eligible coefficient does not establish the joint retained
Gamma/pole/prime sign, cofinal positivity, Robin or RH.

The 233-line source has SHA256 `0b72a6ba263c545fd6ed03958c8d4e8ff82faf05197eb9eee03dc02a81c3f767`; the 138683-byte
directed packet has SHA256 `935b2c0707c3187fa652730b1e40d5937a4e071158b7cb9f1f4a6a78f8459ce6`. The single application
uses 102 exact support cells and 9350 active ordered path-cell
contributions, with 1024 working/640 export bits. It takes
<0.103267seconds excluding serialization. Accepted logarithms,
full-source energies, complete far bounds and endpoint data are read
without replaying their producers or fixtures. There is no new
source action, Gram, inverse, solve or far query and no propagation
order, weight, parameter, precision or partition scan.

The [source and directed packet](https://github.com/the-omega-institute/trureturing-experiments/tree/e08384fdadbf3cf9cd135c824c8d85a480439502/docs/reports/weil-c27)
retain this one application.


### A whole-inverse consumer and its necessary scalar check

The propagated positive row supplies a uniform actual surplus. To use it
on all retained coefficients, reuse the existing inverse order and actual
residual identity, with the SAME original exact support trial $Y$:

$$
H_{\rm ext}\succeq T+gI,\quad T=\Lambda+B_{\rm GP}>0,\qquad
Q=A_N-C_N^*Y-Y^*C_N+Y^*H_{\rm ext}Y,
$$

$$
R=C_N-H_{\rm ext}Y,\qquad S_N=Q-R^*H_{\rm ext}^{-1}R.
$$

All inherited actual common form/domain, basis, trial and sound-cache
premises remain. The bounded operator $T$ keeps the complete positive even
Gamma boundary and pole. The original nineteen-channel Young comparison
satisfies $\overline W\succeq T^{-1}$ on the residual range and
$Q-R^*\overline W R\succeq L_*$, at its original $\rho=1/32$.

For any valid $T\preceq M_T I$, the standard positive-operator calculus
gives

$$
H_{\rm ext}^{-1}\preceq(T+gI)^{-1}\preceq cT^{-1}
\preceq c\overline W,\qquad c=\frac{M_T}{M_T+g}<1,
$$

where comparison with $\overline W$ is on that same residual range.
Consequently there is a coefficient-uniform sufficient lower target

$$
\boxed{S_N\succeq\mathcal L_{\rm unif}
:=cL_*+(1-c)Q.}
$$

Indeed, $Q-cR^*\overline W R
=c(Q-R^*\overline W R)+(1-c)Q$.
The actual $H_{\rm ext}$ need not be bounded; its inverse comparison uses
the inherited closed-form order. This is an application of the existing
operator-order and residual results, without a new general theorem.

The missing separate diagonals of the full initial-trial matrix $Q$
cannot be recovered from a scalar $Q(v)$. A cached scalar nevertheless
supplies a necessary check before producing that matrix. Take the SAME
exact256-bit, all1281-coordinate direction saved by the original
nineteen-channel test, and put

$$
q=Q(v)>0,\qquad\ell=v^*L_*v<0.
$$

Its finite dual packet pins that exact direction and original trial.
For this fixed comparison,

$$
v^*\mathcal L_{\rm unif}v=\frac{M_T\ell+gq}{M_T+g}>0
\quad\Longleftrightarrow\quad
M_T<M_{\rm crit}(v;g):=\frac{gq}{-\ell}.
$$

A negative upper excludes the sufficient target before any complete
retained factorization. A positive lower would pass only this necessary
direction check.

The [cached contraction consumer](https://github.com/the-omega-institute/trureturing-experiments/tree/11b6f791e7ef9acbd2924d89e17dd43da795006a/docs/reports/weil-c27)
uses all exterior weights1281–32768, including the selected support, and
the positive constant far weight $D$. Let

$$
\lambda_{\max}=\max\{W_n^{-1}:1281\le n\le32768,\ D^{-1}\}.
$$

The complete Gamma bound G2 and the positive even pole supply the fixed
rational bound

$$
M_T=\lambda_{\max}+\frac{22}{3}+\frac{729}{364}+\frac{52}{5}.
$$

For its Gamma part, use $\pi<22/7$, $e^2>7$, $\sqrt{27}>5$ and
$\log27<4$ in G2. Its two terms are then bounded by $22/3$ and
$729/364$. The complete even pole has norm at most
$4\sinh(\log27/2)=52/\sqrt{27}<52/5$. Restriction/compression preserves
these norm upper bounds. This uses the full boundary, including every
Gamma rate. The reciprocal maximum uses all exterior modes rather than
only the residual rows after the selected support.

| Quantity | Rounded value or enclosing interval |
|---|---:|
| $\lambda_{\max}$, attained on the far constant | $3.30454609429024$ |
| Supplied complete norm upper $M_T$ | $23.04062668037082$ |
| Accepted uniform surplus lower $g$ | $0.360851119703494$ |
| Whole-inverse contraction $c$ | $0.984579985811736$ |
| Same cached initial-trial $Q(v)$ | $2.97162648706417\cdot10^{-30}$ |
| Same cached $v^*L_*v$ | $-1.17771656935993\cdot10^{-31}$ |
| Necessary ceiling $M_{\rm crit}(v;g)$ | $[9.1050323405,9.1050323406]$ |
| $v^*\mathcal L_{\rm unif}v$ | $[-7.013309373,-7.013309371]\cdot10^{-32}$ |

The archived exact rational endpoints determine the sign. One fixed
Fraction-only consumption takes0.18862seconds, using four pinned packets.
It supplies the norm bound and necessary comparison without another
trial quadratic, residual, Gram, inverse, solve, far query or full target.
No accepted scientific producer or fixture is replayed, and no norm,
weight, direction, parameter or precision scan is used.

This fixed uniform-contraction target is therefore insufficient. The
actual norm of $T$ and the actual retained Weil sign remain undetermined
by this check. A stronger common inverse-residual estimate still needs its
full joint coupling and good-block metric; a scalar initial-trial value
cannot replace those data. The earlier stopped rank-one endpoint family
remains a separate insufficient construction. There is no actual
retained/cofinal positivity, Robin, Lean or RH conclusion here.

#### A whole-space Young gain on the saved nineteen channels

The existing inverse-order, variational projection and good-block Woodbury
interfaces can consume the accepted uniform surplus without a new complete
initial-trial matrix. Keep the SAME actual form/domain, original exact
support trial $Y$, residual $R$, retained basis and sound-cache premises.
Write $J_0=\{1281,\ldots,32768\}$, including the selected support
$E=\{1281,\ldots,2048\}$, and $\mathcal F=\{32769,\ldots\}$.
Use the original nineteen channels and their saved matrices

$$
A=U_{J_0}^*W_{J_0}U_{J_0},\qquad
\beta=U_{J_0}^*W_{J_0}R_{J_0},\qquad
s=1+33\delta_{\rm ch},\qquad\rho=1/32.
$$

Here $A$ includes $E$ even though $R_E=0$ allows its omission from the
production of $\beta$. The charge $\delta_{\rm ch}$ is the original
nineteen-channel far Gram upper, decoded with its original640-bit grid
and1024-bit working precision. It is not any later source-defect charge.

The old comparison restricted to the residual range cannot by itself be
inverted as a full-space statement. Instead apply the SAME Young argument
to every exterior vector, including vectors with nonzero $E$ components.
This gives the full exterior inverse majorant

$$
\mathcal V=
\left[W_{J_0}-W_{J_0}U_{J_0}(A+sI)^{-1}U_{J_0}^*W_{J_0}\right]
\oplus(1+\rho)W_{\mathcal F}
\succeq(\Lambda+UU^*)^{-1}\succeq T^{-1}.
$$

Indeed, in the existing Woodbury variational upper bound insert
$z=(A+sI)^{-1}U_{J_0}^*W_{J_0}x_{J_0}$. Young's inequality pays the far
mixed term by $\rho\|x_{\mathcal F}\|_W^2$ and
$\rho^{-1}z^*U_{\mathcal F}^*W_{\mathcal F}U_{\mathcal F}z$.
The additional far channel Gram costs another
$z^*U_{\mathcal F}^*W_{\mathcal F}U_{\mathcal F}z$.
Their combined channel charge is therefore
$(1+\rho^{-1})\delta_{\rm ch}=33\delta_{\rm ch}$.
No cancellation specific to $R_E=0$ is used in this full-vector argument.

Woodbury also gives

$$
\mathcal V^{-1}=
\left[\Lambda_{J_0}+s^{-1}U_{J_0}U_{J_0}^*\right]
\oplus\frac{\Lambda_{\mathcal F}}{1+\rho}.
$$

Consequently $H_{\rm ext}\succeq T+gI\succeq\mathcal V^{-1}+gI$ and

$$
K_g:=\mathcal V-(\mathcal V^{-1}+gI)^{-1}
=g\mathcal V^2(I+g\mathcal V)^{-1}\succ0.
$$

This uses inverse order followed by functional calculus of the single
operator $\mathcal V$. It does not assume operator monotonicity of
$t^{-1}-(t+g)^{-1}$.

All original far payments remain in

$$
L_*=Q-R^*\mathcal VR-\mathcal E_{\mathcal F},\qquad
\mathcal E_{\mathcal F}=(1+\rho)
(F_{\rm up}-R_{\mathcal F}^*W_{\mathcal F}R_{\mathcal F})\succeq0.
$$

The signed far core is still only part of its paid positive Gram upper;
its complete operator allowance is retained. Thus

$$
S_N\succeq L_*+R^*K_gR.
$$

To use the saved thin observations, set

$$
\Phi=\iota_{J_0}W_{J_0}U_{J_0},\qquad C_A=I+A/s,\qquad
\ell_\Lambda=\max_{n\in J_0}W_n^{-1}.
$$

Only finite middle weights enter this maximum because $\Phi$ has no far
component; all selected $E$ weights still enter. The identities
$\Phi^*R=\beta$ and
$K_g^{-1}=\mathcal V^{-1}+g^{-1}\mathcal V^{-2}$ give

$$
\Phi^*K_g^{-1}\Phi
=AC_A+g^{-1}C_A(U_{J_0}^*U_{J_0})C_A
\preceq D_g:=AC_A+\frac{\ell_\Lambda}{g}C_AAC_A.
$$

The last step uses $U_{J_0}^*U_{J_0}\preceq\ell_\Lambda A$.
For $D_g\succ0$, square completion in the common channel vector $z$ yields

$$
v^*R^*K_gRv\ge2\Re z^*\beta v-z^*D_gz,
\qquad
\boxed{S_N\succeq\mathcal L_g^{(19)}
:=L_*+\beta^*D_g^{-1}\beta.}
$$

This is a joint gain for all retained coefficients. No unsaved
unweighted-channel Gram, complete $Q$ or residual Gram is supplied by
this derivation. It cannot be added to another projection of the SAME
$K_g$ without paying their common observation Gram.

A necessary screen reuses the SAME saved exact256-bit full1281-coordinate
direction $v$. With $u=\beta v$ and the already saved $\ell_v=v^*L_*v$,
it evaluates $\ell_v+u^*D_g^{-1}u$ once. A strictly negative upper rejects
this fixed sufficient target before a new good-block action. A positive
lower passes only this direction and requires the fully paid test

$$
\Sigma_*+\beta_V^*(D_g+\Omega_\beta)^{-1}\beta_V,\qquad
\beta_V=\beta_{\rm bad}-\beta_GX,\qquad
\Omega_\beta=\beta_GP^{-1}\beta_G^*.
$$

Here $P,X,\Sigma_*$ are the saved1263-positive block, old18-column lift
and18-coordinate complement. The old lift and the archived two-row
metric do not provide the inverse action on the nineteen new right sides.
If needed, that action is a new query using the saved $P$ as input; the
old lift solve is not repeated. This is the existing Woodbury interface
with its required good-block payment, not a different inverse algorithm.

The [fixed staged application and new joint metric](https://github.com/the-omega-institute/trureturing-experiments/tree/29e7df207a22d193d516c767dd801a59e760d833/docs/reports/weil-c27)
retain these exact common-object bindings.

The one fixed application takes102.73939seconds; its new19-RHS solve takes
93.58200seconds. The consumer uses1024-bit working precision and a
640-bit output grid, with the exact original charge and all finite middle
weights retained.

| Quantity | Rounded value or enclosing interval |
|---|---:|
| Accepted $g$ | $0.360851119703494$ |
| All-middle reciprocal bound $\ell_\Lambda$ | $3.30451557620074$ |
| Original channel-tail charge $\delta_{\rm ch}$ | $0.000106746688356027$ |
| Original $s=1+33\delta_{\rm ch}$ | $1.00352264071575$ |
| Saved $v^*L_*v$ | $[-1.177716570,-1.177716569]\cdot10^{-31}$ |
| New direction gain $(\beta v)^*D_g^{-1}(\beta v)$ | $[2.250035340,2.250035341]\cdot10^{-31}$ |
| New sufficient target on that SAME $v$ | $[1.072318771,1.072318772]\cdot10^{-31}$ |
| First paid-complement leading minor | $[-3.207347831,3.207347831]\cdot10^{-16}$ |

All19 leading minors of $D_g$ are certified positive, and the saved-direction
screen has a strictly positive lower endpoint. The consumer therefore completes the new1263-by19 inverse
action,19-by19 $\Omega_\beta$ and19-by18 $\beta_V$, using the saved old
18-column lift. All19 leading minors of $D_g+\Omega_\beta$ also pass.
The first leading minor of the resulting18-coordinate complement contains
zero. The fixed application stops there: neither positivity nor failure
of this sufficient target is established. The earlier positive scalar is
only a necessary-direction result.

The new inverse actions and their joint metric are archived for reuse;
they need not be produced again. No original channel, residual, trial,
far Gram, positive-prefix, old lift or inertia fixture is replayed.
Reconstructing the saved positive block supplies input to the new right
sides, rather than repeating the original target producer. There is no
parameter, weight, cutoff, source, direction or precision scan. The stopped
whole-norm contraction and rank-one endpoint families remain stopped.
Under the inherited actual form/domain, exact-trial, normalization and
sound-cache premises, the common lower-bound bridge and the displayed
necessary pass are available. The paid full-target sign, actual retained
and cofinal Weil positivity, Robin, RH and Lean verification remain open.


#### Keep the paid channel border before eliminating its inverse

The existing one-negative-core determinant and Schur/Haynsworth interfaces
also apply directly to the SAME fixed nineteen-channel lower target.
Reuse its newly saved joint arrays

$$
D=D_g+\Omega_\beta\succ0,\qquad B=\beta_V,\qquad
C=\Sigma_*+B^*D^{-1}B.
$$

The matrices have dimensions19,19-by18 and18 respectively. Both the old
inertia $\operatorname{inertia}(\Sigma_*)=(17,1,0)$ and the19 positive
leading-minor certificates for $D$ are already available. They are inputs
to this application; their computations are not repeated.

Instead of evaluating the inverse in $C$, retain the coupled border

$$
\mathcal Z=\begin{pmatrix}D&B\\B^*&-\Sigma_*\end{pmatrix}.
$$

Schur's determinant identity gives

$$
\det\mathcal Z=\det D\,\det(-C)=\det D\,\det C,
$$

because the lower block has even dimension18. The gain $B^*D^{-1}B$ is
positive semidefinite, so the old17 strictly positive eigenvalues give
at least17 strictly positive eigenvalues of $C$. Since $\det D>0$,

$$
\boxed{C\succ0\iff\det\mathcal Z>0,\qquad
n_-(C)=1\iff\det\mathcal Z<0.}
$$

The second equivalence concerns a nonzero determinant; no zero direction
occurs in that case. The updated good block
$P+\beta_G^*D_g^{-1}\beta_G$ remains positive, so its Schur
complement $C$ transports this classification to the fixed1281 lower target
$\mathcal L_g^{(19)}=L_*+\beta^*D_g^{-1}\beta$.
A zero-containing determinant enclosure classifies neither sign. These
are applications of the already owned inertia and determinant methods,
not a new RH criterion or a new determinant algorithm.

The new entry enclosure is formed from the saved $D,B,\Sigma_*$ before
explicit inverse elimination. The SAME $B$ fills both off-diagonal blocks;
$D$ and $\Sigma_*$ may be symmetrized by averaging their transpose
entries. This preserves their actual symmetric matrices. The accepted
positivity premise refers to the actual $D$, while the serialized box
need only contain it. No independently chosen endpoint matrix is used
as a Loewner upper or lower bound.

A single37-by37 FLINT determinant uses the unchanged1024-bit working
precision. Its absolute export grid is $640\cdot37+64=23744$ bits,
following the existing degree-aware rule. Supporting its exact decimal
endpoint strings is a serialization setting, not a precision increase.
No old determinant, inertia, inverse action, $D_g$, joint metric, residual,
source, far Gram or trial producer is rerun. There is no balancing,
parameter, basis, direction, cutoff, weight or precision scan.

The [source and exact archived result](https://github.com/the-omega-institute/trureturing-experiments/tree/0f72c75a1653fedddf023a8c9cdb32b7a41459c7/docs/reports/weil-c27)
are pinned at source/data commit `0f72c75a1653fedddf023a8c9cdb32b7a41459c7`.
The single application takes0.119342seconds and returns
`inconclusive-coupled-border-determinant`.

| Quantity | Value or enclosing interval |
|---|---:|
| Working precision | 1024bits |
| Saved matrix-entry grid | 640bits |
| Coupled-border dimension | 37 |
| Determinant export grid | 23744bits |
| New native determinant calls | 1 |
| Coupled-border determinant | $[-1.391,1.391]\cdot10^{-1859}$ |
| New solve, inverse, source or Gram calls | 0 |
| Old determinant or inertia fixture replays | 0 |

The exact dyadic determinant endpoints have opposite signs. The displayed
rounded enclosure therefore certifies neither positivity nor a negative
direction of the fixed lower target; it is not an exact-zero certificate.
Both target-sign flags remain false. The application stops without a new
minor, determinant, balancing, precision or parameter retry.

This archive supplies the result of the previously missing coupled-border
application; no accepted19-RHS action or earlier scientific certificate
needs recomputation. Under the inherited actual form/domain, original
exact-trial, normalization and sound-cache premises, the earlier common
lower-bound bridge remains available. The paid fixed-target sign, actual
retained/cofinal Weil positivity, Robin, RH and Lean verification remain
open. A bounded certificate for this single trial cannot supply a uniform
cofinal estimate or the core-density and continuity bridge needed to pass
to all admissible tests.


### Complete original-source restricted inertia at eta one

The [complete directed certificate](https://github.com/the-omega-institute/trureturing-experiments/tree/ec7c9fc8c5bbe14a41ef9e3f8b083706831422e2/docs/reports/weil-c27/signed-restriction-eta1)
now supplies the formerly missing original112 inertia `(56,56,0)`.
All112 coordinates are covered exactly once by65 invertible signed pivot
blocks. The already paid21 strictly negative coordinates give original133
border inertia `(56,77,0)` and same-source restriction inertia `(1261,0,0)`.

For the unchanged1263-dimensional positive good metric $P$, retain the two
independent rows $B$, saved actions $PX=B^*$, $G=BX>0$, and the complete
physical majorant

$$
F_0=F K_f F^*+\epsilon I\succeq0,\qquad
\epsilon=\frac{27852372618143874844}{2^{512}}+2^{-542}.
$$

For a full orthonormal basis $Z$ of $\ker B$, the inherited bordered identity
is

$$
\operatorname{In}\bigl(Z^*(P-F_0)Z\bigr)
 =\bigl(1205+n_+(T_{112}),\ n_-(T_{112})-56,\ n_0(T_{112})\bigr).
$$

Thus this count establishes $F_0\prec P$ on $\ker B$, under those original
common-source and action identities. It retains every original good mode,
physical weight, boundary contribution and the complete isotropic allowance.
The partition remains1263 good and18 remaining modes, total1281.
In particular the eta-one restricted domination premise is now paid. The
separate same-source full-border budget is still required; this restricted
count does not determine the actual retained Weil sign.

The successful calculation fixes an exact upper triangular dyadic change
of basis with positive power-of-two diagonal, and then evaluates its full
congruence outward. This basis is invertible independently of the accuracy
of its approximate construction. Midpoint signs do not supply the count.
The two earlier uncertain-pivot eliminations did not establish singularity.
No large1263-dimensional Gram replay was needed for the completed count.

The archive pins all17 files, the executed arithmetic source, the original
contractions and reduction, the fixed basis, the complete interval pivot
transcript, and the independent six-fixture review. The final count took
170.580775291seconds with174096384bytes peak RSS; its actual calculation
and native execution both exited0. The result JSON has SHA256
`53c79a0f9a355b1126482f5e02ba009df8d1515dc6e62556fcbdcf00de942412`.
The portable driver can verify the archived files or replay the small
reduction and fixed-basis count; it does not repeat the large Gram.

This is a finite numerical certificate conditional on the stated source
and action identities. Hash agreement authenticates bytes and does not
prove those identities. No particular rational eta below one, matching
positive downstream budget, new Lean theorem or official kernel acceptance
is supplied here. Neither cofinal Weil positivity, the strict Robin
inequality for every integer above5040, nor RH follows from this count.

### A high-complement norm improves the complete inverse allowance

Keep the SAME actual $c=27$ exterior, $N=1280$, complete $T=\Lambda+B_{\rm GP}$, original support trial $Y$, residual $R$, all nineteen channels, far allowance and source/error premises of the whole-inverse comparison. Reuse its actual surplus $H_{\rm ext}\succeq T+(9/25)I$. The following is a paper application of the existing actual high-mode Gamma estimates and discrete Hilbert bound, not a new Hilbert-transform theorem, numerical execution or retained-sign certificate.

The old $M_T$ uses uncompressed Gamma and pole bounds. The actual exterior contains only Fourier modes $|n|\ge n_0=N+1$. Put $d=\log27<4$, $\omega_n=2\pi n/d$, and $b_j=2j+1/2$. Reuse `arithmetic_archimedean_high_mode_bounds` from [the actual high-mode source](../../D5/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds.lean), the [existing full-form high-mode application](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#5-整个高补空间的统一下界), and G1--G3's same physical Fourier realization. In particular

$$
|s_\Gamma(n)|\le1+|\omega_n|^{-1}.
$$

For the Gamma boundary $B_\Gamma=Q_\Gamma-q_{D_L}$, its off-diagonal entry is the already identified divided difference
$(s_\Gamma(n)-s_\Gamma(m))/(\pi(m-n))$, up to the common phase unitary. Its diagonal correction is

$$
\delta_n=\frac2d\sum_{j\ge0}
\frac{(1-e^{-b_jd})(b_j^2-\omega_n^2)}{(b_j^2+\omega_n^2)^2},
\qquad
|\delta_n|\le\frac1{\pi|n|}+\frac d{2\pi^2n^2}.
$$

The displayed sum is the existing absolutely convergent correction series; its bound uses the same $1+|\omega|^{-1}$ majorant. The two-sided discrete Hilbert matrix $1/(\pi(m-n))$, with zero diagonal, has norm one. Compress it to $|n|\ge n_0$ before taking its commutator with the bounded diagonal $s_\Gamma$. Adding the diagonal correction gives on the actual high Fourier space

$$
\|P_{>N}B_\Gamma P_{>N}\|
\le2+\frac{d+1}{\pi n_0}+\frac d{2\pi^2n_0^2}
<\frac{1001}{500}.
\tag{HCN1}
$$

Here $n_0=1281$, $d<4$ and $\pi>3$ give the final rational bound. This norm estimate restricts to the complex even exterior. It is an operator bound, not a diagonal-only comparison, and includes every Gamma rate. The common closed-form extension is exactly G1--G3's existing bounded-correction extension.

The full even pole is $2|\langle\cosh(x/2),f\rangle|^2$. In the same normalized exterior cosine basis its compressed norm is

$$
\|P_{>N}P_{\rm even}P_{>N}\|
=\frac{4\sinh^2(d/4)}d
 \sum_{n>N}\frac1{(\omega_n^2+1/4)^2}
\le\frac{d^3\sinh^2(d/4)}{12\pi^4N^3}
<\frac1{1000}.
\tag{HCN2}
$$

This follows directly from the already retained pole moments, or from the singleton channel in the pole update. Use $\sum_{n>N}n^{-4}\le1/(3N^3)$, $d<4$, $\sinh(d/4)<3/2$ and $\pi>3$. Both pole evaluations are retained; positivity here uses the even sector.

The accepted whole-exterior reciprocal bound gives $\Lambda\preceq(331/100)I$, including the far constant. HCN1--HCN2 therefore give the SAME complete operator a smaller norm bound

$$
0<T\preceq\left(\frac{331}{100}+\frac{1001}{500}
                       +\frac1{1000}\right)I
\prec\frac{16}{3}I.
\tag{HCN3}
$$

No old weight, retained direction or arithmetic input is changed. In particular no prime term has been dropped from $H_{\rm ext}\succeq T+(9/25)I$; its prime debt was paid by the already accepted propagated-row surplus.

Reuse the same whole-inverse functional calculus and the SAME residual-range majorant $\overline W$. With $M_T^\sharp=16/3$ and $g_0=9/25$, the exact contraction coefficient is

$$
c_\sharp=\frac{M_T^\sharp}{M_T^\sharp+g_0}=\frac{400}{427},
\qquad
H_{\rm ext}^{-1}\preceq c_\sharp T^{-1}
\preceq c_\sharp\overline W
\quad\text{on the original residual range}.
$$

Consequently the complete retained Schur form has the coefficient-uniform lower comparison

$$
\boxed{S_N\succeq\mathcal L_\sharp
:=\frac{400}{427}L_*+\frac{27}{427}Q.}
\tag{HCN4}
$$

All original far payments remain in $L_*$. Since $Q-L_*\succeq R^*\overline W R\succeq0$, this target dominates the old whole-norm target, whose supplied contraction coefficient exceeded $400/427$. The earlier negative check for that old target remains valid for that old target; it is not a negative check for HCN4.

On the SAME saved exact256-bit full1281-coordinate direction $v$, reuse only the already accepted coarse rational consequences

$$
q=Q(v)>\frac{297}{100}10^{-30},\qquad
\ell=v^*L_*v>-\frac{118}{100}10^{-31}.
$$

Ordinary rational arithmetic in the proof, without a new scientific execution, gives

$$
v^*\mathcal L_\sharp v
=\frac{27q+400\ell}{427}
>\frac{3299}{4270}10^{-31}
>7\cdot10^{-32}>0.
\tag{HCN5}
$$

Thus the old whole-norm route's necessary direction screen is now paid by an actual compressed-operator estimate. HCN5 is not a positivity test for the complete1281-dimensional target. The missing full initial-trial matrix is not reconstructed from $q$.

This gain acts on residual directions beyond the nineteen observed channels. To distinguish it from the already paid nineteen-channel projection, reuse the [existing finite-head faithfulness and positive full-tail metric](../Fourier/montgomery1978largesieve.md#a-cancellation-uniform-metric-for-the-complete-finite-head-tail). At $c=27$, the actual far coupling $C_{\mathcal F}$ is injective on the1281-dimensional retained even space. The same finite support trial has range dimension at most768. Hence

$$
\operatorname{rank}R_{\mathcal F}
=\operatorname{rank}(C_{\mathcal F}-(H_{\rm ext}Y)_{\mathcal F})
\ge1281-768=513.
$$

Since $\beta$ has only19 rows, $R_{\mathcal F}$ restricted to $\ker\beta$ has rank at least494. On this kernel the old nineteen-channel update equals $L_*$, whereas HCN4 adds $(27/427)(Q-L_*)$, strictly positive on every vector with nonzero residual. This is a source-specific nonredundancy statement, not global domination of the nineteen-channel target. The two gains both consume the same inverse surplus and must not be added without a common paid comparison.

The complete target sign, good-block/border payment and cofinal positivity remain unresolved. This does not revive the separately excluded rank-one endpoint family or alter any old certificate. No new source action, matrix, inverse, solve, determinant, Gram, numerical sign run, parameter scan, Lean proof or literature-priority claim is supplied.

### The finite channel majorant pays a stronger complete contraction

Keep the SAME actual $c=27$ exterior, $N=1280$, original trial $Y$, residual $R$, nineteen Gamma bins, $\rho=1/32$, far payments and common-form/source premises. Reuse the whole-space Young majorant $\mathcal V$ and its already paid comparison

$$
H_{\rm ext}\succeq\mathcal V^{-1}+g_0I,
\qquad g_0=9/25.
$$

The inverse of this particular majorant retains only the original nineteen finite aggregate columns. Its norm need not pay the entire infinite Gamma boundary or pole. The following estimates apply the existing finite-bin Cauchy--Schwarz and positive-operator calculus to those exact columns; they assert no new general theorem or literature priority.

Put $d=\log27$, $b_j=2j+1/2$ and

$$
h_{j,n}=\frac{2b_j(-1)^n}
 {\sqrt d\,[b_j^2+(2\pi n/d)^2]},\qquad n>N.
$$

The nineteen original bins partition $0\le j<K$, where $K=6765$. For a bin $[a,b)$ the column is $U_{[a,b)}=\sqrt{c_a/(b-a)}\sum_{j=a}^{b-1}h_j$, with $0<c_a=1-e^{-b_ad}<1$. Thus

$$
\|U\|_{\rm HS}^2
 =\sum_{[a,b)}\|U_{[a,b)}\|^2
 \le\sum_{j=0}^{K-1}\|h_j\|^2.
\tag{FCM1}
$$

Every norm here uses the actual normalized even exterior cosine basis. The sum over $n>N$ retains the selected support and the complete infinite far tail. Since the summand decreases with positive $n$, integration gives two bounds for the SAME column:

$$
\begin{aligned}
\|h_j\|^2
&=\frac{4b_j^2}{d}
  \sum_{n>N}\frac1{[b_j^2+(2\pi n/d)^2]^2}\\
&\le\frac{d^3b_j^2}{12\pi^4N^3},
\qquad
\|h_j\|^2\le\frac1{2b_j}.
\end{aligned}
\tag{FCM2}
$$

The first inequality uses $\sum_{n>N}n^{-4}\le1/(3N^3)$; the second enlarges the integral to $[0,\infty)$. Split the finite rate sum at $j=N$. Since $\sum_{j=0}^{N-1}(2j+1/2)^2<4N^3/3$, the first part is less than $d^3/(9\pi^4)$. The remaining part is bounded by

$$
\frac14\sum_{j=N}^{K-1}\frac1{j+1/4}
\le\frac14\log\frac{K-3/4}{N-3/4}
=\frac14\log\frac{27057}{5117}
<\frac7{16}.
$$

For the last inequality, $27057/5117<11/2<e^{7/4}$; the exponential's degree-four positive Taylor sum already exceeds $11/2$. Also $d<10/3$, as certified by the degree-seven positive Taylor sum for $e^{10/3}>27$, and $\pi>3$. Consequently

$$
\boxed{
\|U\|_{\rm HS}^2
<\frac{1000}{19683}+\frac7{16}<\frac12.}
\tag{FCM3}
$$

This is an analytic bound on the complete nineteen-column operator, with no rate truncation beyond the original fixed bins and no finite-mode replacement of its infinite support.

Reuse the original full-space identity, with $J_0=\{1281,\ldots,32768\}$, $\mathcal F=\{32769,\ldots\}$ and $s=1+33\delta_{\rm ch}\ge1$:

$$
B:=\mathcal V^{-1}
=\left[\Lambda_{J_0}+s^{-1}U_{J_0}U_{J_0}^*\right]
 \oplus\frac{\Lambda_{\mathcal F}}{1+\rho}.
$$

The accepted complete reciprocal bound $\Lambda\preceq(331/100)I$, including the far constant, and FCM3 imply

$$
0<B\prec\frac{381}{100}I,
\qquad
H_{\rm ext}^{-1}
\preceq(B+g_0I)^{-1}
\preceq\frac{127}{139}\,\mathcal V.
\tag{FCM4}
$$

Apply the SAME whole-inverse functional calculus to $B$, rather than paying the norm of the larger $T=\Lambda+B_{\rm GP}$. No Gamma or pole term has been removed from the actual $H_{\rm ext}$; the lower comparison with $B+g_0I$ was already proved by the whole-space Young argument and paid prime surplus.

Retain the original complete far allowance

$$
L_*=Q-R^*\mathcal VR-\mathcal E_{\mathcal F},
\qquad\mathcal E_{\mathcal F}\succeq0.
$$

Then $S_N=Q-R^*H_{\rm ext}^{-1}R$ satisfies

$$
\boxed{
S_N\succeq\mathcal L_{\rm fin}
:=\frac{127}{139}L_*+\frac{12}{139}Q,\qquad
\mathcal L_{\rm fin}-\mathcal L_\sharp
=\frac{1371}{59353}(Q-L_*)\succeq0.}
\tag{FCM5}
$$

Indeed the discarded term in the first comparison is $(127/139)\mathcal E_{\mathcal F}\succeq0$. All original far charges therefore remain paid. The second comparison uses HCN4 exactly as published. It is strict as a quadratic inequality on every vector with nonzero residual, since $Q-L_*=R^*\mathcal VR+\mathcal E_{\mathcal F}$. In particular the previously established nonzero residual directions in $\ker\beta$ receive a strictly larger gain than HCN4; their rank argument is reused without repetition.

This pays a strictly stronger complete inverse allowance and a globally stronger sufficient retained target than HCN4. It does not add a second copy of the same surplus to the nineteen-channel projection, and asserts no global ordering with $\mathcal L_g^{(19)}$. The complete matrix $Q$ is still not supplied by a cached scalar. The full retained/border sign, cofinal Weil positivity, the original all-integer strict Robin inequality and RH remain open. These are conditional paper applications under the inherited source, form/domain and sound-cache premises; no new scientific execution, Lean build or kernel certification is supplied.

### A trace-class Hilbert model for the complete Gamma boundary

Reuse G1--G3's actual physical Fourier realization and the complete positive even Gamma series used by the original nineteen channels. Let $c\ge2$, $d=\log c$, and let the integer $N\ge\max(1,d)$. On the actual even exterior with normalized cosine indices $n>N$, write

$$
h(b)_n=\frac{2b(-1)^n}{\sqrt d\,[b^2+(2\pi n/d)^2]},
\qquad b_j=2j+1/2,
\qquad
B_{\Gamma,N}=\sum_{j\ge0}(1-e^{-b_jd})|h(b_j)\rangle\langle h(b_j)|.
$$

The complete series has the inherited bounded positive form interpretation. Define the explicit positive Hilbert matrix

$$
\mathcal C_N(n,m)=\frac{(-1)^{n+m}}{2(n+m)},\qquad n,m>N.
$$

The classical Hilbert inequality gives $0\preceq\mathcal C_N\preceq(\pi/2)I\prec2I$. Its Gram representation and this norm estimate are reused classical facts; the [existing Schur criterion](../Fourier/teschl2009mathematical.md#schur-criterion-for-the-local-frequency-kernel) with weight $n^{-1/2}$ also supplies the bound. The following is an application to the SAME complete Gamma columns, with no numerical execution or priority claim.

#### Pay the complete sum-to-integral error in trace norm

Set $F(b)=|h(b)\rangle\langle h(b)|$. The same column integrals used in FCM2 give

$$
\|h(b)\|^2\le\min\left\{
\frac{d^3b^2}{12\pi^4N^3},\frac1{2b}\right\},
\qquad \|h'(b)\|\le\frac{\|h(b)\|}{b}.
$$

Consequently $F'(b)$ is trace class and

$$
\|F'(b)\|_1\le2\|h(b)\|\|h'(b)\|
\le\min\left\{\frac{d^3b}{6\pi^4N^3},\frac1{b^2}\right\},
\quad
\int_0^\infty\|F'(b)\|_1db
\le\frac dN\left(\frac1{3\pi^2}+\frac1{2\pi}\right).
\tag{GHC1}
$$

For the integral bound split at $b=2\pi N/d$. On each interval $[2j,2j+2]$, compare its sample $F(2j+1/2)$ with half the integral. The trace norm of that difference is at most $\int_{2j}^{2j+2}\|F'(b)\|_1db$. Thus the sum of the cell errors converges in trace norm. Separately,

$$
\frac12\int_0^\infty F(b)\,db=\mathcal C_N,
\qquad
\sum_{j\ge0}b_j^2e^{-b_jd}\le\frac{113}{27}<5.
$$

The first identity follows entrywise from $\int_0^\infty b^2/[(b^2+a^2)(b^2+q^2)]\,db=\pi/[2(a+q)]$. Both positive operator integrals and the unweighted column sums are taken in their strong limits. Their individual trace integrals need not converge; only their difference is summed in trace norm. The exponentially weighted column sum is trace class, with trace at most $5d^3/(12\pi^4N^3)$. Therefore

$$
\boxed{\begin{aligned}
\|B_{\Gamma,N}-\mathcal C_N\|_1
&\le\frac dN\left(\frac1{3\pi^2}+\frac1{2\pi}\right)
       +\frac{5d^3}{12\pi^4N^3}\\
&<\frac d{4N}.
\end{aligned}}
\tag{GHC2}
$$

Indeed $\pi>3$ and $d/N\le1$ bound the coefficient by $11/54+5/972=203/972<1/4$. Every Gamma rate, the selected support and the infinite exterior tail remain. In particular the operator norm has the SAME bound. On the existing cofinal FIB schedule $c_r=3^{F_{r+1}}$, $N_r=\lceil e^{c_r}\rceil$, this actual Gamma replacement has trace-norm error less than $(\log c_r)e^{-c_r}/4$. It is uniform over the complete exterior, without a finite retained dimension or sign-complexity restriction.

#### Retain all arithmetic terms in a full inverse comparison

At the SAME actual $c=27$, $N=1280$, reuse the paid full-source order

$$
H_{\rm ext}\succeq\Lambda+B_{\Gamma,N}+P_{\rm even}+g_0I,
\qquad g_0=9/25,
\qquad 0<\Lambda\preceq(331/100)I.
$$

FCM's elementary $d<10/3$ and GHC2 give $\|B_{\Gamma,N}-\mathcal C_N\|_1<\varepsilon_0:=1/1536$. Replace only that Gamma boundary in the actual full operator:

$$
\widetilde H_{\rm ext}
=H_{\rm ext}-B_{\Gamma,N}+\mathcal C_N.
$$

All prime powers, the full even pole and the physical form domain remain in this model. Both operators are at least $g_0I$. The existing bounded-perturbation and resolvent identities therefore give

$$
\boxed{
\|H_{\rm ext}^{-1}-\widetilde H_{\rm ext}^{-1}\|_1
\le\frac{\varepsilon_0}{g_0^2}
=\frac{625}{124416}.}
\tag{GHC3}
$$

For the original exact residual map $R$, congruence gives trace-norm error at most $(625/124416)\|R\|^2$ in the corresponding retained inverse quadratic. This does not supply an unsaved numerical value of $\|R\|$ or the full initial-trial matrix $Q$.

There is also an explicit full-space inverse upper requiring no inversion of the Hilbert model. Put

$$
\alpha=g_0-\varepsilon_0=\frac{13799}{38400}>0,
\qquad D_0=\Lambda+\alpha I,
\qquad\theta=\frac{\alpha}{\alpha+2}=\frac{13799}{90599}.
$$

GHC2 pays $H_{\rm ext}\succeq D_0+\mathcal C_N$. Since $\|D_0^{-1/2}\mathcal C_ND_0^{-1/2}\|\le2/\alpha$, apply the existing scalar secant inequality for $(1+x)^{-1}$ by functional calculus to obtain

$$
\boxed{
H_{\rm ext}^{-1}\preceq
\mathsf W_{\rm H}:=
D_0^{-1}-\theta D_0^{-1}\mathcal C_ND_0^{-1}.}
\tag{GHC4}
$$

The positive Hilbert correction retains an infinite collection of coupled modes. It is not added to a separate copy of the nineteen-channel or FCM surplus. The original Schur identity consequently gives $S_N\succeq Q-R^*\mathsf W_{\rm H}R$. This quadratic retains all near/far Hilbert cross terms. Contracting it with the actual residual and supplying any numerical tail payments is a separate unpaid task; the old diagonal far allowance must not be substituted for those cross terms.

#### A quantitative consumer on actual exterior states

Reuse the constant far reciprocal $\Lambda_{\mathcal F}=\lambda_{\mathcal F}I$, $0<\lambda_{\mathcal F}\le331/100$, beyond $32768$. For any integer $L\ge32769$ take the normalized actual exterior Fourier polynomial with coefficient vector

$$
u_L(n)=\frac{(-1)^n}{\sqrt L}\mathbf1_{\{L\le n<2L\}}.
$$

These are valid even physical states, not asserted to belong to the saved finite-dimensional residual range. Directly $\langle u_L,\mathcal C_Nu_L\rangle>1/8$. Write $a=\lambda_{\mathcal F}+\alpha<4$ and reuse the raw shifted-diagonal upper $\mathsf W_0=(\Lambda+g_0I)^{-1}$. Then

$$
\boxed{\begin{aligned}
\langle u_L,(\mathsf W_0-\mathsf W_{\rm H})u_L\rangle
&>\frac{\theta/8-\varepsilon_0}{a^2}\\
&>\frac1{16}\left(\frac1{56}-\frac1{1536}\right)
>\frac1{1000}.
\end{aligned}}
\tag{GHC5}
$$

Here $\theta>1/7$. On these same far-supported vectors, $\mathsf W_0\prec(127/139)\mathcal V$ follows from the accepted far block $\mathcal V_{\mathcal F}=(33/32)\lambda_{\mathcal F}^{-1}I$ and $\lambda_{\mathcal F}\le331/100$. The nineteen observations have no far component. GHC5 thus supplies a strict quantitative upper-budget gain on arbitrarily remote, actual Fourier bands. It does not assert global ordering of $\mathsf W_{\rm H}$ with FCM4 or the nineteen-channel inverse, or a gain on an unmeasured saved residual direction.

#### A cofinal full-arithmetic inverse trace bound

The same model comparison also consumes the existing even exterior floor at growing supports. Keep the actual complete operator $H_{\rm ext}(c,N)$ and replace only $B_{\Gamma,N}$ by $\mathcal C_N$ as above. With G1--G4's original diagonal symbol $A(t)$, put

$$
\mathfrak a(c,N)=
A\!\left(\frac{2\pi(N+1)}{\log c}\right)
-2\sum_{2\le n<c}\frac{\Lambda(n)}{\sqrt n}.
$$

The original complex even Gamma boundary and pole are positive. Their Hilbert replacements are positive as well. The existing diagonal monotonicity and full prime-translation norm bound therefore give BOTH $H_{\rm ext}(c,N)\succeq\mathfrak a(c,N)I$ and $\widetilde H_{\rm ext}(c,N)\succeq\mathfrak a(c,N)I$. The sum retains every proper prime power; the shift at $n=c$, when present, is zero almost everywhere. Whenever $\mathfrak a(c,N)>0$, GHC2 and the SAME resolvent identity imply

$$
\|H_{\rm ext}(c,N)^{-1}
 -\widetilde H_{\rm ext}(c,N)^{-1}\|_1
<\frac{\log c}{4N\mathfrak a(c,N)^2}.
$$

Reuse the cited classical $A(t)=\log t+O(1)$ and the elementary complete bound $\sum_{n<c}\Lambda(n)/\sqrt n=O(\sqrt c\log c)$. At $N(c)=\lceil e^c\rceil$, these give $\mathfrak a(c,N(c))/c\to1$, hence $\mathfrak a(c,N(c))\ge c/2$ for all sufficiently large $c$. Thus

$$
\boxed{
\|H_{\rm ext}(c,N(c))^{-1}
 -\widetilde H_{\rm ext}(c,N(c))^{-1}\|_1
<\frac{\log c}{c^2N(c)}
\le\frac{\log c}{c^2}e^{-c}.}
\tag{GHC6}
$$

In particular GHC6 holds at every sufficiently large level of the original cofinal FIB support schedule. It is a complete actual exterior inverse comparison, including all prime powers and the full pole; it imposes no retained dimension bound. Applying it to a retained residual still multiplies the bound by that residual map's squared operator norm. No unmeasured residual bound, finite retained sign or convergence of a complete regularized determinant follows from GHC6 alone.

GHC2 pays a complete source-specific trace-class replacement, GHC3 consumes it with the actual full arithmetic operator, and GHC4--GHC5 supply an explicit infinite-rank inverse-budget consumer. GHC6 pays the complete exterior inverse trace error along the cofinal support schedule. No scientific producer, matrix, solve, determinant or direction screen is executed. These are conditional paper applications under the inherited form/source premises, without Lean/kernel certification. The complete retained/border sign, cofinal Weil positivity, original same-source Robin upper and RH remain unresolved.

### Transport the complete physical Schur block with the Gamma model

Keep GHC1--GHC6's actual complex even Weil operator, its original support and Fourier split. Put $L=(\log c)/2$, let $P_N$ retain the modes $0,\ldots,N$, and write $P_N^\perp=I-P_N$. Reuse G1--G4's SAME decomposition $\mathscr H_c=D_L+V_L$, with $\|V_L\|\le K_L$. The physical retained block and full coupling are

$$
A_{c,N}=P_N\mathscr H_cP_N,\qquad
\mathscr B_{c,N}=P_N^\perp V_LP_N.
$$

The diagonal $D_L$ commutes with $P_N$, so $\mathscr B_{c,N}=P_N^\perp\mathscr H_cP_N$ on the finite Fourier space and $\|\mathscr B_{c,N}\|\le K_L$. This is the original complete physical coupling, including every prime power, both pole evaluations and the Gamma boundary. Finite Fourier vectors belong to the operator domain of $D_L+V_L$; the full exterior retains the common form domain used in GHC6.

Let $H_{\rm ext}$ be that exterior and $\widetilde H_{\rm ext}=H_{\rm ext}+\mathscr E$ its accepted Gamma model, where $\mathscr E=\mathcal C_N-B_{\Gamma,N}$. Define the two exact physical Schur blocks using the SAME retained block and coupling:

$$
S_{c,N}=A_{c,N}-\mathscr B_{c,N}^*H_{\rm ext}^{-1}\mathscr B_{c,N},
\qquad
\widetilde S_{c,N}=A_{c,N}-\mathscr B_{c,N}^*\widetilde H_{\rm ext}^{-1}\mathscr B_{c,N}.
$$

Both inverses exist whenever GHC6's $\mathfrak a(c,N)>0$. The classical two-sided trace-ideal estimate, reused rather than reproved, now consumes G4's actual coupling bound and GHC6:

$$
\boxed{
\|S_{c,N}-\widetilde S_{c,N}\|_1
<\frac{K_L^2\log c}{4N\mathfrak a(c,N)^2}.}
\tag{GHC7}
$$

The norm is the ordinary trace norm on the original $(N+1)$-dimensional orthonormal retained space. There is no multiplying rank or unsupplied residual norm. In particular, reuse G4's explicit full arithmetic budget

$$
K_{(\log c)/2}
=C_\Gamma(\log c)+4\sinh((\log c)/2)
 +2\sum_{2\le n<c}\frac{\Lambda(n)}{\sqrt n}
=O(\sqrt c\log c).
$$

Here $C_\Gamma(\log c)=O(1)$ by G2, the pole budget is $O(\sqrt c)$, and GHC6 already uses the stated complete prime bound. Thus at $N(c)=\lceil e^c\rceil$, for all sufficiently large $c$,

$$
\boxed{
\|S_{c,N(c)}-\widetilde S_{c,N(c)}\|_1
<\frac{K_{(\log c)/2}^{\,2}\log c}{c^2N(c)}
=O\!\left(\frac{(\log c)^3}{c}e^{-c}\right).}
\tag{GHC8}
$$

This controls the entire physical retained block at every sufficiently large original FIB support level, even though its dimension is $\lceil e^c\rceil+1$. The same bound also controls its operator norm and hence the difference of the two least eigenvalues. It gives an absolute model error, not a sign for either Schur block or a relative error at a vanishing eigenvalue.

#### Transport the original trial and its initial quadratic together

The full physical comparison does not require changing the original legal finite-rank trial $Y$. In the earlier notation, let

$$
Q=A_{c,N}-\mathscr B_{c,N}^*Y-Y^*\mathscr B_{c,N}
       +Y^*H_{\rm ext}Y,\qquad
R=\mathscr B_{c,N}-H_{\rm ext}Y.
$$

Its correctly transported model terms are

$$
\widetilde Q=Q+Y^*\mathscr E Y,\qquad
\widetilde R=R-\mathscr E Y.
$$

The existing exact inverse-residual identity, applied with this SAME $Y$ to each operator, gives

$$
Q-R^*H_{\rm ext}^{-1}R=S_{c,N},\qquad
\widetilde Q-\widetilde R^*\widetilde H_{\rm ext}^{-1}\widetilde R
=\widetilde S_{c,N}.
$$

Consequently GHC7--GHC8 control the fully transported trial expression too. Holding $Q$ and $R$ fixed while replacing only their inverse still gives GHC3/GHC6's separate $\|R\|^2$ allowance. The physical comparison here transports the initial quadratic and residual from their common actual coupling; it does not infer an unsaved value of $\|R\|$, construct a new trial or add a second surplus credit.

This `repo-derived` application reuses the existing trace ideal, bounded perturbation and Schur/residual identities. Its additional paid quantity is the dimension-independent absolute error of the SAME complete physical Schur block under the Gamma model. It supplies no finite target matrix, actual retained or border sign, normalized ground-state approximation, complete regularized determinant limit or original same-source Robin upper. The inherited source/form identification remains conditional paper mathematics without Lean/kernel certification, and RH and strict Robin for every integer above5040 remain unresolved. No literature priority is asserted.

### A signed Gamma model for the complete complex Fourier exterior

Keep G1--G4's periodic Fourier diagonal and actual full complex Weil form on $I=(-d/2,d/2)$, with $c\ge2$, $d=\log c$, and integer $N\ge\max(1,d)$. The even exterior uses the normalized cosines from GHC1--GHC8. On the odd exterior use $s_n(x)=\sqrt{2/d}\sin(2\pi nx/d)$, $n>N$, and put $\omega_n=2\pi n/d$. Reflection splits the complete Gamma boundary into these two invariant sectors.

The SAME image kernel already displayed after G6 is

$$
B_L(x,y)=\sum_{j\ge0}\frac{2\cosh(b_j(x-y))}{e^{b_jd}-1},
\qquad b_j=2j+1/2.
$$

Its hyperbolic decomposition retains a positive cosh square and a negative sinh square. Thus the odd compression has the exact bounded-form series

$$
B_{\Gamma,N}^{\rm odd}
=-\sum_{j\ge0}(1-e^{-b_jd})|k(b_j)\rangle\langle k(b_j)|,
\qquad
k(b)_n=\frac{2\omega_n(-1)^n}{\sqrt d\,(b^2+\omega_n^2)}.
$$

Indeed integrating $\sinh(bx)$ against $s_n$ gives $-2\sqrt{2/d}\,\omega_n(-1)^n\sinh(bd/2)/(b^2+\omega_n^2)$, which yields the displayed coefficient and sign. The source's full periodic Gamma correction is therefore not positive on both parities. The positive all-parity Neumann-resolvent completion uses a different odd reference; it is not substituted for this periodic decomposition.

#### Pay the complete odd sum-to-integral error

Reuse GHC1--GHC2's trace-class cell quadrature, with $F_{\rm o}(b)=|k(b)\rangle\langle k(b)|$. Directly from $\sum_{n>N}n^{-2}\le1/N$ and the decreasing resolvent summand,

$$
\|k(b)\|^2\le\min\left\{\frac d{\pi^2N},\frac1b\right\},
\qquad
\|k'(b)\|\le
\min\left\{\frac{2b}{(2\pi N/d)^2},\frac2b\right\}\|k(b)\|.
$$

For the second norm bound enlarge $\sum_{n>N}(b^2+\omega_n^2)^{-1}$ to its integral on $(0,\infty)$; the first uses the full tail. Hence

$$
\|F_{\rm o}'(b)\|_1
\le\min\left\{\frac{d^3b}{\pi^4N^3},\frac4{b^2}\right\},
\qquad
\int_0^\infty\|F_{\rm o}'(b)\|_1db
\le\frac dN\left(\frac2{\pi^2}+\frac2\pi\right).
$$

Split this integral at $b=2\pi N/d$. The classical rational integral gives, with the SAME $\mathcal C_N(n,m)=(-1)^{n+m}/[2(n+m)]$,

$$
\frac12\int_0^\infty F_{\rm o}(b)\,db=\mathcal C_N.
$$

The positive bodies use strong limits, while the differences of each sample and its half-cell integral sum in trace norm as in GHC2. Separately, $d\ge\log2$ gives

$$
\sum_{j\ge0}e^{-b_jd}
=\frac{e^{-d/2}}{1-e^{-2d}}\le\frac4{3\sqrt2}<1,
\qquad
\sum_{j\ge0}e^{-b_jd}\|k(b_j)\|^2<\frac d{\pi^2N}.
$$

Thus, using $\pi>3$,

$$
\boxed{
\|B_{\Gamma,N}^{\rm odd}+\mathcal C_N\|_1
<\frac dN\left(\frac3{\pi^2}+\frac2\pi\right)
<\frac dN.}
\tag{GHC9}
$$

Every Gamma rate remains. No individual positive body's trace integral is assumed finite. GHC9 is an application to the actual odd sine columns; the classical Hilbert Gram and trace-ideal tools are reused.

#### Consume both signs in the full arithmetic operator

Let $B_{\Gamma,N}^{\rm all}=B_{\Gamma,N}^{\rm even}\oplus B_{\Gamma,N}^{\rm odd}$ and define

$$
\mathcal C_N^{\rm signed}=\mathcal C_N\oplus(-\mathcal C_N).
$$

GHC2 and GHC9 give the complete complex-exterior comparison

$$
\boxed{
\|B_{\Gamma,N}^{\rm all}-\mathcal C_N^{\rm signed}\|_1
<\frac{5d}{4N},\qquad
\|B_{\Gamma,N}^{\rm all}-\mathcal C_N^{\rm signed}\|<\frac dN.}
\tag{GHC10}
$$

The operator-norm bound uses the maximum of the two parity blocks. Replace only this exterior Gamma boundary in the actual full complex operator, keeping the full pole and all prime-power terms. In particular the odd pole is $-2|\langle\sinh(x/2),f\rangle|^2$ and remains in the operator; no positive odd-pole or odd-Gamma assumption is used.

Write $H_{\rm ext}^{\rm all}$ and $\widetilde H_{\rm ext}^{\rm all}$ for the actual and signed-model exteriors. G4's complete bounded perturbation and GHC10 give both the SAME floor

$$
\mathfrak b(c,N)=A\!\left(\frac{2\pi(N+1)}{\log c}\right)
-K_{(\log c)/2}-\frac{\log c}{N}.
$$

Whenever $\mathfrak b>0$, the already used resolvent and trace-ideal inequalities apply with trace allowance $5d/(4N)$ and inverse norm $1/\mathfrak b$. At $N(c)=\lceil e^c\rceil$, the owned asymptotics give $\mathfrak b/c\to1$, so $\mathfrak b\ge c/2$ eventually. On all sufficiently large original FIB support levels,

$$
\boxed{\begin{aligned}
\|(H_{\rm ext}^{\rm all})^{-1}-(\widetilde H_{\rm ext}^{\rm all})^{-1}\|_1
&<\frac{5\log c}{c^2N(c)},\\
\|S_{c,N(c)}^{\rm all}-\widetilde S_{c,N(c)}^{\rm all}\|_1
&<\frac{5K_{(\log c)/2}^{\,2}\log c}{c^2N(c)}
=O\!\left(\frac{(\log c)^3}{c}e^{-c}\right).
\end{aligned}}
\tag{GHC11}
$$

Here the physical Schur blocks retain all complex modes $-N,\ldots,N$, equivalently $N+1$ even and $N$ odd coordinates. Their SAME full coupling is $P_N^\perp V_LP_N$ with norm at most $K_L$, exactly as in GHC7. Both pole evaluations, every prime power, the original domain and every Gamma rate remain. The trace bound covers all $2N(c)+1$ coordinates without a rank factor. The original legal-trial transport from GHC7--GHC8 applies with the full signed exterior change; it introduces no reselected trial, separate surplus credit or inferred residual norm.

This `repo-derived` application extends the quantitative model from the complex even sector to the entire complex physical form, with the negative odd boundary and pole explicitly retained. It does not establish positivity of either Schur block, a favorable joint prime discrepancy, the complete determinant limit, the original Robin strict upper or RH. The inherited source/form identification and these deductions remain paper mathematics without Lean/kernel certification. No literature priority is asserted.

### A cubic complete Gamma remainder retains the signed odd endpoint

Keep exactly GHC1--GHC11's full complex exterior, $c\ge2$, $d=\log c$, integer $N\ge\max(1,d)$, rates $b_j=2(j+1/4)$ and columns $h(b),k(b)$. The Hilbert matrix and both complete Gamma series are reused. The extra source-specific input is the fixed quarter-lattice endpoint and the evenness of both column products in $b$; the first-derivative quadrature bound did not use these cancellations. Classical Euler--Maclaurin summation and its periodic Bernoulli remainder are reused, as in [DLMF 2.10(i)](https://dlmf.nist.gov/2.10.i). No new general summation theorem, numerical certificate, literature priority or Lean/kernel verification is asserted.

Put
$$
 \ell_N=k(0),\qquad
 (\ell_N)_n=\frac{\sqrt d\,(-1)^n}{\pi n},\qquad
 \tau_d=\frac{e^{-d/2}}{1-e^{-2d}}-\frac14,
$$
and define the explicit signed model
$$
 \boxed{\mathcal C_N^{[3]}=
 \mathcal C_N\oplus\bigl(-\mathcal C_N+
               \tau_d|\ell_N\rangle\langle\ell_N|\bigr).}
 \tag{GHC12}
$$
The correction is negative for $c\ge25$: $4/\sqrt c\le4/5<1-c^{-2}$. It stays in the odd model with this sign. Also
$\|\ell_N\|^2\le d/(\pi^2N)$, so it is an actual bounded rank-one operator on the entire odd exterior.

#### Use the actual lattice before taking a trace norm

For $F_{\rm e}(b)=|h(b)\rangle\langle h(b)|$ and
$F_{\rm o}(b)=|k(b)\rangle\langle k(b)|$, both $F$ are even and $F'(0)=0$. Apply shifted Euler--Maclaurin first to $0\le b\le2J$ with samples $2j+1/2$, $0\le j<J$, in trace-class pairings. Here
$B_1(1/4)=-1/4$, $B_3(1/4)=3/64$ and
$|B_3(x)|=|x(x-1/2)(x-1)|\le1/8$ on $[0,1]$.
The upper-endpoint terms tend to zero in trace norm. The third-order integral remainder therefore gives
$$
 \boxed{\left\|\mathcal E(F)\right\|_1
 \le\frac1{32}\|F''(0)\|_1+
          \frac1{12}\int_0^\infty\|F'''(b)\|_1\,db,}
 \qquad
 \mathcal E(F)=\sum_{j\ge0}F(b_j)
           -\frac12\int_0^\infty F(b)\,db-\frac14F(0).
 \tag{GHC13}
$$
The displayed difference means the limit of those finite-cutoff differences. Neither positive body is asserted trace class. The inherited strong sums and integrals identify the two bodies after the difference has converged in trace norm.

Here all the trace-class differentiability and endpoint conditions can be paid explicitly. Set $\Omega=2\pi N/d$ and let $u$ denote either $h$ or $k$. Partial fractions give, for $0\le r\le3$,
$$
 |u_n^{(r)}(b)|
 \le\frac{2r!}{\sqrt d\,(b^2+\omega_n^2)^{(r+1)/2}}.
$$
If $U_r$ is the $\ell^2$ norm of this majorant, decreasing-sum integrals give
$$
 U_r(b)^2\le
 \frac{2(r!)^2}{\pi(2r+1)}\Omega^{-2r-1},\qquad
 U_r(b)^2\le
 \frac{2(r!)^2}{\pi}b^{-2r-1}
       \int_0^\infty(1+t^2)^{-r-1}\,dt\quad(b>0).
$$
The four integrals in the second bound are
$\pi/2,\pi/4,3\pi/16,5\pi/32$. Since
$\|F'''\|_1\le2U_0U_3+6U_1U_2$, these imply respectively
$\|F'''(b)\|_1\le6\Omega^{-4}$ for $b\le\Omega$ and
$\|F'''(b)\|_1\le12b^{-4}$ for $b\ge\Omega$. Thus, for either product,
$$
 \boxed{\int_0^\infty\|F'''(b)\|_1\,db
             \le10\Omega^{-3},\qquad
 \|F_{\rm e}''(0)\|_1\le\frac{d^3}{6\pi^4N^3},\qquad
 \|F_{\rm o}''(0)\|_1\le\frac{d^3}{\pi^4N^3}.}
 \tag{GHC14}
$$
For example, the even endpoint is $2|h'(0)\rangle\langle h'(0)|$.
For the odd endpoint, use $k'(0)=0$,
$k''(0)_n=-2(\ell_N)_n/\omega_n^2$ and
$\|\ell_N\|^2\le d/(\pi^2N)$. The same derivative bounds show that
$F,F',F''$ tend to zero in trace norm at infinity, justifying the cutoff passage in GHC13. All derivatives are taken in trace norm on each finite interval.

#### Retain the exponentially weighted body in the same cancellation

Reuse GHC2's entire-rate bound $\sum_jb_j^2e^{-db_j}<5$.
Since $h(0)=0$ and
$\|h(b)\|^2\le b^2d^3/(12\pi^4N^3)$,
$$
 \left\|\sum_{j\ge0}e^{-db_j}F_{\rm e}(b_j)\right\|_1
       \le\frac{5d^3}{12\pi^4N^3}.
$$
For the odd body,
$\|k(b)-\ell_N\|\le(b/\Omega)^2\|\ell_N\|$ and
$\|k(b)\|\le\|\ell_N\|$, hence
$$
 \left\|\sum_{j\ge0}e^{-db_j}
          [F_{\rm o}(b_j)-F_{\rm o}(0)]\right\|_1
       \le\frac{5d^3}{2\pi^4N^3}.
$$
Its omitted constant is exactly
$\sum_je^{-db_j}F_{\rm o}(0)$, already retained in $\tau_d$.
The actual identities are therefore
$$
 B_{\Gamma,N}^{\rm even}-\mathcal C_N
   =\mathcal E(F_{\rm e})-\sum_je^{-db_j}F_{\rm e}(b_j),
$$
$$
 B_{\Gamma,N}^{\rm odd}+\mathcal C_N
       -\tau_d|\ell_N\rangle\langle\ell_N|
   =-\mathcal E(F_{\rm o})
       +\sum_je^{-db_j}[F_{\rm o}(b_j)-F_{\rm o}(0)].
$$
Every Gamma rate and each parity sign remains. GHC13--GHC14 now give
$$
 \boxed{\begin{aligned}
 \|B_{\Gamma,N}^{\rm even}-\mathcal C_N\|_1
 &\le\left(\frac{27}{64\pi^4}+\frac5{48\pi^3}\right)
                   \frac{d^3}{N^3}<\frac{d^3}{100N^3},\\
 \|B_{\Gamma,N}^{\rm odd}+\mathcal C_N
        -\tau_d|\ell_N\rangle\langle\ell_N|\|_1
 &\le\left(\frac{81}{32\pi^4}+\frac5{48\pi^3}\right)
                   \frac{d^3}{N^3}<\frac{d^3}{25N^3},\\
 \|B_{\Gamma,N}^{\rm all}-\mathcal C_N^{[3]}\|_1
 &<\frac{d^3}{20N^3}.
 \end{aligned}}
 \tag{GHC15}
$$
The strict constants follow already from $\pi>3$:
$1/192+5/1296<1/100$ and $1/32+5/1296<1/25$.
The full-space bound sums the two trace norms. It has no finite exterior dimension, coefficient or rank restriction.

At the original $c=27$, $N=1280$, the EVEN Hilbert model is unchanged. GHC3's actual full-arithmetic operators still both exceed $g_0I$, so the same resolvent identity directly improves its allowance to
$$
 \boxed{\|H_{\rm ext}^{-1}-\widetilde H_{\rm ext}^{-1}\|_1
       <\frac{d^3}{100N^3g_0^2}
       <\frac{6250}{2187\cdot1280^3}<10^{-8}.}
 \tag{GHC16}
$$
This is an exact paper bound, without a numerical solve or an inferred saved-residual norm. Congruence with the original residual still carries its squared norm as in GHC3.

#### The same full physical Schur block has a cubic-rate model error

For the entire complex physical operator, replace only the exterior Gamma boundary by $\mathcal C_N^{[3]}$. Call the resulting exterior $\widehat H_{\rm ext}^{\rm all}$ and its physical retained Schur block $\widehat S_{c,N}^{\rm all}$. The actual complete coupling $\mathscr B=P_N^\perp V_LP_N$ is unchanged, with $\|\mathscr B\|\le K_{d/2}$ as in GHC7--GHC11. Every prime power, both pole evaluations, the negative odd pole and the original common form domain remain.

GHC15 gives the common sufficient floor
$$
 \mathfrak b_3(c,N)=
 A\!\left(\frac{2\pi(N+1)}d\right)-K_{d/2}
          -\frac{d^3}{20N^3}.
$$
Whenever $\mathfrak b_3>0$, the existing resolvent and two-sided trace-ideal inequalities apply. At the SAME $N(c)=\lceil e^c\rceil$, $\mathfrak b_3/c\to1$ and hence $\mathfrak b_3\ge c/2$ eventually. Consequently
$$
 \boxed{\begin{aligned}
 \|(H_{\rm ext}^{\rm all})^{-1}
        -(\widehat H_{\rm ext}^{\rm all})^{-1}\|_1
 &<\frac{(\log c)^3}{5c^2N(c)^3},\\
 \|S_{c,N(c)}^{\rm all}-\widehat S_{c,N(c)}^{\rm all}\|_1
 &<\frac{K_{(\log c)/2}^{\,2}(\log c)^3}
                   {5c^2N(c)^3}
 =O\!\left(\frac{(\log c)^5}{c}e^{-3c}\right).
 \end{aligned}}
 \tag{GHC17}
$$
The last step reuses GHC8's $K_{(\log c)/2}^2=O(c(\log c)^2)$. This controls all $2N(c)+1$ actual retained coordinates without a dimension factor, also on the original cofinal FIB supports. The legal-trial transport of GHC7--GHC8 applies with this same exterior change; its initial quadratic and residual must still be transported together.

The gain is the actual cubic complete-source error and its explicit signed odd endpoint, rather than a new determinant or positivity criterion. Absolute accuracy still gives no sign for a vanishing Schur minimum, no relative control at that minimum, no complete determinant limit and no favorable joint prime discrepancy. The original same-source Robin strict upper, all-integer Robin above 5040 and RH remain unresolved. These deductions retain the inherited paper source/form premises and are not Lean/kernel-certified.

### The signed odd endpoint has a nonzero complete physical Schur contribution

Keep GHC10--GHC17's SAME full complex physical operator, retained block and complete coupling $\mathscr B=P_N^\perp V_{d/2}P_N$, now along integer $c\to\infty$, $d=\log c$ and $N=\lceil e^c\rceil$. Let $\widetilde H,\widetilde S$ denote the original uncorrected signed-Hilbert exterior and its Schur block, and $\widehat H,\widehat S$ the endpoint-corrected versions from GHC12--GHC17. The original exterior and Schur block are $H,S$. All these symbols retain the original support, domain, prime powers, both poles and physical orthonormal Fourier coordinates.

The added estimate evaluates the strength of the actual coupled endpoint. Classical partial summation, bounded-discrepancy summation and the rank-one resolvent formula are reused inside this source calculation. No general perturbation criterion, literature-priority claim, numerical execution or Lean/kernel verification is asserted.

#### The existing full prime counts fix the source scales

Reuse the classical unconditional PNT input already used in the [Robin source](../ArithSums/nicolas2025comparison.md), and the exact folded prime variance and consecutive-block discrepancies in [the complete-tail source, (2), (39), (48)](../Fourier/montgomery1978largesieve.md). Partial summation gives
$$
 W_c:=\sum_{2\le j<c}\frac{\Lambda(j)}{\sqrt j}=O(\sqrt c),
 \qquad
 \sum_{2\le j<c}\frac{\Lambda(j)^2}{j}
       \sim\frac12(\log c)^2.
$$
For the second application the proper-power part is $O(1)$, since
$\sum_p(\log p)^2/[p^2(1-1/p)]<\infty$; partial summation with
$\vartheta(x)\sim x$ supplies the prime part. The ordered resonance numerator
$\sum_{ab=c}\Lambda(a)\Lambda(b)$ is $O(d^2)$: it is zero for three or more distinct prime factors, has only the two ordered factors for two distinct prime bases, and equals $(k-1)(\log p)^2$ for $c=p^k$. Thus the SAME exact variance, including all resonances, satisfies
$$
 \boxed{K_{d/2}=O(\sqrt c),\qquad
 \mu_c=\frac12\left[
   \sum_{j<c}\frac{\Lambda(j)^2}{j}
   -\frac1{\sqrt c}\sum_{ab=c}\Lambda(a)\Lambda(b)\right]
       \sim\frac{d^2}{4}.}
 \tag{GHC18}
$$
The $K$ bound applies directly to G4's complete budget, with its full pole and bounded Gamma part. It does not replace that budget by the prime variance.

The existing actual symbol is
$s_c(n)=-\kappa-P_c(n)+h_c(n)$ for $n>0$, with
$\kappa=\pi/4$, $|h_c(n)|\le G_c/n$ and $G_c=O(\sqrt c\,d)$.
Its proved full-symbol budget gives $\sup_n|s_c(n)|=O(\sqrt c)$.
The already owned discrepancies are
$$
 \left|\sum_{n\in J}P_c(n)\right|\le D_cW_c,\qquad
 \left|\sum_{n\in J}(P_c(n)^2-\mu_c)\right|\le D_cW_c^2,
 \qquad D_c=(c+1)d,
$$
on every consecutive integer block $J$. These are polynomial in $c$; every alias remains in $\mu_c$.

#### Evaluate the same complete boundary-to-retained vector

Embed $\ell_N$ from GHC12 in the odd exterior and put
$r_{c,N}=\mathscr B^*\ell_N$. Reflection makes its even retained coordinates zero. Reuse the actual phase-adjusted physical entry
$(s_c(n)-s_c(m))/[\pi(m-n)]$ from the [existing Fourier identification](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.lean). In the normalized physical sine basis its odd folding is
$$
 Q^{\rm o}_{mn}=\frac2\pi(-1)^{m+n}
       \frac{m s_c(n)-n s_c(m)}{m^2-n^2}\qquad(m\ne n).
$$
Consequently every retained odd coordinate, including those next to $N$, has the exact absolutely convergent formula
$$
 \boxed{\begin{aligned}
 (r_{c,N})_m&=\frac{2\sqrt d}{\pi^2}(-1)^m
       [s_c(m)T_1(m)-mT_2(m)],\qquad 1\le m\le N,\\
 T_1(m)&=\sum_{n>N}\frac1{n^2-m^2},\\
 T_2(m)&=\sum_{n>N}\frac{s_c(n)}{n(n^2-m^2)}.
 \end{aligned}}
 \tag{GHC19}
$$
This is a calculation in the already identified physical coupling, not an asserted new Lean identification.

Set
$$
 \mathcal A(t)=\frac{\operatorname{arctanh}t}{t},\qquad
 G(t)=\frac{\log(1+t)}t,\qquad 0<t<1,
$$
with their continuous values at zero. Let $\delta=c^{-8}$ and first take $\delta N\le m\le(1-\delta)N$, $t=m/N$.
Decreasing-sum integration gives
$T_1(m)=\mathcal A(t)/N+O(N^{-2}\delta^{-1})$ and
$$
 m\sum_{n>N}\frac1{n(n^2-m^2)}
 =-\frac{\log(1-t^2)}{2Nt}+O(N^{-2}\delta^{-1}).
$$
Partial summation with the SAME $P_c$ discrepancy bounds its tail contribution to $mT_2$ by $O(D_cW_c/(N^2\delta))$. The full $h_c$ contribution is bounded using $G_c/n$, also at all exterior indices. Inserting $s_c(m)$ in GHC19 and using
$\mathcal A(t)+\log(1-t^2)/(2t)=G(t)$ therefore gives uniformly on this bulk
$$
 (r_{c,N})_m
 =-\frac{2\sqrt d\,(-1)^m}{\pi^2N}
       [\mathcal A(t)P_c(m)+\kappa G(t)]+O(c^{12}/N^2).
$$
For clarity, before the harmless polynomial majorization the error is bounded by
$$
 \frac{C\sqrt d}{N^2\delta}
 \left[\sup_n|s_c(n)|+1+D_cW_c
             +G_c(1+\log(2/\delta))\right].
$$
No cancellation of separately chosen extremizers is used.

All remaining rows are paid. For every $1\le m\le N$,
$T_1(m)\le C(1+\log N)/N$, and $m/n\le1$ in $T_2$.
Thus their complete contribution to $\|r_{c,N}\|^2$ is at most
$$
 C\,dc(1+\log N)^2
       \left(\frac{\delta}{N}+\frac1{N^2}\right)
       =o(d/N).
$$
This includes the last rows where $\mathcal A(m/N)$ would be singular; they are not omitted from the actual vector.

On the bulk, the supremum plus total variation of each weight
$\mathcal A^2,\mathcal A G,G^2$ is $O(d^2)$: $\mathcal A$ is increasing and $G$ decreasing.
The existing consecutive-block discrepancies and ordinary bounded-variation quadrature therefore replace $P_c^2$ by its SAME $\mu_c$ and $P_c$ by zero, with errors polynomial in $c$ divided by $N$. The squared bulk approximation error and its cross with the main profile contribute $o(d/N)$ as well. Finally
$\int_{[0,\delta]\cup[1-\delta,1]} \mathcal A(t)^2dt
=O(\delta\log^2(2/\delta))$.
These bounds establish the complete norm asymptotic
$$
 \boxed{\begin{aligned}
 \frac{\pi^4N}{4d}\|r_{c,N}\|^2
 &=\frac{\pi^2}{6}\mu_c+
      \kappa^2\left(\frac{\pi^2}{6}-2\log^22\right)+o(1),\\
 \|r_{c,N}\|^2&\sim\frac{d^3}{6\pi^2N}.
 \end{aligned}}
 \tag{GHC20}
$$
The integrals used here are
$\int_0^1 \mathcal A^2=\pi^2/6$ and
$\int_0^1 G^2=\pi^2/6-2\log^22$.
For the first, $t=\tanh u$ gives
$\int_0^\infty u^2/\sinh^2u\,du=\sum_{j\ge1}j^{-2}$.
The second follows by integration by parts and
$\int_0^1\log(1+t)/t\,dt=\pi^2/12$.
All source parameters grow together as specified; this is not a fixed-$c$ asymptotic with an unspecified $c$-dependent cutoff.

#### Transport the actual endpoint through the complete exterior inverse

Let
$$
 a_{c,N}=\langle\ell_N,\widetilde H^{-1}\ell_N\rangle,\qquad
 q_{c,N}=\mathscr B^*\widetilde H^{-1}\ell_N.
$$
These use the original uncorrected full-arithmetic model. Its floor is at least $c/2$ eventually. On the exterior the original Fourier diagonal has
$D_n=A(2\pi n/d)=\log(n/d)+O(d^2/n^2)$.
The vector $\ell_N$ belongs to this diagonal's operator domain, and
$$
 \|(D-c)\ell_N\|\le C(1+\log d)\|\ell_N\|,
 \qquad
 \|\ell_N\|^2\sim\frac d{\pi^2N}.
$$
The first inequality follows by summing
$n^{-2}(1+\log^2(n/N)+\log^2d)$; no uniform approximation of the unbounded diagonal by $cI$ is asserted.
GHC18 and the existing resolvent identity now yield
$\|\widetilde H^{-1}\ell_N-\ell_N/c\|
=O(c^{-3/2})\|\ell_N\|$. Multiplication by the SAME
$\|\mathscr B\|\le K_{d/2}=O(\sqrt c)$ gives
$$
 \boxed{\begin{aligned}
 a_{c,N}&\sim\frac d{\pi^2cN},\\
 \|q_{c,N}-r_{c,N}/c\|&=O(\|\ell_N\|/c),\\
 \|q_{c,N}\|^2&\sim\frac{d^3}{6\pi^2c^2N}.
 \end{aligned}}
 \tag{GHC21}
$$
The last relative conclusion uses the paid norm GHC20:
$\|r_{c,N}\|\sim(d/\sqrt6)\|\ell_N\|$. The coupling's global norm alone would not supply this conclusion.

Since $\widehat H=\widetilde H+\tau_d|\ell_N\rangle\langle\ell_N|$, the classical rank-one inverse formula gives the exact signed comparison
$$
 \boxed{\widehat S-\widetilde S=
    \frac{\tau_d}{1+\tau_da_{c,N}}
       |q_{c,N}\rangle\langle q_{c,N}|,\qquad
 \|S-\widehat S\|_1=O\!\left(\frac{d^3}{cN^3}\right).}
 \tag{GHC22}
$$
The denominator is positive eventually and tends to one; $\tau_d\to-1/4$. The second line is GHC17 with GHC18's sharper bound for the SAME $K$. Thus every complete arithmetic and pole contribution remains in $a,q,r$ and in the paid remainder.

In particular, with $e_c=r_{c,N}/\|r_{c,N}\|$ (nonzero eventually), the full retained matrices satisfy
$$
 \boxed{\begin{aligned}
 \left\|\frac{c^2N}{d^3}(S-\widetilde S)
       +\frac1{24\pi^2}|e_c\rangle\langle e_c|\right\|_1
       &\longrightarrow0,\\
 \operatorname{Tr}(S-\widetilde S)
       &\sim-\frac{d^3}{24\pi^2c^2N}.
 \end{aligned}}
 \tag{GHC23}
$$
Indeed
$\|\,|q\rangle\langle q|-|r/c\rangle\langle r/c|\,\|_1
\le(\|q\|+\|r/c\|)\|q-r/c\|=O(d^2/(c^2N))$,
and the cubic remainder is smaller than $d^3/(c^2N)$.
The positive-part trace of $S-\widetilde S$ is
$o(d^3/(c^2N))$, whereas its negative-part trace is
asymptotic to $d^3/(24\pi^2c^2N)$.
These norms compare matrices in the same physical retained space at each $c$; no fixed limiting vector or identification of different finite spaces is assumed.

GHC23 pays a nonzero signed contribution to the ACTUAL model discrepancy, including its complete source strength and direction. It does not assert that the original Schur block is negative or positive. A positivity certificate for the uncorrected Hilbert model must still pay this negative endpoint, and a certificate for the corrected model must still pay its cubic remainder and establish its own sign. No retained/cofinal Weil positivity, dense fixed-window theta positivity, original same-source Robin strict upper, determinant limit or RH follows. The inherited source/form premises and paper-only status remain.

### The complete prime--pole perturbation has sharp square-root spectral edges

Keep the full complex physical form and G1--G4's exact decomposition
$Q_L=q_{D_L}+\langle\cdot,V_L\cdot\rangle$ on its original form domain.
Let $c\to\infty$ through integers, $d=\log c$, $L=d/2$ and $a=e^L=\sqrt c$.
Write $I=(-L,L)$ and extend functions by zero. Put
$$
 u(x)=e^{x/2},\qquad v(x)=e^{-x/2},\qquad
 b=2\sinh L=a-a^{-1}.
$$
The paired prime and true two-pole operators are
$$
 \begin{aligned}
 (\mathsf P_Lf)(x)
 &=\sum_{2\le n<c}\frac{\Lambda(n)}{\sqrt n}
       [f(x+\log n)+f(x-\log n)],\\
 \mathsf R_L&=|u\rangle\langle v|+|v\rangle\langle u|,\\
 V_L&=\mathsf R_L-\mathsf P_L+B_L .
 \end{aligned}
 \tag{JPP1}
$$
These are G4's actual terms, with every prime power, both orientations and both poles retained.
The prime operator preserves nonnegative functions; it is not asserted to be positive semidefinite.
The periodic Gamma boundary correction is the SAME $B_L$ from G1, with
$\|B_L\|\le C_\Gamma(d)=O(1)$ from G2.

This application reuses the classical unconditional PNT already consumed in GHC18, the weighted Schur test, finite-rank block estimates, Riemann--Lebesgue and finite-torus recurrence.
The recurrence is already owned by
[PrimeOnlyNoGap.exists_pos_nsmul_mem](../../D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap.lean)
and the [Kronecker source](../Fourier/onishchik2020kronecker.md); no new general recurrence theorem is proposed.
The added calculation concerns the sharp complete source norm and its finite-complement spectral edges, not a new PNT or abstract perturbation theorem.
No literature-priority or Lean/kernel claim is made.

#### Pay the prime norm and its two actual pole directions together

For $t\ge1$, use the strict-endpoint sums
$$
 \Psi(t)=\sum_{2\le n<t}\Lambda(n),\qquad
 M(t)=\sum_{2\le n<t}\frac{\Lambda(n)}n .
$$
PNT gives $\Psi(t)=t+o(t)$ and the reused Chebyshev/partial-summation bound gives
$M(t)=O(1+\log t)$.
The actual zero-extended translations have the following almost-everywhere actions:
$$
 \begin{aligned}
 \mathsf P_Lu(x)&=u(x)[\Psi(e^{L-x})+M(e^{L+x})],\\
 \mathsf P_Lv(x)&=v(x)[M(e^{L-x})+\Psi(e^{L+x})].
 \end{aligned}
$$
Let $h=u+v>0$. For every fixed $\varepsilon>0$,
$\Psi(t)\le(1+\varepsilon)t+C_\varepsilon$ for all $t\ge1$.
Consequently
$$
 \mathsf P_Lh
 \le[(1+\varepsilon)a+O_\varepsilon(1+d)]h.
$$
Apply the classical weighted Schur inequality to this SAME positive-kernel finite translation sum.
Equivalently, use $2|f(x)f(y)|\le
|f(x)|^2h(y)/h(x)+|f(y)|^2h(x)/h(y)$ separately on each actual shift and then change variables.
Selfadjointness yields
$\|\mathsf P_L\|\le a(1+o(1))$.
No continuum approximation of the prime operator in operator norm has been made.

There is also an actual two-direction approximation, which must be paid before subtracting the pole.
Put $E(t)=\Psi(t)-t$. A change of variables gives
$$
 \|u(x)E(e^{L-x})\|_2^2
   =a\int_1^c\frac{|E(t)|^2}{t^2}\,dt
   =o(a^3).
$$
Here the last equality follows directly from $E(t)/t\to0$ by splitting at a fixed threshold; it is uniform in the growing upper endpoint.
The $M$ term is $O(d)\|u\|_2$, and $\|u\|_2^2=\|v\|_2^2=b\sim a$.
The reflected estimate holds for $v$.
On the SAME vectors
$$
 \mathsf R_Lu=d\,u+b\,v,\qquad
 \mathsf R_Lv=b\,u+d\,v .
$$
Thus, for the orthonormal vectors
$$
 e_+=\frac{u+v}{\sqrt{2(b+d)}},\qquad
 e_-=\frac{u-v}{\sqrt{2(b-d)}},
$$
one obtains
$$
 \boxed{\begin{aligned}
 \mathsf P_Le_+&=a e_++o(a),&
 \mathsf P_Le_-&=-a e_-+o(a),\\
 \|\mathsf P_L\|&\sim a,&
 \|(\mathsf P_L-\mathsf R_L)\mathsf E_L\|&=o(a),
 \end{aligned}}
 \qquad
 \mathsf E_L=|e_+\rangle\langle e_+|+|e_-\rangle\langle e_-|.
 \tag{JPP2}
$$
All vector errors are in $L^2(I)$; the last is an operator-norm estimate on this actual rank-two space.

The pole vanishes on $\mathsf E_L^\perp$.
The $\mathsf E_L$ block and its cross blocks of
$\mathsf R_L-\mathsf P_L$ are $o(a)$ by JPP2 and selfadjointness.
Its remaining block is
$-(I-\mathsf E_L)\mathsf P_L(I-\mathsf E_L)$, of norm at most $a(1+o(1))$.
Therefore
$$
 \boxed{\|\mathsf R_L-\mathsf P_L\|\le a(1+o(1)),
 \qquad \|V_L\|\le a(1+o(1)).}
 \tag{JPP3}
$$
This uses the common pole/prime alignment.
Adding separately optimized norms would give no such estimate.

#### The sharp signed edges survive every finite-dimensional removal

Fix $c$ temporarily.
Finite-torus recurrence supplies an unbounded sequence $t_j$ such that
$e^{it_j\log n}\to1$ for every contributing $n<c$.
It needs no rational independence.
For $U_tf=e^{itx}f$ the finite actual sum then satisfies
$$
 \|U_{t_j}^*\mathsf P_LU_{t_j}-\mathsf P_L\|\longrightarrow0 .
$$
Riemann--Lebesgue gives $U_{t_j}e_\pm\rightharpoonup0$.
The true pole is finite rank, so
$\|\mathsf R_LU_{t_j}e_\pm\|\to0$, while the SAME Gamma contribution remains bounded by $C_\Gamma(d)$.
It follows that the negative Rayleigh edge of $V_L$ is at most
$-\langle e_+,\mathsf P_Le_+\rangle+C_\Gamma(d)$,
and its positive edge is at least
$-\langle e_-,\mathsf P_Le_-\rangle-C_\Gamma(d)$.

More strongly, let $\mathsf F_c$ be ANY finite-rank orthogonal projection at each $c$.
Its rank, choice of vectors and dependence on $c$ are unrestricted.
For fixed $c$,
$\|\mathsf F_cU_{t_j}e_\pm\|\to0$.
Project these vectors into $\mathsf F_c^\perp$ and normalize; their bounded-operator Rayleigh values change by $o_j(1)$.
Writing $\lambda_-(c,\mathsf F_c)$ and $\lambda_+(c,\mathsf F_c)$ for the infimum and supremum of the compression's Rayleigh quotients on that complement, JPP2--JPP3 give
$$
 \boxed{\begin{aligned}
 \lambda_-(c,\mathsf F_c)/\sqrt c&\longrightarrow-1,\\
 \lambda_+(c,\mathsf F_c)/\sqrt c&\longrightarrow 1,\\
 \|V_L\|/\sqrt c&\longrightarrow1 .
 \end{aligned}}
 \tag{JPP4}
$$
The errors in the first two limits can be chosen independently of the finite projection.
The order of choices is essential: for each $c$ and its given finite projection, arbitrarily high recurrence times are allowed; no effective uniform recurrence time or bounded-frequency trial is asserted.
This is a statement about the bounded perturbation $V_L$.
Its modulated vectors pay an unbounded diagonal Gamma energy in the FULL form, so the negative edge proves no negativity of $Q_L$.

#### Consume the joint norm in a smaller complete exterior section

Let $\alpha>1$ be fixed and use the same physical Fourier projections at
$$
 N_\alpha(c)=\left\lceil e^{\alpha\sqrt c}\right\rceil .
$$
This changes only the finite section, with the original support and full operator unchanged.
Since $A(2\pi n/d)=\log(n/d)+O(d^2/n^2)$ on the exterior, JPP3--JPP4 give the actual full-complex exterior floor
$$
 A(2\pi(N_\alpha+1)/d)-\|V_L\|
     =(\alpha-1+o(1))\sqrt c.
$$
In particular the true exterior $H$ is eventually positive.
Let $\widehat H$ be GHC12--GHC17's corrected signed-Hilbert Gamma model on this SAME exterior.
Reuse their complete estimate
$\|H-\widehat H\|_1<d^3/(20N_\alpha^3)$.
Both floors are eventually at least $(\alpha-1)\sqrt c/2$, so the inherited inverse and trace-ideal estimates, with the SAME complete coupling
$\mathscr B=P_{N_\alpha}^\perp V_LP_{N_\alpha}$, give
$$
 \boxed{\begin{aligned}
 H,\widehat H&\succeq
       \frac{\alpha-1}{2}\sqrt c\,I,\\
 \|H^{-1}-\widehat H^{-1}\|_1
   &\le\frac{d^3}{5(\alpha-1)^2cN_\alpha^3},\\
 \|S-\widehat S\|_1
   &=O_\alpha\!\left(\frac{d^3}{N_\alpha^3}\right).
 \end{aligned}}
 \tag{JPP5}
$$
These estimates cover all $2N_\alpha+1$ retained coordinates and every actual source term, with no retained-rank factor.
They apply along any of the original unbounded integer FIB support schedules as well.
The finite section is defined anew at this cutoff; no old finite matrix, trial or cache is identified with it.
GHC20--GHC23's inverse asymptotic at $N=\lceil e^c\rceil$ is not asserted at the new cutoff.

JPP3--JPP5 give a sharp leading complete perturbation budget, its two signed finite-complement edges, and an actual exterior/model comparison at the smaller cutoff.
G4's separate allowance is asymptotic to $6\sqrt c$; no $o(\sqrt c)$ complete-complement norm allowance is possible, despite the pole cancellation on its own two directions.
This last boundary concerns a norm-only method, not the attainable positivity threshold of the full form with its frequency-dependent diagonal.
No finite retained Schur sign, cofinal Weil positivity, original same-source strict Robin upper, determinant limit or RH is established.
The original source/form premises and paper-only status remain.

### The complete odd endpoint has a smaller error at the Schur minimum

Keep GHC18--GHC23's SAME complete physical operator, exterior models and coupling, with integer $c\to\infty$, $d=\log c$ and
$N=\lceil e^c\rceil$.
This subsection uses that original cutoff; it does not transport the inverse asymptotic to JPP5's smaller section.
All vectors and Schur matrices use the inherited physical orthonormal coordinates.
The added source input is the WHOLE action on $\ell_N$, including its exterior component, rather than only the already owned retained vector
$r=\mathscr B^*\ell_N$.

#### Pay every zero-extended prime translate of the boundary vector

In the normalized odd sine basis, GHC12's vector has coefficients
$\sqrt d(-1)^n/(\pi n)$ for $n>N$.
Writing $z=x+d/2\in(0,d)$, its actual physical function is
$$
 g_N(z)=\frac{\sqrt2}{\pi}
       \sum_{n>N}\frac{\sin(2\pi nz/d)}n,\qquad
 \|\ell_N\|^2=\frac d{\pi^2}\sum_{n>N}\frac1{n^2}
       \sim\frac d{\pi^2N}.
$$
Let $\delta=d/N$.
The classical sawtooth Fourier series and Dirichlet summation give, almost everywhere,
$$
 |g_N(z)|\le C\min\!\left(1,
       \frac{\delta}{\operatorname{dist}(z,\{0,d\})}\right).
 \tag{JLS1}
$$
Indeed, away from the endpoints summation by parts bounds the tail by
$C/[N|\sin(\pi z/d)|]$.
Within distance $\delta$, the full sawtooth is bounded and
$\sum_{n\le N}|\sin(2\pi nz/d)|/n\le2\pi$ after reflection to the nearer endpoint.
This is an estimate for the actual Fourier tail, not a replacement profile.

Reuse JPP1's complete prime operator $\mathsf P_L$ and weights
$w_n=\Lambda(n)/\sqrt n$.
Each of its two zero-extended translates has one internal peak, centered at
$\log n$ or $d-\log n$.
Its other endpoint lies outside $(0,d)$ by at least $\log2$, and contributes a pointwise envelope at most $C\delta$.
Coincident internal centers are grouped before estimating.
Each group has multiplicity at most two; the coincidences include every actual ordered resonance $nm=c$.
Distinct grouped centers are separated by at least $1/(2c)$, since either their distance is a nonzero $\log(n/m)$ or a nonzero $\log(nm/c)$ with integer numerator data.

For $a_\xi(z)=\min(1,\delta/|z-\xi|)$, the elementary overlap bounds on $(0,d)$ are
$$
 \int a_\xi^2\le C\delta,\qquad
 \int a_\xi a_\eta
   \le\frac{C\delta^2}{|\xi-\eta|}(1+\log N)
       \quad(\xi\ne\eta).
$$
For the second, partition according to the nearer center; the other factor is at most
$2\delta/|\xi-\eta|$, and $\int a_\xi\le C\delta(1+\log N)$.
The sum of squared grouped weights is at most
$4\sum_{n<c}w_n^2$, and their total weight is at most $2W_c$.
The outside-endpoint envelopes have squared integral at most
$Cd\delta^2W_c^2$.
Thus, retaining all groups, cross terms and outside endpoints, the WHOLE prime action satisfies
$$
 \|\mathsf P_L\ell_N\|^2
 \le C\left[
   \delta\sum_{n<c}\frac{\Lambda(n)^2}{n}
       +\delta^2c(1+\log N)W_c^2\right].
$$
Here $d\le c(1+\log N)$ absorbs the outside-endpoint term.
The original cutoff has $\delta\ll1/c$.
GHC18's existing full prime-power sums give
$W_c^2=O(c)$ and $\sum_{n<c}\Lambda(n)^2/n=O(d^2)$.
Consequently
$\|\mathsf P_L\ell_N\|=O(d)\|\ell_N\|$.
No independence or favorable cancellation of distinct prime translates has been assumed.

The other actual source terms are also paid.
For JPP2's normalized odd pole direction $e_-$, direct integration against the physical sine basis gives
$|\langle\phi_n^{\rm o},e_-\rangle|\le C\sqrt d/n$ for large $c$ and $n>N$.
Since $\mathsf R_Le_-=(d-b)e_-$ and $\ell_N$ is odd,
$$
 \|\mathsf R_L\ell_N\|\le C\sqrt c\,d/N .
$$
The SAME Gamma boundary term has norm $O(1)$ by G2.
It follows that
$$
 \boxed{\|V_L\ell_N\|=O(d)\|\ell_N\|.}
 \tag{JLS2}
$$
This improves the global $\sqrt c$ source budget on this particular actual vector and includes the exterior-to-exterior response.
The recurrence vectors of JPP4 do not give a contrary bound on this fixed vector.

#### Transport the vector and its frequency weight together

Let $\widetilde H,\widetilde S$ be GHC21's original uncorrected signed-Hilbert model and let
$q=\mathscr B^*\widetilde H^{-1}\ell_N$.
The diagonal-domain estimate
$\|(D-c)\ell_N\|=O(1+\log d)\|\ell_N\|$
and the exterior floor $\widetilde H\succeq(c/2)I$ are already owned.
The difference between the original and uncorrected exterior has operator norm $O(d/N)$:
its endpoint is rank one of norm $O(\|\ell_N\|^2)$ and its remaining Gamma error is cubic.
Thus JLS2 and the SAME vector resolvent identity give
$$
 \boxed{\begin{aligned}
 \|\widetilde H^{-1}\ell_N-\ell_N/c\|
     &=O(d/c^2)\|\ell_N\|,\\
 \|q-r/c\|&=O(d/c^{3/2})\|\ell_N\|,\\
 \|q\|&\sim\frac d{\sqrt6\,c}\|\ell_N\|.
 \end{aligned}}
 \tag{JLS3}
$$
The second line uses the complete coupling norm $O(\sqrt c)$.
The last norm is reused from GHC20--GHC21, not recalculated from a generic bound.

The retained diagonal must also be paid on the actual $r$.
Reuse GHC20's complete bulk formula with $\delta_0=c^{-8}$ and its actual profiles
$\mathcal A(t)=\operatorname{arctanh}(t)/t$ and
$G(t)=\log(1+t)/t$.
The additional weights are controlled because
$$
 \int_0^1[\mathcal A(t)^2+G(t)^2]\log^2t\,dt<\infty.
$$
On $\delta_0\le t\le1-\delta_0$ their weighted variations have polynomial bounds in $c$, so the SAME full prime discrepancies give polynomial-in-$c$ errors divided by $N$.
The actual bulk approximation error remains negligible after multiplication by $O(c)$.
Every excluded row is still included: GHC20's bound for its unweighted squared norm is
$O(dc(1+\log N)^2(\delta_0/N+N^{-2}))$.
Multiplying it by $O(c^2)$ gives $o(d^3/N)$.
Thus with $D_N=P_ND_LP_N$ on the full retained space,
$$
 \|(D_N-c)r\|\le C(1+\log d)\|r\|.
$$
This is a new weighted consumption of the existing actual profile, not a fixed-head limit or a deletion of the cutoff rows.

On the retained space $\|D_N-c\|=O(c)$.
Also
$\|\widetilde S-D_N\|\le\|V_L\|+
\|\mathscr B\|^2\|\widetilde H^{-1}\|=O(\sqrt c)$.
Combining these bounds with JLS3, the normalized actual endpoint
$\nu_c=q/\|q\|$ satisfies
$$
 \boxed{\|(\widetilde S-cI)\nu_c\|=O(\sqrt c).}
 \tag{JLS4}
$$
It is concentrated near the high Schur energy $c$; no assertion about a full-form eigenfunction or a simple minimum is used.

#### Pay the negative endpoint at the lowest Schur value

Reuse GHC22's exact signed formula. For sufficiently large $c$, put
$$
 \varepsilon_c=
 -\frac{\tau_d}{1+\tau_d a_{c,N}}\|q\|^2
 \sim\frac{d^3}{24\pi^2c^2N}>0 .
$$
Then
$\widehat S=\widetilde S-\varepsilon_c|\nu_c\rangle\langle\nu_c|$.
JLS4 applies to $\widehat S$ as well, since $\varepsilon_c=o(1)$.
The classical spectral theorem therefore gives the whole low-energy projection bound
$$
 \left\|
 \mathbf1_{(-\infty,c/2]}(\widehat S)\nu_c
 \right\|^2=O(1/c).
$$
The uncorrected Schur minimum is at most
$A_0+\|V_L\|=O(\sqrt c)$ by the retained constant vector and the negative Schur charge.
Thus a unit minimizing vector $w$ for $\widehat S$ lies in this low-energy space.
For any such vector, with no simplicity assumption,
$|\langle\nu_c,w\rangle|^2=O(1/c)$.
The variational principle yields
$$
 \boxed{0\le
 \lambda_{\min}(\widetilde S)-\lambda_{\min}(\widehat S)
       \le C\varepsilon_c/c
       =O\!\left(\frac{d^3}{c^3N}\right).}
 \tag{JLS5}
$$
This uses the evaluated complete source vector and its frequency weight.
The total trace charge from GHC23 alone would give only the larger scale $\varepsilon_c$.

Finally let
$\rho_c=\|S-\widehat S\|\le\|S-\widehat S\|_1
=O(d^3/(cN^3))$, the already paid complete cubic Gamma remainder.
For the ORIGINAL physical Schur matrix,
$$
 \boxed{
 -C\varepsilon_c/c-\rho_c
 \le\lambda_{\min}(S)-\lambda_{\min}(\widetilde S)
 \le\rho_c.}
 \tag{JLS6}
$$
All minima are those of the same finite physical Schur space at the original cutoff; they are not identified with the full operator's ground-state value.
This reduces the asymptotic endpoint allowance needed at the Schur minimum by a factor $c$, while retaining its negative sign and all source terms.
It does not evaluate the remaining model minimum or give its positive margin.
No new sign certificate at $c=27,N=1280$, retained/cofinal Weil positivity, original same-source strict Robin upper, determinant limit or RH follows.
All statements remain paper applications under the inherited source/form premises, without Lean/kernel certification or a literature-priority claim.


### A smaller negative-index budget for the complete physical form

Keep JPP1--JPP5's entire complex physical operator, its original form domain and its source/form identification. Let $c\to\infty$ through integers, $d=\log c$, $a=\sqrt c$, and write
$$
 \mathcal H_c=D_L+\mathsf R_L-\mathsf P_L+B_L
 \quad\text{on }L^2((-d/2,d/2)).
$$
The Gamma diagonal has compact resolvent and the remaining operator is bounded, so $\mathcal H_c$ is selfadjoint, bounded below and has compact resolvent. Let $n_-(\mathcal H_c)$ count its strictly negative eigenvalues, with multiplicity. Then
$$
 \boxed{\limsup_{\substack{c\to\infty\\c\in\mathbb N}}
 \frac{\log(1+n_-(\mathcal H_c))}{\sqrt c}\le\frac23.}
 \tag{NPC1}
$$
Equivalently, for every fixed $\varepsilon>0$, eventually
$n_-(\mathcal H_c)\le\exp((2/3+\varepsilon)\sqrt c)$.
The start can depend on $\varepsilon$. This is an upper bound on possible negative multiplicity, not an assertion that a negative eigenvalue exists.

This source-specific application reuses JPP's complete prime/pole norm and exterior comparison, the classical bounded-variable exponential estimate, Selberg's discrete large sieve, Hilbert--Schmidt ideal bounds, the min--max principle and the trace inequality of [Junge--LaRacuente, arXiv:2009.11866v2, Theorem 1.2](https://arxiv.org/pdf/2009.11866v2). Independent circle variables below extract finite Laurent coefficients exactly; they are not a probability model for actual prime phases. No new general concentration, trace or spectral-counting theorem, literature-priority claim or Lean/kernel certification is proposed. All proper prime powers, both orientations, both poles and the actual Gamma boundary remain present.

#### Growing moments on the actual Fourier exterior

Fix $0<\kappa<1$, $\tau>1$ and $0<\eta<\kappa$. Put
$$
 N=\lceil e^{\kappa a}\rceil,\qquad Q=\mathbf1_{\{|m|>N\}},
 \qquad A=Q\mathsf P_LQ\big|_{\operatorname{ran}Q},
 \qquad \rho=Qe^{-\tau D_L}Q,\quad Z=\operatorname{Tr}\rho.
$$
The projection uses JPP's physical orthonormal Fourier coordinates; it is not a finite band or a periodic replacement of the zero-extended prime translations. The actual Gamma eigenvalues $A_m$ give, with $h_m=e^{-\tau A_m}$,
$$
 \log Z=-(\tau-1)\kappa a+o(a),\qquad
 \frac{h_{N+1}}{Z}=O_\tau(N^{-1}).
$$
For sufficiently large $c$, uniformly for integers $1\le r\le\lfloor\eta a/d\rfloor$, there is an absolute $C$ such that
$$
 \boxed{\frac{\operatorname{Tr}(\rho A^{2r})}{Z}
       \le(Crd^2)^r.}
 \tag{NPC2}
$$
The starting scale may depend on the three fixed parameters. Here every intermediate $Q$ in $A^{2r}$ is included.

To pay both arithmetic frequencies and these projections, write $w_n=\Lambda(n)/\sqrt n$, $W=\sum_{2\le n<c}w_n=O(a)$ and $K=\|\mathsf P_L\|\sim a$. Expand $\mathsf P_L^r\phi_m$ into actual signed translation words. A word with partial sums $S_j$ contributes only where $x+S_j\in(-d/2,d/2)$ for every $0\le j\le r$. Group its nonnegative coefficient function by its exact rational endpoint $q=e^{S_r}$, and denote the resulting function by $C_r(q,x)$. Put
$$
 E_r=\frac1d\int_{-d/2}^{d/2}\sum_q C_r(q,x)^2\,dx.
$$
For each surviving word, its total positive and negative logarithmic increments differ by less than $d$. Counting the two signs therefore bounds both reduced endpoint integers by $H_r=c^{\lceil r/2\rceil}$. If two endpoints are active at the same $x$, their ratio lies strictly between $1/c$ and $c$. Distinct endpoints cannot then alias modulo multiplication by an integral power of $c$. Their active circular Fourier frequencies have separation at least
$$
 \delta_r=\frac{\log(1+1/(cH_r^2))}{d},\qquad
 D_r=\delta_r^{-1}\le2d\,c^{r+2}.
$$
At each fixed $x$, restrict to its finite active endpoint set. The discrete large-sieve inequality (1) of the [existing Montgomery source](../Fourier/montgomery1978largesieve.md) applies to its $\delta_r$-separated circular frequencies and coefficients $C_r(q,x)$. Its constant is uniform in both the active set and the initial integer sample. After integration, for every integer $U\ge0$ and $H\ge1$ it gives
$$
 \sum_{m=U+1}^{U+H}\|\mathsf P_L^r\phi_m\|^2
 \le(H-1+D_r)E_r.
$$
Here disjoint-support aliases are removed separately at each $x$; no assertion of separation for the global endpoint list is needed. With $U=N$, summation by parts against the actual decreasing $h_m$ gives
$$
 \sum_{m>N}h_m\|\mathsf P_L^r\phi_m\|^2
 \le E_r\left[\sum_{m>N}h_m+(D_r-1)h_{N+1}\right].
$$
The terminal term vanishes since the unweighted partial sums are $O(H)$ for each fixed $c,r$. The negative modes have the same norms by complex conjugation, so
$$
 \frac{\operatorname{Tr}(\rho\mathsf P_L^{2r})}{Z}
 \le E_r\left[1+2(D_r-1)\frac{h_{N+1}}Z\right]
 \le E_r\left[1+O_\tau\!\left(\frac{D_r}{N}\right)\right].
 \tag{NPC3}
$$
This relative bound uses the coefficient energy rather than the sum of absolute cross coefficients. Its trace retains all output frequencies; it has not yet replaced the compressed moment in NPC2.

Dropping the surviving-prefix indicators gives nonnegative unrestricted word coefficients $G_r(q)$ and $E_r\le\sum_qG_r(q)^2$. Unique prime factorization identifies the latter sum with the constant coefficient of the $2r$th power of the finite Laurent polynomial for the paired prime-power shifts. Grouping by prime gives independent auxiliary circle polynomials
$$
 X_p(\theta_p)=2\log p\sum_{\substack{j\ge1\\p^j<c}}
                 p^{-j/2}\cos(j\theta_p),\qquad
 |X_p|\le b_p=\frac{2\log p}{\sqrt p-1},\qquad
 \sum_{p<c}b_p^2\le C_0d^2.
$$
The last estimate is the classical Chebyshev bound with partial summation. Each $X_p$ has mean zero. The classical convexity bound
$\mathbb E e^{tX_p}\le\cosh(tb_p)\le e^{t^2b_p^2/2}$ gives the even-moment estimate
$E_r\le(C_1rd^2)^r$ for every integer $r\ge1$. This is exact finite coefficient extraction followed by an auxiliary integral bound; the actual Fourier phases remain accounted for in NPC3. Uniformly on the stated range,
$$
 \log\!\left(\frac{D_r}N\right)
 \le(\eta-\kappa)a+o(a),
$$
so NPC3's relative factor tends to one.

It remains to pay every intermediate projection. Write $F=I-Q$. The actual Fourier translation overlaps give
$$
 |(\mathsf P_L)_{nm}|\le\frac{2W}{\pi|n-m|}\quad(n\ne m),
 \qquad
 L_N^2:=\|F\mathsf P_LQ\|_{\rm HS}^2
       \le C_2W^2(1+\log N).
$$
Extend $A$ by zero on $\operatorname{ran}F$. Exact telescoping on exterior inputs gives
$$
 (\mathsf P_L^r-A^r)Q
 =\sum_{j=0}^{r-1}\mathsf P_L^{r-1-j}F\mathsf P_LQ A^jQ.
$$
The Hilbert--Schmidt ideal inequality, with the heat factor kept on the right, therefore gives
$$
 \frac{\|(\mathsf P_L^r-A^r)\rho^{1/2}\|_{\rm HS}}{\sqrt Z}
 \le rK^{r-1}L_N\sqrt{h_{N+1}/Z}
 \le\exp\!\left(\left[\frac{\eta-\kappa}{2}+o(1)\right]a\right).
$$
This tends to zero uniformly. The Hilbert--Schmidt triangle inequality and NPC3 prove NPC2 after increasing $C$. No ordering between $(Q\mathsf P_LQ)^{2r}$ and $Q\mathsf P_L^{2r}Q$ is used.

#### Use the heat bound as a count, without asserting positivity

On the same exterior let
$$
 H_E=Q\mathcal H_cQ\big|_{\operatorname{ran}Q}
     =D_E-A+C_E,\qquad C_E=Q(\mathsf R_L+B_L)Q.
$$
JPP's actual pole bound
$\|\mathsf R_LQ\|\le(\sqrt2/\pi)a\sqrt{d/N}$ and $\|B_L\|=O(1)$ give $\|C_E\|=O(1)$. The cited trace inequality, applied with the faithful reference $e^{-\tau D_E}$ and bounded factors $-\tau C_E/2$, $\tau A/2$, gives
$$
 \operatorname{Tr}e^{-\tau H_E}
 \le e^{\tau\|C_E\|}\operatorname{Tr}(\rho e^{\tau A}).
$$
Equivalently one may first bound the eigenvalues after replacing $C_E$ by $-\|C_E\|I$ and then use the ordinary Golden--Thompson trace inequality. This is trace monotonicity from min--max, not operator monotonicity of the exponential.

Take $r=\lfloor\eta a/d\rfloor$. For real $|x|\le K$, Taylor's remainder gives
$$
 e^{\tau x}\le\sum_{j=0}^{2r-1}\frac{(\tau x)^j}{j!}
           +e^{\tau K}\frac{x^{2r}}{K^{2r}}.
$$
In the positive state $\rho/Z$, NPC2 and scalar Hölder on $A$'s spectral measure bound the polynomial term by
$\exp(\tau\sqrt{Cr}\,d)=\exp(o(a))$. Its remainder allowance is
$$
 e^{\tau K}\left(\frac{Crd^2}{K^2}\right)^r
 =\exp\!\left(\left[\tau-\frac\eta2+o(1)\right]a\right).
$$
Consequently the complete exterior heat trace satisfies
$$
 \boxed{\limsup_{c\to\infty}
 \frac{\log\operatorname{Tr}e^{-\tau H_E}}a
 \le L(\kappa,\tau,\eta):=
 \tau-(\tau-1)\kappa-\frac\eta2.}
 \tag{NPC4}
$$
All three parameters stay fixed in this limit. The positive value of $L$ prevents this allowance from certifying exterior positivity; it still supplies a signed spectral count.

Every negative eigenvalue of $H_E$ contributes more than one to its heat trace. Restricting a full negative subspace to the Fourier exterior loses at most $\operatorname{rank}F=2N+1$ dimensions, regardless of its cross blocks. The min--max principle thus gives
$$
 \boxed{n_-(\mathcal H_c)
 \le 2N+1+n_-(H_E)
 \le2N+1+\operatorname{Tr}e^{-\tau H_E}.}
 \tag{NPC5}
$$
In particular its upper exponential rate is at most $\max(\kappa,L)$. Set
$\kappa=2/3$, $\tau=1+\delta$, $\eta=2/3-\delta$ for any fixed $0<\delta<2/3$. Then
$$
 L=\frac23+\frac56\delta.
$$
First take $c\to\infty$ at each fixed $\delta$, then let $\delta\downarrow0$. This proves NPC1 without taking the inadmissible values $\tau=1$ or $\eta=\kappa$, and without a uniform starting scale at either endpoint. The norm-only comparison using JPP3 gives an upper rate $1$ instead of $2/3$.

#### Consume the count in the original retained Schur matrix

For every fixed $\alpha>1$, JPP5 supplies the positive complete exterior for all sufficiently large integer $c$; the starting scale may depend on $\alpha$. Use its actual Fourier cutoff $N_\alpha=\lceil e^{\alpha a}\rceil$ and denote that exterior by $H_\alpha$. Let $F_\alpha=I-Q_{N_\alpha}$, $\mathscr B_\alpha=Q_{N_\alpha}(\mathsf R_L-\mathsf P_L+B_L)F_\alpha$, and keep the original finite Schur matrix
$$
 S_\alpha=F_\alpha\mathcal H_cF_\alpha
          -\mathscr B_\alpha^*H_\alpha^{-1}\mathscr B_\alpha.
$$
Completion of the square in the full form, using the strictly positive $H_\alpha$, gives the classical exact inertia identity
$$
 \boxed{n_-(S_\alpha)=n_-(\mathcal H_c),\qquad
 \limsup_{c\to\infty}
 \frac{\log(1+n_-(S_\alpha))}{\sqrt c}\le\frac23.}
 \tag{NPC6}
$$
Thus the bound applies to the same complete retained matrix, including every coupling and every arithmetic, pole and Gamma term. It covers every original source direction; no positive subclass replaces the full form. It also applies along the original unbounded integer FIB support schedules.

NPC1 and NPC6 bound possible negative multiplicity more strongly than the leading norm-only budget. They do not identify a negative eigenspace, provide a computable smaller Fourier section, determine the remaining Schur minimum or prove that its negative index is zero. In particular they give no $\kappa<1$ positive exterior floor, cofinal Weil positivity, original same-source Robin upper or RH proof. The inherited source/form premises and paper-only status remain.
