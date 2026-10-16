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
