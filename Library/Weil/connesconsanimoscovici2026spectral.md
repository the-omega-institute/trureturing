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
The outstanding task is a directed full-space consumer with the
common-form error congruence, including these small directions.
The fixed-vector pilot does not prove full retained positivity, the
original Robin tail, cofinal Weil positivity or RH. No new general
residual theorem, originality or Lean-verification claim is made.

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
