---
bibkey: wang2026proportions
authors: Biao Wang
year: 2026
title: Proportions of the non-trivial zeros of the Riemann zeta function
doi: null
url: https://arxiv.org/abs/2609.24167v1
claim: Historical v1 reports a spectral correction and a three-point improvement for zero proportions; v2 was withdrawn on 6 October 2026. The retained finite identities are independently checked in Section 21, whose same-kernel analytic consumer uses Lamzouri's energy estimate and supplies no full Weil positivity or FIB-to-zeta identification.
strata_touched: []
license: citation-only
triage: anchor
---

# The September spectral correction to the zero-proportion method

**Version status, checked 8 October 2026.** [arXiv:2609.24167v2](https://arxiv.org/abs/2609.24167v2), dated 6 October 2026, is withdrawn. The author's comments field reads: “New method is need to obtain good improvement”. The theorem and lemma numbers below refer to the preserved [v1 text](https://arxiv.org/html/2609.24167v1), and its displayed mathematical claims retain that historical status. The new [Section 21](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) gives its own finite proof and uses [Lamzouri v2 §3](https://arxiv.org/html/2609.02882v2) for the matching analytic energy. The [trmdy source note](trmdy2026simplezeros.md) records the stronger October proportions and their explicit computational proof assumptions.

This note records the incremental interface beyond the existing [golden-observer research account](../../docs/develop/theory/GOLDEN_OBSERVER_RH_ROUTE.md). The inspected primary versions are [Alpöge–Furman v2](https://arxiv.org/abs/2608.13637v2), submitted 19 August 2026; [Lamzouri v2](https://arxiv.org/abs/2609.02882v2), submitted 8 September; and [Wang v1](https://arxiv.org/abs/2609.24167v1), submitted 21 September. These are the version dates in their arXiv histories checked on 1 October 2026; their internal PDF dates differ. This is a review of statements and selected proof interfaces, without a full independent proof audit or a new Lean build.

## The finite correction stated in Wang v1

Let $Z$ be a nonempty finite multiset invariant under complex conjugation, including multiplicities. For real even $\eta\in L^2(\mathbb R)$ supported in $(-\lambda,\lambda)$, with $\lambda>0$ and $\int\eta^2=1$, put $K=\widehat{\eta^2}$ using Fourier phase $e^{-2\pi i\xi u}$. Let $x_1,\ldots,x_n$ be exactly the simple real elements of $Z$, and define

$$
G_K=(K(x_j-x_\ell))_{j,\ell=1}^n,\qquad
\Psi(t)=\begin{cases}(t-1)^2,&0\le t\le2,\\2t-3,&t\ge2,\end{cases}
\qquad \Delta_K(Z)=\operatorname{tr}\Psi(G_K).
$$

Here $G_K$ is positive semidefinite and $\Delta_K\ge0$, with $\Delta_K=0$ when $n=0$. With $N=|Z|$ counting multiplicity and $D$ counting distinct elements, Wang v1 Proposition 2.1 states

$$
n\ge2N-E_K(Z)+\Delta_K(Z),\qquad
D\ge\frac32N-\frac12E_K(Z)+\frac12\Delta_K(Z),
\qquad E_K(Z)=\sum_{z,s\in Z}K(z-s)^2.
$$

The summands in $E_K$ are **complex squares**, not squared absolute values. For the self-adjoint finite operator $A=\sum_{z\text{ distinct}}m_zf_z\otimes f_{\bar z}$, where $f_z(u)=\eta(u)e^{-2\pi iuz}$, the inner product is linear in its first argument and $(v\otimes w)\xi=\langle\xi,w\rangle v$, the exact identities are $\operatorname{tr}A=N$ and $\operatorname{tr}(A^2)=E_K$. The total is real and nonnegative; individual summands need not be. Dropping $\Delta_K$ recovers equations (2.4)–(2.5) of Lamzouri's Proposition 2.1.

There is a necessary dimension condition when reusing this correction. The synthesis map $V:\mathbb C^n\to W$ gives $P=VV^*$ and $G_K=V^*V$. Their nonzero spectra agree, but $\Psi(0)=1$, so one cannot replace $\operatorname{tr}\Psi(G_K)$ by $\operatorname{tr}\Psi(P)$ in a different ambient dimension. The proof instead transports $\Phi(t)=2t-1+\Psi(t)$, for which $\Phi(0)=0$, obtaining $\operatorname{tr}\Phi(P)=n+\Delta_K$.

## What controls the correction

Lemma 3.1 bounds $\Delta_K\ge2e_*J$ when there are $J$ disjoint triples of simple real points, each with the sum of its three squared pair overlaps at least $e_*$, where $0\le e_*\le1/2$. For the Montgomery–Taylor density and kernel,

$$
f_0(u)=\frac{\cos(\sqrt2u)}{\sqrt2\sin(1/\sqrt2)}\mathbf1_{[-1/2,1/2]}(u),
\qquad K_0=\widehat f_0,
$$

Lemma 3.2 gives, for $H>0$, $u,v\ge0$ and $u+v\le H$,

$$
K_0(u)^2+K_0(v)^2+K_0(u+v)^2
\ge e(H):=\frac{(\sqrt5-2)^2}{(1+2\pi^2H^2)^2}>0.
$$

For zeta, the multiset is $Z_T=\{i(\rho-1/2)\log T/(2\pi):0<\operatorname{Im}\rho\le T\}$, with multiplicities. Its simple real points are exactly the simple critical zeros. Splitting their containing interval into cells of fixed length $H>0$ supplies the triples. The smoothing and pair-correlation estimate in Lemma 4.1 give the matching value of $E_K$ for this same multiset. The order is $T\to\infty$ at fixed smoothing, then smoothing tends to zero. Lamzouri's §3 removes the original pair-correlation weight by modifying the test functions; deleting that weight without this argument would not give the required unweighted sum.

The historical v1 Theorem 1.1 states the unconditional lower limiting proportions

$$
\liminf_{T\to\infty}\frac{N_0^s(T)}{N(T)}\ge C_0+\delta_0,
\qquad
\liminf_{T\to\infty}\frac{N_d(T)}{N(T)}\ge\frac{1+C_0}{2}+\frac{\delta_0}{2},
$$

where $C_0=3/2-\cot(1/\sqrt2)/\sqrt2$ and $\delta_0=6.66624\ldots\cdot10^{-8}$. These are the paper's stated values. The gain comes from controlling additional overlap information of the actual configuration. It does not exclude every off-line zero.

## Reuse and the remaining FIB obligation

The project already contains the [AF rank–trace port](../../D5/S3/Weil/ZetaLinear/RankTrace.lean) from upstream commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`; a new wrapper would repeat existing mathematics. Its [inverse-fourth zero-tail bounds](../../D5/S3/Weil/BurnolGram/ExplicitWeilFourthMomentTail.lean) have a different purpose from asymptotics for $\operatorname{tr}(\widetilde G^4)$. The latter require joint prime/zero correlation estimates, which are not supplied by an inverse-power tail bound.

Likewise, [negative rational test functions from an off-line zero](../../D5/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy.lean) are already available under the module's explicit `ZeroData` interface. The missing all-zero input is an independent lower bound for the prime-side energy of the same required tests, strong enough to rule out their negative margins. The source existence, test class and approximation/tail premises must be retained when applying those interfaces. None of the three reviewed proportion papers supplies this full positivity assertion.

There is a numerical connection worth keeping in its exact scope: $\sqrt5-2=\varphi^{-3}$ equals the absolute contraction rate of a three-position FIB window. Wang obtains the constant from a three-point trigonometric compatibility estimate, not from a Zeckendorf address or its seam automaton. The identity of constants supplies no map from FIB branches to the actual zeta tests or their Gram overlaps.

An invertible change of test coordinates transports both the positive Gram metric $H$ and Weil matrix $Q$ to $S^*HS$ and $S^*QS$. For an independent family, the represented operator $H^{-1}Q$ changes by similarity, while the form's inertia is preserved. Thus a FIB rotation or nonunitary scale used solely as a coordinate change supplies no spectral gain. Selecting genuinely new test subspaces or controlling their overlaps could add information; it requires an explicit synthesis into the actual Weil test space and estimates for that same arithmetic realization. No such FIB identification is established here.

## Scope of the often quoted two-moment ceiling

AF §7.2 restricts its approximately $0.6818$ obstruction to configuration-wise valid bandwidth-one certificates with specified moment information. Its numerical argument includes `hvalid`, the interval-enclosure hypothesis `EnclOK`, and a derivative remainder. For the displayed regularity range it obtains a bound below $0.6819$; the bare decimal is not a universal ceiling for every finite Weil or FIB method. The paper says the enclosure certificate at tag v1.0 is not Lean-kernel checked, and its configuration-averaging step is on paper. No external formal project was rebuilt in this review. Higher normalized moments or even a proportion-one conclusion also leave possible finite or zero-density exceptions; full RH requires the additional all-zero control described above.


## Gaussian-localized short multipliers and the quadratic certificate

R. Arun Chandru, *Quadratic deformations of reflected zeta-zero forms*,
[DOI 10.5281/zenodo.22817955](https://doi.org/10.5281/zenodo.22817955),
§1.1, equations (1.4)–(1.9), pp.2–3, and §7, pp.14–15, states a uniform
exclusion for a specified analytic deformation. This interface is used
at paper level; its arithmetic proof has not been independently audited
and has no new Lean certification here.

Use an even nonnegative fixed $f\in C_c^\infty(\mathbb R)$ with
$\int f=1$ and support in $[-\sigma/2,\sigma/2]$, where $0<\sigma<1$.
Write $K=\widehat f$, $g=f*f$, and

$$
a=g(0),\qquad B_0=\int_0^\sigma xg(x)\,dx,\qquad
\mathscr R=a+2B_0\le\frac75.
$$

Choosing the earlier density as $\eta=\sqrt f$ identifies its kernel
with this $K$. The finite-multiset accounting above applies to the
paper's centered dyadic multiset

$$
Z_T=\left\{\frac{i(\rho-\tfrac12)\log T}{2\pi}:
T<\operatorname{Im}\rho\le2T\right\},
$$

retaining multiplicities. Its original simple-critical Gram matrix gives
the same clipped correction $\Delta_K$; the zero eigenvalues and its
original dimension remain part of that correction.

Fix a polynomial-length exponent $\nu>0$ with $\sigma+\nu<1$, and put

$$
Y_T(s)=\sum_{n\le T^\nu}c_n(T)n^{-s},\qquad
\|Y_T\|_D^2=\sum_{n\le T^\nu}\frac{|c_n(T)|^2}{n}.
$$

The coefficients may be arbitrary complex numbers depending on $T$.
The theorem uses the entire Gaussian multiplier from equation (1.6),
with center $s_*=1/2+3iT/2$ and width $T/\log T$. Let $G_T,D_T$ be its
reflected finite operators and $N_T$ the original total zero count. Set

$$
Q(W)=4\operatorname{tr}W-\operatorname{tr}(W^2),\qquad
W_t=G_T-tD_T,\qquad t\ge0.
$$

Equation (1.7) states, without an assumption on the zeros' real parts,

$$
\frac{\operatorname{tr}((G_T-2I)D_T)}{N_T}
\le\left(-\frac{427}{3125}+\varepsilon_T\right)\|Y_T\|_D^2,
\qquad\varepsilon_T\longrightarrow0.
$$

The fixed profile, support and length exponents determine
$\varepsilon_T$; it is uniform over the coefficient vector. Equations
(1.9) and (2.8) retain the original Gram correction and count budget,
and give

$$
Q(W_t)-Q(G_T)
=2t\operatorname{tr}((G_T-2I)D_T)-t^2\operatorname{tr}(D_T^2)
\le0
$$

for all sufficiently large $T$, all such polynomials and every $t\ge0$,
including choices of $t$ depending on $T$. Thus this entire class of
Gaussian-localized short multipliers cannot increase that compensated
quadratic counting lower bound. Its negative variation supplies no
positive margin for the selected Robin source.

The Gaussian localization and fixed positive gap $1-\sigma-\nu$ are
part of the theorem. Section 7.3 leaves longer polynomials, different
localizations or energies, and bounded nonlinear trace witnesses outside
this exclusion. In particular it supplies no estimate for the fourth
trace discussed above. No map from this deformation to the original
complete $I_\psi(A)$ or the required prime-side energies of the FIB
negative tests has been established. Those signed comparisons remain
unproved.


## Sharp finite blocks and the same-configuration packing bound

The [FIB-ATOM foundational volume, §§15–18](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)
gives paper derivations of the local divisor-event Gram, the complete three-point energy envelope,
fractional packing of overlapping principal blocks, and a quantitative approximation condition
for the actual difference-kernel realization.

The underlying trace methods are classical. Wolkowicz–Styan,
*Bounds for eigenvalues using traces*, Linear Algebra and its Applications 29 (1980), 471–506,
give the mean/variance eigenvalue bounds; see the [author-hosted paper](https://www.math.uwaterloo.ca/~hwolkowi/henry/reports/PAPER31.pdf).
For a three-dimensional unit-diagonal PSD Gram, their upper-bound form
$\lambda_{\max}\le m+s\sqrt{n-1}$ specializes to
$\lambda_{\max}\le1+2\sqrt{e/3}$, with $e=\sum_{i<j}|G_{ij}|^2$.
Applying the displayed clipped function, and retaining the original dimension, yields the sharp envelope
$$
\operatorname{tr}\Psi(G)\ge
F(e)=2e-\left(2\sqrt{e/3}-1\right)_+^2,\qquad 0\le e\le3.
$$
Real equicorrelation matrices attain every value on this lower boundary.
The volume proves the formula directly from the two trace identities.

Hansen–Pedersen, *Jensen's trace inequality in several variables*,
International Journal of Mathematics 14 (2003), 667–681,
[Theorem 2, equation (1)](https://arxiv.org/html/math/0303060v1), supplies the relevant convex trace compression.
For a coordinate projection $P_S$, use the unital pair $P_S,I-P_S$ with matrices $G,I$.
The complement contributes $\Psi(1)=0$, giving
$\operatorname{tr}\Psi(G[S])\le\operatorname{tr}(P_S\Psi(G))$.
This application retains $\Psi(0)=1$; a contraction version requiring $f(0)\le0$ would have the wrong hypothesis.
Consequently, nonnegative weights satisfying $\sum_{\alpha:i\in S_\alpha}w_\alpha\le1$ give
$$
\operatorname{tr}\Psi(G)\ge
\sum_\alpha w_\alpha\operatorname{tr}\Psi(G[S_\alpha])
\ge\sum_\alpha w_\alpha F(e_\alpha^*)
$$
when the actual three-point energies satisfy $e(G[S_\alpha])\ge e_\alpha^*$.
Maximizing the last expression is a finite linear program for one fixed Gram.
These are explicit finite specializations of the cited trace methods.

For Wang's already displayed $e(H)$, one has $e(H)<1/2$, hence $F(e(H))=2e(H)$.
The larger linear window $e\le3/4$ therefore leaves that numerical input unchanged.
Any improved asymptotic zero proportion requires a stronger lower bound for the normalized packing value
of the same actual simple-critical configuration, together with its matching energy estimate.

The modular source also imposes a realization condition. Its $q=3$ Gram is rank two,
whereas every Gram on distinct real points from a nonzero absolutely continuous Fourier density is strictly positive definite.
The volume proves a positive approximation cost when a density lower bound and a distinguished-pair separation are fixed,
and proves that the cost can tend to zero when the separation is removed.
The arithmetic local model has not supplied those actual-zero approximation certificates.

Finally, the cyclic pair Gram of the two triplet wheels is identical at every modulus.
All powers of that same matrix remain identical even where arithmetic three-point correlations differ.
A higher spectral moment therefore requires a proved identification with the intended arithmetic observable.
The separate cubic-theta comparison is recorded in
[the fixed-half-plane source note](../Analytic/openai2026quasirh.md).


## 本仓对原三点证书的解析推论

This derivation retains Wang's original kernel and supplies an explicit lower bound for the normalized packing value discussed above. Convex compression, consecutive-point averaging, and shifted-block counting are existing methods; the calculation below specializes them to Wang's displayed three-point certificate. It is not a claim of a new general method or of the best current zero proportion. The stronger multi-point consumer in §19 of the [main volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) uses a different profile and matching certificate.

The imported analytic and kernel premises are Proposition 2.1 and Lemmas 3.2 and 4.1 of [Biao Wang, arXiv:2609.24167v1](https://arxiv.org/html/2609.24167v1). Consecutive-point, frame, and shifted-block methods also appear in the [ainta manuscript](https://github.com/ainta/zeta-simple-zeros/blob/main/paper/riemann.tex) and the [later refined deduction](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97/docs/refined-deduction.md). These sources supply the provenance of the averaging mechanism; the closed-form envelope and arithmetic evaluation below specialize it to Wang's displayed certificate.

### 1. Source premises and notation

Put
$$
 a=(\sqrt5-2)^2=9-4\sqrt5,\qquad b=2\pi^2,\qquad
 e(h)=\frac{a}{(1+bh^2)^2}.
$$
Wang's real even probability density and Fourier kernel are
$$
 f_0(t)=\frac{\cos(\sqrt2t)}{\sqrt2\sin(1/\sqrt2)}
            \mathbf1_{[-1/2,1/2]}(t),\qquad K_0=\widehat f_0.
$$
Its three-point certificate states, for $u,v\ge0$,
$$
 K_0(u)^2+K_0(v)^2+K_0(u+v)^2\ge e(u+v).       \tag{1}
$$
Define $D(G)=\operatorname{tr}\Psi(G)$, with
$$
 \Psi(t)=(t-1)^2\quad(0\le t\le2),\qquad
 \Psi(t)=2t-3\quad(t\ge2).
$$
For a unit-diagonal $3\times3$ Gram block of off-diagonal energy at least $e_*\le a<1/2$, the finite spectral inequality gives $D(G)\ge2e_*$.

The smooth densities $f_\delta=\eta_\delta^2$ supplied by Wang, with $\eta_\delta$ real and even, satisfy
$$
 f_\delta\ge0,\quad\int f_\delta=1,\quad
 \eta_\delta\in C^\infty_c(-1/2,1/2),\quad
 r_\delta=\|f_\delta-f_0\|_1\longrightarrow0.
$$
For their Fourier kernels $K_\delta$,
$$
 |K_\delta-K_0|\le r_\delta,\qquad |K_\delta|,|K_0|\le1
 \quad\hbox{on }\mathbb R.                     \tag{2}
$$

### 2. The exact lower convex envelope

Let
$$
 s_*=\sqrt{\frac{\sqrt{17}-3}{2}},\qquad
 h_*=\frac{s_*}{\sqrt b}
     =\sqrt{\frac{\sqrt{17}-3}{4\pi^2}}
     =0.168667121383325\ldots .
$$
The greatest convex minorant of $e$ on $[0,\infty)$ is
$$
 g(h)=
 \begin{cases}
 a+e'(h_*)h,&0\le h\le h_*,\\
 e(h),&h\ge h_*.
 \end{cases}                                  \tag{3}
$$
It is nonnegative and decreasing.

To prove this, scale $t=\sqrt b\,h$ and set $f(t)=(1+t^2)^{-2}$. Then
$$
 f''(t)=\frac{4(5t^2-1)}{(1+t^2)^4}.
$$
The tangent condition $f(s)-1=sf'(s)$, after division by the nonzero factor $s^2$, becomes
$$
 s^4+3s^2-2=0,
$$
whose positive solution is $s_*$. Define
$$
 M(t)=\frac{1-f(t)}t
     =\frac{t(2+t^2)}{(1+t^2)^2}.
$$
For $t>0$,
$$
 M'(t)=\frac{2-3t^2-t^4}{(1+t^2)^3},
$$
so $M$ has its unique maximum at $s_*$. Hence the line through $(0,1)$ tangent to $f$ at $s_*$ lies below $f$ everywhere. The line joins $f$ with matching first derivative in a region where $f''\ge0$, proving convexity. Any other convex minorant is bounded above, on $[0,s_*]$, by the chord connecting its endpoint values, which in turn is bounded above by this line; on $[s_*,\infty)$, it is bounded above by $f$. This proves maximality.

### 3. Exact finite span estimate

Let $x_1<\cdots<x_n$, $n\ge3$, lie in an interval of length at most $L$, and let $G_0=(K_0(x_i-x_j))_{i,j}$. Put $M=n-2$. For the $M$ consecutive triple spans
$$
 h_i=x_{i+2}-x_i,
$$
one has
$$
 \sum_{i=1}^M h_i
 =(x_n-x_1)+(x_{n-1}-x_2)\le2L.                \tag{4}
$$
Each point belongs to at most three such blocks. Convex compression, applied with weight $1/3$, together with (1), therefore gives
$$
 D(G_0)\ge\frac23\sum_{i=1}^M e(h_i)
         \ge\frac23M\,g\!\left(\frac1M\sum_i h_i\right)
         \ge\boxed{\frac23M\,g\!\left(\frac{2L}{M}\right)}. \tag{5}
$$
The middle step is Jensen's inequality for $g$; the last uses that $g$ is decreasing. For $n\le2$ retain the trivial bound $D\ge0$; do not evaluate the displayed quotient.

The same argument applies to the smooth kernel with a uniform error. Equation (2) implies that the sum of the three squared off-diagonal entries changes by at most $6r_\delta$. Thus each smooth triple has
$$
 D(G_\delta[\{i,i+1,i+2\}])
 \ge 2(e(h_i)-6r_\delta)_+
 \ge 2e(h_i)-12r_\delta.
$$
Consequently,
$$
 \boxed{\displaystyle
 D(G_\delta)\ge
 \frac23M\,g\!\left(\frac{2L}{M}\right)-4Mr_\delta.} \tag{6}
$$
This estimate is uniform over all real point configurations, including arbitrarily large triple spans. It is therefore legitimate to fix $\delta$, take the zero-height limit, and only afterwards send $\delta\to0$.

### 4. The actual zero-counting consumer

Write
$$
 C_0=\frac32-\frac1{\sqrt2}\cot\frac1{\sqrt2}
     =0.672500703679411645734379790803\ldots .
$$
For the actual multiset
$$
 \mathcal Z_T=
 \left\{ i(\rho-\tfrac12)\frac{\log T}{2\pi}:
                   0<\Im\rho\le T\right\},
$$
let $N=N(T)$, $n=N^s_0(T)$, and $d=N_d(T)$. Its simple real points occupy an interval of length at most
$$
 L_T=\frac{T\log T}{2\pi}=N+o(N).
$$
For each fixed smooth source kernel the imported inequalities are
$$
 n\ge2N-\mathcal E_\delta+D(G_\delta),\qquad
 d\ge\frac32N-\frac12\mathcal E_\delta+\frac12D(G_\delta),
$$
and
$$
 \limsup_{T\to\infty}\mathcal E_\delta/N\le C_\delta,\qquad
 C_\delta\longrightarrow2-C_0.
$$
The squared energy $\mathcal E_\delta$ is the source's full complex-multiset energy. It is not the Frobenius energy of the simple-real-point Gram.

The baseline follows by discarding $D\ge0$; it ensures $\liminf n/N\ge C_0>0$. Along any subsequence with $n/N\to r>0$, $M/N\to r$ and
$$
 \frac{2L_T}{M}\longrightarrow\frac2r\ge2>h_*.
$$
Therefore (3) and (6), after $T\to\infty$, then $\delta\to0$, give the pressure
$$
 \Phi(r)=\frac{2a}{3}\frac{r^5}{(r^2+8\pi^2)^2}. \tag{7}
$$
For $r=\liminf n/N$, the finite counting inequality yields
$$
 r\ge C_0+\Phi(r).                              \tag{8}
$$
There is exactly one $r_*\in(C_0,1)$ satisfying equality. Indeed,
$$
 \Phi'(r)=\frac{2a}{3}
 \frac{r^4(r^2+40\pi^2)}{(r^2+8\pi^2)^3}>0
$$
and $\Phi'(r)\le10a/3<1$, so $r-\Phi(r)$ is strictly increasing. Also $C_0<3/4$, $a<1/16$, and $\Phi(1)<1/24$, which ensure a sign change before one. Thus
$$
 \liminf\frac{N_0^s(T)}{N(T)}\ge r_*,
$$
$$
 r_*=0.6725015140968083192010988474865\ldots,
\qquad
 r_*-C_0=8.104173966734667190566832213\ldots\times10^{-7}. \tag{9}
$$
For the distinct-zero bound, apply its own finite inequality along a subsequence realizing its lower limit. Every accumulation point of $n/N$ is at least $r_*$; monotonicity of $\Phi$ then gives
$$
 \liminf\frac{N_d(T)}{N(T)}
 \ge\frac{1+C_0+\Phi(r_*)}{2}
 =\frac{1+r_*}{2}
 =0.8362507570484041596005494237433\ldots .       \tag{10}
$$
One must not replace this argument by an unsupported finite relation between the distinct count and the actual simple count.

### 5. A strict rational improvement requiring no decimal root

The following elementary bounds are sufficient:
$$
 C_0>\frac{84}{125},\qquad a>\frac1{18},\qquad
 \pi<\frac{22}{7}.
$$
For the first, write $x=1/\sqrt2$,
$$
 C=\cos x,\qquad S=\frac{\sin x}{x}.
$$
Alternating-series estimates give
$$
 C\le\frac{73}{96},\qquad
 S\ge1-\frac1{12}+\frac1{480}-\frac1{40320},
$$
and
$$
 \frac{207}{250}
 \left(1-\frac1{12}+\frac1{480}-\frac1{40320}\right)
 -\frac{73}{96}=\frac{967}{3360000}>0.
$$
Thus $C/S<207/250$ and $C_0=3/2-C/S>84/125$. For $a>1/18$, use $\sqrt5<161/72$, since $161^2-5\cdot72^2=1$.

Since $\Phi$ is increasing in $r$ and $a$, and decreasing in $\pi$,
$$
 \Phi(C_0)>
 \frac{(84/125)^5}
      {27((84/125)^2+8(22/7)^2)^2}
 =\frac{1452729852}{1807717071735125}
 >\frac8{10^7}.                               \tag{11}
$$
The exact difference in the last inequality is
$$
 \frac{65561946119}{18077170717351250000}>0.
$$
In particular, under the source premises,
$$
 \liminf N_0^s(T)/N(T)>C_0+8\cdot10^{-7}.
$$
This is an explicit improvement of Wang v1's particular fixed-cell consumer, not a new best bound after the later multi-point developments.

### 6. General span-envelope statement

For one fixed Gram kernel, fix integers $m\ge2$ and $n\ge m$. Suppose every consecutive $m$-point block of span $h$ has $D\ge J_m(h)$, where $J_m\ge0$ is decreasing. If $\varphi_m$ is any nonnegative, decreasing, convex minorant of $J_m$, then
$$
 D(G)\ge\frac{n-m+1}{m}
 \varphi_m\!\left(\frac{(m-1)L}{n-m+1}\right).   \tag{12}
$$
The proof is the same: weight each consecutive block by $1/m$, and note that the sum of their spans is at most $(m-1)L$. For $n<m$, retain $D\ge0$ without evaluating the displayed quotient.

When the same analytic source has baseline $C$, this yields the pressure
$$
 P_m(r)=\frac rm\varphi_m((m-1)/r),\qquad P_m(0)=0,
$$
and $r\ge C+P_m(r)$, subject to the same approximation requirements. Nonnegativity and monotonic decrease of $\varphi_m$ imply that $P_m$ is nondecreasing.

For the following comparison only, take $\varphi_m$ to be the greatest convex minorant of $J_m$. It weakly dominates every standard fixed-cell pigeonhole guarantee using that same local certificate. For each $H>0$, the function
$$
 h\longmapsto J_m(H)(1-h/H)_+
$$
is a decreasing convex minorant of $J_m(h)$. Hence
$$
 \varphi_m(h)\ge\sup_{H>0}J_m(H)(1-h/H)_+.
$$
After multiplication by $r/m$ and substitution $h=(m-1)/r$, this is precisely the comparison with
$$
 \frac{J_m(H)}m\left(r-\frac{m-1}{H}\right)_+.
$$
This comparison concerns the standard guarantee obtained from the number of cells. It does not assert dominance over a cell argument supplied with additional information about the actual distribution of points.

All these averaging identities are structural tools. Better current multi-point certificates, coupling their pressure correctly, and verifying the actual analytic interface are separate tasks. None of these proportion estimates proves RH.

## The independently proved elementary consumer in Section 21

[Section 21 of the finite-structure volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) proves, for arbitrary real $a,u,v$,
$$
F_a(u)^2+F_a(v)^2+F_a(u+v)^2\ge\frac34,
\qquad F_a(t)=at\sin(\pi t)-\cos(\pi t).
$$
Its two-dimensional circle-vector proof is independent of the historical v1 estimate $(\sqrt5-2)^2$. The constant $3/4$ is sharp when the parameter $a$ is allowed to vary, as the example $a=0$, $u=v=2/3$ shows. No sharpness assertion is made for the fixed Montgomery–Taylor parameter. The proof also supplies the stated all-point and nonnegative-weight extensions.

The connection to the original kernel is the directly integrated identity
$$
(1-2\pi^2t^2)K_0(t)
=\cos(\pi t)-\sqrt2\pi\cot(1/\sqrt2)\,t\sin(\pi t).
$$
Thus, for $u,v\ge0$ and $h=u+v$,
$$
K_0(u)^2+K_0(v)^2+K_0(u+v)^2
\ge\frac{3}{4\max\{1,(2\pi^2h^2-1)^2\}}.
$$
The identity holds at its removable singularities by continuity. This is a bound for the same specified kernel; an arbitrary probability-density Fourier kernel need not satisfy it.

The finite counting step is reproved in Section 21.6 using the self-adjoint reflected operator, its positive-inertia budget, and the scalar threshold function $\Phi(t)=2t-1+\Psi(t)$ with $\Phi(0)=0$. An additional primary formulation is [Knausgård, arXiv:2610.08965v1, Lemma 2.1 and equation (5.1)](https://arxiv.org/html/2610.08965v1), with threshold $c=2$. The proof keeps the original simple-real Gram dimension and obtains both finite counting inequalities displayed earlier in this note.

The actual energy estimate comes directly from [Lamzouri v2, Lemma 3.2 and equations (3.3)–(3.4)](https://arxiv.org/html/2609.02882v2). It uses $f_\varepsilon=\psi_\varepsilon^2f_0/A_\varepsilon=\eta_\varepsilon^2$, with $\eta_\varepsilon\in C_c^\infty((-1/2,1/2))$, $\int f_\varepsilon=1$, and convergence to $f_0$ in $L^1\cap L^2$. The two fixed test functions $f_\varepsilon*f_\varepsilon$ and its second derivative give the unweighted complex-square energy after cancellation of the pair-correlation weight. For each fixed smoothing parameter, the energy divided by $N(T)$ tends to $C_\varepsilon$, and $C_\varepsilon\to2-C_0$ as the smoothing is removed. These are the explicit analytic premises of the new consumer. Wang v1's status is historical context for the finite estimate, rather than an additional unresolved premise of this proof.

Let $r$ be any accumulation point of the simple-critical ratio $N_0^s(T)/N(T)$. Section 21 combines fixed-size consecutive windows, their exact point-use cost, and the order $T\to\infty$ followed by smoothing removal to obtain
$$
r\ge C_0+\frac{r^5}{2(8\pi^2-r^2)^2}.
$$
Its unique threshold $r_{\rm geom}$ satisfies
$$
r_{\rm geom}=0.672511864084414704\ldots,
\qquad r_{\rm geom}>C_0+\frac{11}{10^6}.
$$
Consequently the paper-level consumer gives a $67.2511864\ldots\%$ simple-critical lower bound under the matching analytic input. Its distinct-zero consequence is $(1+r_{\rm geom})/2$, using a subsequence for the distinct count itself. The strict gain uses rational inequalities, independently of the displayed decimal root. The finite proof uses no local interval enumeration, and no new Lean verification is claimed here.

The [updated comparison in the trmdy note](trmdy2026simplezeros.md) records both the earlier nine-point conditional consumers and Knausgård's stronger October preprint, with its fixed source revision and theorem-specific `native_decide` assumptions. The elementary Section 21 number is lower than those simple-critical figures. Its proof that three points are optimal concerns only the specified uniform-numerator, support-line, sliding-window family. It supplies no global priority result, no upper limit on other geometric methods, and no control of every zero required for RH.
