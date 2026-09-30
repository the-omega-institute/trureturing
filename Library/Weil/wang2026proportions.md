---
bibkey: wang2026proportions
authors: Biao Wang
year: 2026
title: Proportions of the non-trivial zeros of the Riemann zeta function
doi: null
url: https://arxiv.org/abs/2609.24167v1
claim: A nonnegative spectral correction to the finite-multiset inequality, bounded using three-point kernel overlaps, slightly improves the unconditional lower proportions of simple critical zeros and distinct zeros. It supplies neither full Weil positivity nor a FIB-to-zeta identification.
strata_touched: []
license: citation-only
triage: anchor
---

# The September spectral correction to the zero-proportion method

This note records the incremental interface beyond the existing [golden-observer research account](../../docs/develop/theory/GOLDEN_OBSERVER_RH_ROUTE.md). The inspected primary versions are [Alpöge–Furman v2](https://arxiv.org/abs/2608.13637v2), submitted 19 August 2026; [Lamzouri v2](https://arxiv.org/abs/2609.02882v2), submitted 8 September; and [Wang v1](https://arxiv.org/abs/2609.24167v1), submitted 21 September. These are the version dates in their arXiv histories checked on 1 October 2026; their internal PDF dates differ. This is a review of statements and selected proof interfaces, without a full independent proof audit or a new Lean build.

## The finite quantity added by Wang

Let $Z$ be a nonempty finite multiset invariant under complex conjugation, including multiplicities. For real even $\eta\in L^2(\mathbb R)$ supported in $(-\lambda,\lambda)$, with $\lambda>0$ and $\int\eta^2=1$, put $K=\widehat{\eta^2}$ using Fourier phase $e^{-2\pi i\xi u}$. Let $x_1,\ldots,x_n$ be exactly the simple real elements of $Z$, and define

$$
G_K=(K(x_j-x_\ell))_{j,\ell=1}^n,\qquad
\Psi(t)=\begin{cases}(t-1)^2,&0\le t\le2,\\2t-3,&t\ge2,\end{cases}
\qquad \Delta_K(Z)=\operatorname{tr}\Psi(G_K).
$$

Here $G_K$ is positive semidefinite and $\Delta_K\ge0$, with $\Delta_K=0$ when $n=0$. With $N=|Z|$ counting multiplicity and $D$ counting distinct elements, Wang's Proposition 2.1 states

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

Theorem 1.1 therefore states the unconditional lower limiting proportions

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
