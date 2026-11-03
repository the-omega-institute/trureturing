---
slug: wang-wang-tang-ren-2018-bernoulli-noise-walk-gaussian-limit
bibkey: wangwangtangren2018bernoulliwalk
doi: 10.1155/2018/2507265
url: https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.result
---

# Every localized quantum Bernoulli noise walk has the standard Gaussian limit

## Problem

C. Wang, C. Wang, Y. Tang and S. Ren, *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*, Advances in Mathematical Physics 2018, Article 2507265, DOI 10.1155/2018/2507265, Section 6, “Conclusion Remarks,” published PDF p. 8:

> It is still unclear whether or not the walk has a limit probability distribution for a general localized initial state.

> Thus we conjecture that, for a general localized initial state, the QBN-based walk might still have the same limit probability distribution as the classical random walk.

The source's coin space $h$ has orthonormal basis $\{Z_\sigma:\sigma\in\Gamma\}$, where $\Gamma$ consists of the finite subsets of $\mathbb N$ (Section 2, Eq. (7), p. 2). Its annihilation and creation operators remove or add a coordinate when permitted, and otherwise give zero (Lemmas 1–2, Eqs. (8)–(9)). Lemma 5 and Definition 6, p. 3, specify

$$
R_k=\tfrac12(\partial_k^*+\partial_k+I),\qquad
L_k=\tfrac12(\partial_k^*+\partial_k-I),\qquad
\Phi_{n+1}(x)=R_n\Phi_n(x-1)+L_n\Phi_n(x+1).
$$

A localized initial state is $\Phi_0(0)=\varphi$, $\Phi_0(x)=0$ for $x\ne0$, with $\|\varphi\|=1$ (Eq. (53), p. 6); the position probabilities are $\Pr(X_n=x)=\|\Phi_n(x)\|^2$ (Section 3, p. 3).

Issue [#22700](https://github.com/the-omega-institute/trureturing/issues/22700) fixes the reading: for every unit vector $\varphi\in h$, the law of $X_n/\sqrt n$ converges weakly to $N(0,1)$. This is proved in the coefficient-space model below. The source definitions and their locators are also described in [the literature note](../Library/Asymptotics/wangwangtangren2018bernoulliwalk.md).

## Motivation

The question asks whether the classical diffusive Gaussian limit persists throughout the infinite-dimensional coin space. Theorem 21 of Wang, Wang, Tang and Ren (2018, DOI 10.1155/2018/2507265), p. 8, treats only $\varphi=\alpha Z_\emptyset+\beta Z_{\{0\}}$ with $|\alpha|^2+|\beta|^2=1$. Its measures are the spectral laws of normalized sums of creation-plus-annihilation observables; Eq. (67), p. 7, identifies them with scaled position laws for those states. Extending the walk limit to every unit vector removes the restriction on the localized coin state and addresses the question in the final remarks.

## Gap

The bounded literature check recorded in #22700 before any Lean reports:

- Crossref listed one citing work.
- The search contributor, identified there as the ChatGPT Pro deep-track search author, reported that Wang–Ren–Tang, Entropy 22(4), 486 (2020), treats canonical basis vectors; Wang–Wang, Entropy 22(5), 504 (2020), imposes an additional decay condition; Li–Wang–Fu (2021) treats the two-term states above; and arXiv:2006.08090 assumes regularity. These theorem-level readings are contributor-reported.
- That contributor also reported searches of Zenodo, ResearchGate, SSRN and GitHub without finding a settlement. The preregistration author separately reported an arXiv title search returning 2006.08090, 2211.07948, 2610.12949 and 2610.14467, with no general-state limit theorem stated in their titles or abstracts.
- The preregistration records no matching repository issue or dossier and distinguishes the existing finite-hypercube QBN results.

`not-found-in-searched-scope`. The 2018 conjecture itself is present in the published source quoted above. No arXiv version is identified by the preregistration or Library note; the front matter therefore uses the publisher URL.

## Route

Write $H=\ell^2(\Gamma;\mathbb C)$ for `ObserverHilbertSpace (Finset ℕ)` and $T_k\varphi(\sigma)=\varphi(\sigma\mathbin\triangle\{k\})$. The definitions `annihilation`, `creation`, `R`, `L` and `walk` implement the operators and recursion above. The definition `walkLaw` is the finite measure

$$
\mu_n^\varphi=\sum_{x=-n}^{n}\|\operatorname{walk}(\varphi,n,x)\|^2\,
\delta_{x/\sqrt n}.
$$

1. **Coordinate operators.** For every $k\in\mathbb N$, `operators_eq_flip` identifies creation plus annihilation with $T_k$. For every $k$ and every $\varphi\in H$, `right_apply` and `left_apply` give $R_k\varphi=(T_k\varphi+\varphi)/2$ and $L_k\varphi=(T_k\varphi-\varphi)/2$. For every $k$, `projections` proves $R_k^2=R_k$, $L_k^2=-L_k$ and $R_kL_k=L_kR_k=0$; `flip_commute` proves commutation for all coordinate pairs and all vectors.
2. **Exact position law.** For $\sigma\subseteq\{0,\ldots,n-1\}$, let $B_{n,\sigma}$ be `branch n σ`, the ordered product of $-L_k$ when $k\in\sigma$ and $R_k$ otherwise, over $k<n$. If both $\sigma$ and $\tau$ are subsets of this prefix and $\sigma\ne\tau$, `branch_orthogonal` gives $\langle B_{n,\sigma}\varphi,B_{n,\tau}\psi\rangle=0$ for arbitrary $\varphi,\psi\in H$. For every $n$ and $\varphi$, `branch_resolution` gives $\sum_\sigma B_{n,\sigma}\varphi=\varphi$. For every $\varphi$, $n\in\mathbb N$ and $x\in\mathbb Z$, `walk_expansion` expresses the amplitude as $\sum_{\sigma:\,n-2|\sigma|=x}(-1)^{|\sigma|}B_{n,\sigma}\varphi$, where the sum is over subsets of the prefix; `walk_exact_law` gives its squared norm as the sum of $\|B_{n,\sigma}\varphi\|^2$. For every $\varphi$ and $n$, `walk_mass` gives total mass $\|\varphi\|^2$; if $\|\varphi\|=1$, `walkLaw_probability` makes $\mu_n^\varphi$ a probability measure for every $n$.
3. **Characteristic function.** Define $U_0(u)=I$ and $U_{n+1}(u)=(\cos u\,I+i\sin u\,T_n)U_n(u)$, as in `phaseProduct`. For every $\varphi\in H$, $n\in\mathbb N$ and $t\in\mathbb R$, `charFun_formula` gives $\widehat\mu_n^\varphi(t)=\langle\varphi,U_n(t/\sqrt n)\varphi\rangle$. For every $n$, real $u$ and $\varphi\in H$, `phaseProduct_isometry` gives $\|U_n(u)\varphi\|=\|\varphi\|$.
4. **Finite-coordinate limit.** Suppose $m,n\in\mathbb N$, $m\le n$, and $\eta\in H$ satisfies $\eta(\sigma)=0$ whenever $\sigma\not\subseteq\{0,\ldots,m-1\}$. For every real $u$, `finite_tail_factorization` gives
   $$\langle\eta,U_n(u)\eta\rangle=(\cos u)^{n-m}\langle\eta,U_m(u)\eta\rangle.$$
   For every real $t$, `cosine_gaussian_limit` gives $\cos(t/\sqrt n)^n\to e^{-t^2/2}$ by applying Mathlib's characteristic-function central limit estimate to the symmetric measure on $\{-1,1\}$. For every $\eta,m$ with the stated support condition and every real $t$, `finite_matrix_limit` combines this limit with continuity of the fixed product at zero to obtain $\langle\eta,U_n(t/\sqrt n)\eta\rangle\to\|\eta\|^2e^{-t^2/2}$. Normalization of $\eta$ is not required.
5. **Density and weak convergence.** For every $\varphi\in H$ and $\varepsilon>0$, `finite_vectors_dense` supplies a vector $\eta$ with the preceding support condition for some $m$ and $\|\varphi-\eta\|<\varepsilon$. For every $n$, real $u$ and arbitrary $\varphi,\eta\in H$, `matrix_lipschitz` gives
   $$|\langle\varphi,U_n(u)\varphi\rangle-\langle\eta,U_n(u)\eta\rangle|
   \le(\|\varphi\|+\|\eta\|)\|\varphi-\eta\|.$$
   For every unit $\varphi$ and real $t$, `matrix_gaussian_limit` consequently gives the Gaussian limit of the matrix coefficient. For such $\varphi$, `result` applies Mathlib's characteristic-function criterion to the probability measures $\mu_n^\varphi$ and $N(0,1)$ and obtains convergence against each bounded continuous real function.

## Falsifier

The settlement would miss the conjecture if its coin space, operator signs, normalization or scaling differed from the source's. The coefficient map $\varphi\mapsto(\langle Z_\sigma,\varphi\rangle)_\sigma$ identifies the source's orthonormal-basis Hilbert space with $H$. On coefficient vectors, annihilation reads the flipped coefficient only when $k\notin\sigma$, and creation only when $k\in\sigma$; these are precisely the source's basis actions in Eqs. (8)–(9). The recursion retains $L_k=(T_k-I)/2$, including its sign. The weights in `walkLaw` are squared norms of that recursion, and the scaling is $x/\sqrt n$, without centering or a state-dependent variance.

The hypothesis of `result` is exactly $\|\varphi\|=1$, with $\varphi$ otherwise arbitrary in $H$; its test functions are all bounded continuous $f:\mathbb R\to\mathbb R$. There is no finite-support, regularity or decay hypothesis. At $n=0$, Lean's real division convention places the initial mass at zero; the convergence statement concerns $n\to\infty$ and agrees with the source's positive-time scaling.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.lean`.

- **Proof.** It proves `result (φ : ObserverHilbertSpace (Finset ℕ)) (hφ : ‖φ‖ = 1) (f : ℝ →ᵇ ℝ)` with the integral-convergence conclusion stated below.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.lean.json`.

Declaration statements:

- `result`: `sha256:3530f2344d8e4d0c8c9d4a48be7c98697c4b13235053b1842dbcaab257869edf`.

## Triage

Tier 1 conjecture of a 2018 paper, preregistered in issue #22700 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $\varphi\in\ell^2(\Gamma;\mathbb C)$ with $\|\varphi\|=1$ and every bounded continuous $f:\mathbb R\to\mathbb R$,

$$
\int_{\mathbb R} f(y)\,d\mu_n^\varphi(y)
\longrightarrow
\int_{\mathbb R} f(y)\,dN(0,1)(y)
\qquad(n\to\infty),
$$

where $\mu_n^\varphi$ is `walkLaw φ n`, defined from the localized recursion above.

**Computed, not formalized:** exact rational evaluation of the walk recursion for equal-amplitude initial vectors on the subsets of the first few coordinates reproduced the deterministic-then-classical law described in the uniformity obstruction below.

**Argued, not formalized.**

- *Decisive mechanism.* The proof does not require independent outcomes for an arbitrary initial vector. For every finite-coordinate vector $\eta$ supported on subsets of the first $m$ coordinates and every $n\ge m$, `finite_tail_factorization` isolates the classical cosine factor; `finite_matrix_limit` gives its limit for every real frequency. The bound of `matrix_lipschitz`, valid for arbitrary vectors and every $n,u$, lets a fixed vector be approximated before taking the limit. Thus the finite-coordinate cutoff may depend on the initial vector; no common cutoff over all unit vectors is needed.
- *Uniformity has a concrete obstruction.* For each integer $N\ge1$, put $\eta_N=2^{-N/2}\sum_{\sigma\subseteq\{0,\ldots,N-1\}}Z_\sigma$. Orthonormality makes $\eta_N$ a unit vector, and toggling any $k<N$ permutes its summands, so $T_k\eta_N=\eta_N$. The definitions of $R_k,L_k$ therefore give $R_k\eta_N=\eta_N$ and $L_k\eta_N=0$ for $k<N$; induction in the walk recursion puts all mass at $X_N=N$. The single bounded continuous function $f(y)=\max(0,1-|y|)$ has integral zero against this scaled law for every $N\ge1$, whereas its Gaussian integral is positive, since $f\ge1/2$ on $[-1/2,1/2]$ and the Gaussian density is positive there. Consequently convergence for this test function is not uniform over unit initial vectors. This argument concerns a varying family $\eta_N$ and does not contradict the fixed-vector quantifiers of `result`.
- *Effect on the source.* No theorem in Wang, Wang, Tang and Ren (2018, DOI 10.1155/2018/2507265) is stated conditional on the conjecture in the final remarks. The corresponding walk-limit conclusion of Theorem 21 now extends beyond its two-term initial vectors. For the spectral-law interpretation of Eq. (61) and Remark 22, the finite joint projections $B_{n,\sigma}$ have eigenvalue $(n-2|\sigma|)/\sqrt n$ for $n^{-1/2}\sum_{k<n}T_k$ when $n\ge1$: for every $k<n$, `branch_eigen` gives the sign determined by membership in $\sigma$. For each unit vector $\varphi$, `branch_resolution` sums its components over all subsets of the prefix to $\varphi$, and `branch_orthogonal` makes components indexed by distinct such subsets orthogonal. Its spectral weights in a unit vector $\varphi$ are $\|B_{n,\sigma}\varphi\|^2$, which `walk_exact_law` groups by the same displacement. This identifies the spectral law with $\mu_n^\varphi$ and hence gives the same weak Gaussian limit for every unit vector. The spectral-measure identification itself is not a formalized statement of `result`.
- *Neighbouring questions.* Quantitative rates for a fixed vector in terms of its coefficient tails, limits for nonlocalized initial states, and higher-dimensional walks remain open here. Convergence of unbounded moments is not asserted by the bounded-continuous-test-function conclusion. The source's heuristic interpretation in terms of environmental decoherence is not an additional formal conclusion.

## ASSUMED-UNVERIFIED

The bounded literature check in #22700 does not establish exhaustive novelty or priority. Its citing-work count, follow-up theorem readings and searches are attributed reports and were not independently reproduced here; in particular, the Li–Wang–Fu (2021) item has no complete bibliographic identifier in the issue. The original source was independently read from the published PDF, including Section 6 on p. 8; the publisher HTML and direct publisher PDF fetches returned HTTP 403, so the PDF copy was obtained from Semantic Scholar. No arXiv version was available in the supplied source records.

The source's Bernoulli probability space and its orthonormal-basis coefficient equivalence with $H$ are not constructed in this module. The computed finite family, the nonuniformity argument, the spectral-law identification and its extension of the source's quantum central limit interpretation are not formalized by `result`. The neighbouring questions and the physical decoherence interpretation remain outside the settlement's scope.
