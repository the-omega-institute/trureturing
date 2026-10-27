---
slug: wu-wu-2025-unified-imaginarity-monotone-comparison
bibkey: wuwu2025unifiedimaginarity
doi: 10.1088/1572-9494/adbdbd
url: https://arxiv.org/abs/2506.09799v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.result
---

# Comparing the Wu–Wu unified imaginarity monotones in every finite dimension

## Problem

Chuanfa Wu and Zhaoqi Wu, *Two imaginarity monotones induced by unified $(\alpha,\beta)$-relative entropy* (Commun. Theor. Phys. 77, 095101 (2025), DOI 10.1088/1572-9494/adbdbd; arXiv:2506.09799v1), Section 4, Example 1, state:

> We have not found a proof of $M_{\alpha,\beta}^H(\rho)\geq M_{\alpha,\beta}^E(\rho)$ for any $\alpha\in (0,1)$, $\beta\in (0,1]$ and any qubit state $\rho$, however, numerical experiments shows that it might be true, and it seems difficult to find a counterexample. It is also conjectured that $M_{\alpha,\beta}^H(\rho)\geq M_{\alpha,\beta}^E(\rho)$ for any $\alpha\in (0,1)$, $\beta\in (0,1]$ and any quantum state $\rho$.

This quotation is from lines 573–579 of the downloaded v1 TeX, `20250301WuCF-imaginarity_monotone_R2.tex` (md5 `eb104c03d3638b12044677758c200bae`).

Fix the coordinate basis and let $\bar\rho$ mean entrywise complex conjugation, denoted $\rho^*$ in the paper. For density matrices, write

$D_{\alpha,\beta}(\rho\Vert\sigma)=\big[(\operatorname{Re}\operatorname{tr}(\rho^\alpha\sigma^{1-\alpha}))^\beta-1\big]/\big[(\alpha-1)\beta\big]$,

$M^H_{\alpha,\beta}(\rho)=D_{\alpha,\beta}(\rho\Vert\bar\rho)$, and

$M^E_{\alpha,\beta}(\rho)=\inf_{\sigma\in\mathcal F}D_{\alpha,\beta}(\rho\Vert\sigma)$,

where $\mathcal F$ consists of positive semidefinite matrices of trace one with real entries. Matrix powers are spectral powers from continuous functional calculus. These are the module's definitions; the source's Eqs. (7), (13) and (20) use the trace without an explicit real part, and Eq. (20) uses a minimum. The corresponding source definitions and locators are in [the literature note](../Library/Divergence/wuwu2025unifiedimaginarity.md).

Issue [#20971](https://github.com/the-omega-institute/trureturing/issues/20971) fixes the formal reading: for every natural $d\ge1$, every density matrix $\rho\in M_d(\mathbb C)$, every $0<\alpha<1$ and every $0<\beta\le1$, $M^E_{\alpha,\beta}(\rho)\le M^H_{\alpha,\beta}(\rho)$. Singular states are included. This infimum comparison is proved.

## Motivation

The paper constructs two ways to quantify imaginarity: comparison with the conjugate state and optimization over real states. The former gives a directly specified divergence; the latter requires an optimization. A universal comparison determines which quantity bounds the other without solving that optimization separately for every input or dimension. The conjecture asks for all states, beyond the special qubit family treated analytically in Remark 3 and the numerical illustrations in Example 1.

## Gap

The bounded literature check recorded in #20971 reports:

- The v1 source retains the conjecture. Its text and definitions are directly verified above.
- OpenAlex and Semantic Scholar supplied 14 distinct citing works; eleven full texts were read without finding a settlement. Three remained unread, including Tong–Wu–Wu, *Quantifying imaginarity via quantum $\alpha$–$z$ Jensen-Tsallis divergence* (Laser Physics, 2026), DOI 10.1088/1555-6611/ae95f1. The issue records an abstract reading concerning a different divergence.
- The related-paper searches covered Xu, arXiv:2311.12547; Chen–Lei, arXiv:2404.00637; and Liu et al., arXiv:2510.25313. The issue also records negative MathDB, formal-conjectures and repository searches.

`not-found-in-searched-scope`. The citation census and related-paper searches are reported evidence from the preregistration, not an exhaustive novelty claim.

## Route

All matrices below are complex $d\times d$ matrices for a natural $d$. A density matrix means `IsDensity`: positive semidefinite with complex trace equal to one. The helper lemmas are private declarations in the canonical module.

1. **A real competitor.** For any density matrix $\rho$, `conjugate_state` shows that $\bar\rho$ is a density matrix, and `real_competitor` shows that $\tau=(\rho+\bar\rho)/2$ is a density matrix fixed by conjugation. These lemmas have no parameter restriction or invertibility hypothesis.
2. **Overlap bounds.** `overlap_nonneg` states $0\le\operatorname{Re}\operatorname{tr}(\rho^\alpha\sigma^{1-\alpha})$ for arbitrary matrices $\rho,\sigma$ and every real $\alpha$, using the positive semidefinite powers supplied by the total CFC definition. For density matrices $\rho,\sigma$ and $0<\alpha<1$, `overlap_le_one` bounds this overlap above by one. Its spectral proof expresses the trace as an eigenvalue bilinear form with doubly stochastic squared-unitary-entry weights; weighted arithmetic–geometric mean and the trace-one identities give the upper bound. Consequently, for density matrices $\rho,\sigma$, $0<\alpha<1$ and $0<\beta\le1$, `divergence_nonneg` gives $D_{\alpha,\beta}(\rho\Vert\sigma)\ge0$.
3. **Operator concavity at the midpoint.** For a density matrix $\rho$ and $0<\alpha<1$, set $q=\operatorname{Re}\operatorname{tr}(\rho^\alpha\bar\rho^{1-\alpha})$ and $r=\operatorname{Re}\operatorname{tr}(\rho^\alpha\tau^{1-\alpha})$. The lemma `midpoint_overlap` gives $(1+q)/2\le r$. It applies `CFC.concaveOn_rpow` with exponent $1-\alpha\in(0,1)$ to the two positive semidefinite states, then takes the real trace against $\rho^\alpha$. The identity $\rho^\alpha\rho^{1-\alpha}=\rho$ uses two strictly positive exponents and permits zero eigenvalues.
4. **The scalar step and half-factor.** For real $q,r$ with $q\ge0$, $(1+q)/2\le r$ and $0<\beta\le1$, `scalar_midpoint` gives $(1+q^\beta)/2\le r^\beta$ by concavity and monotonicity of the real power. For a density matrix $\rho$, $0<\alpha<1$ and $0<\beta\le1$, `competitor_half` therefore gives $D_{\alpha,\beta}(\rho\Vert\tau)\le M^H_{\alpha,\beta}(\rho)/2$; division reverses the overlap inequality because $(\alpha-1)\beta<0$.
5. **A valid infimum comparison.** For a density matrix $\rho$, $0<\alpha<1$ and $0<\beta\le1$, `values_bddBelow` supplies the lower bound zero for the set defining $M^E$. The real state $\tau$ supplies an element of that set. Under exactly these hypotheses, `inf_le_competitor` applies `csInf_le` to obtain $M^E\le D(\rho\Vert\tau)$. In `result`, for $d\ge1$ and these state and parameter hypotheses, `divergence_nonneg` applied to $\rho,\bar\rho$ also gives $M^H\ge0$, completing $M^E\le D(\rho\Vert\tau)\le M^H/2\le M^H$.

## Falsifier

The proof would not settle the registered reading if conjugation, matrix powers, the free-state set or the real infimum represented different quantities from those specified in the issue.

- `entrywiseConj` conjugates each entry; it is not the adjoint. On Hermitian matrices it equals the transpose.
- `unifiedDivergence` uses CFC matrix powers, not entrywise powers. On states these are the spectral powers in the paper, including at zero eigenvalues. For Hermitian positive semidefinite factors $A,B$, $\overline{\operatorname{tr}(AB)}=\operatorname{tr}(BA)=\operatorname{tr}(AB)$, so taking the real part preserves the overlap. This identity is an explanatory bridge, not an additional assertion of `result`.
- `imaginarityE` uses `sInf` over real density matrices. The boundedness and the explicit real competitor in the route prevent an unsupported use of the conditionally complete real infimum. The module does not assert attainment of that infimum; the compactness argument relating it to the source's minimum is separated below.
- The theorem covers $d=1$, rank-deficient states and $\beta=1$. It excludes $d=0$, $\alpha=0,1$ and $\beta=0$; the source's separately defined limiting entropies are not included.

## Evidence

The canonical source is `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.lean` (235 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.lean.json`, statement `sha256:66006d944f4c2c4770177c85806e06a52f66ca64ff7a14f442b68c568cfecc3a`.

Declaration statements:

- `result`: `sha256:355957495bba9ccbcbe23055c30e24b2dc7112a6a72b888789f1c41195fb3285`;
- `claim`: `sha256:49b27ef51345873a6536f572199ff1fff403e35a33c1eaaac5c44dc12b78c55c`.

## Triage

Tier 1 explicit conjecture of a 2025 paper, preregistered in issue #20971 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $d\ge1$, every positive semidefinite complex $d\times d$ matrix $\rho$ of trace one, every real $0<\alpha<1$ and every real $0<\beta\le1$, the infimum of $D_{\alpha,\beta}(\rho\Vert\sigma)$ over real density matrices $\sigma$ is at most $D_{\alpha,\beta}(\rho\Vert\bar\rho)$. This includes singular density matrices.

**Argued, not formalized.**

- *Decisive mechanism and stronger bound.* For a density matrix $\rho$, $0<\alpha<1$ and $0<\beta\le1$, the private lemmas `real_competitor`, `midpoint_overlap`, `scalar_midpoint`, `competitor_half`, `values_bddBelow` and `inf_le_competitor`, with exactly the hypotheses listed in the route, give the stronger chain $M^E\le D(\rho\Vert\tau)\le M^H/2$. Conjugation averaging places an explicit competitor in the real-state set, and operator concavity controls its cost. These intermediate bounds are present in the compiled helper lemmas; `result` itself states only $M^E\le M^H$.
- *Sharpness uniformly over the registered parameters.* Let $|\psi\rangle=(|0\rangle+\mathrm{i}|1\rangle)/\sqrt2$ and $P=|\psi\rangle\langle\psi|$. Then $P\bar P=0$, $P^\alpha=P$ for $\alpha>0$, and $\tau=I/2$. For any real qubit density matrix $\sigma$, its real symmetric spectral power $\sigma^{1-\alpha}$ has expectation $\langle\psi|\sigma^{1-\alpha}|\psi\rangle=\operatorname{tr}(\sigma^{1-\alpha})/2$. Its eigenvalues are $\lambda,1-\lambda$ for some $\lambda\in[0,1]$, so scalar concavity for $0<\alpha<1$ gives this expectation at most $2^{\alpha-1}$, with equality at $\sigma=I/2$. For any $\beta>0$, the divergence decreases with the nonnegative overlap, so this competitor minimizes it. Writing $c=(1-\alpha)\beta>0$ gives $M^H(P)=1/c$, $M^E(P)=(1-2^{-c})/c$ and $M^E(P)/M^H(P)=1-2^{-c}$. At $\beta=1$, this ratio tends to $1/2$ as $\alpha\downarrow0$ within the registered range. Thus no constant smaller than $1/2$ works uniformly over that range, even just for qubits. This does not determine the best constant for each fixed parameter pair or classify equality cases.
- *A neighbouring parameter range.* For every density matrix $\rho$ in a finite positive dimension and $0<\alpha<1$, `conjugate_state` supplies the density hypothesis for $\bar\rho$, so `overlap_nonneg` and `overlap_le_one` applied to $\rho,\bar\rho$ give $0\le q\le1$, and `midpoint_overlap` gives $r\ge(1+q)/2\ge q$. For every $\beta>0$, monotonicity gives $r^\beta\ge q^\beta$ and the negative denominator gives $D(\rho\Vert\tau)\le M^H$. For any two density matrices, the same overlap bounds give nonnegative divergence when $\beta>0$, so the value set remains nonempty and bounded below and its infimum is at most the competitor value. The argument extends the comparison to all $\beta>0$; that extension is not a statement of any theorem in this module. The half-factor cannot extend to all such parameters: the pure qubit above at $\alpha=1/4$, $\beta=2$ has ratio $1-2^{-3/2}>1/2$.
- *The source's minimum.* For fixed finite $d\ge1$, density matrix $\rho$, $0<\alpha<1$ and $0<\beta\le1$, the real-state set is nonempty by `real_competitor`. It is closed by its positivity, trace and reality constraints, and bounded because nonnegative eigenvalues summing to one lie in $[0,1]$; hence it is compact. For fixed $\alpha$, the spectral power $\sigma\mapsto\sigma^{1-\alpha}$ is continuous there: uniformly approximate the continuous function $t^{1-\alpha}$ on $[0,1]$ by polynomials and apply spectral calculus. Multiplication, trace and the nonnegative real $\beta$ power preserve continuity. The divergence therefore attains its infimum. This identifies the infimum comparison with the source's minimum comparison by an unformalized argument, not a Lean attainment theorem.
- *Effect on the paper.* The universal comparison includes the qubit conjecture and the special family of Remark 3. Reading the v1 main text and appendices identifies no theorem whose proof assumes the conjecture: Theorems 1–9 concern properties of the measures separately, while the conjecture occurs in Example 1. The settlement resolves that comparison without validating those separate proofs or the source's explicit optimization formulas. In particular, the real competitor need not be an optimizer for general inputs; finding minimizers and sharp constants for fixed parameters remains outside `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #20971 does not establish exhaustive worldwide novelty or priority. Its OpenAlex and Semantic Scholar census, eleven citing-full-text readings, related-paper readings, follow-up abstract, version-listing and negative database/repository searches have not been independently reproduced. Three citing works were unread in that check, including the Tong–Wu–Wu follow-up identified above; a resolution there is not excluded.

The direct v1 TeX reading verifies the quoted conjecture, definitions and their locations. It does not establish that every source theorem or example formula is correct. The source's numerical experiments, figures and general qubit optimization formula were not reproduced.

The pure-qubit minimization and sharpness argument, the extension to $\beta>1$, the identification of the source minimum with the formal infimum, and the discussion of dependencies in the paper are not formalized by `result`. The half-factor is certified internally by the named private helpers under their stated hypotheses; it is not the conclusion of `result`. Parameter endpoints and the limiting entropy definitions, general equality conditions and best constants at each fixed parameter pair are not settled by this module.
