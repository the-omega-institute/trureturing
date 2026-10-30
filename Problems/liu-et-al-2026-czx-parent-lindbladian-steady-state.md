---
slug: liu-et-al-2026-czx-parent-lindbladian-steady-state
bibkey: liuetal2026parentlindbladians
doi: 10.1103/1qyd-59z7
url: https://arxiv.org/abs/2501.10552v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.result
---

# The CZX parent Lindbladian reaches the conjectured steady state on every even ring of at least four qubits

## Problem

Y. Liu, A. Ruiz-de-Alarcón, G. Styliaris, X.-Q. Sun, D. Pérez-García and J. I. Cirac, *Parent Lindbladians for matrix product density operators*, arXiv:2501.10552v2 (Phys. Rev. Research 8, 013210, 2026), Appendix F, “Evolution”, `main.tex`, lines 5038–5042:

> We conjecture that this relation holds for general $N$.

The referenced relation concerns the initial state $\rho_0^{(N)}=2^{-N}(\mathbb 1+\sigma_x^{\otimes N})$ and the limiting state $\rho_\infty^{(N)}=2^{-N}(\mathbb 1+2^{1-N/2}U_{CZX}^{(N)})$; the preceding source sentence reports numerical verification for $N=4,6,8$. The source restricts the construction to even $N$ (`main.tex`, lines 3085–3093 and 4940).

Here $U_{CZX}^{(N)}=(\prod_{j=1}^N CZ_{j,j+1})\sigma_x^{\otimes N}$, with cyclic indices. The source defines the four-site channel $\mathcal E=\mathcal T\circ\mathcal S$ from its renormalization channels and the generator $\mathcal L^{(N)}=\sum_{i=1}^{N/2}(\mathcal E_{2i-1}-\mathrm{id})$ (`main.tex`, lines 3135, 3152 and 4951–4952). The definitions and source locators are collected in [the literature note](../Library/Eigenstructure/liuetal2026parentlindbladians.md).

Issue [#23957](https://github.com/the-omega-institute/trureturing/issues/23957) fixes the reading: for every even $N\ge4$, $e^{t\mathcal L^{(N)}}(\rho_0^{(N)})$ converges to $\rho_\infty^{(N)}$ as real $t\to+\infty$. The lower bound makes the four window sites distinct. This is proved.

## Motivation

The CZX example tests the parent-Lindbladian construction beyond the paper's weak-Hopf-algebra setting. A family of available steady states does not determine which member a specified initial state reaches. The conjecture identifies that member and its dependence on ring size, connecting the evolution example to the source's bounds on preparation from separable states.

## Gap

Issue #23957 records the literature check by the orchestrator (Claude Code, Opus):

- the arXiv v2 source contains the conjecture, and the issue reports its retention in the published version;
- of 18 citing records listed by INSPIRE, 15 arXiv sources were read; the issue reports that arXiv:2605.04159 uses the CZX parent channels on inputs already carrying the CZX symmetry, without settling the specified initial state's coefficient;
- title-and-conjecture searches and repository searches found no prior settlement; additional searches of Zenodo, ResearchGate, SSRN, GitHub and LionSR/TNLean are attributed in the issue to GPT Pro.

`not-found-in-searched-scope`. These are bounded search reports, with the unreproduced readings identified below.

## Route

Write $x,\delta\in\{0,1\}^N$, with bit addition modulo two, and define the gauged matrix unit $B_{\delta,x}=(-1)^{\sum_j\delta_jx_jx_{j+1}}|x+\delta\rangle\langle x|$, corresponding to `gaugedUnit`.

1. **The source channel.** For every complex $16\times16$ matrix, `local_channel_formula` in `CZXParentLindbladianWindowChannel` rewrites $\mathcal T\circ\mathcal S$ as conjugation by the source's signed permutation $V$, block pinching and partial trace, reinsertion of the four-dimensional identity divided by four, and conjugation back. The ratio $\nu_\lambda/m_\lambda=\mathbb 1_4/4$ is derived from the source weights.
2. **Gauge and commutation.** For $N\ge4$, every cyclic starting site $i$, and every $\delta,x$, `gauged_window_sector` sends $B_{\delta,x}$ to the uniform average over the two middle window bits if $\delta$ is constant on that window, and to zero otherwise. For $N\ge4$, `window_idempotent` makes every window superoperator idempotent, and `window_channels_commute` proves commutation for every pair of starting sites acting on any complex matrix. These helper lemmas do not require even $N$.
3. **The exponential limit.** For any finite list of pairwise commuting idempotent square complex matrices, `finite_projection_limit` gives convergence of the exponential of the sum of their differences from the identity to their product. For even $N\ge4$, `exponential_limit` applies this to the zero-based even starts of `parentLindbladian` and obtains the limiting superoperator `projection`.
4. **The limiting projection.** For $N\ge4$, `all_good_iff_constant` identifies the sectors constant on every selected window with the globally constant sectors. For even $N\ge4$, `middle_sites_cover` shows that the middle sites of the selected windows cover the ring. For even $N\ge4$ and every complex matrix $A$ on the $N$ qubits, `projection_formula` consequently computes the product projection as $P_N(A)=2^{-N}[\operatorname{tr}(A)\mathbb 1+\operatorname{tr}((U_{CZX}^{(N)})^\dagger A)U_{CZX}^{(N)}]$.
5. **The coefficient.** For even $N\ge4$, `transfer_coefficient` proves $\operatorname{tr}((U_{CZX}^{(N)})^\dagger\sigma_x^{\otimes N})=2^{N/2+1}$, using the transfer matrix $H=\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$ and $H^2=2\mathbb 1$. For every $N>0$, `symmetry_trace` gives $\operatorname{tr}(U_{CZX}^{(N)})=0$ and `flip_diagonal` gives zero diagonal entries of $\sigma_x^{\otimes N}$. For even $N\ge4$, `projection_initial` evaluates $P_N(\rho_0^{(N)})$ as the claimed target. `evolution_limit`, for any $N$ given convergence of the exponential superoperator to `projection`, transfers that convergence to the specified initial matrix; `result` combines these facts for every even $N\ge4$.

## Falsifier

A mismatch between the formal channel and the source channel would defeat the interpretation as a settlement. The correspondence is explicit:

- `czxU` and `czxV` use the source matrices in `main.tex`, lines 4858–4863 and 4933–4936; `renormS` and `renormT` implement the two block projections, multiplicity partial trace and insertion with the source weights.
- `windowCode` makes the first site the most significant bit, and `windowChannel` inserts the four-site channel cyclically with the identity on the complement; $N\ge4$ excludes repeated window sites.
- Zero-based even starts in `parentLindbladian` correspond to the source's one-based odd starts. `evolution` is the matrix exponential of this sum acting on matrix entries.
- `tensorX` flips every bit, `czxUnitary` is CZ times that flip, and the identity matrix has dimension $2^N$. The exponent $1-N/2$ in `claim` is an integer exponent, so negative exponents are retained.

A different limit at any even $N\ge4$ would contradict `claim`; finite-size agreement alone would not establish its universal quantifier. Odd rings and smaller rings are outside that quantifier.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.lean.json`.

Declaration statements:

- `result`: `sha256:b1bead68d09e339731ba94f191dde02bf8d4739875140a4af52b1bd9af4ab0bb`;
- `claim`: `sha256:500fa0d7fec9cd9469ea7c495d878cb785b01f333198d4be32666532496937f5`.

## Triage

Tier 1 conjecture of a 2025 preprint published in 2026 with the conjecture retained, preregistered in issue #23957 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N$ that is even and at least four, the evolution of the complex matrix $2^{-N}(\mathbb 1+\sigma_x^{\otimes N})$ under `parentLindbladian` converges, as real $t\to+\infty$, to $2^{-N}(\mathbb 1+2^{1-N/2}U_{CZX}^{(N)})$.

**Computed, not formalized** (orchestrator, Claude Code, Opus; exact arithmetic recorded in #23957):

- The source four-site channel was idempotent on all 256 window matrix units.
- The bit formula for the signed permutation agreed entry by entry with the source's $16\times16$ matrix $V$.
- The selected window channels commuted on every matrix unit at $N=4,6$.
- The product of the selected window channels sent the specified initial state to the conjectured target exactly for $N=4,6,8,10,12$.

**Argued, not formalized.**

- *Mechanism and arbitrary inputs.* For even $N\ge4$, `exponential_limit` gives convergence of the superoperator itself, and `projection_formula` gives its action on every complex matrix $A$. Applying the continuous finite-dimensional linear map $T\mapsto T(A)$ therefore gives convergence to $P_N(A)$ for every such $A$. This is an arbitrary-input corollary of the two named lemmas; the type of `result` specifies only $\rho_0^{(N)}$.
- *Separable input and sharpness.* For every even $N\ge4$, $\rho_0^{(N)}$ is the uniform mixture of product $\sigma_x$ eigenstates with eigenvalue signs $s_j\in\{\pm1\}$ satisfying $\prod_j s_j=1$. Expanding the product projectors $\bigotimes_j(\mathbb 1+s_j\sigma_x)/2$ and averaging over these signs cancels every proper nonempty sign product, leaving precisely $2^{-N}(\mathbb 1+\sigma_x^{\otimes N})$. Proposition F.1 of the source (`main.tex`, lines 5044–5053) bounds $|c|$ by $2^{1-N/2}$ for every fully separable initial state on an even ring. Conditional on that source bound, this separable input attains the bound for every even $N\ge4$.
- *Relation to the intended CZX state.* The source defines $\rho_{CZX}^{(N)}=2^{-N}(\mathbb 1+U_{CZX}^{(N)})$ at `main.tex`, lines 3085–3093. For even $N\ge4$, $N/2\ge2$ gives $0<2^{1-N/2}\le1/2<1$. Since $U_{CZX}^{(N)}$ sends every computational basis vector to a signed complementary vector and is therefore nonzero, this limit differs from $\rho_{CZX}^{(N)}$.
- *Effect on the paper and neighbouring questions.* The source's general-$N$ conjectural evolution example is justified for every even $N\ge4$. Its full steady-state classification, rapid-mixing assertion, Proposition F.1 and the block-separable extension have separate arguments in Appendix F; they are not additional conclusions of `result`. Sharpness for other initial-state families, quantitative convergence bounds, odd rings and windows with repeated sites remain outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #23957 does not establish exhaustive worldwide novelty or priority. The INSPIRE citation listing, the 15 citing-paper readings (including the reported scope of arXiv:2605.04159), the repository searches and the external search results are attributed to their authors in that issue and have not been independently reproduced. The published-PDF retention of the conjecture and Crossref bibliographic metadata are taken from the preregistration and Library note; the source reading supporting the quotation is the arXiv v2 TeX.

The exact-arithmetic computations are reports by the preregistration author and have not been independently rerun. The arbitrary-input corollary, separable decomposition, conditional sharpness argument and comparison with $\rho_{CZX}^{(N)}$ are not separately formalized. Proposition F.1 is an external premise of the sharpness comparison; its upper bound, the block-separable bound, the full density-matrix steady-state classification and quantitative mixing claims are not asserted as proved by `result`. Extensions beyond even $N\ge4$ remain open within the scope of this dossier.
