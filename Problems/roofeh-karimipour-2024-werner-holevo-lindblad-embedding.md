---
slug: roofeh-karimipour-2024-werner-holevo-lindblad-embedding
bibkey: roofehkarimipour2024wernerholevo
doi: 10.1103/PhysRevA.109.052620
url: https://arxiv.org/abs/2310.15353v7
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.result
---

# The noisy qutrit Werner–Holevo channel is a GKSL exponential only at zero noise on $[0,2/3]$

## Problem

Shayan Roofeh and Vahid Karimipour, *The noisy Werner-Holevo channel and its properties*, Phys. Rev. A 109, 052620 (2024), arXiv:2310.15353v7, subsection “Spectral properties of the channel,” ask:

> The question remains whether, within the range of $0\leq x\leq \frac{2}{3}$, the channel can be described as the exponential of Lindbladian dynamics. We will explore this question in our future work.

This is verbatim from `ModifiedLSChannel-12.tex`, line 249, in the downloaded v7 source, md5 `bcff52a86196a2e1a0054a34c48a8117`. The channel formula is at line 153; its spectral multipliers and determinant are at lines 237–247. The [literature note](../Library/QuantumContext/roofehkarimipour2024wernerholevo.md) records these locators.

The module defines, for every real $x$, the complex-linear map on $M_3(\mathbb C)$

$\Lambda_x(X)=(1-x)X-\frac{x}{2}X^{\mathsf T}+\frac{x}{2}\operatorname{tr}(X)I_3.$

This is `wernerHolevo`; the source uses the same formula with $0\le x\le1$. `IsGKSLGenerator G` means that there exist $m\in\mathbb N$, a Hermitian $H\in M_3(\mathbb C)$ and matrices $V_k\in M_3(\mathbb C)$ indexed by $k\in\mathrm{Fin}\,m$ such that, for every $X\in M_3(\mathbb C)$,

$G(X)=-i(HX-XH)+\sum_k\left(V_kXV_k^\dagger-\frac12(V_k^\dagger V_kX+XV_k^\dagger V_k)\right).$

The empty jump family is allowed. `generatorExp G` is the ordinary exponential of the $9\times9$ complex matrix of $G$ in the matrix-unit basis, transported back to a linear map. Equality is equality on the entire complex matrix space.

Issue [#21274](https://github.com/the-omega-institute/trureturing/issues/21274) fixes the statement: for every $x\in[0,2/3]$, there exists such a $G$ with $\operatorname{generatorExp}(G)=\Lambda_x$ if and only if $x=0$. This statement is proved.

## Motivation

The question distinguishes a noise channel specified by its input-output action from a finite-time exponential of a time-independent Lindblad generator. A positive determinant alone leaves the interior $0<x<2/3$ undecided: the two nontrivial spectral multipliers are positive there. The settlement supplies a stronger obstruction involving their relative decay rates. It also clarifies the relation to the source's small-angle random-rotation approximation at TeX lines 212–216.

## Gap

The bounded literature check in #21274 records:

- the v7 source retains the explicit question; the quotation and source hash are independently reproduced here;
- the issue reports OpenAlex work `W4396887671` with six citations and five distinct citing works from OpenCitations: arXiv:2405.11216v3, 2506.13397v3, 2411.19644v2, 2402.07700v5, and Luo et al., DOI `10.1007/s10773-025-06093-4`;
- the issue reports full-text readings of the four arXiv papers, only an abstract reading of Luo et al., and readings of related arXiv:2401.16312v6, 2408.05733v5, 2610.03706v1, 2609.40355v2, 2603.12130v1 and 2603.07761v1, without finding a settlement;
- the preregistration records no existing repository issue, module or Problems record for this question.

These citation counts, secondary-paper readings and repository-search readings are attributed to #21274, not independently reproduced here. The search outcome is `not-found-in-searched-scope`, not an exhaustive novelty claim. Conditional complete positivity and the determinant obstruction are known ingredients recorded in the issue; the target is the answer for this specified family and parameter interval.

## Route

All linear maps and matrices below are over $\mathbb C$ on $M_3(\mathbb C)$. Define the module's two projections by

$P(X)=\frac12(X+X^{\mathsf T})-\frac13\operatorname{tr}(X)I_3,\qquad Q(X)=\frac12(X-X^{\mathsf T}),$

and put $s(G)=\operatorname{Re}\operatorname{Tr}(G\circ P)$ and $a(G)=\operatorname{Re}\operatorname{Tr}(G\circ Q)$. Here $\operatorname{Tr}$ is the endomorphism trace; $\operatorname{tr}$ is the matrix trace. These are `symmetricProjection`, `antisymmetricProjection`, `symmetricTrace` and `antisymmetricTrace`.

1. **Zero noise.** `zero_gksl` supplies the zero generator with $H=0$ and $m=0$. `generatorExp_zero` and `wernerHolevo_zero` identify its exponential and $\Lambda_0$ with the identity map.
2. **The singular endpoint.** `generatorExp_injective` applies to every complex-linear $G$, with no GKSL hypothesis. `endpoint_kernel` gives the nonzero matrix $E_{00}-E_{11}$ annihilated by $\Lambda_{2/3}$. Thus `endpoint_not_exp` excludes $\operatorname{generatorExp}(G)=\Lambda_{2/3}$ for every $G$.
3. **A GKSL trace inequality.** For every $H\in M_3(\mathbb C)$, `sector_trace_hamiltonian` gives $s(\mathcal H_H)-5a(\mathcal H_H)=0$, where $\mathcal H_H(X)=-i(HX-XH)$; this identity does not require $H$ to be Hermitian. For every $V\in M_3(\mathbb C)$, `sector_trace_dissipator` gives

   $s(\mathcal D_V)-5a(\mathcal D_V)=2\sum_{i<j}|V_{ii}-V_{jj}|^2+3\sum_{i<j}|V_{ij}+V_{ji}|^2,$

   where $\mathcal D_V(X)=VXV^\dagger-\frac12(V^\dagger VX+XV^\dagger V)$ and $0\le i<j\le2$. Summing these identities proves `gksl_trace_inequality`: for every $G$ satisfying `IsGKSLGenerator G`, $s(G)-5a(G)\ge0$. No unitality or commutation hypothesis is needed for this inequality.
4. **The required commutation.** `generatorExp_commute` applies to every $G$. `gksl_trace_zero` gives $\operatorname{tr}(G(X))=0$ for every $X$ whenever `IsGKSLGenerator G`. For a real $x\ne0$, a $G$ satisfying `IsGKSLGenerator G` and $\operatorname{generatorExp}(G)=\Lambda_x$, `generator_unital` proves $G(I_3)=0$, `generator_transpose` proves $G(X^{\mathsf T})=G(X)^{\mathsf T}$ for every $X$, and `generator_projection_commute` proves that $G$ commutes with both $P$ and $Q$. These lemmas do not infer generator unitality merely from exponential unitality without their other hypotheses.
5. **Branch-independent sector traces.** For complex-linear $G,R$, `projected_log_trace` assumes $R^2=R$, $GR=RG$, a real $d>0$, and $\operatorname{generatorExp}(G)R=dR$. It proves $\operatorname{Re}\operatorname{Tr}(GR)=\operatorname{Re}\operatorname{Tr}(R)\log d$. On the range of $R$, every eigenvalue $\mu$ of $G$ satisfies $e^\mu=d$, hence $\operatorname{Re}\mu=\log d$; summing characteristic roots supplies the trace without choosing a logarithm branch. `symmetricProjection_idempotent`, `antisymmetricProjection_idempotent`, `symmetricProjection_trace` and `antisymmetricProjection_trace` give idempotence and traces $5$ and $3$. For every real $x$, `wernerHolevo_symmetricProjection` and `wernerHolevo_antisymmetricProjection` give $\Lambda_xP=(1-3x/2)P$ and $\Lambda_xQ=(1-x/2)Q$. Consequently, `spectral_traces`, with all its hypotheses $0<x<2/3$, `IsGKSLGenerator G` and $\operatorname{generatorExp}(G)=\Lambda_x$, gives

   $s(G)=5\log(1-3x/2),\qquad a(G)=3\log(1-x/2).$

6. **The interior contradiction.** For a real $x$ with $0<x<2/3$, `strict_log_inequality` uses strict Bernoulli and logarithm monotonicity to prove $5\log(1-3x/2)<15\log(1-x/2)$. Together with `spectral_traces` and `gksl_trace_inequality`, `interior_not_exp` excludes $\operatorname{generatorExp}(G)=\Lambda_x$ for every $G$ satisfying `IsGKSLGenerator G` under those same strict interval hypotheses. `result` combines this with the two endpoints.

## Falsifier

The formalization would miss the question if it excluded only a particular logarithm, assumed a symmetric generator without justification, or changed the channel or generator class. Its definitions use the source's ordinary transpose, the full complex matrix space and arbitrary finite GKSL jump families with a Hermitian Hamiltonian. Its interior obstruction applies to every such generator, including logarithms with nonzero imaginary branches; the needed projection commutation is derived with the hypotheses stated above.

The theorem concerns an exact exponential of one time-independent generator. It does not assert nonexistence of a time-dependent evolution, a product of different generator exponentials, an approximation, or a limiting realization. Complete positivity of $\Lambda_x$ as a channel is source context, not a separate conclusion of `result`.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.lean` (459 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The axiom closure is read from `#print axioms` on the imported `result`; the source scan for those forbidden constructs has no matches.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.lean.json`, statement `sha256:e8aafc82c498f30e7909e12fec4d9e2957d5e577e3bb8b2dcb74d1bdb8624844`.

Declaration statements:

- `result`: `sha256:ba8cd229ed7fa12e768f0e1783787fbe516cf6ad26cc3490575357d47ae1635f`;
- `claim`: `sha256:3b03c90ddc64af18d11c11c1f88a45118bbd716020ff816e431bad9f9c6ecee2`.

## Triage

Tier 1: an explicit open question of a 2024 paper left for future work, preregistered in issue #21274 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $x\in[0,2/3]$, existence of a complex-linear $G$ on $M_3(\mathbb C)$ satisfying `IsGKSLGenerator G` and $\operatorname{generatorExp}(G)=\operatorname{wernerHolevo}(x)$ is equivalent to $x=0$.

**Argued, not formalized**:

- *Decisive mechanism.* Under the full hypotheses of `spectral_traces`, namely $0<x<2/3$, `IsGKSLGenerator G` and $\operatorname{generatorExp}(G)=\Lambda_x$, that lemma and `gksl_trace_inequality` force $b\ge c^3$. The polynomial difference $c^3-b=x^2(6-x)/8$ is positive for $0<x<2/3$, since $x^2>0$ and $6-x>0$. The obstruction is therefore a relation between two positive decay multipliers, stronger than a determinant sign test, and excludes every logarithm branch.
- *A neighbouring necessary condition.* Let $P_0(X)=\operatorname{tr}(X)I_3/3$ and $\Phi_{b,c}=P_0+bP+cQ$, where $b,c>0$ and $1,b,c$ are pairwise distinct. If $G$ satisfies `IsGKSLGenerator G` and $\operatorname{generatorExp}(G)=\Phi_{b,c}$, commutation with its exponential (`generatorExp_commute`) makes $G$ commute with $P$ and $Q$: these are polynomials in $\Phi_{b,c}$, for example $P=(\Phi_{b,c}-\mathrm{id})(\Phi_{b,c}-c\,\mathrm{id})/((b-1)(b-c))$. The projections are idempotent with traces $5$ and $3$, and the exponential acts on them by $b$ and $c$. These are all the hypotheses needed to apply `projected_log_trace` separately to $P$ and $Q$. Thus $s(G)=5\log b$ and $a(G)=3\log c$, and `gksl_trace_inequality` gives $b\ge c^3$. This argument gives a necessary condition, not a classification of all such channels; coincident multipliers require a separate argument.
- *Sharpness of this neighbouring obstruction.* Let $E_{ij}$ be the matrix units and $W_{ij}=E_{ij}-E_{ji}$ for $0\le i<j\le2$; sums over $W_{ij}$ range over these three pairs. The skew-jump identities admit an entrywise verification: the diagonal entries of $\sum W_{ij}XW_{ij}^\dagger$ are $\operatorname{tr}(X)-X_{ii}$ and its off-diagonal entries are $-X_{ji}$. With $\sum W_{ij}^\dagger W_{ij}=2I_3$, their dissipator sum is $L_0(X)=\operatorname{tr}(X)I_3-X^{\mathsf T}-2X=-3P(X)-Q(X)$. For any $\gamma\ge0$, $\gamma L_0$ has a finite GKSL representation with $H=0$ and jumps $\sqrt\gamma W_{ij}$. Their definitions give $P_0+P+Q=\mathrm{id}$, $P_0^2=P_0$, and zero products between distinct projections; $P$ and $Q$ are idempotent as recorded in the Route. Thus its exponential is $P_0+e^{-3\gamma}P+e^{-\gamma}Q$. Hence $b=c^3$ is attained by this neighbouring family. This construction and its exponential are not declarations of the settlement module.
- *Small noise and temporal scope.* Algebraically $\Lambda_x=\mathrm{id}+(x/2)L_0$, whereas the genuine exponential $e^{(x/2)L_0}$ has multipliers $e^{-3x/2}$ and $e^{-x/2}$. Their Taylor expansions agree with the channel multipliers to first order at zero; the discrepancy starts at second order. Exact non-embedding at every positive $x\le2/3$ therefore permits an infinitesimal Lindblad approximation. Also, for a time-independent finite GKSL generator $L$ and any $t\ge0$, $tL$ has the same form using $tH$ and $\sqrt t V_k$, so the time-one convention includes arbitrary nonnegative finite times. Neither statement settles time-dependent embeddability.
- *Effect on the source.* The question at TeX line 249 receives a negative answer for every $0<x\le2/3$, with the identity as its sole affirmative case. The source explicitly leaves this question to future work, rather than asserting an embedding theorem there. Its separate determinant observation on $2/3<x\le1$ is outside `result`. Its random-rotation discussion reaches the noisy-channel formula through the small-angle approximation at lines 212–216; an approximation does not entail an exact exponential representation. The settlement neither verifies nor refutes the source's separate capacity and degradability calculations, or its questions about higher-spin and higher-dimensional generalizations at lines 911–913. Those assertions do not acquire a new proof from this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #21274 does not establish exhaustive worldwide novelty or priority. Its OpenAlex and OpenCitations counts, secondary-paper readings, abstract-only Luo et al. reading, assertion that v7 is the latest version, and repository-search results are not independently reproduced here. The v7 TeX quotation, locator and md5 are reproduced; the DOI and journal metadata are recorded in the Library note and preregistration, without an independent Crossref query here.

Everything labelled “Argued, not formalized” lies outside the compiled statement of `result`. In particular, the generic two-multiplier necessary condition, its sharpness construction, the polynomial identity as a named theorem, the Taylor comparison, and absorption of a time parameter are not formalized in this module. No sufficiency classification for general $\Phi_{b,c}$, time-dependent embedding result, higher-dimensional extension, or conclusion about the other open questions of the source is claimed; these remain open in this dossier.
