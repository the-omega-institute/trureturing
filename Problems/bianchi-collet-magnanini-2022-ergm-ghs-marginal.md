---
slug: bianchi-collet-magnanini-2022-ergm-ghs-marginal
bibkey: bianchicolletmagnanini2022ghs
doi: 10.30757/ALEA.v19-64
url: https://arxiv.org/abs/2107.08889v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result
---

# Edge marginals at least one half do not imply GHS for general exponential random graphs

## Problem

A. Bianchi, F. Collet and E. Magnanini, *The GHS and other correlation inequalities for the two-star model*, arXiv:2107.08889v2 (ALEA 19 (2022), 1679–1695), Section 4, closing paragraph, conjecture:

> Since $\text{Cov}_{n;\boldsymbol{\beta}}(x_i,x_j) \geq 0$, due to the GKS inequality \eqref{GKS_g}, we can conjecture that the necessary and sufficient condition for the GHS inequality to hold in the present general setting is again only the requirement $\mathbb{E}_{n;\boldsymbol{\beta}}(x_i) \geq 1/2$.

This is the verbatim sentence at line 1322 of the downloaded v2 source, `GHS_arXiv-replacement.tex` (md5 `b353bfa014348d3c29f4b9c509b5665d`). The general setting is specified at lines 1248–1287; the model and third Ursell function are defined at lines 286–312 and 577–589, respectively. The definitions and source locators are also in [the literature note](../Library/StatisticalMechanics/bianchicolletmagnanini2022ghs.md).

Issue [#22390](https://github.com/the-omega-institute/trureturing/issues/22390) fixes the following reading. For every $n,k\in\mathbb N$, take a nonempty family $h_j$ of finite simple graphs on $\mathrm{Fin}(m_j)$, indexed by $j\in\mathrm{Fin}(k+1)$, with $h_0=K_2$, and real coefficients $\beta_j$ with $\beta_j\geq0$ for every $j\ne0$. The coefficient $\beta_0$ is unrestricted. The source indexes this family from one instead of zero. On the labeled simple graphs $G$ with vertex set $\mathrm{Fin}(n)$, put

$t(h_j,G)=|\operatorname{hom}(h_j,G)|/n^{m_j}$, $H(G)=n^2\sum_{j=0}^k\beta_jt(h_j,G)$ and $\mu(G)=e^{H(G)}/\sum_{G'}e^{H(G')}$.

Write $\mathcal E_n=E(K_n)$, $X_e(G)=\mathbf1_{e\in E(G)}$ and

$u_3(e,f,g)=\mathbb E(X_eX_fX_g)-\mathbb E(X_e)\mathbb E(X_fX_g)-\mathbb E(X_f)\mathbb E(X_eX_g)-\mathbb E(X_g)\mathbb E(X_eX_f)+2\mathbb E(X_e)\mathbb E(X_f)\mathbb E(X_g)$.

The proposition `claim` asserts, for every such choice,

$(\forall e\in\mathcal E_n,\ \mathbb E(X_e)\geq1/2)\ \Longleftrightarrow\ (\forall e,f,g\in\mathcal E_n,\ u_3(e,f,g)\leq0)$.

The triple quantifier includes repeated edges. The equivalence is refuted by its sufficiency direction.

## Motivation

GHS controls third joint cumulants of edge indicators. In the source's two-star model, under nonnegative interaction and field parameters, it yields concavity of the mean edge density in the common external field (Section 3.3, TeX lines 1194–1225). The conjecture would turn a condition on individual edge marginals into a criterion for all these third-order correlations for arbitrary graph motifs.

## Gap

Issue #22390 records the bounded literature check before any Lean:

- The orchestrator's web searches for the conjecture, two-star GHS and triangle/Ursell counterexamples, together with its checks of related preprints and Zenodo searches, found no settlement.
- The search author reported no settlement in the citing works it read and no match in formal-conjectures; its MathDB request returned HTTP 403.
- The orchestrator reported no existing repository issue, module, Library note or dossier settling the conjecture at preregistration.

`not-found-in-searched-scope`.

## Route

The private `models` and `parameters` specify $n=3$, $k=1$, $h_0=K_2$, $h_1=K_3$, $\beta_0=0$ and $\beta_1=(\log2)/2$. Let $e_{01},e_{02},e_{12}$ be the three unordered edges of $K_3$.

1. **Homomorphisms and Hamiltonian.** For every simple graph $G$ on $\mathrm{Fin}(3)$, `triangle_count` gives $|\operatorname{hom}(K_3,G)|=6$ if $G=K_3$, and zero otherwise. An adjacency-preserving map from $K_3$ is injective because the target is loopless; on these three vertices it is also surjective, forcing the target to be complete. For every such $G$, `hamiltonian_value`, with the fixed `models` and `parameters`, gives $H(G)=\log2$ at $K_3$ and zero otherwise.
2. **The finite graph sum.** `graph_bijective` identifies all simple graphs on $\mathrm{Fin}(3)$ with Boolean triples recording the three adjacencies; `graph_top` identifies $K_3$ with the all-true triple. For every real observable on these graphs, `sum_graphs` reindexes its sum by that bijection. For every simple graph $G$ on $\mathrm{Fin}(3)$ and the fixed `models` and `parameters`, `weight_value` gives $\mu(G)=2/9$ if $G=K_3$ and $1/9$ otherwise; its partition-sum calculation is $Z=9$.
3. **Moments and Ursell function.** For every $e\in\mathcal E_3$, `marginal_value` gives $\mathbb E(X_e)=5/9$ under the fixed `models` and `parameters`. For the three specified pairs $(e_{01},e_{02})$, $(e_{01},e_{12})$ and $(e_{02},e_{12})$, `joint_values` gives pair moment $1/3$ and, for their three edges together, triple moment $2/9$. For exactly $(e_{01},e_{02},e_{12})$ in this model, `ursell_value` gives $u_3=2/9-3(5/9)(1/3)+2(5/9)^3=7/729$.
4. **Contradiction.** The proof of `result` verifies $\beta_j\geq0$ at every nonzero index of this family and $5/9\geq1/2$ for every edge. Specializing the forward implication of `claim` at $n=3$, $k=1$ and these data would give $7/729\leq0$.

## Falsifier

The refutation must use the source's homomorphism-density model and GHS condition. The module:

- counts all adjacency-preserving vertex maps, rather than induced copies, and divides their number by $n^{m_j}$ in `homDensity`;
- uses the factor $n^2$, exponential weights and the sum over all labeled simple graphs in `hamiltonian` and `gibbsWeight`, with `expectation` their finite weighted sum;
- uses unordered nonloop edges in `edgeIndicator`, the full third-cumulant expression in `u3`, and all triples, including repetitions, in `claim`;
- leaves the edge coefficient unrestricted and requires every other coefficient to be nonnegative.

The natural-number quantifiers in Lean include $n=0$ and $n=1$, with total real division when a density denominator vanishes. Both sides of the equivalence have vacuous edge quantifiers at those sizes. The witness has $n=3$, so neither convention supplies the contradiction.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:70f23b800432f24a6b2f484963ae14a65418e8d67e9e7fb65f9a727cf1418223`;
- `claim`: `sha256:3d3a1f6a4f5072d0135129937541ea7f0bc199ca2691ba755cb1092527e33962`.

## Triage

Tier 1 conjecture in a 2021 preprint published in 2022, preregistered in issue #22390 before any Lean; the issue's bounded search found no prior settlement.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal equivalence `claim` is false: it is not the case that for every natural $n,k$, every family indexed by $\mathrm{Fin}(k+1)$ whose first graph is $K_2$, and every real coefficient vector nonnegative at each nonzero index, all edge marginals being at least $1/2$ is equivalent to all third Ursell functions being nonpositive.

**Computed, not formalized** (independent exact enumeration):

- For the three-vertex model in Route, enumeration of all eight graphs and all $27$ ordered edge triples reproduced the three marginals $5/9$ and found maximum $u_3=7/729$, attained exactly at the six permutations of the three distinct edges.
- For the same model, the sum of $u_3$ over all $27$ ordered edge triples is $-2/27$.

**Argued, not formalized.**

- *The surviving necessary condition.* For any finite Gibbs law defined above with $n\geq2$, finite real coefficients give positive weight to every graph; graphs containing and omitting a specified edge both exist, so $0<p_i=\mathbb E(X_i)<1$. Since $X_i^2=X_i^3=X_i$, substitution gives $u_3(i,i,i)=p_i(1-p_i)(1-2p_i)$. Thus GHS still forces every marginal to be at least $1/2$; the refutation concerns sufficiency.
- *The missing control.* The same substitution gives $u_3(i,i,j)=(1-2p_i)\operatorname{Cov}(X_i,X_j)$. Consequently, when all marginals are at least $1/2$ and all edge covariances are nonnegative, every triple with a repeated edge has nonpositive $u_3$. The source's GKS conclusion supplies these nonnegative covariances for an unrestricted edge coefficient and nonnegative other coefficients (Section 4, TeX lines 1275–1287). This controls repeated-edge triples without controlling the third cumulant of three distinct edges.
- *An algebraic family explaining the failure.* Fix exactly three vertices, $h_0=K_2$, $h_1=K_3$, $\beta_0=0$ and $\beta_1=(\log w)/2$, with $w\geq1$. The seven proper subgraphs have exponential weight one and $K_3$ has weight $w$. Counting graphs containing one specified edge, two specified distinct edges, or all three gives $p=(w+3)/(w+7)$, $q=(w+1)/(w+7)$ and $t=w/(w+7)$. Hence $p-1/2=(w-1)/(2(w+7))$, $q-p^2=2(w-1)/(w+7)^2$ and $t-3pq+2p^3=[w(w+7)^2-3(w+3)(w+1)(w+7)+2(w+3)^3]/(w+7)^3=(w-1)(9-w)/(w+7)^3$. The denominator is positive. The repeated-edge identities above and $p\geq1/2$, $q-p^2\geq0$ give nonpositive cumulants for repeated edges, whereas the distinct-edge cumulant is positive exactly for $1<w<9$. Within this particular family, GHS therefore holds at $w=1$ and for $w\geq9$, and the marginal criterion is insufficient throughout $1<w<9$.
- *Effect on the paper and remaining scope.* The conjecture ends Section 4 immediately before the bibliography; no subsequent theorem in that text depends on it. The source's two-star GHS theorem assumes nonnegative pair-interaction and field vectors (Section 3.2, TeX lines 879–885), and its common-field monotonicity and concavity conclusions assume $\alpha,h\geq0$ (Section 3.3, lines 1194–1225). Those statements use the quadratic two-star Hamiltonian, whereas this witness has a genuine three-edge interaction. Their arguments do not rely on the conjecture. The marginal criterion cannot justify an extension of GHS to arbitrary motif families. A positive individual third cumulant also does not determine the sign of their sum, so the refutation alone does not refute common-field concavity. A replacement sufficient criterion for arbitrary motif families remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #22390 does not establish exhaustive worldwide novelty or priority. The orchestrator's web and Zenodo searches, its comparison with related preprints and repository records, and the search author's readings of citing works and formal-conjectures check were not independently reproduced. The issue reports two citing works in OpenAlex and three in OpenCitations; those counts were not independently reproduced. MathDB coverage remains unverified because the issue records HTTP 403. The arXiv v2 TeX and Crossref's DOI metadata were checked directly; the journal text was not independently compared with the arXiv version.

The computations and the arguments in the corresponding labelled groups are not formalized, including the general necessary condition, the repeated-edge identities and the parameterized three-vertex family. The source's GKS and two-star GHS results are cited literature results, not additional conclusions of `result`. No classification for arbitrary motif families, larger graph sizes or thermodynamic limits is supplied.
