---
slug: gudder-2019-informationally-complete-pairs
bibkey: gudder2019finiteconvexeffect
doi: 10.48550/arXiv.1912.05110
url: https://arxiv.org/abs/1912.05110v1
triage: theorem
motivation_gids:
  - D5/S3/Observer/Tomography/InformationallyCompletePairForest.result
---

# Informationally complete pairs are exactly complementary pairs with forest fiber graphs

## Problem

S. Gudder, *Finite-Dimensional Convex Effect Algebras* (2019), arXiv:1912.05110v1, Section 5, ends with this question. The following is the verbatim TeX text at line 588 of `finitedimensionalCEA.tex` (md5 `9dfe03bd484881c9db3b8b737095b005`):

> We conclude from Example~5 that complementarity is a necessary but not a sufficient condition for IC. It is an open problem to find a simple characterization of IC for a pair $\brac{f,g}\subseteq\rscript (X)$.

The source macros denote $\{f,g\}$ and $\mathcal R(X)$, respectively. Here $X=\{1,\ldots,n\}$ with $n\ge2$, $\mathcal R(X)$ consists of all maps $X\to\mathbb R$, and a probability weight $\mu$ has $\mu(x)\ge0$ and $\sum_x\mu(x)=1$. Its distribution under $f$ is $\Phi_{f,\mu}(\Delta)=\sum_{x:\,f(x)\in\Delta}\mu(x)$ for every $\Delta\subseteq\mathbb R$ (TeX lines 435–439). The pair is informationally complete (IC) when, for every two probability weights $\mu,\nu$, equality of their distributions under both $f$ and $g$ implies $\mu=\nu$ (line 474).

Let $\Gamma(f,g)$ have vertices in two tagged copies of $\mathbb R$, with a left value $a$ adjacent to a right value $b$ exactly when some $x\in X$ satisfies $f(x)=a$ and $g(x)=b$. Issue [#23501](https://github.com/the-omega-institute/trureturing/issues/23501) fixes the reading:

$\{f,g\}$ is IC if and only if $x\mapsto(f(x),g(x))$ is injective and $\Gamma(f,g)$ is acyclic.

Injectivity is precisely the source's complementarity condition: every nonempty intersection of an $f$-level set and a $g$-level set is a singleton (lines 507–508). The characterization is proved, for every finite domain, without the restriction $n\ge2$. The definitions and source locators are also recorded in [the literature note](../Library/Observer/gudder2019finiteconvexeffect.md).

## Motivation

Gudder (2019), arXiv:1912.05110v1, Section 5, line 433, asks about pairs of individually incomplete observables:

> For example, we would like to characterize pairs of observables $(A_1,A_2)$ that are informationally complete where $A_1$ and $A_2$ are not.

The section reduces the sharp classical setting to random variables on a finite probability space. Its Theorem 5.2 gives strong complementarity as a sufficient condition and complementarity as a necessary condition; neither converse is asserted. The forest condition fills the gap between these two conditions using only the two level-set partitions. It determines when separate marginal distributions identify every underlying probability weight, including weights with zero coordinates.

## Gap

The bounded literature check recorded in #23501 reports:

- the v1 source explicitly leaves this characterization open; the arXiv record lists only v1 and no journal reference;
- an OpenAlex lookup reported two citing works, Filippov–Gudder–Heinosaari–Leppäjärvi (2020), arXiv:1912.08538, and Leppäjärvi (2021), arXiv:2106.03588, with no characterization reported in either;
- the orchestrator's searches of Gudder's related work, including arXiv:1802.01265 (2018) and arXiv:2108.07925 (2021), found no characterization;
- the issue identifies classical incidence-matrix and transportation-polytope theory as prior art for the underlying mechanism, but reports no source applying it to this question;
- repository searches reported no existing record of arXiv:1912.05110.

`not-found-in-searched-scope`. This is a bounded report of the search in #23501, not an assertion of worldwide novelty.

## Route

All the module's lemmas below concern a finite type $\alpha$ with `Fintype α` and `DecidableEq α`, and real-valued maps $f,g:\alpha\to\mathbb R$.

1. **Replace distributions by level sums.** `distribution_eq_iff_fiber_sums`, for any real weights $\mu,\nu$ and any $f$ on this finite domain, equates equality of distributions on all subsets of $\mathbb R$ with equality of the sums on every $f$-level set. No probability hypothesis is needed for this lemma. Singleton sets give one direction; finite grouping by values gives the other.
2. **Exclude repeated joint values.** `not_injective_not_ic` assumes that $x\mapsto(f(x),g(x))$ is not injective. Distinct points with the same joint value give distinct point-mass probabilities with equal distributions under each map. Thus `ic_injective`, assuming `IsICPair f g`, obtains injectivity.
3. **Construct signed trail weights.** `walk_weights` assumes joint injectivity and a walk $p$ from $u$ to $v$ in `fiberGraph f g` satisfying `p.IsTrail`. It constructs $w:\alpha\to\mathbb R$ with $|w(x)|\le1$, nonzero exactly at the points whose edges occur in $p$. Its $f$-level sum at $a$ is $\mathbf{1}_{u=\operatorname{inl}(a)}-\mathbf{1}_{v=\operatorname{inl}(a)}$; its $g$-level sum at $b$ is $\mathbf{1}_{v=\operatorname{inr}(b)}-\mathbf{1}_{u=\operatorname{inr}(b)}$. The signs depend on the direction in which an edge crosses the bipartition.
4. **Turn a cycle into indistinguishable probabilities.** `zero_fibers_not_ic` assumes a nonzero real weight $w$, the bound $|w(x)|\le1$ at every point, and zero sums on every $f$-level set and every $g$-level set. Nonzeroness implies $n=|\alpha|>0$; the lemma constructs the distinct probability weights $\mu(x)=(1+w(x))/n$ and $\nu(x)=1/n$ with equal distributions. `cycle_not_ic` assumes joint injectivity and that `fiberGraph f g` is not acyclic. A cycle is a nonempty closed trail, so `walk_weights` gives a nonzero weight whose endpoint contributions cancel, satisfying all the hypotheses of `zero_fibers_not_ic`. Hence an IC pair with an injective joint map has an acyclic graph, as stated in `ic_acyclic`.
5. **Use a leaf in the nonzero support.** `injective_acyclic_ic` assumes joint injectivity and acyclicity of `fiberGraph f g`. Given probability weights $\mu,\nu$ with equal distributions under both maps, put $w=\mu-\nu$. Every level sum is zero. If $w\ne0$, `supportGraph f g w` is an acyclic subgraph with finitely many edges, by `supportGraph_edge_finite`. A component containing an edge from a nonzero coordinate is a nontrivial tree; it has finitely many edges and is locally finite. These are the hypotheses of `SimpleGraph.IsTree.exists_ne_and_degree_eq_one`, which supplies a degree-one vertex. Joint injectivity makes its level sum equal to the single nonzero weight on its incident edge, a contradiction. This leaf argument is applied to that nontrivial component, not to isolated vertices of the ambient graph. Therefore $\mu=\nu$.

`result` combines these directions into the stated equivalence.

## Falsifier

The settlement would not answer the source's question if informational completeness or the graph encoded different data. The module uses:

- probability weights with every coordinate nonnegative and total mass one, via `CycleSingleCutMinimax.Probability`;
- distributions as functions on every subset of $\mathbb R$, not just expectations or a joint distribution;
- two tagged copies of the real line, so equal real numbers occurring as an $f$-value and a $g$-value remain different vertices;
- a simple fiber graph, which merges repeated joint values, together with an explicit injectivity condition that detects this multiplicity.

The real vertex set need not be finite: its edge set is finite, and values outside the ranges are isolated. The empty domain has no probability weight of total mass one, so its IC condition is vacuous; its joint map is injective and its graph has no edges. On a singleton domain there is one probability weight, an injective joint map, and one edge. Both cases are included in `result`.

## Evidence

The canonical source is `D5/S3/Observer/Tomography/InformationallyCompletePairForest.lean`.

- **Proof.** It proves `result : IsICPair f g ↔ Function.Injective (fun x => (f x, g x)) ∧ (fiberGraph f g).IsAcyclic` for every finite type with decidable equality and every two real-valued maps on it.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Observer/Tomography/InformationallyCompletePairForest.lean.json`.

Declaration statements:

- `result`: `sha256:fc0c64cba301bfc4d4b0d6febc6bfc88ecd450e38afde6c692ba84291441183d`.

## Triage

Tier 1 open problem of a 2019 arXiv paper, preregistered in issue #23501 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every finite type $\alpha$ with decidable equality and every $f,g:\alpha\to\mathbb R$, equality of the two distributions determines every probability weight uniquely if and only if the joint value map is injective and the bipartite fiber graph is acyclic.

**Computed, not formalized** (codex-cli, exact enumeration): across all pairs of set partitions on labelled domains of zero through six points, no disagreement was observed between full column rank of the stacked block-incidence matrix and the conjunction of joint injectivity and acyclicity of the simple bipartite graph.

**Argued, not formalized.**

- *Why the rank comparison tests the same information.* For a nonempty finite domain, the stacked block-incidence matrix sends a real weight to its two lists of level sums. Full column rank makes equal marginal lists imply equal weights. Conversely, a nonzero kernel vector has total sum zero, by summing the $f$-block equations. Scale it to have absolute coordinates at most one; perturbing the uniform probability as in `zero_fibers_not_ic`, with the nonzero, bounded, zero-level-sum hypotheses all satisfied, gives distinct probabilities with the same marginal lists. Thus the obstruction concerns identification of probability weights as well as signed weights. The empty-domain matrix has no columns and no kernel obstruction.
- *Both conditions are sharp.* With two points and both maps constant, the graph is a single edge but the joint map is not injective; the two point masses are indistinguishable, as in `not_injective_not_ic`. Gudder's Example 5 has $P(f)=\{\{1,2\},\{3,4\}\}$ and $P(g)=\{\{1,3\},\{2,4\}\}$ (TeX lines 563–586). Here the joint map is injective and the graph is a four-cycle, meeting both hypotheses of `cycle_not_ic`. Adding $\varepsilon(1,-1,-1,1)$ to the uniform probability, with $0<\varepsilon\le1/4$, preserves all four block masses and gives a distinct probability. Complementarity alone therefore leaves an alternating cycle ambiguity.
- *The source's sufficient condition is stronger than necessary.* Strong complementarity means every point is a singleton block for at least one map (TeX lines 528–533). It implies joint injectivity, since a singleton block cannot contain a second point with the same joint value. Every edge of its graph has a degree-one endpoint, which excludes cycles. A three-edge path is a forest even though its middle edge has neither endpoint of degree one. For instance, take $f=(0,0,1)$ and $g=(0,1,1)$: both maps repeat a value, but the $g$-block at $0$ determines the first mass and the $f$-block at $1$ determines the third; total mass determines the second. This gives an IC pair outside strong complementarity and outside individual injectivity, matching the form of the second pair in the source's Example 3.
- *Relabelling extends the criterion.* For maps from a finite domain into arbitrary value sets, restrict to their finite images and injectively label each image by real numbers. This preserves every level set and identifies the active bipartite graphs, hence preserves both marginal information and cycles. Applying `result` to the relabelled maps gives the corresponding criterion; a compiled theorem for arbitrary codomains is not supplied here.
- *Effect on the paper and neighbouring questions.* Theorem 5.2's necessary and sufficient conditions remain valid and fit inside the characterization; Example 5 is explained by its four-cycle. The open question ends Section 5, and the subsequent Section 6 does not state a theorem conditional on its answer. The broader motivation concerning general observables is not settled: more than two random variables, general non-sharp convex effect algebras, and Hilbert-space quantum observables are outside `result`. Characterizations in those settings and quantitative recovery from approximate distributions remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenAlex citation lookup, the readings of the two citing works, the related-work searches, and the transportation-polytope literature comparison are reports from #23501; those external readings were not independently reproduced here. The source TeX, its quoted question and definitions, and the arXiv version/DOI record were checked directly. The earlier repository-search results are likewise the preregistration's report, not a new exhaustive search.

The enumeration and the arguments in "Computed, not formalized" and "Argued, not formalized" are not additional Lean results. In particular, the identification of source complementarity with joint injectivity, the matrix-rank formulation, the concrete partition examples as separate instances, the comparison with strong complementarity, and the arbitrary-codomain relabelling have no separate compiled declarations here. The assessment of dependencies in the source is a textual comparison, not a compiled result. The finite enumeration makes no claim about untested domain sizes. Extensions to more variables, infinite domains, non-sharp or quantum observables, and quantitative stability are not verified by this module.
