---
slug: delascuevas-klingler-netzer-2024-nonfactorizable-doubled-triangle
bibkey: delascuevasetal2024invariantpolynomialdecompositions
doi: 10.1016/j.laa.2024.05.025
url: https://arxiv.org/abs/2109.06680v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result
---

# A nonfactorizable doubled triangle

## Problem

G. De las Cuevas, A. Klingler and T. Netzer, *Polynomial decompositions with invariance and positivity inspired by tensors*, arXiv:2109.06680v2; Linear Algebra and its Applications 698 (2024), 537–588, DOI 10.1016/j.laa.2024.05.025, ask in Question 38:

> Are there non-factorizable $(\Omega,G)$ structures?

This is the verbatim question at lines 1546–1549 of the v2 TeX source `Manuscript_final.tex` (md5 `e601e0a3202f352cba4bf6d4d13e7db4`). Question 38 is also on PDF page 28; the conclusion repeats the existence question at TeX line 2035. Definitions and further quotations are in [the literature note](../Library/QuantumContext/delascuevasetal2024invariantpolynomialdecompositions.md).

The source's definitions at lines 318–332, 425–444 and 1515–1522 give the following reading. A weighted simplicial complex on $[n]=\{0,\ldots,n\}$ assigns natural weights $\Omega(S)$ to vertex subsets, with $\Omega(S)\mid\Omega(T)$ whenever $S\subseteq T$, and nonzero singleton weights. Each maximal nonzero-weight subset $F$ is a facet with $\Omega(F)$ distinct copies. Write $\widetilde{\mathcal F}$ for these multifacets and $\widetilde{\mathcal F}_i$ for those containing $i$. A finite group $G$ acts on vertices preserving weights and on multifacets compatibly with collapse to their underlying facets. Its action on labelings is inverse pullback, ${}^g\gamma(x)=\gamma(g^{-1}x)$.

For each finite index set $\mathcal I$ and labeling $\alpha:\widetilde{\mathcal F}\to\mathcal I$, define
$K_\alpha=\left|\left\{\gamma:\widetilde{\mathcal F}\to\mathcal I:\ \forall i\in[n],\ \exists g_i\in G,\ g_i i=i\ \text{and}\ ({}^{g_i}\gamma)|_i=\alpha|_i\right\}\right|$.
Factorizability requires, for every finite $\mathcal I$, strictly positive real factors $C^{[i]}_\beta$, equivariant under $C^{[gi]}_{{}^g\beta}=C^{[i]}_\beta$, satisfying $\prod_{i\in[n]}C^{[i]}_{\alpha|_i}=K_\alpha^{-1}$ for every global labeling $\alpha$.

Issue [#21655](https://github.com/the-omega-institute/trureturing/issues/21655) fixes the formal `claim` as universal factorizability: for every natural $n$, every such weight function, every finite group and every compatible pair of actions, the structure is factorizable. `result : ¬ claim` refutes that universal assertion and answers the quoted existence question affirmatively.

## Motivation

Factorizability supplies local normalization factors for the source's conversion from separable decompositions over local sum-of-squares polynomials to invariant sum-of-squares decompositions. It is an explicit hypothesis of the rank inequalities in Proposition 39(iii)–(iv), TeX lines 1561–1564. An affirmative answer to Question 38 identifies structures to which those conditional inequalities cannot be applied solely from the complex and action axioms.

## Gap

Issue #21655 records the bounded literature check before any Lean:

- the orchestrator read v2, which retains the question, and reported that arXiv lists v1 and v2;
- the orchestrator's web search found the source, arXiv:1909.01737 and arXiv:2304.13478, without a settlement in that searched scope;
- the search seat reported reading the three Semantic Scholar citing papers arXiv:2211.13532, arXiv:2304.13478 and arXiv:2404.15053 without finding a settlement;
- the orchestrator reported no existing repository issue, module, Library note or dossier addressing the question.

`not-found-in-searched-scope`.

## Route

1. **The fixed complex.** On $\{0,1,2\}$, set $\Omega(S)=1$ for $|S|\le1$, $\Omega(S)=2$ for $|S|=2$, and $\Omega(S)=0$ for $|S|=3$. `triangle_valid` establishes the weighted-complex conditions for this function. For every $S\subseteq\mathrm{Fin}\,3$, `triangle_facets` identifies its being a facet with $S=\{0,1,2\}\setminus\{e\}$ for some $e\in\mathrm{Fin}\,3$. Each edge has two copies. `copy_bijective` identifies the multifacets with $(e,k)\in\mathrm{Fin}\,3\times\mathrm{Fin}\,2$; `copy_incident` says, for every vertex $i$ and such pair, that the copy is incident to $i$ exactly when $i\ne e$.
2. **The fixed actions.** Let $G=\operatorname{Multiplicative}(\mathbb Z/2\mathbb Z)$. The vertex action is trivial. `facetAction` fixes copies under the identity and swaps the two copies of every edge simultaneously under the other element. `triangle_compatible` establishes compatibility for precisely this complex and these two actions.
3. **Eight binary labelings.** For $a,b,c\in\mathrm{Fin}\,2$, `alpha a b c` labels copy $0$ of each edge by $0$ and copy $1$ of the edges omitting $0,1,2$ by $a,b,c$, respectively. For these labelings on this fixed complex with these actions, `count_transfer` transfers the source's stabilizer count to binary functions on the six indexed copies, and `counts` proves $K_{\alpha_{000}}=1$ and $K_{\alpha_{abc}}=2$ for every $(a,b,c)\ne(0,0,0)$.
4. **A necessary product identity.** For any real local factors $C:(i:\mathrm{Fin}\,3)\to(\operatorname{Incident}(\Omega,i)\to\mathrm{Fin}\,2)\to\mathbb R$ on this fixed doubled triangle, let $P_{abc}=\prod_i C_i(\alpha_{abc}|_i)$. `parity_identity` proves $P_{000}P_{011}P_{101}P_{110}=P_{001}P_{010}P_{100}P_{111}$, with no positivity or equivariance hypothesis on $C$. The locality step `restrict_alpha` applies for $a,b,c,a',b',c'\in\mathrm{Fin}\,2$ and $i\in\mathrm{Fin}\,3$ whenever the two triples agree in every coordinate $e\ne i$; their restrictions at $i$ are then equal.
5. **Contradiction.** Assuming factorizability for the fixed complex and actions of steps 1–2, `triangle_not_factorizable` takes $m=2$ in `Factorizable`. The defining equations and `counts` give $P_{000}=1$ and every other $P_{abc}=1/2$. In the identity of step 4 this gives $1/8=1/16$. `result` applies the universal `claim` to this weighted complex, finite group and compatible pair of actions to obtain the contradiction.

## Falsifier

The settlement would miss Question 38 if it changed the allowed complexes, actions, stabilizer count or quantifiers. The module preserves these features:

- `WeightedSimplicialComplex` includes divisibility for all nested vertex subsets and nonzero weight at every singleton. A zero weight on the full triangle is permitted; every natural number divides zero.
- `Multifacet` retains exactly the prescribed number of distinct copies of each maximal nonzero-weight subset. `Compatible` requires both weight invariance and equivariance of collapse. The source explicitly permits fixed vertices with exchanged copies in its double-edge example, lines 1535–1540.
- `K` counts global labelings, with an independently chosen vertex-stabilizing element at each vertex. It counts neither tuples of stabilizer elements nor just a single global group orbit.
- `Factorizable` quantifies over all $m\in\mathbb N$ through $\mathrm{Fin}\,m$, including $m=0$, and requires real positivity, equivariance and every global product equation. The contradiction uses $m=2$. The finite-group scope matches the source's standing convention at line 444.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.lean` (300 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses the binary-element lemma `ExponentialSquareWeightCatalanParity.binary`, the inverse-pullback function action, finite-cardinality transport, finite enumeration with `decide`, and real ring normalization.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.lean.json`, statement `sha256:3bec10a3c59f72c45d68d22acb919164cc64a711bbc9eea1b78361251517721d`.

Declaration statements:

- `result`: `sha256:236deb0ed9b74dc51e28b642e63553b736c8c5c480b196fd392b32f78fad2f3e`;
- `claim`: `sha256:e05a824aba8d3a58e337f7d5e910755dbce3ccb4b6eb78b466c108d66ee6c3c9`.

## Triage

Tier 1 explicitly posed question of the 2024 journal paper, preregistered in issue #21655 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: the fixed counterexample reduces to finite counts and a real product identity | open-problem-resolution |
| `WeightedSimplicialComplex`, `Multifacet`, `collapse`, `Incident`, `Compatible`, `transport`, `K`, `Factorizable`, `claim` | bind-only | none | definitions used by `claim` |
| the complex, action, counting and parity helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is not the case that, for every natural $n$, every weighted simplicial complex on $\mathrm{Fin}(n+1)$, every finite group and every compatible pair of vertex and multifacet actions, the structure is factorizable in the sense of `Factorizable`.

**Computed, not formalized** (exact enumeration and rational elimination; the same readings are recorded by the orchestrator in #21655):

- Across all $64$ binary labelings of the fixed doubled triangle, $K=1$ on $8$ labelings and $K=2$ on $56$.
- Identifying local binary labelings under simultaneous reversal gives $30$ equivariant logarithmic variables. For positive factors, setting $x_i(\beta)=\log(C_i(\beta))/\log2$ gives a system whose exact rational elimination on the $64$ equations gives coefficient rank $22$ and augmented rank $23$. This rank calculation is not part of the formal proof.

**Argued, not formalized.**

- *Mechanism and scope.* On the fixed doubled triangle with the binary labelings $\alpha_{abc}$, each vertex sees only the two coordinates corresponding to its incident edges. For arbitrary real local factors $C$ of the type in `parity_identity`, each of the four possible pairs occurs once on each side at each vertex, giving that lemma's identity. The values supplied by `counts` violate it. Thus deleting positivity, deleting equivariance, or deleting both cannot make these particular product equations solvable. This is a failure of compatibility between local factors and the joint dependence of $K$ on all three edge coordinates. The argument does not establish a classification for other complexes or cycle lengths.
- *Two meanings of freeness.* The witness is connected because every pair of vertices shares an edge. Its nonidentity group element swaps both copies of every edge, so it fixes no multifacet, although it fixes every vertex. The source defines a free action on a weighted simplicial complex by: “We call the action $G$ on the weighted simplicial complex $\Omega$ free if the action of $G$ on $\widetilde{\mathcal{F}}$ is free” (TeX line 437, emphasis removed). Thus connectedness and freeness on multifacets do not imply factorizability. These additional properties are not separate conclusions in `result`'s type.
- *A surviving sufficient condition.* The source states: “This in particular shows that $(\Omega,G)$ is factorizable whenever the action of $G$ on the vertices $[n]$ is free” (line 1531). Indeed, for any weighted complex satisfying the singleton assumption, any compatible actions with free vertex action, and any finite index set, every element fixing a vertex is the identity. Any counted $\gamma$ therefore agrees with $\alpha$ at every incident multifacet. Every facet is nonempty, since the vertex set is nonempty and every singleton has nonzero weight. Hence $\gamma=\alpha$. Conversely, $\alpha$ itself is counted by choosing the identity at every vertex, so $K_\alpha=1$ for every global labeling and the constant choice $C_i(\beta)=1$ gives positive equivariant factors. Empty index sets cause no exception to this argument: it is conditional on a global labeling, and the constant factors are still defined.
- *The double edge survives.* For the source's two fixed vertices with two edge copies exchanged by $C_2$, both vertices see the entire labeling. For every finite index set, the counted labelings are just the given ordered pair and its reversal, with count $1$ when the entries agree and $2$ otherwise. Giving each vertex the factor $1$ in the equal case and $1/\sqrt2$ otherwise is positive, invariant under reversal and has product $K^{-1}$. This verifies the source's statement “Hence, $(\Delta,G)$ is also factorizable” (line 1540), with the factors of lines 1537–1539. The locality obstruction in the doubled triangle is absent here.
- *Effect on the paper.* For a polynomial $p\in\mathcal P$, Proposition 39(iii) states: “If $(\Omega,G)$ is factorizable, then $\textrm{sos-rank}_{(\Omega,G)}(p)\leq\textrm{sep-rank}_{(\Omega,G)}(p)$ for the separable cone over local sos polynomials” (line 1562, rank macros expanded). Part (iv) assumes that $\Omega$ is connected, the action on the complex is free and $(\Omega,G)$ is factorizable; for every $G$-invariant $p\in\mathcal P$ it concludes $\textrm{sos-rank}_{(\Omega,G)}(p)\leq|G|\textrm{sep-rank}_{\Omega}(p)$ for the separable cone over local sos-polynomials (line 1564). These conditional statements are not refuted. The doubled triangle shows that their factorizability premise is not automatic, even under the connectedness and freeness assumptions of part (iv). In the proof of part (iii), the positive invariant normalization factors are chosen at line 1588, and their product equations are used at lines 1598–1600; that construction is unavailable for this witness. No polynomial violating either rank inequality is supplied, and whether either inequality extends to this nonfactorizable structure remains unsettled here. The other open questions in the conclusion are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The v1 contents, the orchestrator's web-search coverage and repository-absence search, and the search seat's readings of arXiv:2211.13532, arXiv:2304.13478 and arXiv:2404.15053 were not independently reproduced. The cited v2 TeX passages and PDF pages 27–29 were read directly; the latter identify Question 38 and Proposition 39 on page 28. The DOI, journal volume, year and pagination agree with the Crossref record for 10.1016/j.laa.2024.05.025.

The full $64$-labeling histogram and matrix ranks are computations, not kernel-verified conclusions. The arguments about connectedness, the two notions of freeness, dropping positivity or equivariance, the surviving free-vertex and double-edge cases, and the consequences for the source's rank inequalities are not separate formal statements of this module. General classification, other cycle lengths and extensions or counterexamples to the rank inequalities for nonfactorizable structures remain open here.
