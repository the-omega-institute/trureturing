---
slug: bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices
bibkey: bochniak2025quantumtwins
doi: 10.48550/arXiv.2502.10521
url: https://arxiv.org/abs/2502.10521v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result
---

# Quantum twins in three finite classical graphs

## Problem

Bochniak, Chełstowski, Kasprzak and Sołtan, “Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings”, arXiv:2502.10521v2, Question 3.17, p. 13:

> Do the above-mentioned graphs possess quantum twin vertices?

The graphs are $K_2\mathbin\square K_5$, $C_4\mathbin\square C_3$ and the tesseract $Q_4$. Definition 3.8 requires two distinct actions of a compact quantum group whose compositions with the adjacency operator agree. Issue [#19959](https://github.com/the-omega-institute/trureturing/issues/19959) fixes the stronger algebraic claim: for each graph and every unital complex algebra $B$, no two distinct unital complex algebra homomorphisms $\mathbb C^V\to B$ agree after adjacency.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Classical function algebra and adjacency | `adjacencyOperator`, with function carrier $V\to\mathbb C$ and `Matrix.toLin'` of `SimpleGraph.adjMatrix` | Literal preregistered expression |
| Two different actions agreeing after adjacency | `HasTwinsIn` retains distinctness and agreement, allowing arbitrary `AlgHom` targets | A strengthening: excluding all such homomorphisms excludes actions |
| $K_2\mathbin\square K_5$ | `prism` | Mathlib complete graphs and Cartesian product |
| $C_4\mathbin\square C_3$ | `cycleProduct` | Mathlib cycle graphs and Cartesian product |
| Tesseract | The literal Hamming-distance-one graph on `Fin 4 → Bool` in `claim` | The proof uses `Hypercube.hypercube` through the private equality `tesseract_eq_hypercube`; no duplicate graph definition |
| Negative answer for the three graphs | `claim`, proved by `result` | Every complex algebra $B$, without commutativity or finite-dimensionality assumptions |
| General twin-free hypothesis | `algHom_eq_of_adjacency_eq` assumes injectivity of adjacency rows | A hypothesis of the general lemma, discharged for all three graphs in `result`; not an extra settlement premise |

The compact quantum group structure and the action-to-homomorphism passage are mathematical interpretation, not additional Lean declarations in this module.

## Motivation

`D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result` answers the named question in the negative through the exact preregistered strengthening. Its public general lemma, `algHom_eq_of_adjacency_eq`, treats every finite twin-free simple graph and every complex target algebra. The source's singular adjacency matrices do not prevent the neighbourhood indicators from generating the function algebra multiplicatively.

## Gap

The source leaves the three graphs as candidates and asks whether quantum twins are broader than ordinary twins for classical graphs. The literature screen recorded in #19959 reads v1 and v2, searches arXiv for quantum twins and quantum Mycielskians, and screens Crossref results. It found no settlement in that scope. Source Remark 3.9 already supplies ordinary twins implying quantum twins. Literature completeness is ASSUMED-UNVERIFIED; no exhaustive novelty claim is made.

## Route

For a finite twin-free graph, write $h_v=A_G\delta_v$. At $x$, the product of the $h_v$ with $x\sim v$ and the $1-h_v$ with $x\not\sim v$ has value one. At a different vertex $y$, distinct adjacency rows supply a vanishing factor. Thus this product is $\delta_x$. The private `separating_product_eq_single` proves this identity.

The equalizer subalgebra of two homomorphisms agreeing after adjacency contains every $h_v$, hence every such product, every $\delta_x$, and every function by its finite point-indicator expansion. The public `algHom_eq_of_adjacency_eq` proves equality of the homomorphisms. The three finite row-injectivity checks occur inside `result`; `no_twins_of_twin_free` is the private consumed existential-negation consequence. The proof uses the frozen Boolean hypercube definition directly and does not require adjacency-matrix invertibility.

## Falsifier

For the formal claim, a target complex algebra and two distinct unital homomorphisms agreeing after adjacency for any of the three graphs contradict `result`. For the source interpretation, a compact quantum group action that does not provide the stated unital complex algebra homomorphism would invalidate the bridge. A prior literature settlement would invalidate a priority claim, not the algebraic theorem. The bounded literature screen does not exclude work outside its scope.

## Evidence

### Formal evidence and escape audit

The settling declaration is `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result`, with the expanded proposition in its Blueprint. The general witness is `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.algHom_eq_of_adjacency_eq`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$; the delivery PR gives the compiled readings.

Escape audit unfinished: [#19959](https://github.com/the-omega-institute/trureturing/issues/19959), for both public theorems named above. The attempted dependent-family registrations lack bad-realization variation, whole-family sensitivity, actual observational dependence and exact source-occurrence reconstruction. No successful Reg source or declared-validated registration is asserted.

### Experiment

The exact-arithmetic program is [the experiment directory at commit `9f3dcb3baf7b3b158f03f978e2374438ab86873f`](https://github.com/the-omega-institute/trureturing-experiments/tree/9f3dcb3baf7b3b158f03f978e2374438ab86873f/docs/reports/bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices), file `check.py`, SHA-256 `ac23852c0ba3c73e653eb13498b478dca8b75a4e91d3ea1b12395e56d153fed0`. The pinned blob was read with `git -C /Users/auric/trureturing-experiments show 9f3dcb3baf7b3b158f03f978e2374438ab86873f:docs/reports/bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices/check.py` and materialized outside the main repository. `/opt/homebrew/bin/python3 /Users/auric/.op-scratch/op/qtw2502-stageb/check.py` exits 0.

| Graph | Vertices | Degree | Adjacency rank | Ordinary twin pairs | Product identity |
| --- | --- | --- | --- | --- | --- |
| $K_2\mathbin\square K_5$ | 10 | 5 | 6 | 0 | $p_x=\delta_x$ for all vertices |
| $C_4\mathbin\square C_3$ | 12 | 4 | 11 | 0 | $p_x=\delta_x$ for all vertices |
| $Q_4$ | 16 | 4 | 10 | 0 | $p_x=\delta_x$ for all vertices |

All three adjacency matrices are singular. The control $C_4$ has twin pairs $(0,2)$ and $(1,3)$, so its neighbourhood indicators do not distinguish those pairs. These are computed readings for exactly these four graphs; they are not a uniform computation over graph families. The stronger algebraic assertion for the three target graphs is supplied by `result`.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| Settlement | Proved, kernel-checked: `result` | Negative answer for all three graphs, via the exact strengthening over arbitrary complex algebras |
| Escape witness | Proved, kernel-checked: `algHom_eq_of_adjacency_eq` | Every finite twin-free simple graph; noncommutative targets and empty vertex types are permitted |
| Mechanism | Proved in prose below; the twin-free product identity is also kernel-checked by private `separating_product_eq_single` | Neighbourhood indicators generate the finite function algebra exactly when the graph is twin-free |
| Broader consequence and source's general comparison | Proved in prose below using the general lemma and source Remark 3.9 | Quantum twins and ordinary twins coincide for finite classical simple graphs; the quantum-group bridge and converse action construction are not formalized in Lean |
| Graph and product checks | Computed: experiment entry above | Exactly the three target graphs and control $C_4$, with the ranks and twin pairs displayed above |
| Novelty and literature | Open as an exhaustive claim; literature reading: #19959 | No settlement found in the stated screen; completeness ASSUMED-UNVERIFIED |
| Formal handoff | Proved, kernel-checked: `result` and its live helpers | The retained public surface has two theorems; there are no remaining Lean goals in their proofs |

For the generation equivalence, the forward twin-free direction is the product construction in Route. Conversely, if distinct $x,y$ are twins, every $h_v$ agrees at $x,y$. Functions agreeing at these two vertices form a unital subalgebra, so the subalgebra generated by the $h_v$ lies inside it. It cannot contain $\delta_x$, whose values at $x,y$ differ. This proves the converse in prose; no additional public Lean theorem is claimed.

For the quantum-twin equivalence, if there are no ordinary twins, the general algebraic lemma forces any two actions agreeing after adjacency to coincide, because actions are unital complex algebra homomorphisms. If ordinary twins exist, source Remark 3.9 supplies distinct $\mathbb Z_2$ actions agreeing after adjacency. These two implications answer the source's general classical-graph comparison mathematically. The source's six-vertex example becomes an instance of the general twin-free direction; its other quantum-graph results are not re-proved here. Extension of this equivalence to nonclassical quantum graphs is open.

The separating construction needs neither a nonempty vertex type nor a commutative target algebra, and is not limited to the three graphs. Dropping twin-freeness fails already for the two evaluation homomorphisms at ordinary twins, which agree on every adjacency output and differ on a point indicator. The source's quantum action conditions remain part of the interpretation boundary.

## ASSUMED-UNVERIFIED

Literature completeness and absence of prior settlements outside the searched scope are ASSUMED-UNVERIFIED. The compact quantum group formalism, the action-to-AlgHom bridge and the converse action construction are not formalized in Lean. The four-slot escape audit is unfinished under #19959. No exhaustive literature novelty, nonclassical quantum-graph classification or completed escape registration is claimed.
