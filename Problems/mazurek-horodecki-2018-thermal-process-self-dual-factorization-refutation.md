---
slug: mazurek-horodecki-2018-thermal-process-self-dual-factorization-refutation
bibkey: mazurekhorodecki2018decomposability
doi: 10.1088/1367-2630/aac057
url: https://arxiv.org/abs/1707.06869v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result
---

# A self-dual irreducible extreme thermal process can factor on proper subspaces

## Problem

P. Mazurek and M. Horodecki, *Decomposability and convex structure of thermal processes*, New J. Phys. 20, 053040 (2018), arXiv:1707.06869v2, Section IV.B, “Detailed balance symmetry”, Conjecture 1:

> If an extremal TP $C$ for $d$ dimensional space is decomposable into a sequence of extremal TPs $A$, $B$, each acting non-trivially on at most $d-1$ dimensional space: $C=AB$, and $C$ is not a direct sum of extremal TPs from lower dimensional subspaces, then $C$ is not self-dual with respect to the conjugation associated with the operator scalar product.

This quotation is from `manuscript.tex`, lines 425–427, read from the [arXiv v2 source](https://arxiv.org/src/1707.06869v2), md5 `69e7001dd049721e95968ea93ad550c2`. The source's matrix characterization of thermal processes is at line 159, its discussion of proper-subspace factors at lines 208–211, and its conjugation at lines 415–420. These passages are also located in [the literature note](../Library/StatisticalMechanics/mazurekhorodecki2018decomposability.md).

Issue [#20157](https://github.com/the-omega-institute/trureturing/issues/20157) fixes the following precise reading. For every $d\ge2$ and every positive, pairwise distinct weight vector $g\in\mathbb R^d$ with $g_i\le g_0$ for every $i$, let

$\mathrm{TP}(g)=\{T\in\mathbb R^{d\times d}:T_{ij}\ge0\text{ for all }i,j,\ \sum_iT_{ij}=1\text{ for all }j,\ Tg=g\}$.

For all extreme points $A,B,C$ of this set, suppose $C=AB$, each of $A$ and $B$ has a diagonal entry equal to one, and there is no nonempty proper set of levels whose two cross-blocks in $C$ are zero. The claim concludes that $C$ is not self-dual: $C_{ij}g_j\ne C_{ji}g_i$ for some $i,j$. The module calls these predicates `thermalProcesses`, `actsOnFewerLevels`, `irreducible` and `selfDual`, and calls the universal implication `claim`.

The universal claim is refuted. Its additional restriction to distinct weights makes it weaker than the source's unrestricted conjecture, so refuting this restriction also refutes Conjecture 1.

## Motivation

The problem concerns whether detailed balance obstructs building an extreme thermal process from extreme operations that each leave some energy level untouched. Such an obstruction would constrain the geometry and the required elementary operations of higher-dimensional thermal-process sets. The source motivates Conjecture 1 by the three-level examples and explicitly excludes the direct-sum construction using factors on disjoint subspaces. The counterexample uses overlapping active levels and a product without any block decomposition.

## Gap

The bounded literature check in #20157 reports:

- The orchestrator read arXiv v2, which contains Conjecture 1.
- Semantic Scholar listed 31 citing works; the orchestrator screened the TeX sources of 22 arXiv citing works for the conjecture, self-duality and decomposition. No settlement was found in that screened set. The listed examples include arXiv:1810.05578, 2111.12130, 2209.15213, 2212.04305, 2303.12840, 2410.14550 and 2609.04057.
- The GPT Pro research report identifies a related reversible five-state matrix in Kirkland, Electron. J. Linear Algebra 39 (2023), 556–571, Example 3.8, up to permutation and transpose, but reports no factorization there into extreme processes on proper subsets. It also reports no resolution in Hack–Mendl, J. Phys. A 58, 315302 (2025), or in its SSRN, Zenodo and OSF searches. These readings are not independently reproduced here.
- The orchestrator reports no existing repository record in its Problems, Library and issue searches for the arXiv identifier.

`not-found-in-searched-scope`. This is a bounded search outcome, not an exhaustive novelty claim.

## Route

Use $d=5$, weights $g=(8,7,4,2,3)$, and the following matrices, indexed from zero:

$\displaystyle A=\begin{pmatrix}0&1&0&\tfrac12&0\\ \tfrac14&0&1&\tfrac12&0\\ \tfrac12&0&0&0&0\\ \tfrac14&0&0&0&0\\ 0&0&0&0&1\end{pmatrix},\qquad B=\begin{pmatrix}1&0&0&0&0\\ 0&\tfrac17&1&1&0\\ 0&\tfrac17&0&0&1\\ 0&\tfrac27&0&0&0\\ 0&\tfrac37&0&0&0\end{pmatrix}$.

$\displaystyle C=\begin{pmatrix}0&\tfrac27&1&1&0\\ \tfrac14&\tfrac27&0&0&1\\ \tfrac12&0&0&0&0\\ \tfrac14&0&0&0&0\\ 0&\tfrac37&0&0&0\end{pmatrix}$.

1. **Thermal membership and weights.** The entries are nonnegative, every column sums to one, and all three matrices preserve $g$. Its entries are positive and distinct, with $g_0$ maximal.
2. **Extremality.** Nonnegativity forces both terms of any strict convex decomposition to vanish wherever the decomposed matrix vanishes. For each displayed support, the column sums and Gibbs-preservation equations determine every remaining entry uniquely. The module proves this support uniqueness and applies it to Mathlib's `Set.extremePoints`.
3. **Proper-subspace factorization.** The product is $C=AB$, with $A_{44}=1$ and $B_{00}=1$.
4. **No block decomposition.** The non-loop support edges of $C$ are $0$–$1$, $0$–$2$, $0$–$3$ and $1$–$4$. Any partition with zero cross-block entries must put the endpoints of each edge on the same side, hence must put all five levels on the same side.
5. **Detailed balance.** Entrywise rational equalities give $C_{ij}g_j=C_{ji}g_i$ for every pair. The proof of `result` applies the assumed universal `claim` to these certificates and obtains a contradiction.

## Falsifier

The source-to-formal bridge would fail if extremality, proper-subspace action, direct sums or self-duality had materially different meanings. Here:

- Extremality is Mathlib's extreme-point predicate for the entire set $\mathrm{TP}(g)$, not for a selected family or support face.
- `actsOnFewerLevels` means exactly that some $T_{kk}=1$. For a nonnegative column-stochastic matrix preserving positive $g$, this fixes the whole level: the other entries of column $k$ vanish by its column sum, and the other entries of row $k$ vanish by Gibbs preservation. The argument is given below.
- `irreducible` means exactly the absence of a nontrivial block-diagonal partition. This excludes, in particular, a direct sum of lower-dimensional extreme thermal processes.
- `selfDual` is exactly detailed balance. For $D=\operatorname{diag}(g)$, the source's conjugation $\widetilde T=DT^{\mathsf T}D^{-1}$ satisfies $\widetilde T=T$ precisely when $T_{ij}g_j=T_{ji}g_i$.
- The weights need not sum to one in Lean. Normalizing to $g/24$ leaves the thermal-process set and detailed-balance equations unchanged. The normalization and the Gibbs-energy interpretation are algebraic bridges described below, not additional formal theorems.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.lean` (309 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.lean.json`, statement `sha256:1117da27d6c489125591d74ae27b2db4820cbe70b529b3ba7e2eab6eb286830c`.

Declaration statements:

- `result`: `sha256:98408a97a2f370a0983f175b6df78992cbf682c23dee5ba70b2b437fb1e74757`;
- `claim`: `sha256:fc8dd9bf7c359d517d597c8d1bfc8d6fc61428c3852638d14e768f93635fbe6b`.

## Triage

Tier 1 conjecture of a 2017 preprint published in 2018, preregistered in issue #20157 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. No escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal `claim` in Problem is false. It is not true that, for every $d\ge2$ and positive, pairwise distinct $g$ with $g_0$ maximal, every extreme product $C=AB$ of extreme thermal processes, with each factor fixing a level and $C$ having no nontrivial block-diagonal partition, is non-self-dual. The theorem's type is $\neg\mathrm{claim}$; it does not assert a family in every dimension.

**Computed, not formalized** (exact rational arithmetic for the displayed five-level instance):

- The linear column-sum and Gibbs-preservation constraint matrices restricted to the supports of $A,B,C$ have ranks $8,8,9$, respectively, equal to their support sizes. These rank computations are separate from the Lean support-uniqueness certificates.
- Neither factor is self-dual: $A_{01}g_1=7$ while $A_{10}g_0=2$, and $B_{12}g_2=4$ while $B_{21}g_1=1$.
- The factors do not commute: $AB\ne BA$.

**Argued, not formalized.**

- *Mechanism.* The active level sets $\{0,1,2,3\}$ and $\{1,2,3,4\}$ overlap. They produce the connected symmetric weighted-flow matrix
  $\displaystyle CD=\begin{pmatrix}0&2&4&2&0\\ 2&2&0&0&3\\ 4&0&0&0&0\\ 2&0&0&0&0\\ 0&3&0&0&0\end{pmatrix}$.
  Thus balance of the composite flows need not be inherited from either factor. The direct-sum exclusion removes the disjoint-subspace example mentioned by the source at line 428, but does not exclude this overlapping construction. Noncommutation alone also does not restore the conclusion, as the exact computation above shows.
- *A sufficient added condition.* Conjugation reverses products: $\widetilde{AB}=D(AB)^{\mathsf T}D^{-1}=(DB^{\mathsf T}D^{-1})(DA^{\mathsf T}D^{-1})=\widetilde B\widetilde A$. Consequently, if both factors are self-dual, their product is self-dual exactly when they commute. Requiring self-dual factors and $AB\ne BA$ is therefore sufficient for the original conclusion; neither extremality nor irreducibility is needed for this implication. The displayed factors do not meet the added self-duality requirement. This is an algebraic consequence, not a formalized replacement theorem.
- *Restricted statements that survive.* If $T_{kk}=1$, nonnegativity and the column sum give $T_{ik}=0$ for $i\ne k$. Gibbs preservation gives $\sum_{j\ne k}T_{kj}g_j=0$; positivity of $g$ then gives $T_{kj}=0$ for $j\ne k$. Hence two factors fixing the same level have a product with that isolated level, so cannot meet the irreducibility hypothesis. In dimension two, a factor fixing a level is the identity: its other column has no entry into that level and must sum to one. Both factors are therefore identities, and their product is reducible. The dimension-two restriction of `claim` holds vacuously. The existence of counterexamples in dimensions three or four is not settled here.
- *Gibbs normalization and energies.* For any $c>0$, $T(cg)=cg$ is equivalent to $Tg=g$, and detailed balance scales by the same nonzero factor $c$. Thus $g/24$ gives the same process set, extreme points and self-duality condition. At $\beta=1$, set $E_i=\log(8/g_i)$. Then $E_0=0$, the energies are nonnegative and distinct, and $e^{-E_i}=g_i/8$; normalization gives precisely $g/24$. No quantum system–bath dilation is constructed in Lean.
- *Scope and extension.* The formal proof uses one five-level instance. Issue #20157 reports a GPT Pro argument for families in every $d\ge5$ on an open set of Gibbs weights; that argument is not reproduced or used here. No such family conclusion or minimal-dimension classification is claimed.
- *Effect on the paper.* In the concluding discussion, `manuscript.tex` line 848 says: “The conjectured non-decomposibility of self-dual extremal points of Thermal Processes may be a helpful property in the analysis of the geometry of the set of $d$ level Thermal Processes.” This proposed general obstruction is unavailable: detailed balance and the absence of direct sums do not suffice. The source's separate construction of non-decomposable processes in Section III and its three-level enumeration in Section IV.A are not contradicted by a five-level counterexample; their full arguments are not reverified here. The geometry and decomposition program described at lines 428 and 851 remains a research question with the conjectured obstruction removed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The 31-item citation count, the screening of 22 arXiv citing works, the repository search, the Kirkland matrix correspondence and claimed absence of a factorization there, and the Hack–Mendl, SSRN, Zenodo and OSF readings are reports in #20157, not independently reproduced literature checks. The arXiv v2 TeX quotation and the source passages cited above are directly checked.

The rank, individual-factor self-duality and commutation computations are exact computations for the displayed instance, not additional compiled Lean declarations. The arguments labelled “Argued, not formalized”, including normalization, the Gibbs-energy correspondence, the sufficient added condition, the restricted-dimension discussion and the assessment of the paper's dependencies, are not formalized. The general family reported for $d\ge5$ is unverified here. Minimal dimension, robustness over an open weight set and a classification of factorizable self-dual extreme thermal processes are not settled. The source's full three-level enumeration and its other independent results are not reproduced, and no operational quantum dilation or physical implementation is verified.
