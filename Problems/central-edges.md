---
slug: central-edges
bibkey: dovgosheyrovenska2026centraledges
doi: 10.48550/arXiv.2610.11596
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result
url: https://arxiv.org/abs/2610.11596v1
---

# Three-central edge extremality against all metrics

## Problem

Dovgoshey and Rovenska, *On the Graph Corresponding to Center of Distances of
Metric Space*, arXiv:2610.11596v1, Conjecture 4.2, p. 13, assert an equivalence
for every finite ultrametric space $X$ with $|X|\ge4$ and three central distances.
The center is
$C(X)=\{t\ge0:\forall p\in X\;\exists y\in X,\ d(y,p)=t\}$.
The central graph joins distinct vertices whose distance belongs to $C(X)$;
the diametrical graph joins vertices at the diameter.

Clause (i) says that the diametrical graph is complete bipartite on a partition
$X=A\sqcup B$ with $\min(|A|,|B|)=2$, and that the central graph is its union
with one star on each part. Clause (ii) says that its central graph has at most
as many edges as every metric space $Y$ with $|Y|=|X|$ and $|C(Y)|=3$.
The comparator is unrestricted: it need not be ultrametric.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Definition 1.1, nonnegative center including zero | `center` | The realizing point may depend on the base point. |
| Definition 1.2, simple central graph | `centralGraph` | `SimpleGraph.fromRel` excludes loops; metric symmetry gives the stated unordered adjacency. |
| Definition 2.14, diameter graph | `diametricalGraph` | `Metric.diam` on the whole carrier. |
| Finite ultrametric, order at least four, three central values | `claim` quantifiers and hypotheses on $X$ | No restriction omitted. |
| Complete bipartite partition, smaller part of size two, two stars | `conditionI` | Disjoint sets cover the carrier; subtype star centers ensure nonempty parts. Graph maps preserve the original carrier. |
| Every equal-order three-central metric comparator | `claim` quantifiers on $Y$ and edge inequality | No ultrametric assumption on $Y$. |
| Equivalence of (i) and (ii) | `claim` biconditional | `result` proves its literal negation. |

`Fintype` supplies the source finiteness. `Nat.card` counts actual center values
and unordered edges. No binder adds a condition absent from the source on the
nonempty finite carriers in question. The five public definitions retain the
preregistered expressions; the module uses the existing metric and graph
constructions rather than redefining those constructions.

## Motivation

The frozen settling declaration is
`D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result`.
It refutes the published assertion under its unrestricted comparator class.
The source and binding conventions are identified in
[preregistration #22906](https://github.com/the-omega-institute/trureturing/issues/22906).
The source note is [dovgosheyrovenska2026centraledges](../Library/Geometry/dovgosheyrovenska2026centraledges.md).

## Gap

The implication from the proposed bipartite-and-stars structure to extremality
fails. Sparse central graphs of ordinary metrics are allowed competitors.
The four-point settlement does not provide a Lean theorem for the sharp
unrestricted minimum, an all-order counterexample family, or the version in
which the comparator is restricted to ultrametrics.

## Route

On $\mathrm{Fin}\,4$, pull back the $2$-adic metric along $0,1,2,3$.
The center is $\{0,1/2,1\}$. Its central graph has six edges; its diametrical
parts are $\{0,2\}$ and $\{1,3\}$, with one single-edge star on each part.
For the comparator, pull back the real metric along $0,4,5,9$.
Its center is $\{0,4,5\}$ and its four central edges are
$\{0,1\},\{0,2\},\{1,3\},\{2,3\}$.
Thus (i) holds and (ii) would require $6\le4$.
These facts occur in the private proofs used by `result`; they are not separate
public general theorems.

## Falsifier

The settled source assertion is `claim`, and the kernel-checked theorem is
`result : ¬ claim`. A failure of any metric condition, exact center count,
partition-and-stars identity, equal carrier size or strict edge comparison
would invalidate this witness. The theorem verifies all these obligations
within the same two induced metric structures.

## Evidence

Kernel evidence: `D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges.result`.
The axiom closure of every public declaration is contained in
$\{\mathtt{propext},\mathtt{Classical.choice},\mathtt{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There are no other public theorem or owner-publication audit targets.

### Exact finite experiment

The [experiment directory at commit b43e249214c62d9db0aa173ebce49fee6c792470](https://github.com/the-omega-institute/trureturing-experiments/tree/b43e249214c62d9db0aa173ebce49fee6c792470/docs/reports/central-distance-ultrametric-edges)
contains `check.py`. The immutable script was extracted with
`git -C /Users/auric/trureturing-experiments show b43e249214c62d9db0aa173ebce49fee6c792470:docs/reports/central-distance-ultrametric-edges/check.py`.
The executed command was
`python3 /Users/auric/.sshx/c728f5f9ce837ffe6490c5e2/attempt-1/check.py`, exit 0.
Its SHA-256 is `632f89f2254e25666c83fff36e78c82d263199b8f0f2091484c1bc4378b56005`.
Exact rational checks verify the family for $n=4,\ldots,32$: the ultrametric and
metric inequalities, exact centers, condition (i), unordered edge counts,
disjoint spanning covers, and $3n-6>2\lceil n/2\rceil$.
The experiment uses a separate family of rational distance tables; its
four-point comparator is not the real-line comparator used by Lean.

The same script exhausts symmetric distance tables with positive entries in
$\{1,2,3\}$ for $n=2,3,4$. It counts respectively $3,24,482$ metric tables and
$3,12,60$ ultrametric tables. Its checks reproduce the paper's Theorem 3.10
bound on nonempty central graphs and Theorem 3.13 bound and star equality in
that finite scope. These are computed checks, not general Lean theorems.

## Triage

| Target item | Status | Evidence and scope |
| --- | --- | --- |
| Four-point refutation | proved | Kernel-checked `D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges.result`, the literal negation of `claim`. |
| All-order family $n=4,\ldots,32$ | computed | The immutable exact checker above, exit 0, verifies the stated conditions at each of these 29 orders. No unbounded inference follows from this computation. |
| Sharp unrestricted lower bound and all-order realization | open | The incidence/edge-cover argument and proposed realization in #22906 are a route; no general theorem for them is delivered in Lean. |
| Comparator restricted to ultrametrics | open | The real-line comparator does not settle that modified assertion. |

### What the settlement shows

The proved settlement separates the proposed structure from unrestricted
metric extremality. In the four-point instance the structure gives all six
edges, while the ordinary metric comparator has only four.
The explanation is that each positive central distance supplies an incident
edge at every vertex; an unrestricted metric can realize sparse disjoint
spanning covers. This explains the construction, without asserting a new
kernel-checked lower-bound theorem.

The finite family computation shows the same strict gap, $3n-6$ versus
$2\lceil n/2\rceil$, for exactly $4\le n\le32$. Sharpness for all orders and
a uniform family theorem remain open formalization targets. Restricting the
comparator to ultrametrics is the nearest unresolved variant. The source's
Theorems 3.10 and 3.13 precede this conjecture and are not refuted by it;
Conjecture 4.1 and the adjoining question remain separate problems. No source
theorem in the paper uses Conjecture 4.2 as a proved premise.

### Literature status

The screen recorded in #22906 identifies arXiv v1, no exact-title journal
record among five Crossref returns, and zero Semantic Scholar citations.
The recorded author-work, arXiv terminology, MathOverflow, Zenodo and
repository screens found no settlement in their stated windows. OpenAlex
returned HTTP 429. These are bounded literature readings, and completeness is
`ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Completeness of the external literature screen; OpenAlex citation coverage;
and originality of the all-order construction beyond the screened sources.
The general lower bound, all-order realization, and ultrametric-comparator
variant are not established by this module.
