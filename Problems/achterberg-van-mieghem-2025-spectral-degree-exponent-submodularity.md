---
slug: achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity
bibkey: achterbergvanmieghem2025spectral
doi: 10.48550/arXiv.2502.01815
url: https://arxiv.org/abs/2502.01815v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result
---

# The spectral degree exponent is not submodular

## Problem

M. A. Achterberg and P. Van Mieghem, *The spectral degree exponent of a graph*,
arXiv:2502.01815v1, Section 7, p. 15, asks:

> Several other properties of the SDE have not yet been established, e.g. whether the SDE is submodular or if the SDE can be used successfully in applications to enhance or reduce assortativity.

This is the tier-2 external question preregistered in
https://github.com/the-omega-institute/trureturing/issues/19958.
The settlement is **Refuted** for edge sets on a fixed vertex set.

Definition 2.1 and equation (2.1), p. 1, define the exponent by
$\lambda_1=((1/N)\sum_i d_i^q)^{1/q}$ for a simple undirected nonregular graph.
Theorem 2.2 places it in $[2,\infty]$. Here every exponent used is a finite real
number and $\lambda_1$ is the supremum of the real adjacency spectrum.

### Statement echo

| Source clause or explicit interpretation | Lean counterpart | Fidelity |
| --- | --- | --- |
| Simple undirected graph on $N$ vertices | `SimpleGraph (Fin n)` | Unweighted finite graphs form a subclass of the source's graphs. |
| Degree mean $((1/N)\sum_i d_i^q)^{1/q}$ | `degreePowerMean` | Natural degrees and $n$ are cast to real numbers; both powers are real powers. |
| Nonregular graph | `IsRegular`, negated in `IsSpectralDegreeExponent` | Regularity is exactly existence of a common natural degree, using `SimpleGraph.IsRegularOfDegree`. |
| Largest adjacency eigenvalue | Real-spectrum supremum in `IsSpectralDegreeExponent` | The literal preregistered expression is inlined. The private correspondence `spectral_sup_eq_edgeMax` connects it to the reused `SpikeEdgeEstimate.edgeMax` in the proofs. |
| Finite solution with $q\ge2$ | `IsSpectralDegreeExponent G q` | Includes nonregularity, the lower bound and the defining equation. Infinite exponents are outside this restricted claim. |
| Submodular on the possible edges of one vertex set | `claim` | All $n,G,H,q_G,q_H,q_U,q_I$ are quantified; all four defining equations precede $q_U+q_I\le q_G+q_H$. |
| Answer to the question | `result` | Negation of that whole universal proposition. |

The source does not specify the ground set. The fixed-vertex edge-set
interpretation is fixed by #19958. Refuting its finite-exponent restriction
also refutes a submodularity claim whose domain includes these instances.
The induced-vertex interpretation has separate numerical evidence below.
Uniqueness of the exponent and monotonicity of all degree means are not
hypotheses of the Lean refutation.

## Motivation

The settling GID is
`D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result`.
There is no anchor atom or coverage operation: this is an external named
open-problem resolution through `deposit-uncovered`.

## Gap

The literature screen recorded in #19958 identifies Section 7 as an open
question and Hofmeister's spectral mean characteristic as related prior work.
The recorded probe screen found only the source paper in OpenAlex's combined
SDE/submodularity queries and no matching invariant title in ten Crossref
results. Semantic Scholar returned HTTP 429; the Hofmeister sources were not
retrieved in that screen. These are bounded searches, not an exhaustive
literature theorem. Completeness remains `ASSUMED-UNVERIFIED`.

## Route

On vertices $0,\ldots,4$, put
$E_0=\{01,02,03,14,23\}$, $e=24$ and $f=34$.
Write $H_0=E_0$, $H_e=E_0\cup\{e\}$,
$H_f=E_0\cup\{f\}$ and $H_{ef}=E_0\cup\{e,f\}$.
The private `union_graph` and `inter_graph` identify the join and meet.
The degree sequences, in vertex order, are
$(3,2,2,2,1)$, $(3,2,3,2,2)$, $(3,2,2,3,2)$ and $(3,2,3,3,3)$.
These are the statements of `degrees0`, `degreese`, `degreesf` and `degreesef`;
`nonregular` excludes regularity.

Characteristic-polynomial evaluation and real spectral bounds give

| Graph | Characteristic polynomial | Strict spectral interval |
| --- | --- | --- |
| $H_0$ | $(z-1)(z+1)(z^3-4z-2)$ | $(11/5,9/4)$ |
| $H_e,H_f$ | $z(z+2)(z^3-2z^2-2z+2)$ | $(49/20,249/100)$ |
| $H_{ef}$ | $z(z+1)(z^3-z^2-6z+2)$ | $(571/200,143/50)$ |

The polynomial and interval statements are kernel-checked by the private
`charpoly0_eval`, `charpolye_eval`, `charpolyf_eval`, `charpolyef_eval`,
`spectral0`, `spectrale` and `spectralef`.
The private mean comparison lemmas place $M_3$ below the spectrum at $H_0$
and $H_{ef}$, and above it at $H_e,H_f$.
`mean0_four` and `meanef_four` give the other endpoint at $4$;
`meane_two` gives the endpoint at $2$.
`mean_continuous` and `exponent_of_endpoints` apply the intermediate value
theorem on these finite intervals. Thus `exponent0`, `exponente` and
`exponentef` provide exponents with
$q_0>3$, $q_e<3$, $q_f<3$, $q_{ef}>3$.
Their sums satisfy $q_e+q_f<6<q_0+q_{ef}$, contradicting `claim`.

## Falsifier

A difference between the source's equation and the displayed definition, or
between the graph join/meet and the specified edge sets, would invalidate the
interpretation. Lean checks the complete restricted claim and its negation.
Numerical exponent values alone do not establish the Lean refutation, uniform
blowup invariance or a positive classification of restricted graph classes.

## Evidence

The D5 module and its matching Blueprint Scribe contain the four public
definitions and the single public theorem `result`. The admission basis is
`open-problem-resolution (#19958; Refuted)`. All proof steps are classified
`bind-only`; no separate escape witness is claimed.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The owner publication `D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.adjMatrix_complex_map` has an unfinished escape audit tracked in https://github.com/the-omega-institute/trureturing/issues/22239. Its statement and proof are preserved; no successful Reg registration is claimed.

### Finite experiment

The program is in the [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/9f3dcb3baf7b3b158f03f978e2374438ab86873f/docs/reports/achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity),
file `check.py`, SHA-256
`80286464841329a5980d58b789ba8104621b2ee054cad885c5b0f756418897d2`.
A byte-identical extraction was run with
`python3 /Users/auric/.sshx/b018bcccbc7dc73643980461/attempt-1/evidence/experiment-check.py`,
exit 0. Part (a) checks the exact characteristic polynomials, rational
certificates and third degree moments. Parts (b)–(d) compute the following
finite numerical values, rounded to six decimals:

| Tested instance | Computed exponents or comparison |
| --- | --- |
| Original witness and uniform blowups $t=2,3$ | For each $t=1,2,3$: $(q_0,q_e,q_f,q_{ef})=(3.404621,2.641523,2.641523,3.174472)$; submodularity difference $-1.296047$. |
| The specified seven-vertex bipartite induced-subgraph example | $q(S)=q(T)=q(S\cap T)=2.000000$; $q(S\cup T)=2.501215$. |
| The specified six-vertex edge-set example | $(q(E),q(E+e),q(E+f),q(E+e+f))=(3.911305,3.303203,3.303203,2.357898)$; $q(E+e)+q(E+f)>q(E)+q(E+e+f)$. |

The induced example has parts $\{a,b,c\}$ and $\{x,y,z,w\}$, edges
$ax,ay,az,aw,bx,by,bz,cx,cy,cw$, and sets
$S=\{a,b,x,y,z\}$, $T=\{a,c,x,y,w\}$.
The six-vertex example has
$E=\{01,45,35,24,15,34,13\}$, $e=05$, $f=25$.
The computed cases assert no uniform result for other sizes or blowup factors.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Five-vertex fixed-edge-set failure with finite exponents | Proved; kernel-checked `result`, using `nonregular`, `exponent0`, `exponente`, `exponentef`, `union_graph`, `inter_graph` | Nonregular witnesses refute the universal inequality. The proof uses neither exponent uniqueness nor global mean monotonicity. |
| Third-mean comparison and failure mechanism | Proved; kernel-checked private `spectral0`, `spectrale`, `spectralef`, `mean0_three`, `meane_three`, `meanef_three`, and `exponent_of_endpoints` | The spectrum is above $M_3$ at the intersection and union, below $M_3$ at the single additions. Finite solutions fall on opposite sides of $3$, reversing the required sum inequality. |
| Uniform blowups $t=2,3$, induced-vertex failure and six-vertex supermodularity failure | Computed; parts (b)–(d) of the pinned experiment, command, exit code and SHA-256 in Evidence | Exactly the instances and numbers in the experiment table; these are not Lean-proved extensions. |
| General blowup invariance, positive restricted submodularity and exhaustive literature completeness | Open | No uniform formal blowup theorem or positive classification is claimed. Literature completeness is `ASSUMED-UNVERIFIED`. |
| Effect on the source's other results | Proved in prose from the source scope; Section 7 and the source scope quoted in Problem | Section 7 poses a question. Its refutation does not invalidate Definition 2.1 or any earlier theorem of the paper. |

The closest unconditional surviving equality is elementary: for the same graph
with the same chosen finite exponent in all four positions, both sides equal
$2q$. This is proved in prose by substitution, and gives no assertion for
distinct graphs. Positive classes with a nontrivial edge-set lattice remain
open here. The four graphs share the spanning tree with edges $01,02,03,14$;
therefore connectedness alone cannot repair the edge-set assertion (proved in
prose from the displayed edge sets). Additional edge structure or a different
inequality would need a separate statement and proof.

## ASSUMED-UNVERIFIED

Literature completeness, including later settlements and the relation to all
Hofmeister sources, is not established. General blowup invariance and positive
restricted submodularity are outside the kernel-checked result. The induced
and supermodularity examples and $t=2,3$ blowups have only the finite numerical
experiment evidence stated above.
