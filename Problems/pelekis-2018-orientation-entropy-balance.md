---
slug: pelekis-2018-orientation-entropy-balance
bibkey: pelekis2019orientationentropy
doi: 10.4418/2019.74.1.8
url: https://arxiv.org/abs/1808.04166
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance
---

# Entropy maximisers need not have balanced degrees

## Problem

Pelekis, Le Matematiche 74(1), pp. 119–130, Conjecture 1.3, p. 122:
“Let the positive integers m,n,r be such that m ≥ n > r ≥ 2. A hypergraph
H = (V,ℰ) from D_{n,m,r} for which it holds H(X_H) ≥ H(X_G), for all
G ∈ D_{n,m,r} is such that |deg_H(v₁) − deg_H(v₂)| ≤ 1, for all v₁,v₂ ∈ V.”
Here $D_{n,m,r}$ includes repeated edges and isolated vertices. Each edge
independently selects a uniformly random vertex, and $X$ counts the vertices
selected at least once. Entropy uses logarithms of base two and $0\log 0=0$.
The title's zero-in-degree count is $n-X$; that bijection preserves entropy.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $m\ge n>r\ge2$ | `claim` quantifies over `n m r`, with `n ≤ m`, `r < n`, `2 ≤ r` | All parameters are positive under these hypotheses. |
| $r$-uniform multi-hypergraphs | `E : Fin m → Finset (Fin n)` and every edge has cardinality `r` | Ordered edges retain multiplicities; isolated vertices remain. |
| Uniform independent orientations | The literal orientation filter inside `entropyX r E`, with denominator $(r:\mathbb R)^m$ | Mathlib `Fintype.piFinset` supplies the public correspondence. |
| $X$ is the number with nonzero in-degree | `X E o` counts the image of `o` | The edge argument labels the family; the value depends on `o`. |
| Shannon entropy | `entropyX r E` sums $-p\log_2p$ over $k=0,\ldots,n$ | `r` is explicit; zero-probability outcomes are included. |
| Entropy at least every competitor | Every uniform `F` satisfies `entropyX r F ≤ entropyX r E` | Full competitor class, with no sampling restriction. |
| Absolute degree difference at most one | Every ordered pair satisfies the integer difference bound | Both orders give the two signs of the absolute-value bound. |
| Refutation | `result : ¬ claim` | Unconditional negation of the complete conjecture. |

## Motivation

The conjecture proposes degree balance as a necessary condition for entropy
maximality. A counterexample must be globally maximal in the stated class;
beating one balanced competitor would be insufficient.

## Gap

The bounded source and literature checks recorded in #15995 and #15996 found
no settlement in their inspected scope: arXiv v1, the journal version, the
located citing work Silva–Andrade–Bazeia (arXiv:2101.05250), and eleven later
arXiv works of the author. This does not establish exhaustive absence or
worldwide priority. The full Pelekis–Schauer chapter remains unread.

## Route

Take $n=m=3$, $r=2$, with edges $\{0,1\},\{0,1\},\{0,2\}$.
Its degrees are $(3,2,1)$ and its orientation counts for $X=0,1,2,3$ are
$(0,1,5,2)$, with total eight. For counts $c_k$ with a common positive
denominator $N$ and total $N$, the logarithm laws give
$H=\log_2N-\log_2(\prod_k c_k^{c_k})/N$, with $0^0=1$.
The certificate checks every one of the 27 ordered uniform edge tuples and
proves that its product is at least $12500=5^5 2^2$, the witness product.
Logarithm monotonicity proves maximality; vertices zero and two have degree
difference two, contradicting `claim`.

## Falsifier

A failure of uniformity, global maximality, the count certificate, or the degree
difference would invalidate this witness. Any source convention excluding
repeated edges would require a different target; the source explicitly allows
them.

## Evidence

`D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.lean` contains the
literal definitions, private finite certificates and the public `result`.
The private certificates `witness_counts`, `witness_degrees`,
`all_counts_certificate` and `witness_maximises` are on its proof path.
The public helpers `orientations_eq` and `sum_entropy_formula` identify the
orientation set and express entropy through the count product. Both are used
by the three-vertex and circular comparisons. The axiom closure of every public
declaration is contained in {propext, Classical.choice, Quot.sound}.

Their four-slot escape audits are unfinished: the source-to-law bridges elaborate without diagnostics,
but variation, sensitivity and observational-dependence evidence is missing;
see [#16296](https://github.com/the-omega-institute/trureturing/issues/16296).

The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Fixed experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/220859308ef43c350c4a0f0ad13ca34ea6bbf53c/docs/reports/pelekis-2019-entropy-zero-indegree).
Command: `python3 check.py`; exit 0; SHA-256 of `check.py`:
`33d20a7f5953e1b2e41631b562d584f91b7774ae2cb6c38024db385db60c7213`.
It enumerates loopless multigraphs and every orientation for exactly
$(n,m)\in\{3\}\times\{3,\ldots,10\}\cup\{4\}\times\{4,\ldots,7\}
\cup\{(5,5),(5,6),(6,6)\}$, with $r=2$. All fifteen cases have zero
balanced maximisers according to its floating entropy comparisons, with
comparison tolerance $10^{-12}$; the final reading is `bad=0`.
At $(3,3)$ the maximum is $1.298795$ bits and a maximiser has sorted degrees
$(3,2,1)$; at $(3,4)$ the displayed degrees are $(4,2,2)$.
These finite numerical readings do not establish a uniform family theorem.

## Triage

### What the settlement shows

| Item | Evidence kind | Result and boundary |
| --- | --- | --- |
| Three-vertex mechanism | Kernel-checked private certificates on `result`'s proof path | `witness_counts` gives $(0,1,5,2)$; `witness_degrees` gives $(3,2,1)$; `all_counts_certificate` and `witness_maximises` prove maximality over all 27 ordered tuples. `result` refutes Conjecture 1.3. |
| Why entropy rewards the spread | Open explanation | Repeated edges retain the rare outcome $X=1$ alongside the other two outcomes. The exact product comparison establishes the finite advantage; no general monotonicity of entropy under an increase of support size is proved here. |
| Three-vertex family for every $m\ge3$ | Open | Lemmas 1–3 in #15995 propose counts $(\varepsilon,\frac12+\varepsilon,\frac12-2\varepsilon)$ for $\varepsilon=2^{-m}$ and an entropy gap. This family is not proved here. |
| Beyond three vertices | Computed | The experiment entry covers exactly the fifteen cases above; no balanced maximiser is located under its comparison tolerance. A uniform extension and classification of all maximisers remain open. |
| Simple connected five-vertex case | Proved in prose | The simple graph with edges $01,02,03,04,12$ has degrees $(4,2,2,1,1)$ and greater entropy than every balanced simple graph with five vertices and five edges; the derivation below gives both count vectors and the exact product comparison. |
| Restrictions under which balance remains optimal | Open | Neither this instance nor the finite experiments characterize such restrictions. |
| Pelekis–Schauer chapter | Open literature check (ASSUMED-UNVERIFIED) | Subscription preview only; supplied Firecrawl HTTP 402; see the final section. |

### Simple connected five-vertex comparison

Let $G$ have edges $01,02,03,04,12$. It is simple and connected, and its
degrees are $(4,2,2,1,1)$. Condition on edge $12$ choosing vertex $1$.
Among edges $02,03,04$, let $B$ count those choosing their outer endpoint.
For $B<3$, at least one of these edges chooses $0$, so the selected-vertex
count is $X=2+B$, independently of edge $01$. The corresponding numbers
of orientations are $2,6,6$ for $B=0,1,2$. For $B=3$, edge $01$ choosing
$0$ gives $X=5$, while choosing $1$ gives $X=4$. Thus the conditional
counts for $X=2,3,4,5$ are $(2,6,7,1)$. Conditioning on vertex $2$ instead
has the same counts by the symmetry swapping $1$ and $2$. The full counts
are therefore $(4,12,14,2)$ out of $32$.

A balanced simple graph on five vertices with five edges has every degree
$2$: the average degree is $2$, and integral degrees differing by at most
one cannot have that average unless they are all $2$. Its components are
cycles of length at least three; on five vertices there is room for only one
component, so it is $C_5$. Describe an orientation of $C_5$ by a cyclic
binary word of length five. A vertex of in-degree zero corresponds to one
$0$-to-$1$ transition. There are $2$ constant words, $2\binom{5}{2}=20$ words
with two transition locations, and $2\binom{5}{4}=10$ with four. The selected
vertex counts are respectively $5,4,3$, giving counts $(10,20,2)$.

The two entropy denominators are $32$. Their count products satisfy
$4^4 12^{12}14^{14}2^2<10^{10}20^{20}2^2$. After cancellation this is
$3^{12}7^{14}<16\cdot5^{30}$: use $21<25$ and
$49<16\cdot5^6$ to obtain
$3^{12}7^{14}=21^{12}\cdot49<5^{24}\cdot49<16\cdot5^{30}$.
The count-product entropy identity then gives $H(X_G)>H(X_{C_5})$.
This is a prose proof of a separate five-vertex comparison; the settling
Lean module certifies the three-vertex multigraph instance.

The failure concerns degree balance as a necessary condition for a maximiser;
it supplies no classification of the unrestricted optimisers. The source's
proved entropy bounds do not acquire new hypotheses or lose their proofs.
Its circular maximality statement is separately refuted by
`D5.S0.Certificates.Hypergraphs.CircularOrientationEntropy.result`.
The asymptotic Conjecture 4.1 remains open here.

## ASSUMED-UNVERIFIED

The Pelekis–Schauer chapter, “Network Coloring and Colored Coin Games”,
Springer (2013), DOI 10.1007/978-1-4614-6825-7_4, was accessible only as a
subscription preview; the supplied Firecrawl reading returned HTTP 402.
Its full contents and worldwide prior-art clearance are ASSUMED-UNVERIFIED.
