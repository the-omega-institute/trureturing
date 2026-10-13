---
slug: pelekis-2018-circular-orientation-entropy
bibkey: pelekis2019orientationentropy
doi: 10.4418/2019.74.1.8
url: https://arxiv.org/abs/1808.04166
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy
---

# Circular hypergraphs do not maximise orientation-count entropy

## Problem

Pelekis, Le Matematiche 74(1), pp. 128–129, Section 4:
“We conjecture that circular hypergraphs are such that H(X_{C_{n,r}}) ≥ H(X_H),
for all H ∈ D_{n,n,r}.” The preceding definition assumes $r\ge3$ and $n>r$;
$C_{n,r}$ has all $n$ cyclic paths of $r$ vertices as edges. The competitor
class consists of multi-hypergraphs and permits repeated edges and isolated
vertices. Every edge independently selects one uniformly random vertex, and
$X$ counts the selected vertices. The title's complementary zero-in-degree
count has the same entropy.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $r\ge3$ and $n>r$ | `claim` quantifies over `r n`, with `3 ≤ r` and `r < n` | No additional hypothesis. |
| All cyclic paths of size $r$ | `circular n r` maps each starting vertex to the image of natural residues $(i+j)\bmod n$, $0\le j<r$ | Its bound derives $n>0$ from the actual index `i : Fin n`; for $n=0$ there is no index. |
| $D_{n,n,r}$ | `E : Fin n → Finset (Fin n)` with all cardinalities equal to `r` | Exactly $n$ labelled edges; multiplicities retained. |
| Uniform independent orientations and Shannon entropy | Shared `X` and `entropyX r E` from OrientationEntropyBalance | Literal filter, denominator $(r:\mathbb R)^n$, base-two logarithm and zero-probability convention. |
| Circular entropy at least every competitor | `entropyX r E ≤ entropyX r (circular n r)` for every uniform `E` | No restriction of the competitor class. |
| Refutation | `result : ¬ claim` | Unconditional negation; the numbered asymptotic Conjecture 4.1 is a separate statement. |

## Motivation

Uniform placement of edges around a circle is proposed to maximise entropy.
A single admissible competitor with strictly larger entropy disproves that
maximality without any need to classify all optimisers.

## Gap

The bounded source and literature checks recorded in #15995 and #15996 found
no settlement in their inspected scope: arXiv v1, the journal version, the
located citing work Silva–Andrade–Bazeia (arXiv:2101.05250), and eleven later
arXiv works of the author. This does not establish exhaustive absence or
worldwide priority. The full Pelekis–Schauer chapter remains unread.

## Route

At $n=4$, $r=3$, take $\{0,1,2\},\{0,1,2\},\{0,1,3\},\{0,1,3\}$.
Its counts for $X=0,1,2,3,4$ are $(0,2,27,44,8)$; those of $C_{4,3}$ are
$(0,0,24,48,9)$. Both total 81. The exact integer inequality
$2^2 27^{27}44^{44}8^8<24^{24}48^{48}9^9$, together with
$H=\log_2 81-\log_2(\prod c^c)/81$, gives a strict entropy advantage.
The claim applied to this uniform witness gives the opposite weak inequality.

## Falsifier

A failure of edge uniformity, either exact count vector, or the strict product
comparison would invalidate this witness. Replacing the literal modular
construction or excluding source-permitted multiplicities changes the problem.

## Evidence

`D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.lean` imports
OrientationEntropyBalance for `X`, `entropyX`, `orientations_eq` and
`sum_entropy_formula`. Its entropy comparison directly applies the shared
count-product formula.
Its private `witness_counts`, `circular_counts`, `counts_certificate` and
`witness_entropy_gt` establish the finite comparison on the public `result`'s
proof path. The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Fixed experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/b0d389210cd1664822ff581855ec977b421fc669/docs/reports/pelekis-2019-entropy-zero-indegree).
Command: `python3 check_circular.py`; exit 0; SHA-256 of `check_circular.py`:
`6631b05d7b320fb08b39fa72e9541e4ad5e5a6d30e01edb240553ad3cdba35ca`.
It enumerates every multi-hypergraph and orientation for exactly
$(n,r)=(4,3),(5,3),(6,3),(5,4)$. The final reading is `bad=0`, including a
true exact integer comparison at $(4,3)$. Floating maximum and circular
entropies, respectively, are $1.468283$ and $1.319521$, $1.703670$ and
$1.450639$, $1.907803$ and $1.583841$, $1.594842$ and $1.522207$ bits.
The script uses tolerance $10^{-12}$ to update a maximiser and $10^{-9}$
for the entropy advantage test. Numerical maximisation is not a uniform
classification theorem.

## Triage

### What the settlement shows

| Item | Evidence kind | Result and boundary |
| --- | --- | --- |
| Circular failure mechanism | Kernel-checked private certificates on `result`'s proof path | `witness_counts` gives $(0,2,27,44,8)$, `circular_counts` gives $(0,0,24,48,9)$; `counts_certificate` and `witness_entropy_gt` give the strict comparison at $(4,3)$. `result` refutes circular maximality. |
| Relation to the three-vertex mechanism | Kernel-checked sibling result | OrientationEntropyBalance's private `witness_counts`, `witness_degrees` and `witness_maximises`, used by its `result`, establish counts $(0,1,5,2)$, degrees $(3,2,1)$ and maximality over all 27 ordered tuples at $n=m=3$, $r=2$. |
| Why concentration can increase entropy | Open explanation | A common core retains the rare outcome $X=1$, absent in $C_{4,3}$. Support size alone does not order entropy; the exact product inequality establishes this advantage. |
| What maximises in the tested cases | Computed | The experiment displays a maximiser with a common core in each of exactly four cases above. It does not classify every maximiser or any unbounded family. |
| Further circular counterexamples | Computed | Strict numerical advantages occur at $(5,3),(6,3),(5,4)$ in the fixed experiment. Only $(4,3)$ is certified by this Lean module. |
| Three-vertex family for every $m\ge3$ | Open | The Lemmas 1–3 candidate of #15995 is not proved here. |
| Restrictions preserving balance optimality | Open | No characterization follows from the two finite refutations. |
| Asymptotic Conjecture 4.1 | Open | Its lower bound is logically distinct from maximality and is not settled here. |
| Pelekis–Schauer chapter | Open literature check (ASSUMED-UNVERIFIED) | Subscription preview only; supplied Firecrawl HTTP 402; see the final section. |

The counterexample breaks the proposed optimum, without contradicting the
source's separate proved entropy bounds. Any inference using the maximality
conjecture lacks that premise; the source's numbered asymptotic question
retains its stated open boundary.

## ASSUMED-UNVERIFIED

The Pelekis–Schauer chapter, “Network Coloring and Colored Coin Games”,
Springer (2013), DOI 10.1007/978-1-4614-6825-7_4, was accessible only as a
subscription preview; the supplied Firecrawl reading returned HTTP 402.
Its full contents and worldwide prior-art clearance are ASSUMED-UNVERIFIED.
