---
slug: bozovic-2026-sierpinski-limited-domination
bibkey: bozovic2026limiteddomination
doi: 10.48550/arXiv.2610.01584
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.result
---

# Božović Conjecture 12: k-limited domination of Sierpiński graphs

## Problem

D. Božović, *On k-limited domination: complexity and Sierpiński graphs*,
arXiv:2610.01584v1, Section 6, Conjecture 12, states:

> Let n, m, and k be integers such that n ≥ 1 and 1 ≤ k ≤ m − 1. Then γ_k^L(S(n, m)) = (m − k) m^(n−1).

Section 2 defines S(n,m) for n ≥ 1 and m ≥ 2. Its vertices are words of
length n over {0,…,m−1}. Adjacency means that for some coordinate h the
preceding coordinates agree, the h-coordinates differ, and each later
coordinate equals the other word's h-coordinate. A dominating set D is
k-limited when every selected vertex has at most k neighbors outside D;
γ_k^L is its minimum cardinality.

## Motivation

The exact formula determines the parameter for all graph sizes and all
1 ≤ k ≤ m−1. The source's previously proved k=1 and m=3 cases are included
in the universal result.

## Gap

This is a tier-1 externally named conjecture, preregistered in
[issue #12456](https://github.com/the-omega-institute/trureturing/issues/12456).
That issue records the source quotation and quantified statement, and reports
bounded MathDB, web, predecessor-paper and repository searches with no
settlement in their searched scope. The arXiv record has only v1, whose
Section 6 presents the assertion as a conjecture. This delivery establishes
the assertion; it makes no exhaustive literature or publication-priority claim.

## Route

The module uses rank r=n−1 and words Fin (r+1) → Fin m. It uses the existing
SimpleGraph.IsDominating predicate with the finite set coerced to a Set, and
Mathlib's neighborFinset, Fin.init and Fin.snoc directly.

For the upper bound, a recursive ZMod m coloring is constant on linking
edges and bijective within every base clique. Selecting the m−k colors
with least representatives below m−k gives (m−k)m^r vertices. Each base
clique has a selected vertex, and every selected vertex has exactly k
unselected internal neighbors while its linking neighbor, when present,
has the same color and is selected.

For the lower bound, a nonempty base clique contains at least m−k selected
vertices. An empty base clique forces its linking endpoints' external
neighbors to be selected. Their cliques contain at least m−k+1 selected
vertices. Within each quotient base clique, an empty fiber therefore forces
all m−1 other fibers to have this surplus. Their total is at least
(m−1)(m−k+1)=m(m−k)+(k−1). Summing the disjoint quotient-clique groups gives
the sharp lower bound. The n=1 complete graph case is handled separately.

## Falsifier

A graph in the stated parameter range with a k-limited dominating set of
cardinality below (m−k)m^(n−1), or a failure of the coloring construction to
attain this cardinality, would contradict the target. Source fidelity requires
the open-neighborhood constraint only for vertices in D and the exact
Section 2 adjacency rule.

## Evidence

The frozen declaration is
D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.result : claim.
The claim quantifies n,m,k : ℕ with 1≤n, 2≤m, 1≤k and k≤m−1, and concludes
gamma (n−1) m k = (m−k)m^(n−1). The standard axiom closure of result is
propext, Classical.choice and Quot.sound. The Scribe resolution is Proved.
No finite numerical check substitutes for this universal kernel proof.

The independent ILP calculation uses SciPy 1.16.0 and the command
`scipy.optimize.milp(c=ones, integrality=ones, bounds=Bounds(zeros, ones), constraints=LinearConstraint(M, lower, inf))`.
For adjacency matrix A and binary selection vector x, the objective is
sum(x); the domination constraints are (A+I)x≥1, and the limited constraints
are (Ax)_u−(deg(u)−k)x_u≥0. Thus the second constraint imposes the required
bound precisely when u is selected. All 25 runs return optimal solver status
0 and MIP gap 0; the returned binary solutions satisfy both constraints.
The following values, indexed by k=1,…,m−1, agree with issue #12456:

| n | m | computed γ values in increasing k |
| --- | --- | --- |
| 1 | 2 | 1 |
| 1 | 3 | 2, 1 |
| 2 | 2 | 2 |
| 2 | 3 | 6, 3 |
| 3 | 3 | 18, 9 |
| 2 | 4 | 12, 8, 4 |
| 2 | 5 | 20, 15, 10, 5 |
| 3 | 4 | 48, 32, 16 |
| 4 | 3 | 54, 27 |
| 2 | 6 | 30, 24, 18, 12, 6 |

## Triage

`theorem`: Conjecture 12 is proved in the stated source range.

### What the settlement shows

- **Proved in this module:** the coloring constant on linking edges produces
  a k-limited dominating set meeting the formula; the lower-bound charging
  accounts for at least k−1 surplus vertices in a quotient group containing
  an empty base clique. These are local steps in result, not additional
  public theorem declarations.
- **Proved as specializations of result:** Theorem 10 (k=1, all m≥2) and
  Theorem 11 (m=3, k∈{1,2}) have the same formulas. The conjectural universal
  parameter formula is settled, while those source results remain valid.
  The source's separate complexity theorems are outside this settlement.
- **Computed:** the 25 ILP values above, with the stated SciPy command and
  constraints, agree with the sharp formula.
- **Open:** a retained characterization of all minimum k-limited dominating
  sets, including exclusion of empty base cliques for k≥2. Equality cases of
  the charging estimates are a follow-up candidate; this module's public
  result states only the minimum value.
- **Open:** an analogous sharp formula for generalized Sierpiński graphs
  S(G,n). The present argument uses complete base cliques and does not
  establish the general-base-graph statement.

## ASSUMED-UNVERIFIED

The mapping from the paper's notation to the typed graph and domination
predicate is a source-fidelity judgement, not itself a kernel statement.
The searches reported in issue #12456 are bounded literature evidence;
absence from all literature and publication priority are unverified.
The universal proof covers exactly the stated parameter range. The two
neighboring statements identified as open carry no resolution claim here.
