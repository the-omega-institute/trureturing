---
slug: zheng-2026-morse-ensemble-chromatic-recovery-refutation
bibkey: zheng2026morseensemble
doi: 10.48550/arXiv.2605.24689
url: https://arxiv.org/abs/2605.24689v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result
---

# Zheng's chromatic recovery question: a negative answer

## Problem

Chong Zheng, "On the Morse Ensemble Polynomial of Simplicial Complexes",
arXiv:2605.24689v3, section 7, Open problem (4), p. 29, asks:

> Recovery from Φ(G). Theorem 6.4 shows that Φ(G) determines ME_G, and hence the Laplacian spectrum of G. Which further graph parameters are functions of Φ(G)? For instance, is the chromatic polynomial χ(G; t) always recoverable from Φ(G)? For which restricted graph classes, such as forests, bipartite graphs, or planar graphs, does Φ(G) separate non-isomorphic graphs?

Definition 6.1 sets Φ(G) = ME_Ind(G). Definition 1.1 sums one monomial
per acyclic matching of the nonempty face poset, with exponent c_i equal
to the number of unmatched i-simplices. The matching reverses its Hasse
arrows; the resulting digraph must have no directed cycle.

The paper defines acyclicity as absence of directed cycles, whereas Acyclic requires a natural-valued rank strictly increasing along every arc. These definitions agree for finite directed graphs: a directed cycle contradicts a strictly increasing rank; conversely, an acyclic finite digraph admits a topological order, whose positions give the rank.

The exact formal claim quantifies over all n,m : ℕ and all simple graphs
G on Fin n and H on Fin m: equality of their complete Morse-vector
coefficient functions implies equality of their labelled proper-colouring
counts for every k : ℕ. Different counts at k = 4 refute chromatic-polynomial
recoverability. No connectedness, vertex-count equality or nonemptiness
hypothesis restricts the quantified claim.

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result`
proves `¬ claim`, answering the printed question negatively. Two graphs
on eight vertices have equal Φ and unequal proper four-colouring counts.
The full coefficient function is retained; equality includes all coefficients.

## Gap

Preregistration issue #12702 classifies this as Tier 1 and records the
source clauses, quantified claim, witness and bounded literature screen.
That screen includes the arXiv versions, citing work, MathDB,
google-deepmind/formal-conjectures and the repository; it records no prior
resolution in that searched scope. It establishes neither an exhaustive
literature result nor publication priority. The source record lists v3,
with Open problem (4) present.

## Route

On vertices 0 through 7 let H1 have edges 01, 07, 12, 23, 27, 34, 47, 56,
and H2 have edges 03, 04, 12, 17, 25, 26, 57, 67. Set G1 = complement H1
and G2 = complement H2. Both H_i are triangle-free. Their nonempty clique
complexes, equivalently Ind(G_i), have eight vertices and eight edges.
A size-r vertex-edge matching has Morse vector [8-r,8-r].

The recursive candidate generator enumerates each compatible subset once.
Private certificate lists supply a base-16 rank or a nonempty directed
cycle for each candidate. Kernel reduction verifies every certificate,
its correspondence with the candidate list, and both size histograms:
[1,16,102,332,581,516,180,0,0]. The positive certificates describe acyclic
matchings; cycle certificates exclude every other candidate. There are
1830 candidates for H1 and 1872 for H2, with 1728 acyclic matchings each.
No certificate multiplicity enters a coefficient of Φ.

The colouring [0,0,1,1,2,3,3,2] is proper for G1. The vertices
{1,3,4,5,6} form a five-clique in G2. Mathlib's clique-colouring bound
therefore gives chromaticCount G2 4 = 0, whereas chromaticCount G1 4 > 0.

## Falsifier

A mismatch between the source's face-poset convention and nonempty faces,
a missing or repeated candidate, an invalid rank or cycle, unequal size
histograms, an invalid displayed colouring or a missing edge of the
five-clique would defeat the counterexample. The kernel checks the finite
claims and certificate completeness. Source-to-formal fidelity also uses
the stated finite topological-ranking interpretation of acyclicity.

## Evidence

The public surface contains the general ensemble and colouring definitions,
`claim`, and only one public theorem, `result : ¬ claim`. The only named
private theorems prove completeness and uniqueness of the recursive
candidate enumeration. All other proof helpers are local to `result`.
The frozen IndependentPartitionDeletion.configurations definition enumerates
independent subsets; a Nonempty filter gives the face poset. Its declaration
statement_id is sha256:7db22ad633fa73946f2bfaf142d0a64a4cfa39147b167168fbaa55a96a0bb603;
the frozen owner statement_id is sha256:8014b9cde4f69ed8e5049e30e505073622cbf5d96e9707ac8cda86d3aa47ff93.
Information-escape registration is paused under CLAUDE.md §3.9.
The Scribe result node records `OpenProblemResolutionClaim(Refuted)`.

## Triage

`theorem`; Tier 1 external named question, preregistered in #12702.
`proof_shape: content`; `admission_basis: open-problem-resolution`.
The new histogram facts prove equality of the two entire ensembles,
which feeds the colouring contradiction. The utility is a certified
instance with the typed refutation edge from `result` to `claim`.

### What the settlement shows

- **Proved in this module:** for this pair, the independence complexes are
  exactly H1 and H2; their acyclic-matching size distributions and full Φ
  agree, while their proper four-colouring counts differ. Thus equality of
  Φ does not preserve the chromatic polynomial or four-colourability.
- **Literature relation:** the paper's section 2 rooted-forest expansion
  interprets the one-dimensional ensemble through rooted spanning forests
  and the Laplacian determinant. The Lean proof uses exhaustive matching
  certificates; it does not formalize the general forest expansion.
- **Computed:** both complements have 20 edges, and their chromatic polynomials are
  χ(G1;t) = t(t-1)(t-2)(t-3)(t⁴-14t³+77t²-194t+187) and
  χ(G2;t) = t(t-1)(t-2)(t-3)²(t-4)(t²-7t+16).
  The proper-colouring values for k = 0,…,8 are respectively
  [0,0,0,0,72,2040,24120,168840,824880] and
  [0,0,0,0,0,1440,21600,161280,806400]. In particular χ(G1;4) = 72
  and χ(G2;4) = 0. Exact 72 and the full polynomials are computed results,
  not additional theorems of this module.
- **Computed:** both independence polynomials are 1+8x+8x², so the pair does
  not refute independence-polynomial recovery. Their clique numbers are
  4 and 5, so the pair also separates clique number. Their H_i Laplacian
  determinants det(tI+L) coincide:
  t⁸+16t⁷+102t⁶+332t⁵+581t⁴+516t³+180t².
- **Proved by the forest chromatic formula:** Φ(F) recovers the vertex count n
  and edge count m, which determine χ(F;t) = t^(n−m)(t−1)^m. Thus chromatic
  recovery holds for forests. This formula argument is not a theorem of this module.
- **Open:** forest isomorphism separation, and isomorphism separation within
  bipartite graphs or planar graphs, are the restricted-class questions in
  Zheng §7(4). Chromatic recovery within bipartite graphs or planar graphs
  also remains open here. Both
  complements have 20 edges on eight vertices, so neither is a forest or
  planar; each has a clique of size at least four, so neither is bipartite.
  These exclusions are computed properties of the pair. Existence of a
  smaller counterexample is open; no exhaustive smaller-order search is asserted.
- **Boundary:** Theorem 6.4 and the paper's established results require no
  chromatic-recovery hypothesis. The pair preserves the independence
  polynomial and Laplacian data; the negative answer affects the proposed
  further recovery and does not refute those established results.

The exact chromatic polynomials and neighbouring numerical properties can be
reproduced by enumerating proper set partitions, then expanding
Σ a_k t(t-1)…(t-k+1). This command prints the coefficient vectors, factored
polynomials, values at 4, independence counts, clique numbers and determinants:

```sh
python3 - <<'PY'
import itertools as it
import sympy as s
Es = [[(0,1),(0,7),(1,2),(2,3),(2,7),(3,4),(4,7),(5,6)],
      [(0,3),(0,4),(1,2),(1,7),(2,5),(2,6),(5,7),(6,7)]]
for E in Es:
    H = {frozenset(e) for e in E}
    G = {frozenset(e) for e in it.combinations(range(8),2)} - H
    a = [0]*9
    def visit(c):
        i = len(c)
        if i == 8:
            a[max(c)+1] += 1
            return
        for k in range(max(c, default=-1)+2):
            if all(k != c[j] or frozenset((i,j)) not in G for j in range(i)):
                visit(c+[k])
    visit([])
    t = s.Symbol('t')
    P = sum(a[k]*s.prod(t-j for j in range(k)) for k in range(9))
    indep = [sum(all(frozenset(e) not in G for e in it.combinations(C,2))
                 for C in it.combinations(range(8),k)) for k in range(9)]
    omega = max(k for k in range(9) if any(
        all(frozenset(e) in G for e in it.combinations(C,2))
        for C in it.combinations(range(8),k)))
    L = s.zeros(8)
    for u,v in E:
        L[u,u] += 1; L[v,v] += 1; L[u,v] -= 1; L[v,u] -= 1
    print(a, s.factor(P), P.subs(t,4), indep, omega,
          s.expand((t*s.eye(8)+L).det()))
PY
```

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. The Lean
kernel verifies the encoded statement and proof; it does not certify the
external paper's wording or the general polynomial-carrier correspondence.
The numerical chromatic polynomials, clique maxima and Laplacian determinants
are computed outside Lean. Forest isomorphism separation, bipartite and planar recovery or isomorphism
separation, and minimality remain open.
