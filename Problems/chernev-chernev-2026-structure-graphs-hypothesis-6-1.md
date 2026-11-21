---
slug: chernev-chernev-2026-structure-graphs-hypothesis-6-1
bibkey: chernevchernev2026structuregraphs
doi: 10.48550/arXiv.2611.07521
url: https://arxiv.org/abs/2611.07521v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.result
---

# Nontrivial structure-graph cycles over finite extension fields

## Problem

Andrey M. Chernev and Nikolay A. Chernev, *On the Connected Components of
Structure Graphs of Associative Rings* (2026), Hypothesis 6.1, p. 8, state:

> The structure graph of a Galois field of extension degree > 1 different from GF (4) contains a cycle of length > 1.

Definition 3.1, p. 3, gives the directed edges $(a,b)\to(a+b,ab)$ on
ordered pairs. The extension degree is over the prime field. The cycle
has pairwise distinct vertices, with the final edge returning to its
first vertex. [Versioned paper](https://arxiv.org/pdf/2611.07521v1#page=8)

## Motivation

The problem asks for a nontrivial cycle uniformly in every eligible finite
extension field. In the formal statement, $K$ is any type with a field
structure and finite enumeration, $p$ is prime, $n>1$, $|K|=p^n$, and
$|K|\ne4$. The conclusion supplies $r>1$ and an injective list of $r$
vertices with each directed successor at index $(i+1)\bmod r$.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/27776)

## Gap

The paper's Statement 6.2 derives the result for characteristics other
than 2, 3 and 7 conditional on Hypothesis 5.5. Statement 6.3 treats
characteristics 3 and 7, and Section 6 reports characteristic-two checks
through extension degree 13. The uniform theorem uses the finite-field
cardinality and embedding theorems and finite-orbit periodicity.
Hypotheses 4.2 and 5.5 are outside its scope.
[Paper, Sections 5–6](https://arxiv.org/pdf/2611.07521v1#page=8)

## Route

Write $g(x)=x-x^2$. Two structure-graph steps send $(-1,x)$ to
$(-1,g(x))$. A nonzero periodic point of $g$ gives a nonfixed periodic
vertex, whose least period yields the directed cycle.

In odd extension degree, the prime-field complement is invariant
under $g$. A point sent into the prime field satisfies a quadratic
over that field, so its minimal-polynomial degree is at most two and
divides the odd extension degree. Consequently the degree must be one.
The complement is nonempty and finite, so it contains a periodic point.

In odd characteristic and even extension degree, a square root of $-1$
in the quadratic subfield gives a four-cycle. In characteristic two,
every eligible degree has an odd prime divisor or is divisible by four.
The corresponding subfield supplies an odd-degree cycle or the
eight-cycle in $\mathrm{GF}(16)$ constructed using a root of $X^4+X+1$.
Field embeddings and the finite-field isomorphism to $K$ preserve all
edges and vertex distinctness.

## Falsifier

An allowed finite field whose structure graph had only fixed-point
cycles would falsify the assertion. Among $p$ prime and $n>1$, the
equation $p^n=4$ holds exactly for $(p,n)=(2,2)$.

For the excluded field, put $u^2=u+1=v$, so $v^2=u$ and $uv=1$. Every
pair with a zero coordinate reaches a fixed vertex $(a,0)$. The pair
$(1,1)$ reaches $(0,1)$, and the pairs $(u,u)$ and $(v,v)$ reach pairs
with a zero coordinate. A pair containing 1 and one of $u,v$ reaches
$(u,v)$ or $(v,u)$, each of which reaches $(1,1)$. These exhaust the
ordered pairs and show directly that only loops are cycles in
$\mathrm{GF}(4)$, as illustrated in Figure 1.
[Paper, Figure 1](https://arxiv.org/pdf/2611.07521v1#page=5)

## Evidence

The theorem `Trureturing.StructureGraphCycles.result` proves
`Trureturing.StructureGraphCycles.claim`. Its finite-orbit argument
uses `finite_orbit_and_readout_eventually_periodic` from
`D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound`. The Lean axiom
closure is `Classical.choice`, `Quot.sound`, and `propext`.
The source-equivalence registration binds the occurrence of $p^n$ in
the cardinality premise. Its intervention replaces that readout by the
constant 2 and its continuation is unknown.

## Triage

`theorem`. The Lean result proves the complete Hypothesis 6.1. The
order-four boundary calculation above is a finite argument in prose.

## ASSUMED-UNVERIFIED

The preregistration's bounded literature search found no other
settlement in its searched scope. Citation coverage and publication
priority remain unverified.
[Preregistration literature screen](https://github.com/the-omega-institute/trureturing/issues/27776)
