---
slug: butera-2015-dimer-virial-bounds-regular-biconnected
bibkey: butera2015virial
doi: 10.1016/j.physa.2015.05.106
url: https://arxiv.org/abs/1502.06734v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result
---

# The dimer bounds for k at most 4 on regular biconnected graphs

## Problem

P. Butera, P. Federbush, M. Pernici, *Positivity of the virial coefficients
in lattice dimer models and upper bounds on the number of matchings on
graphs*, Physica A 437 (2015) 278–294, arXiv:1502.06734v2, Section IV B:

> For all the graphs examined in this section, Eq. (\ref{Delta0}) is
> satisfied for $k \le 4$. It would be interesting to know whether these
> bounds, Eq. (\ref{Delta0}) for $k \le 4$, are always satisfied for
> regular biconnected graphs.

Eq. (1) is $\Delta^k\ln(i!\,N(i))\le0$ for $k=2,\dots,\nu$ and
$i=0,\dots,\nu-k$, where $N(i)$ is the number of configurations of $i$
dimers on the graph ($i$-edge matchings), $\Delta$ is the forward difference
in $i$, and $\nu$ is the matching number.

## Motivation

The paper derives Eq. (1) on finite regular graphs as the counterpart of the
positivity of the virial coefficients of the monomer-dimer model on infinite
regular lattices, and tests it on lattice graphs and on regular biconnected
graphs. For $k=2$ the bound is the Heilmann–Lieb inequality; the reported
violations on regular biconnected graphs all have $k\ge5$. The question asks
whether $k\le4$ is safe on the whole class. The frozen declaration
`D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result`
answers it negatively.

## Gap

Issue #12197 classifies the question as Tier 1 and records the checks before
any Lean:

- arXiv:1502.06734 v2 is the latest version, and the question is printed as
  quoted;
- the later work of Butera, Federbush and Pernici and of Federbush
  (arXiv:2105.10772, 2107.05110, 2012.10927, 2202.00727, 1712.00613,
  1409.4549; Pernici, J. Stat. Phys. 168 (2017)) proves asymptotic or
  random-graph statements; results on matching sequences (Csikvári
  arXiv:1406.0766 and 1407.5409, Abért–Csikvári–Hubai arXiv:1405.6740,
  Gurvits arXiv:1106.2844, Friedland–Krop–Markström arXiv:0801.2256,
  Davies–Jenssen–Perkins–Roberts arXiv:1508.04675, Craven–Csordas 1989,
  Brändén arXiv:1410.6601) do not decide $k=3$ or $k=4$.

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty. The graph below is the necklace $(K_7)_{xy}N_4$ of M. Borbényi and
P. Csikvári, Trans. Comb. 10(2) (2021) 73–95, arXiv:2006.16815, whose
transfer formula $M(H,z)=\operatorname{tr}(T(z)^4)$ also gives its matching
polynomial; that paper does not apply it to Eq. (1).

## Route

1. For an edge $e$ of an edge set $E$,
   $N(E,i+1)=N(E-e,i+1)+N(E_e,i)$, where $E_e$ is the set of edges of $E$
   disjoint from $e$.
2. For two edge sets without a common vertex, the matching sequence of the
   union is the Cauchy product of the two sequences.
3. The graph $H$: vertices $7b+t$ with $b\in\{0,1,2,3\}$ and
   $t\in\{0,\dots,6\}$; each block is $K_7$ minus the edge between
   positions $0$ and $1$, and position $1$ of block $b$ is joined to
   position $0$ of block $b+1\bmod4$. It is $6$-regular with $84$ edges.
4. Rule 1 on the four connecting edges and rule 2 on the four blocks
   reduce $N(H,\cdot)$ to the matching sequences $(1,20,95,90)$ of
   $K_7-e$, $(1,15,45,15)$ of $K_6$ and $(1,10,15)$ of $K_5$:
   $N(10)=845745750$, $N(11)=506745000$, $N(12)=141530625$,
   $N(13)=9922500$, $N(14)=101250$.
5. $\nu=14$: $N(14)>0$, and $28$ vertices carry at most $14$ disjoint
   edges.
6. The cycle through positions $0,2,3,4,5,6,1$ of blocks $0,1,2,3$ is
   Hamiltonian; deleting a vertex leaves a Hamiltonian path, so $H$ is
   biconnected.
7. With $A_i=i!\,N(i)$, $\Delta^4\ln A$ at $i=10$ is
   $\ln(A_{10}A_{12}^6A_{14})-\ln(A_{11}^4A_{13}^4)>0$, since
   $A_{11}^4A_{13}^4<A_{10}A_{12}^6A_{14}$ as integers.

## Falsifier

The kernel-checked `result` is the negation of the universal statement over
finite simple graphs on `Fin n`: regular (a common degree), biconnected
(connected, and connected after deleting any vertex), every $k$ with
$2\le k\le4$ and every $i$ with $i+k\le\nu$. $N(i)$ counts the elements of
the frozen `MatchingFiber.Matching n i` all of whose pairs are edges of the
graph, and $\Delta^k$ is the $k$-th iterate of `fwdDiff 1`. A different
reading of "regular biconnected", of $N(i)$ or of the index range changes the
question.

## Evidence

An exact-integer Python recomputation (issue #12197) by the vertex recurrence
$Z(H)=Z(H-v)+z\sum_{u\sim v}Z(H-u-v)$ gives
$N(0..14)=1, 84, 3066, 63944, 843751, 7376220, 43536830, 173694800,
462062375, 796173900, 845745750, 506745000, 141530625, 9922500, 101250$;
among $k\le4$ the only violation of Eq. (1) is $k=4$, $i=10$, with
$A_{14}A_{12}^6A_{10}/(A_{13}^4A_{11}^4)=
3532327221883443718533774700941/3277304638880937076085488855040$. The
controls $C_9$, $C_{12}$, $K_6$, $K_7$, $K_8$, the Petersen graph, the
$3$-cube and $K_{3,3}$ show no violation for $k\le4$.

The canonical source is
`D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.lean`. Its
public declarations are `matchingCount`, `matchingNumber`, `Biconnected`,
`claim` and `result`. The frozen module state has statement identity
`sha256:32ed2ba9f725d2034bb819fe7042db935546c840e6a89a12e50428b2081bafb9`. The result declaration has statement identity `sha256:ebe660409a6567de1886e4c9be2d425afb1ea34b1c8426e39c337b34963c3083`.
The Freeze event is `sha256:e80a71b9dacc1ecc95aa0929c2223e0c23cdecb7da1547d0cc86033f04ef1632`; its project-level frozen prerequisite is
the Freeze event of `D5/S3/Zeros/Convolution/MatchingFiber`. The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published question; resolution `Refuted` by
`D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12197). Utility kind `certified-instance`, basis `refutes` the module's
`claim`.

### What the settlement shows

- **Proved by `result`:** the bounds of Eq. (1) for $k\le4$ fail on a
  $6$-regular biconnected graph on $28$ vertices, at $k=4$, $i=10=\nu-4$.
- **Proved inside the proof of `result`:** the deletion rule (Route,
  step 1) and the product rule (step 2) for matching counts of finite edge
  sets, and the counts $N(10..14)$ of $H$.
- **Mechanism (computed, not stated in Lean):** each block has $7$
  vertices, so a perfect matching of $H$ covers exactly one end of the
  connecting edges in every block; only the two alternating pairs of
  connecting edges do this, each leaving four copies of $K_6$, so
  $N(14)=2\cdot15^4=101250$, and $A_{13}=7A_{14}$.
- **Computed, not in Lean (issue #12197):** in the rings of $B$ copies of
  $K_r-e$ with $3\le r\le8$, $2\le B\le8$ and at most $40$ vertices, the
  only violations for $k\le4$ are $B=4,r=7$ (this graph) and $B=5,r=7$
  ($k=4$, $i=13$); none of them violates $k=3$.
- **Open here:** whether some regular biconnected graph violates Eq. (1)
  with $k=3$; whether a regular biconnected *bipartite* graph violates it
  for some $k\le4$ (the graph $H$ contains triangles); and the conjecture
  that motivates Eq. (1), positivity of all virial coefficients on infinite
  regular lattices, which a finite non-lattice graph does not address.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority or absence of an
independent answer. The Lean kernel verifies the encoded statement and its
axiom closure; its correspondence to the paper, including the reading of the
question as a universal statement and of "regular biconnected" as stated in
Falsifier, is checked by reading the source and the definitions.
