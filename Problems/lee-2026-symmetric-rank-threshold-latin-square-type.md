---
slug: lee-2026-symmetric-rank-threshold-latin-square-type
bibkey: lee2026assignmentpolytopes
doi: 10.48550/arXiv.2611.12780
url: https://arxiv.org/abs/2611.12780v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.result
---

# Lee’s symmetric rank-threshold fusion can fail positive Latin-square type

## Problem

Jon Lee, *The dimension of multi-index assignment polytopes and Latin-square
transversal polytopes, via association schemes*, arXiv:2611.12780v1, asks
“whether the relation ‘rank at least d’ is of Latin-square type for all such m
we leave open.” This is the last paragraph of §6.3 on printed and PDF page 34,
after Proposition 6.5. Section 2.3 defines the positive type on page 5.
[Question](https://arxiv.org/pdf/2611.12780v1#page=34) · [Definition](https://arxiv.org/pdf/2611.12780v1#page=5)

For every finite field $K$ of prime-power size, consider positive $m$ in the
classes $m\equiv3\pmod 4$ and $m\equiv0\pmod 4$. Take $d=(m+3)/2$ in the
first class and $d=(m+2)/2$ in the second.
The full vertex set $V$ consists of symmetric $m\times m$ matrices over $K$.
Distinct vertices $A,B$ are adjacent exactly when $\operatorname{rank}_K(A-B)\ge d$.
The question asks for positive integers $n,t$ such that $|V|=n^2$, every vertex
has degree $t(n-1)$, and the exact restricted real adjacency spectrum is
$\{n-t,-t\}$. In Lean the spectrum clause quantifies every real $\lambda$.
Membership in that set is equivalent to the existence of a nonzero real
function $f$ on $V$ with $\sum_A f(A)=0$ and
$\sum_{B\sim A} f(B)=\lambda f(A)$ for every $A$.
[Preregistered Tier 1 problem #33805](https://github.com/the-omega-institute/trureturing/issues/33805)

## Motivation

Lee’s Propositions 6.4 and 6.5 give the first two dimensions, $m=3$ and $m=4$.
The universal question tests whether their positive Latin-square-type
structure extends to the indicated rank-threshold fusions. The witness
$q=2,m=7,d=5$ belongs to the first dimension case and uses the graph on all
symmetric matrices. [Lee v1, §6.3](https://arxiv.org/pdf/2611.12780v1#page=32)

## Gap

Schmidt’s published valencies count individual rank/type classes of
symmetric bilinear forms. One can sum them over the threshold to compute
the fused degree. At the binary witness the published formula gives
$262{,}802{,}624$, with remainder $2{,}921$ modulo $16{,}383$.
This is an elementary specialization of an existing formula. The
preregistration’s scoped literature screen found no stated answer to Lee’s
exact universal fusion question. The Lean argument uses an orbit congruence
on the actual neighbor set. [Schmidt (2020), equation (9) and Proposition 2.4](https://alco.centre-mersenne.org/item/10.5802/alco.88.pdf#page=7)

## Route

The upper-triangular entries give a bijection between the vertices and
28 binary coordinates. The vertex count $2^{28}=268{,}435{,}456$ forces
$n=2^{14}=16{,}384$. At zero, adjacency is equivalent to rank at least five.
Simultaneous reindexing of rows and columns by $(0\ 1\ 2)(3\ 4\ 5)$ preserves
rank and induces a permutation of order three on this neighbor set.

Reindexing and transpose partition all 49 ordered index pairs into ten
classes. Lean checks symmetry, invariance, representative membership and
reachability, then constructs a two-way equivalence between fixed symmetric
matrices and the $2^{10}$ assignments to the classes. For each assignment,
the parity test counts the kernel among all $2^7$ binary vectors. The
kernel equivalence and rank-nullity give rank at least five exactly when
the kernel has at most four elements. A product equivalence covers all
1,024 masks by 32 disjoint chunks of 32. The kernel checks the chunk counts
and the restricted equivalences transfer their sum, 770, to the fixed
zero-neighbors.

## Falsifier

The 770 fixed zero-neighbors contribute one each. The other orbits each
contribute three, so $\deg(0)\equiv770\equiv2\pmod 3$. Positive
Latin-square type requires degree $t(n-1)$ there. The forced square order
$n=4^7$ gives $n\equiv1\pmod 3$ by the base-four residue theorem, so
$3\mid(n-1)$ and $t(n-1)\equiv0\pmod 3$ for every $t$. Failure of the
valency clause refutes the conjunction.

## Evidence

The [Lean module](../D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.lean)
defines the closed proposition `claim` and proves the literal `Not claim`
as its sole public theorem, `result`. The checked transitive axiom closure is
`Classical.choice`, `Quot.sound`, and `propext`. The live proof uses the
frozen `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_three` for the
required residue of $n$. The proof substitutes that residue into
$n=(n\bmod 3)+3\lfloor n/3\rfloor$ to derive $n-1=3\lfloor n/3\rfloor$.
The actual degree residue follows from the finite certificate and permutation
congruence. The designated
refutation result is the §3.9 escape-registration exemption.
[Library source note](../Library/QuadraticForms/lee2026assignmentpolytopes.md)

## Triage

### What the settlement shows

- **Proved** (`D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.result`). The universal positive Latin-square-type claim is false in
  its $m\equiv3\pmod4$ case at $q=2,m=7,d=5$.
- **Proved.** The obstruction is divisibility of the actual valency.
  The proof uses neither a computation of the restricted spectrum nor an
  evaluation of all $2^{28}$ potential zero-neighbors.
- **Computed from published valencies.** The full degree at the binary
  witness has the same obstruction. The arithmetic use of Schmidt’s
  formula supplies no publication-priority claim.
- **Source results.** Lee’s Propositions 6.4 and 6.5 settle the cases
  $m=3$ and $m=4$. Their proofs need only those dimensions.
- **Open here.** The universal assertion restricted to $m\equiv0\pmod 4$,
  the classification of all positive-type fusions, and the separate
  polytope dimension question. The settlement concerns rank-at-least
  adjacency.

## ASSUMED-UNVERIFIED

Worldwide literature completeness and publication priority remain
unverified. The preregistered search records focused Crossref results and
an OpenAlex record with no indexed citations. OpenAlex rate-limited broader
keyword and citation-list queries. [Search scope in #33805](https://github.com/the-omega-institute/trureturing/issues/33805)
