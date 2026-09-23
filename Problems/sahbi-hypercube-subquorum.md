---
slug: sahbi-hypercube-subquorum
bibkey: sahbi2026subquorum
doi: 10.48550/arXiv.2609.25128
url: https://arxiv.org/html/2609.25128v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Hypercube.hypercube
---

# Sahbi Conjecture 6.4

## Problem

For every integer `n>=2`, prove that the sub-quorum chromatic number of the
Boolean cube is

    psi_sq(Q_n)=2^(n-1).

Definition 2.2 permits a partial coloring: it is an onto map from a colored
support `S` to a positive set of `k` colors. At every `v` in `S`, the center
and the same-color colored neighbors must comprise at least half of the
center and all colored neighbors. The center is counted once and uncolored
neighbors are excluded.

## Motivation

Sahbi's source proves the equality through dimension six and poses the
all-dimensional statement as Conjecture 6.4. The frozen repository
hypercube supplies the exact graph on `Fin n -> Bool`, with adjacency given
by Hamming distance one and degree `n`. The target concerns the maximum
over all partial supports, not only parity colorings or total colorings.

## Gap

The finite cases in the source do not imply the universal statement. An
upper bound must control an arbitrary support, where uncolored cube
neighbors are invisible to the source condition. A cardinality comparison
between real function spaces cannot use `Fintype.card_le_of_injective`;
the relevant comparison is finite-dimensional rank after constructing an
injective linear map.

## Route

The canonical consumer is
`D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube`.
For an arbitrary admissible coloring, divide the colors into those with an
internal colored edge and those without. Select two endpoints from each
edged class and one representative from each edge-free class. If `A` is
the full selected set and `T` the edge-free representatives, injectivity of
the selection gives `|A|+|T|=2k`.

Each column indexed by `T` has at most one selected neighbor, by the
sub-quorum condition. Each row indexed by `A` has at most `n-1` neighbors
in `T`: an edge-free representative uses the same degree bound, and an
edged-class endpoint has its selected partner outside `T`.

Bridge Huang's symmetric signed adjacency operator from pinned
`Archive.Sensitivity` to the actual repository cube. It is supported with
absolute value one exactly on cube edges and satisfies `S^2=nI`. For a
vector supported on `T`, rowwise Cauchy-Schwarz and reverse summation bound
the energy on `A` by `(n-1)||x||^2`. The full identity gives `n||x||^2`,
so restriction to `B=V\A` has energy at least `||x||^2` and is injective.
Finite-dimensional rank then gives `|T|<=|B|`. Together with
`|A|+|B|=2^n`, this proves `k<=2^(n-1)`.

For the reverse inequality, give each even-parity vertex its own color.
The support is edgeless, has `2^(n-1)` vertices, and satisfies the exact
partial-color condition. The bounded maximum is proved positive and
attained, so the bounds yield equality.

## Falsifier

An admissible onto partial coloring of some `Q_n`, `n>=2`, with more than
`2^(n-1)` colors would refute the result. A candidate must evaluate closed
neighborhood counts only inside its colored support and count the center
once. A failure of the selected row or column bounds, of the Huang
edge-support bridge, or of injectivity of the restricted map would refute
the proof route. A total-coloring counterexample to a different convention
does not address Definition 2.2.

## Evidence

The versioned HTML for arXiv:2609.25128v1 was read at Definition 2.2,
Lemma 5.4, and Conjecture 6.4. The exact source and quantifiers were
preregistered in issue 9523 before probes. The native Lean source proves
the symbolic result for every `n>=2`, using the existing hypercube and the
pinned `Archive.Sensitivity` operator. Huang's matrix properties are
literature ingredients; the restricted norm/count argument described above
is on the live proof path for the full partial-coloring target.

## Triage

Tier 1: a named conjecture in a paper dated 20 September 2026,
preregistered in issue 9523 under programme issue 8654.
`admission_basis: open-problem-resolution` applies to the exact public
result and its typed Scribe claim.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `IsSubQuorumColoring` | definition | none | not applicable |
| `SubQuorumAttainable` | definition | none | not applicable |
| `subQuorumChromaticNumber` | definition | none | not applicable |
| `subQuorumChromaticNumber_hypercube` | content | none | open-problem-resolution |

The theorem's live content is the restricted signed-matrix energy estimate,
the resulting injection from functions on `T` to functions on `B`, and the
cardinality assembly for arbitrary admissible partial colorings. Its
`escape_witness` is this norm/count/injection argument, while its admission
is the separately preregistered named-open-problem resolution. The theorem
is uniform in `n`, not bounded enumeration, a checker, numeric reduction,
or a certified instance. No standalone wrapper or partial utility theorem
is delivered.

## ASSUMED-UNVERIFIED

The absence of an equivalent prior resolution is known only within the
bounded repository, pinned-library, ecosystem, and literature searches
recorded by issue 9523. No worldwide novelty or priority claim is made.
Independent review, canonical Freeze, CI, merge, and completion audit are
separate lifecycle steps and are not established by this dossier.
