---
slug: adamson-positive-uniform-hierarchy
bibkey: adamson2026twoword
doi: null
url: https://arxiv.org/abs/2605.27183v1
triage: theorem
motivation_gids:
  - D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform
  - D5/S0/Diagonal/PigeonholeFiber
  - D5/S1/Words/GraphRepresentation/UniformVertexExtension
  - D5/S1/Words/GraphRepresentation/UniformHierarchy.result
---

# Every positive-uniform adjacent class inclusion is proper

## Problem

Adamson, Dietz, Fleischmann, Huch and Sacher, *2-word-π-representable Graphs*,
arXiv:2605.27183v1, Conjecture 31, PDF p. 15, states:

> For each k ∈ ℕ, the inclusion 𝒢_k ⊆ 𝒢_(k+1) is proper.

The source convention starts ℕ at 1. For a finite simple graph G on V,
membership requires actual words w,v over V, each containing every vertex
exactly k times. For every distinct a,b, G.Adj(a,b) holds if and only if
their ordered two-letter List projections in w and v are equal. Positive
counts give both full alphabets. Single-word alternation and unions of word
representation languages are different models.

The exact full target has two clauses for every positive k: inclusion for
every finite graph, and existence of a finite graph on one and the same
carrier with a (k+1)-uniform representation and no k-uniform representation.
An assumed nonuniversality theorem, a fixed-k result, or vertex extension
alone does not settle either the full family or this named problem.

## Motivation

The earlier Dietz–Fleischmann–Huch–Sacher four-author contribution in IFIG
Report 2501, printed pp. 21–24 (PDF pp. 29–32), states the same assertion as
Conjecture 3.2 on printed p. 23. Its Open Problems section on p. 24 says
that only k=1 strictness was proved. Its actual body is available at
<https://www.informatik.uni-giessen.de/theorietag2025/2025-Theorietag35-Schotten.pdf>.
This is an earlier statement of the same problem, not a second question.

The full hierarchy asks for an unbounded proof about the representation
parameter. It is a Tier-1 proof/family target under issue
<https://github.com/the-omega-institute/trureturing/issues/12945>.
No global priority or established central-bottleneck claim is made.

## Gap

[`UniformHierarchy.result`](../D5/S1/Words/GraphRepresentation/UniformHierarchy.lean)
proves the complete assertion. Its closed claim quantifies over every positive
k and every finite carrier at an arbitrary type universe. It also supplies an
induced subset of the finite membership graph on
Fin(64k²) ⊕ Finset(Fin(64k²)), with a (k+1)-uniform representation and no
k-uniform representation on precisely the same original subset subtype.
Both representation clauses use the admitted literal InG and actual List words.
The only hypotheses within the claim are positive k, finiteness and decidable
equality of the arbitrary carrier; none assumes a mathematical part of the target.

## Route

The known all-positive-k nonuniversality component is proved inside the full
consumer. In the membership graph with m=64k², each right vertex has two
ordered k-cut lists with entries at most km. Their signatures occupy at most
(km+1)^(2k) ≤ 2^(20k²) < 2^m states. The existing arbitrary-cut reconstruction
and pigeonhole suppliers force two distinct subsets to have equal neighborhoods,
a contradiction. Right labels are normalized separately by their injective
Unit-marker maps; their original differently labelled projections are not equated.
The two left restrictions may have different orders, and tied cuts are retained.

Nat.find selects a nonrepresented induced subset of least cardinality.
The whole-set subtype is a witness by actual word transport. The empty
subtype has []/[] representations, so a vertex x exists. The erased subset
is represented at k by minimality. Its graph is literally the vertex deletion
after E=optionCongr(d).trans(optionSubtypeNe(x)), where d keeps retained
underlying vertices. The frozen extension gives actual words at k+1;
mapping both through E preserves every count and both directions of each
adjacency iff on the original carrier. No hereditary-class axiom or executable
minimum search is used. A common once-each enumeration appended to both
words proves inclusion, including the empty carrier.

## Falsifier

An equivalent prior settlement, a source-model mismatch or an unresolved
premise in the full consumer bars a named-problem settlement. An auxiliary
checkpoint contributes no solved-problem count. The full result would fail
source fidelity if either actual list omitted a whole-carrier count or the
adjacency equivalence omitted a distinct pair, a nonedge, a reversed pair
or an empty carrier. Kernel closure does not establish global priority.

## Evidence

The primary v1 PDF has SHA-256
`f978a9e9de5cfaf8adfba59125cf16293b17f6b969f5f72594eab7a0cec719ca`.
The earlier IFIG PDF has SHA-256
`2aaa473fb648f515a69f9ce488bf557b83b4329eea009182f5131243eee81af2`.
Definitions and the relevant construction, graph-operation and hierarchy
proof sections were read from the actual bodies.

Bounded repository and authenticated issue/PR searches found the
preregistration and the earlier explicit G₂ obstruction, without an exact
hierarchy settlement or owner in that searched scope. Pinned Mathlib and
public Lean repository searches found no exact extension supplier. The
inspected public WordRepTensor source uses single-word alternation.

## Triage

`theorem` classifies the full unbounded family target. The new module retains
only the necessary parameterized membership graph, the full source claim and
one result. `result` has `proof_shape: content`: its live ordered cut encoding,
all-parameter cardinal estimate and minimum-induced-subset inference are not
a specialization or logical repackaging of frozen results. Its
`admission_basis: open-problem-resolution` is the preregistered full
Conjecture 31 assertion in issue 12945. The graph and claim are supporting
definitions, not separate settlements. `utility: none` denotes an unbounded
structural proof, without finite graph enumeration, a checker, numerical
reduction or certified positive instance. Reg enrollment is paused.
Narrow final-byte review and ordinary required-CI publication remain
necessary before a normally merged problem settlement
can increment the KPI.

## ASSUMED-UNVERIFIED

The same-title *Gradiva*, 8(9) (2022), pp. 528–533 citation is a bibliographic
match; neither its journal body nor the body associated with SSRN DOI
10.2139/ssrn.5336494 has been verified. The SSRN abstract page returned
HTTP 403. Their source-model and result comparison remains unverified.
These observations support no worldwide absence guarantee or priority claim.
