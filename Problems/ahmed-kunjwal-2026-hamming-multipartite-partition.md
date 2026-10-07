---
slug: ahmed-kunjwal-2026-hamming-multipartite-partition
bibkey: ahmedkunjwal2026quasiprocess
doi: 10.48550/arXiv.2610.00579
url: https://arxiv.org/html/2610.00579v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result
---

# All-direction maximal clique partitions of mixed-alphabet Hamming graphs

## Problem

Ahmed and Kunjwal, *Characterizing unitaries via quasi-process functions*,
arXiv:2610.00579v1, Conjecture V.1 in Section V.2, ask for genuine
multipartiteness of maximal-clique partitions whenever the number of
coordinates exceeds three. The surrounding definitions mean that every
coordinate direction must occur. Alphabet sizes are independent and at
least two. Definition V.1 defines adjacency by disagreement at exactly one
coordinate; maximal means inclusion-maximal, not maximum cardinality.

The exact formal statement is: for every natural `n` with `4 ≤ n`, every
`d : Fin n → ℕ` with `∀ i, 2 ≤ d i`, and
`V = (i : Fin n) → Fin (d i)`, there is a set `P : Set (Set V)` such that

- Every `S ∈ P` is nonempty, is a full coordinate line, and satisfies
  `Maximal (graph d).IsClique S`.
- For every `x : V`, there is exactly one `S` such that `S ∈ P ∧ x ∈ S`.
- For every `i : Fin n`, some `x : V` has `line i x ∈ P`.

There is no equal-alphabet assumption, upper dimension bound, finite search
bound, or assumed binary matching supplier.

## Motivation

The graph partition is the source's combinatorial formulation of using each
party in mutually exclusive controlled-circuit constructions. The Lean
result supplies the entire graph statement. It does not formalize the
circuit interpretation, unitary operators, or quasi-process functions.

## Gap

Issue #13221 preregisters the complete universal assertion before any Lean
probe. The accessible-source check is recorded in the matching literature
note and in the issue. No exact supplier was found in the relevant project
Hamming declarations or pinned Mathlib SimpleGraph APIs. Mathlib's clique,
maximality, dependent update, and finite tuple APIs are reused directly.
The source's binary case is attributed to Erde, arXiv:2404.03950; the binary
construction is an internal ingredient, not an independent novelty claim.

## Route

A binary selector chooses a coordinate at each vertex and keeps that choice
when the chosen coordinate is flipped. The four-coordinate seed selects the
edges 0110–1110, 0111–1111, 1000–1100, 1001–1101, 0000–0010,
0001–0011, 0100–0101, and 1010–1011. Kernel-reduced `decide` checks its
stability, every-direction witnesses, and two distinct reserve edges in the
first direction.

Induction appends one Boolean coordinate. Over one reserve edge's two tails,
it chooses the new direction; elsewhere it keeps the old selector. Flip
involution proves the complement of that removed orbit is invariant.
Nonzero-direction witnesses avoid the orbit, the other distinguished edge
survives, and its two layer copies become the next reserves. This proves the
uniform construction for every dimension at least four.

For mixed alphabets, project zero to false and every positive symbol to true.
At a mixed vertex use its binary image's chosen direction. Along the entire
full line the binary image either stays unchanged or becomes its binary
partner; therefore the selector and selected full line are constant. Fixing
actual off-direction coordinates splits the inverse image of a binary edge
into several full lines. The range of selected lines gives existence and
unique membership. To exclude an outsider from a larger clique, retain its
off-direction disagreement and select a line point that also disagrees in
the direction. Each alphabet has two symbols, so such a point exists.
The coordinatewise zero/one section gives a witness in every direction.

## Falsifier

A vertex omitted from the family, two distinct family members containing the
same vertex, a member omitting a symbol from its varying coordinate, an
extendible member clique, or a missing coordinate direction would violate
the statement. The theorem proves each of these clauses for all permitted
parameters. A different source meaning of genuine multipartiteness or
maximality would invalidate the source transfer, even with a correct Lean
proof; that transfer remains subject to independent review.

## Evidence

The scoped canonical build of
`D5.S3.Combinatorics.Hamming.HammingMultipartitePartition` succeeds at
project base `e4365d8215799efe75a9e5bf74091c39d0b5d20f`, Lean 4.33.0, and
Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. A current exact
application with the dependent product written out also compiles. The
source-bound scoped inspector and stock axiom check agree: the result's
recursive proof-and-type closure is exactly `propext`, `Classical.choice`,
and `Quot.sound`. The public graph and line definitions have no axioms.
There is no `sorry`, new axiom, `native_decide`, or `Lean.ofReduceBool`.

The only public declarations are `Vertex`, `graph`, `line`, and `result`.
The result's statement identity is
`sha256:c59baac6ce3f9997e6571f28a464a453ef48319f008315115e8290dc4854cd1c`.
All seed, selector, induction, projection, and clique helpers are private
and consumed by the result. A finite seed alone is not the delivered result.

## Triage

`theorem`, with the complete universal graph assertion kernel proved.
The public definitions have `proof_shape: definition`; the result has
`proof_shape: content`. Its live construction uses the all-dimension selector
induction and full-line lifting. The private finite seed is normalization
and carries no separate contribution claim. `admission_basis:
open-problem-resolution` refers to issue #13221. `utility: kind=none` applies
to the universal theorem; it is not an independently delivered positive
finite instance. Registration is paused; no Reg sources or registration
issues are part of this contribution.

The mechanism shows that binary selector stability is sufficient to lift
partitions to independently varying alphabets. It supplies existence, not
optimal line counts or prescribed numbers of lines in each direction.
Lower-dimensional impossibility and the source's quantum interpretation
are separate questions. The module is frozen in the current worktree through
the canonical uncovered deposit route; generated Blueprint validation,
independent review, required CI, and the remote PR lifecycle remain separate
gates. The current whole-repository report is
`sha256:1139946c59d808af62edf7cd3fddcf2f2eec97fee78884a0f92aa0942a8d966f`.
No LeanEval score mapping, acceptance, priority, or campaign completion is
claimed.

### What the settlement shows

The proved mechanism is the binary selector induction together with its
stability under coordinate flips. Projecting each positive alphabet symbol to
one lifts that selector to every mixed-alphabet full line, and fixing the
off-direction coordinates gives unique membership and maximality. The result
therefore covers every dimension `n ≥ 4` and every independent alphabet-size
function with `d(i) ≥ 2`; it does not establish optimal line counts or a
prescribed number of lines in any direction. The binary case remains credited
to Erde as recorded above, while the source's circuit, unitary and
quasi-process interpretations remain outside this formal theorem.

## ASSUMED-UNVERIFIED

Source transfer to Conjecture V.1 awaits the controller's independent review.
The accessible literature check is not exhaustive; unindexed or inaccessible
resolutions remain unexcluded. The source's identification with MECC circuits
and quasi-process functions is not formalized. The result is a development
contribution at Lean 4.33.0, not an official Lean 4.35 benchmark certificate.
Repository admission and publication require their own evidence.
