---
slug: oeis-a334595-value-one
bibkey: kagey2020a334595
doi: null
url: https://oeis.org/A334595
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/XorTriangle/ValueOne.result
---

# The value-one terms of OEIS A334595 are exactly the powers of two

## Problem

Peter Kagey's OEIS A334595, revision 18, gives the sequence name
"Binary interpretation of the right diagonal of the XOR-triangle with first
row generated from the binary expansion of n." Its fourth `%C` comment states:

> Conjecture: a(n) = 1 if and only if n is a power of two.

The entry's definition uses the unpadded binary expansion of `n`. The literal
formal claim is
`forall n : Nat, 1 <= n -> (a n = 1 <-> exists k : Nat, n = 2 ^ k)`.
The exponent is allowed to be zero, so `n = 1` is included; `n = 0` is outside
the positive-index domain. The right edge is read from the upper-right corner
to the apex with every position retained, including zero bits.

## Motivation

The frozen theorem settles the exact value-one characterization asked by the
OEIS conjecture while preserving the source's orientation, finite row width,
and positive-index scope. The result is a classification of all positive
inputs, rather than a bounded table or a statement about only record terms.

## Gap

The current OEIS A334595 page still presents the value-one statement as a
conjecture. The bounded source check read the current page and the cited
revision-18 text, including the `%C` conjecture and the `n = 19` example.
Repository search and the checked source notes found no settled proof or
refutation of this exact claim in the searched scope. This is bounded
literature evidence and does not prove that no earlier or external resolution
exists.

The preregistered task is issue [#13120](https://github.com/the-omega-institute/trureturing/issues/13120).
Its target is this positive-index equivalence, with the unpadded
most-significant-first input and the full right-edge word fixed before the
proof. The separate record-position and rotational fixed-point conjectures in
the OEIS entry are outside this settlement.

## Route

The Lean definitions build adjacent Boolean-XOR differences, retain the left
edge at the original row length, reverse the input bits to obtain the
most-significant-first source row, and decode the top-right-to-apex edge as a
binary word. The proof reconstructs a fixed-width source row from its edge,
so the edge map is injective at that width. A value-one edge has only its
final bit set; its unique source row has only its first bit set, which decodes
to a power of two. Conversely, a one-bit source row followed by the reversible
XOR reconstruction yields value one. The reversible-triangle relation is used
as a proof idea adapted from Ilya Bogdanov's MathOverflow answer; no literature
axiom or assumed inverse is imported into Lean.

## Falsifier

A positive natural number `n` for which `a n = 1` but no natural `k` satisfies
`n = 2 ^ k`, or a power of two with `a n != 1`, would contradict the theorem.
Changing the input padding, edge orientation, or retained width would falsify
the source-to-formal correspondence even if a different sequence happened to
have the same initial values.

## Evidence

- Lean source: `D5/S3/Combinatorics/XorTriangle/ValueOne.lean`.
- Frozen result statement identity:
  `sha256:6c80414c7a8fa45b4a58acad5ae5e0f9074246cba40b34d5faece5d4be41b82a`.
- Current source hash:
  `c728ea9c1b66d570d1e0cbef6fc5c82179c468dfc554bf1572dcd0e25448cadb`.
- Current canonical Lean report hash:
  `b942b23bf011115f866e9a9f8e27d3fd2a049f42187ac3818891b8d27b40fc5c`.
- Freeze event `sha256:ed62c7ffabc6a1997763d475dc2d7af0199e8f5aa725619aae7daf38bf7628bd`,
  accepted event file hash
  `6606dcc4136e3d984dfe99bde0b4e9dc67ab36bb48d5cbf7fad528e9dc7f7a92`,
  and generated module-state identity
  `sha256:58a31e6988e11d1b93176a4baf851d4fb489c5325b799f17392e9f0ec3a74904`.
- The compiled declaration has only `propext`, `Classical.choice`, and
  `Quot.sound` in its accepted axiom closure, with no `sorry` or added axiom.
- The OEIS source note and the Bogdanov MathOverflow note preserve the source
  locators, attribution, adaptations, and CC BY-SA 4.0 notices.

## Triage

`theorem`; resolution `proved` for the exact positive-index OEIS conjecture.
The Scribe result carries
`OpenProblemResolutionClaim(ProblemSlugRef("oeis-a334595-value-one"), Proved)`.
No claim is made about the other A334595 conjectures, a least counterexample,
record positions, or rotational fixed-point counts.

**Proved mechanism.** Fixed-width edge reconstruction makes the edge map
injective. The edge word representing one has only its final bit set, and its
unique source row has only its first bit set. With the accepted unpadded input
and edge orientation, this gives the power-of-two characterization for every
positive input, including `n = 1`.

**Extension limits (unresolved here).** Classification of other edge values,
padded inputs, changed edge orientation, and the zero input are outside this
settlement. Reconstruction at a fixed width does not by itself settle these
separate questions; each needs its own statement and proof.

**Consequences and source followups.** The proved positive-index equivalence
can be cited in place of the OEIS value-one conjecture, retaining its input
and edge conventions. The record-position and rotational fixed-point
conjectures remain unresolved here: this settlement supplies no proof of
either and establishes no further dependent claim in the source.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish nonexistence of a prior
resolution, exhaustive priority, or publication novelty. The source-to-Lean
correspondence remains a semantic review obligation in addition to kernel
verification. Finite numerical examples and the `n = 19` orientation check
support encoding review only; the universal result rests on the compiled Lean
proof.
