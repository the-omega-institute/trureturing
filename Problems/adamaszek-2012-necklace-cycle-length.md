---
slug: adamaszek-2012-necklace-cycle-length
bibkey: adamaszek2012hardsquares
doi: null
url: https://arxiv.org/abs/1202.1655v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result
---

# Adamaszek's Conjecture 7.4 on necklace cycle lengths

## Problem

M. Adamaszek, *Hard squares on cylinders revisited*, arXiv:1202.1655v2,
Section 7, Conjecture 7.4, states:

> The length of every cycle in the graph Neck(k, n) divides n−3k. In other
> words, for every (k, n)-necklace N we have Tⁿ⁻³ᵏN = N.

The section assumes even positive circumference n and positive k. A necklace
has 2k distinct stones, each with signed vector −2, −1, 1 or 2. Consecutive
stones have opposite directions. Away-facing gaps are odd; toward-facing gaps
plus both vector lengths are odd. A toward-facing gap is at least three,
and at gap three both vectors have length one. Necklaces are identified under
circle isometries. T performs simultaneous JUMP, then TURN
(−2→1, −1→2, 1→−2, 2→−1), then FIX of facing gaps three by shortening
length-two vectors to one. Issue #11582 fixes this reading before the probe.

## Motivation

`D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result` proves
that for every legal necklace N the iterate Tⁿ⁻³ᵏN equals an isometric copy of
N. The witness in the proof is a rotation. This proves the source's equivalent
return statement on the isometry classes used as the vertices of Neck(k, n).

## Gap

The source records experimental verification for even n≤36. The literature
check in #11582 classifies this as a tier-1 named conjecture. The five arXiv
sources among the six citing records were checked; none supplied a settlement.
The arXiv searches for hard squares, independence complexes on cylinders, and
Adamaszek necklaces, and the formal-conjectures searches, yielded no matching
settlement in their searched scope. This is `not-found-in-searched-scope`;
the unread citing record and MathDB limitation are retained below.

## Route

1. Sort the occupied integer sites and extend them to positions xᵢ on ℤ,
   with xᵢ₊₂ₖ=xᵢ+n and periodic vectors vᵢ. The source's odd-gap rules make
   every gap integral, so choosing an occupied point as origin loses no
   isometry class.
2. Compress each labelled stone to yᵢ=2xᵢ+vᵢ−3i. These positions are strictly
   ordered and have circumference 2L, where L=n−3k. The pair conditions imply
   4k≤n and hence L>0. The compressed velocity is
   uᵢ=sign(vᵢ)(2|vᵢ|−3), which is either −1 or 1.
3. A physical step is compressed free motion yᵢ↦yᵢ+uᵢ followed by relabelling.
   FIX acts exactly at disjoint crossing pairs and exchanges the compressed
   velocities. The integer lift represents both the original configuration
   and every physical iterate, including the pair across the origin.
4. At time L, displacements L and −L agree modulo 2L. Strict ordering makes
   the resulting bijection of the integer labels a translation i↦i+r.
5. Telescoping the first moment over a full label window gives r as minus the
   number of initial negative compressed velocities. The even physical
   circumference and gap parities give r≡L (mod 2), recovering the physical
   signs as well as the compressed velocities. This recovers each vector
   and translates every physical position by (L−3r)/2, a rotation modulo n.

## Falsifier

A faithful proof requires the complete cyclic representation, unique incoming
stones for JUMP, simultaneous FIX, preservation of the legal pair conditions,
and recovery of physical signs from winding parity. A compressed-velocity
argument omitting sign recovery would not establish the physical return:
two different physical vectors share each compressed velocity.

## Evidence

The canonical Lean source is
`D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.lean`.
Its only source-authored public theorem is `result : claim`. The definitions
retain the source's entire legal-necklace domain. Circle isometries use pinned
Mathlib `DihedralGroup n`; the configuration action also reverses vectors on
reflection. The proof uses no project-level frozen prerequisite, `sorry`,
`native_decide`, or new axiom. Its axiom closure is `propext`,
`Classical.choice`, and `Quot.sound`.

## Triage

Tier 1 external named conjecture from the 2012 source; preregistered in #11582
before the Lean probe. Resolution: proved. Admission basis:
`open-problem-resolution`. Proof shape: `content`, with the public result
itself produced by cyclic representation, compressed motion, winding and
parity reconstruction. Utility: `none`; this is a universal theorem rather
than a bounded computation or certified instance.

### What the settlement shows

- **Proved in this module:** every legal necklace in the stated even-n,
  positive-k domain returns after L=n−3k steps up to rotation. The source
  permits both rotations and reflections; the proof needs only rotations.
  The period bound is a common return time and does not assert that each
  cycle has length exactly L.
- **Proved inside the result's live proof:** legal configurations admit the
  complete periodic integer lift, JUMP has unique inflow, T preserves legality,
  4k≤n follows from consecutive-pair conditions, and compressed free motion
  plus winding parity recovers physical positions and signed vectors.
  No additional 4k≤n hypothesis is imposed on the public theorem.
- **Open as further Lean obligations:** extension to odd n or altered gap
  rules, classification of exact periods, and formal translation of the
  source's pattern generating functions. The parity reconstruction uses the
  source's even-n hypothesis; no relaxed-hypothesis result is asserted here.
- **Literature consequence:** Theorem 7.6 states that Conjecture 7.4 implies
  Conjecture 1.4; Theorem 7.5 relates generating-function denominators to
  necklace cycle lengths. The return theorem supplies their conjectural
  necklace-period input. Those source implications are not formalized in
  this module; no separate Lean settlement of Conjecture 1.4 is claimed.

## ASSUMED-UNVERIFIED

The non-arXiv citing record was not read in the literature check in #11582.
The MathDB search was client-rendered and was not independently verified.
The bounded search establishes no exhaustive worldwide novelty or priority.
Kernel checking establishes the encoded theorem; source fidelity and these
literature boundaries remain distinct from the proof.
