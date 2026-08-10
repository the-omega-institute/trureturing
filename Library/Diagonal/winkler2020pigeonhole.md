---
bibkey: winkler2020pigeonhole
authors: Peter Winkler
year: 2020
title: The Pigeonhole Principle
doi: 10.1201/9780429262913-ch12
claim: Assigning more objects than available readings forces two distinct objects to receive the same reading.
strata_touched:
  - D5/S0/Diagonal/PigeonholeFiber
license: citation-only
triage: anchor
---

# The Pigeonhole Principle

Peter Winkler's chapter supplies a modern literature anchor for the classical
pigeonhole principle. The repository theorem states the same collision
principle in cardinal language: if the cardinality of the codomain is strictly
smaller than the cardinality of the domain, a function between them is not
injective and therefore has a fiber containing two distinct elements.

Only the collision statement is attributed to the chapter. The repository
proof is a thin formal reduction through Mathlib's characterization of
cardinal comparison by injections and its characterization of a
non-injective function by two unequal arguments with equal images. The note
does not attribute those Lean definitions or the exact proof term to the
source.

## Search log

- 2026-08-11: Queried DOI metadata for
  `10.1201/9780429262913-ch12`. The resolver identified Peter Winkler, the
  exact chapter title "The Pigeonhole Principle", the 2020 publication date,
  the containing book *Mathematical Puzzles*, A K Peters/CRC Press, and pages
  151-162.
- 2026-08-11: Cross-checked the formal boundary against the pinned Mathlib
  declarations `Cardinal.mk_le_of_injective` and
  `Function.not_injective_iff`. The Lean statement uses the strict cardinal
  inequality directly, so the finite case is a specialization rather than a
  separate hypothesis.

## Verified locator

- DOI: https://doi.org/10.1201/9780429262913-ch12
