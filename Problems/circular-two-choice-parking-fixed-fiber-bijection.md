---
slug: circular-two-choice-parking-fixed-fiber-bijection
bibkey: recioui2026circular
doi: 10.48550/arXiv.2609.23607
url: https://arxiv.org/html/2609.23607v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CircularTwoChoiceParkingBijection.result
---

# A canonical fixed-fiber bijection for circular two-choice parking

## Problem

Open Problem 1 of the linked paper asks:

> Give a bijective proof of the factorization of Corollary 1 for d=1,
> refining Theorem 2 to a canonical bijection between each anchor class
> {E=j} intersect C_kappa and the set of classical parking functions.

The relevant specialization has `n>=1`, `m=n+1`, `s=2`, and `d=1`. Every car
has an ordered pair consisting of an anchor and a distinct second choice. The
anchor is tried first. If it is occupied, the car begins a clockwise scan at
the second choice itself, so offset zero must be inspected before later spots.
The matrix `kappa` fixes the positive clockwise increment from anchor to second
for every car, and `j` fixes the actual unique vacancy.

The exact formal target is `result n hn increments j`: for every natural `n`
with `1<=n`, every per-car increment matrix with entries in `1..n`, and every
circular spot `j`, it certifies `Function.Bijective (fixedFiberEquiv n increments
j)`. The referenced equivalence remains the explicit forward map and inverse
between the corresponding literal actual fiber and classical length-`n` parking
functions; `result` is its sole source-level settlement theorem.

## Motivation

The paper proves that every fixed-increment vacancy fiber has the classical
cardinality, but asks for a canonical two-sided map. The formal endpoint keeps
the actual ordered choices rather than replacing them by a count or by an
increment-only encoding. Consequently its inverse answers the structural
question: it reconstructs each car's anchor and second choice while retaining
the prescribed vacancy.

The auxiliary `globalParkingEquiv` packages the result for arbitrary actual
preferences. Its forward map returns the classical parking function, the
original increment matrix, and the actual vacancy. This makes the fixed-fiber
construction observable and reusable, but it is not another resolution of the
paper's fixed-class problem.

## Gap

Rotational equidistribution, Pollak's classical count, the paper's conditioned
count, and the factorization into anchor and increment factors establish only
equal cardinalities. They do not provide a canonical map, an inverse, or a
proof that the inverse reconstructs the literal ordered data. Selecting an
arbitrary equivalence from equal finite cardinalities would also fail to expose
the anchor-priority and offset-zero parking dynamics.

The missing content is therefore an explicit route through the operational
process, with forward and reverse simulations and both inverse laws. Known
enumerative facts receive no new credit in this dossier.

## Route

The construction has two explicit stages.

First, encode each ordered pair by its anchor and positive clockwise increment.
For a fixed increment matrix, extract the anchor vector and rotate it so that
its one-choice vacancy is the prescribed `j`. The reverse map rotates a
one-choice vector according to the vacancy produced after rebuilding with the
fixed increments, then reconstructs every ordered pair as
`(anchor, anchor+increment)`. Rotation equivariance proves the vacancy clauses.
The pointwise identity between decoding and rebuilding, followed by cancellation
of the two vacancy-dependent rotations, proves both inverse laws for
`fixedFiberOneChoiceEquiv`.

Second, cut the circle at `j`. Since `j` is the unique vacancy, all circular
landings lie away from the cut. The `firstFree_cut` theorem shows that the
offset-zero circular scanner becomes the frozen supplier's linear `parkStep`.
Induction on the feedback state proves `cut_run`, so cutting a one-choice fiber
produces a classical parking function. In reverse, add `j` to every classical
preference. The supplier's first-free specification and the theorem that a
free position before the cut prevents the scanner from reaching `j` establish
the reverse feedback-state simulation. Cut and uncut cancel pointwise within
the proved bounds, giving both inverse laws for `oneChoiceClassicalEquiv`.

Composing these stages is `fixedFiberEquiv`. The theorem `result` certifies that
exact map as bijective for every `n>=1`, increment matrix, and `j`; it does not
enumerate fibers or select representatives from a cardinality equality.

## Falsifier

Any of the following would refute the claimed correspondence: a positive `n`,
valid increment matrix, and vacancy `j` for which either composite is not the
identity; a car whose reconstructed anchor or second choice differs from the
input; a run that chooses a later clockwise spot while the second choice is
free; or a forward global output whose increment matrix or actual vacancy
differs from the input observables.

The boundary cases are load bearing. At `n=1`, anchor priority must still win
when the anchor is free and the second choice must be selected at offset zero
when the anchor is occupied. At `n=2`, the scan must continue cyclically past
an occupied second choice to the next free spot. A count agreement alone would
not answer any of these falsifiers.

## Evidence

- Formal endpoint:
  `D5/S3/Combinatorics/CircularTwoChoiceParkingBijection.result`, whose statement
  certifies the bijectivity of the explicit `fixedFiberEquiv` construction.
- Operational support: literal `actualStep`, prefix freshness, unique vacancy,
  rotation laws, increment encode/decode, `fixedFiberOneChoiceEquiv`,
  `firstFree_cut`, `firstFree_ne_vacancy`, and `cut_run`.
- Classical bridge: `oneChoiceClassicalEquiv`, built against the frozen
  `UnitIntervalParkingFoata` supplier without changing that supplier.
- Auxiliary interface: `globalParkingEquiv`; its definition exposes original
  increments and actual vacancy, and its two-sided equivalence recovers every
  car's anchor and second choice.
- Kernel verification at the recorded source hashes covered both fixed-fiber
  inverse laws, both global inverse laws, the two observable projections,
  inverse increment recovery, per-car ordered-choice recovery, and the `n=1`
  and `n=2` priority and scan boundaries. The endpoint axiom closure was
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Preregistration: https://github.com/the-omega-institute/trureturing/issues/9771.
- Primary source and locator: `Library/Combinatorics/recioui2026circular.md`,
  which records the full current-version reading and exact problem wording.

## Triage

`theorem`. The formal endpoint is a uniform theorem certifying the explicit
equivalence with its forward and inverse functions, not a bounded computation
or a count-selected map. The triage applies only to the fixed-increment,
fixed-vacancy statement requested by Open Problem 1. The global observable
equivalence is supporting API surface and carries no separate problem-resolution
claim. No KPI, programme-completion, or worldwide-priority conclusion follows
from this classification.

## ASSUMED-UNVERIFIED

- The repository does not machine-verify that the paper's prose and notation
  are semantically identical to the Lean model. The correspondence above comes
  from reading the full primary source and tracing the literal rule, parameters,
  and quantifiers through the formal definitions.
- Two exact arXiv searches and the first twenty Crossref title results found no
  later exact fixed-increment circular construction. OpenAlex returned HTTP 429
  and was unread. This bounded result does not establish worldwide absence or
  priority, and unpublished, unindexed, paywalled, or author-held material was
  not exhaustively checked.
- The current source record is arXiv:2609.23607v1. A later source version could
  change the problem wording or scope and would require a new comparison.
