---
slug: rectangle-rowmotion-max-minus-min-homomesy
bibkey: elder2024toggling
doi: 10.48550/arXiv.2307.08520
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy
---

# Max-minus-min homomesy for rectangle interval-closed rowmotion

## Problem

Elder, Lafrenière, McNicholas, Striker and Welch, *Toggling, rowmotion, and
homomesy on interval-closed sets*, arXiv:2307.08520v2, Conjecture 4.9, states
that for every product of two finite chains the number of maximal elements
minus the number of minimal elements is 0-mesic under rowmotion on
interval-closed sets. Lafrenière, Lewis, McNicholas, Striker and Welch,
*Interval-closed set rowmotion and homomesy on products of two chains*,
arXiv:2505.04000v1, restates this target as Conjecture 4.2.

The exact formal target keeps all source quantifiers: positive `m,n`, every
`N` and equivalence `e : Fin N ≃ Fin m × Fin n` satisfying the reverse
linear-extension condition, and every order-convex initial set `I`, including
the empty set. `literalOrbit e I` is the finite set of distinct states reached
by iterating the literal successive toggle trace. `maxMinusMin` is the integer
cardinality difference of global maxima and minima in the actual state. The
conclusion is the sum of this statistic over the actual distinct orbit states.

## Motivation

The result gives the exact all-rectangle resolution requested by the original
conjecture. It is a uniform symbolic theorem: the legal enumeration is an
explicit parameter, the orbit contains actual reachable states once each, and
no finite testing range or generic rowmotion law is used.

## Gap

The source conjecture did not supply a proof for all products of two chains.
The formal gap is the zero sum of `maxMinusMin` over each literal orbit under
the complete reverse extension and interval-closed toggle definitions.

## Route

The proof counts strict rectangular floor corners with the frozen
`RectangularCorner.rectangular_corner_card` theorem. Coordinate reversal gives
the dual count. The frozen `RowmotionEndpointTransport.endpoint_transport`
theorem transports the actual endpoint pairs through one literal trace; a
reverse trace recovers the initial state. These facts yield an integer
coboundary for `maxMinusMin`. The actual finite orbit is closed and the trace
is injective on it, hence a permutation, so the coboundary telescopes.

## Falsifier

A natural pair of positive dimensions, a legal complete reverse extension, and
an order-convex initial set whose actual distinct trace orbit has a nonzero
integer sum would refute the theorem. A test using a different toggle,
repeated orbit states, a selected finite prefix, or a stronger reversal-
commutation premise would test a different statement.

## Evidence

The theorem `result` in
`D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.lean` compiles at the
pinned Lean and Mathlib versions. Its exact imported declaration has the full
telescope above, and its complete kernel axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`. The source has exactly the
two essential definitions `literalOrbit` and `maxMinusMin` and one public
result; all endpoint, duality, counting, and orbit arguments are local to
that result. The published source correspondence is arXiv:2307.08520v2
Conjecture 4.9 and arXiv:2505.04000v1 Conjecture 4.2. Preregistration for
this exact external target is issue
[11891](https://github.com/the-omega-institute/trureturing/issues/11891).

## Triage

`theorem`; resolution `proved` for the original all-rectangle max-minus-min
homomesy conjecture. The result is admitted under
`admission_basis: open-problem-resolution`, with conservative
`proof_shape: bind-only` and `utility: none`. The follow-up paper's separate
signed-cardinality result, its explicit orbit descriptions for `[2] × [n]`,
and any broader poset or higher-product statement are outside this result.

### What the settlement shows

Proved in this module: let `H(S)` count pairs `(b,a)` with `b` maximal in
`lowerClosure S \ S`, `a` maximal in `S`, and both coordinates of `b`
strictly smaller than those of `a`. The rectangular corner identity and its
coordinate-reversed dual, together with endpoint transport, give
`maxMinusMin S = H(R(S)) - H(S)` in the integers, where
`R(S) = trace(e,S,N)`. The reverse trace recovers every order-convex input,
so `R` permutes the finite set of distinct reachable states. Summing this
coboundary over that set gives zero. Trace indices beyond `N` retain the
completed trace state for a fixed input; repeated rowmotion instead reapplies
`R` to the resulting state.

Proved in this module: this mechanism covers every positive product of two
finite chains, every complete reverse extension, and every interval-closed
initial set, including the empty set. It settles the max-minus-min assertion
of arXiv:2307.08520v2 Conjecture 4.9 and its restatement in
arXiv:2505.04000v1 Conjecture 4.2. For the `[2] × [n]` cases discussed in the
follow-up, it supplies this same zero-sum statistic without an explicit orbit
classification. The follow-up's separate signed-cardinality result and orbit
descriptions retain their separate statements and proofs.

Outside this module: no extension to general posets or products of more than
two chains is established here. The unrestricted higher-product extension is
false: [arXiv:2307.08520v2, Remark 4.10](https://arxiv.org/html/2307.08520v2#S4.Thmthm10)
gives counterexamples `[2] × [2] × [5]` and `[2]^4`. No relaxation of the stated
hypotheses, consequences for other source questions, or claims about their
open status follow from this result.

## ASSUMED-UNVERIFIED

The source review is bounded to the named arXiv versions and the registered
exact target; it does not establish exhaustive worldwide priority or exclude
unindexed, unpublished, or later proofs.
