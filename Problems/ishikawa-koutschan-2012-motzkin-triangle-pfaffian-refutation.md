---
slug: ishikawa-koutschan-2012-motzkin-triangle-pfaffian-refutation
bibkey: ishikawa2012holonomic
doi: 10.48550/arXiv.1201.5253
url: https://arxiv.org/abs/1201.5253v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result
---

# Ishikawa and Koutschan's Pfaffian conjecture for the Motzkin triangle, part (i)

## Problem

Ishikawa and Koutschan write `𝓜^{(k)}_i` for the number of Motzkin paths
from `(0,0)` to `(i−1,k−1)`, with steps `U = (1,1)`, `H = (1,0)`,
`D = (1,−1)` that never run below the horizontal axis, and define the
Pfaffian of a skew-symmetric `2n × 2n` matrix as the signed sum over the
partitions of `[2n]` into two-element subsets. Part (i) of their Conjecture
`conj.gen` states, for positive integers `n` and `k`:

> Pf((j−i)𝓜^{(k)}_{i+j−2})_{1≤i,j≤2n} equals ∏_{i=0}^{m−1}∏_{j=0}^{k−1}(4ki+2j+k)
> if m = n/k is an integer, and it equals
> (∏_{j=1}^{⌊k/2⌋} 1/(2j−k))(∏_{i=0}^{m−1}∏_{j=1}^{k}(4ki+2j−k)) if k is odd and
> m = (n+⌊k/2⌋)/k is an integer. The Pfaffian is zero in all other cases.

At `k = 1` this is the paper's Theorem `thm.pfMotz`. Issue #10039 fixes the
readings: the Pfaffian is the source's matching sum over the rationals; the
value `𝓜^{(k)}_0` enters only the diagonal entry at `i = j = 1`, where it is
multiplied by `j − i = 0`; the first case is read as `k ∣ n` and the second as
`k` odd with `k ∣ n + ⌊k/2⌋`, the first taking precedence (both hold only at
`k = 1`, where the two products agree); part (ii) is not settled.

## Motivation

The frozen declaration
`D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result`
proves that part (i) is false as printed: at `k = n = 2` the Pfaffian is `−8`
and the printed product is `8`. The formal statement makes no claim about a
sign-corrected version of the conjecture.

## Gap

Issue #10039 preregisters the published conjecture and its literature check.
MathDB `/p/322920` has status `open` with zero solutions. Semantic Scholar
lists ten citing items; the Motzkin section of arXiv:2008.09776 reproves the
case `k = 1` and treats Delannoy, Schröder and Narayana analogues, and
arXiv:1112.0647 and arXiv:2401.08481 contain no Motzkin-triangle Pfaffian; the
remaining items are lecture notes, reports and book chapters whose full text
was not obtained. The source remarks that its method does not apply for
`k ≥ 2`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent refutation.

## Route

The column `𝓜^{(2)}_1, …, 𝓜^{(2)}_5` is `0, 1, 2, 5, 12`, so the upper
entries of the `4 × 4` matrix are `a₁₂ = 0`, `a₁₃ = 2`, `a₁₄ = 6`, `a₂₃ = 2`,
`a₂₄ = 10`, `a₃₄ = 12`, and

`Pf = a₁₂a₃₄ − a₁₃a₂₄ + a₁₄a₂₃ = 0 − 20 + 12 = −8`.

Since `2 ∣ 2` with `m = 1`, the printed value is `∏_{j=0}^{1}(2j+2) = 8`. The
Lean kernel evaluates both sides from the definitions.

## Falsifier

The refutation would fail if the source's Pfaffian convention gave `+8` for
this matrix. The source fixes the convention by its matching-sum definition,
under which its own Theorem `thm.pfMotz` holds with a positive sign; the
formal definitions reproduce that theorem at `n = 1, 2`.

## Evidence

Exact rational computation with two independent Pfaffian routines (first-row
expansion and the permutation formula divided by `2^n n!`) gives `−8` at
`k = n = 2`, reproduces `∏(4i+1)` at `k = 1` for `n = 1, …, 6`, and finds the
mismatches `(k,n) = (2,2), (3,3), (3,5)` among `k, n ≤ 5`, each a pure sign
flip. A skew elimination routine, checked against the expansion for
`k ≤ 3`, `n ≤ 4`, extends this to `k ≤ 8`, `n ≤ 16`: the zero pattern of the
printed statement is right in all 128 cases, and the 12 mismatches among its
52 nonzero cases, at `(k,n) = (2,2), (2,6), (2,10), (2,14), (3,3), (3,5),
(3,9), (3,11), (3,15), (6,6), (7,7), (7,11)`, are pure sign flips. Part (ii)
behaves the same way, with 14 sign flips among 59 nonzero cases, starting
with `−15` against the printed `15` at `k = n = 2`. In Lean, the formal `motzkinTriangle` gives `1, 1, 1, 2, 4, 9, 21` at
`k = 1` and `0, 0, 1, 2, 5, 12` at `k = 2` for `i = 0, …, 6` and `0, …, 5`,
the formal Pfaffian gives `1` and `5` at `k = 1`, `n = 1, 2`, and `0` at
`(k,n) = (2,1), (3,1)`; the kernel also rejects the value `−5` at
`k = 1, n = 2`. The Lean proof has only the standard axiom closure `propext`,
`Classical.choice`, and `Quot.sound`.

## Triage

Tier 1 external named conjecture, preregistered in issue #10039 before the
probe. The result has `proof_shape: bind-only`, `escape_witness: null`, and
`admission_basis: open-problem-resolution`. Its computational use is a
`certified-instance` with `basis=refutes`: the result negates the closed
claim. Resolution: `refuted`, for part (i) as printed. Part (ii) and any
sign-corrected statement are outside its scope.

## ASSUMED-UNVERIFIED

No sign-corrected formula is proposed or checked beyond the listed range. The
citing items without obtained full
text were not read. The bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent refutation. The
Lean kernel does not authenticate the external source or its version history.
