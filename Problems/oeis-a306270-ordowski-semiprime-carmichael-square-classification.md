---
slug: oeis-a306270-ordowski-semiprime-carmichael-square-classification
bibkey: ordowski2020a306270
doi: null
url: https://oeis.org/A306270
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification
---

# Ordowski's A306270 semiprime classification

## Problem

OEIS A306270, NAME (`%N`, verbatim):

> Composite numbers k such that b^(k(k-1)) == 1 (mod k^2) for every b coprime to k.

The offset is `%O 1,1`. The explanatory COMMENT (`%C`, verbatim) is:

> These are composites k such that lambda(k^2) divides k(k-1), where lambda is the Carmichael function A002322.

Ordowski's settled COMMENT (`%C`, verbatim) is:

> Conjecture: all semiprimes > 4 in this sequence are in A190275. - _Thomas Ordowski_, Jul 19 2020

The following COMMENT records the finite verification:

> The conjecture was verified up to 1063290841. - _Amiram Eldar_, Jul 19 2020

OEIS A190275, NAME (`%N`, verbatim):

> Semiprimes of the form p*(p^2 - p + 1).

Define `mem k` to mean that `k` is composite, `1 < k`, and for every natural
`b` coprime to `k`, `b^(k*(k-1)) ≡ 1 [MOD k^2]`. The full-quantifier reading
is: for every pair of natural primes `p` and `q` with `p ≤ q`, if `4 < p*q`
and `mem (p*q)`, then `q = p^2-p+1`. Thus the semiprime is
`p*(p^2-p+1)`, as required for A190275. All subtraction is truncated natural
subtraction. The scope wall is only Ordowski's Conjecture sentence for every
semiprime `k > 4`; no assertion about non-semiprimes or the finite verification
bound is included.

## Motivation

The independent question is Ordowski's named classification of every
semiprime greater than four in A306270. It connects the universal modular
condition defining A306270 with the explicit factor form defining A190275.
The public surface is exactly the membership definition and the classification
theorem.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the line Conjecture
(2020-07-19) with only Eldar's finite verification to 1063290841; OpenAlex
`"A306270"` 0 hits; Math.SE API `A306270` 0 hits and
`b^(k(k-1)) mod k^2 semiprime` 0 hits; GitHub code search in
google-deepmind/formal-conjectures 0 hits. The Carmichael-function facts used
are textbook; the named classification itself was not found in these surfaces. A GPT Pro reading of arxiv.org, openalex.org and math.stackexchange.com by A-number and by the defining phrases also found no proof; that reading is reported by the selection seat and is ASSUMED-UNVERIFIED.
Historical openness beyond them is ASSUMED-UNVERIFIED.

Repository prior art at `origin/dev`: `git grep -E 'A306270|A190275'` found 0
files in D5, Blueprint, Library, and Problems. Pinned Mathlib has
`Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean` and
`Mathlib/RingTheory/ZMod/UnitsCyclic.lean`, including
`ZMod.isCyclic_units_of_prime_pow`, but no statement of this classification
was found. A search of D5 for the conclusion shape and the two OEIS identifiers
also returned no result. Numerics over all 5,081 semiprimes `k ≤ 20000` found
the members `4, 6, 21, 301, 2041` and zero violations for `k > 4`.

Pre-registration: issue #8213 (2026-09-15T22:10:45Z).

The theorem has `proof_shape: content` and
`admission_basis: escape-witness` under issue #8213. The escape witness is the
public conclusion in the permitted second form, produced by a new live
divisibility construction rather than by binding an existing classification.
The new intermediate propositions on that path are the bridge
`lambda((pq)^2) | pq(pq-1)`, the two consequences
`p(p-1) | pq(pq-1)` and `q(q-1) | pq(pq-1)`, the strict inequality `p < q`,
and, in the odd-prime branch, `p-1 | q-1` together with
`q-1 | p(p-1)`. Writing `q-1=(p-1)t` then gives `t | p`; primality and the
strict inequalities force `t=p`, which is the claimed equality.

The four section 3.2 tests hold. First, the public conclusion is the type of
the elaborated `result` constant, and every named intermediate proposition is
represented by a live `have` in its proof term. Second, repository and pinned
Mathlib searches found no classification theorem, and the conclusion cannot
be obtained from the membership hypothesis by instantiation, projection, or
normalization; the Carmichael bridge and factor-divisor construction are
required. Third, the witness is not a definition, alias, or restatement of a
hypothesis. Fourth, the bridge, equal-prime contradiction, and final divisor
chain remain on the live path after reduction; removing any of those branches
leaves the corresponding conclusion unproved. Direct frozen dependencies:
none, Mathlib only.

The computational-content classification is `none`: both declarations are
unbounded symbolic mathematics, not bounded enumeration, a certified finite
instance, checker infrastructure, or a conditional numerical reduction.

## Route

1. Convert the universal congruence into
   `carmichael ((p*q)^2) ∣ (p*q)*(p*q-1)` through the exponent of the unit
   group modulo `(p*q)^2`.
2. Use divisibility under `p^2 ∣ (p*q)^2` and `q^2 ∣ (p*q)^2`, together with
   the Carmichael values at prime squares, to obtain the two factor-order
   divisibilities.
3. Exclude `p=q` by applying the Carmichael value at `p^4`; the resulting
   divisibility would force the prime `p` to divide one.
4. Resolve `p=2` directly. Otherwise cancel coprime factors to prove
   `p-1 ∣ q-1` and `q-1 ∣ p(p-1)`, then use primality to identify the quotient
   as `p` and rearrange to `q=p^2-p+1`.

## Falsifier

A pair of primes `p ≤ q` with `4 < p*q` satisfying the universal A306270
congruence but with `q ≠ p^2-p+1` would falsify the theorem. A failure of the
Carmichael bridge or either prime-square divisor consequence would invalidate
the proof route. Finite numerical agreement cannot establish the universal
claim.

## Evidence

- Final Lean module:
  `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.lean`;
  152 lines and 6632 UTF-8 bytes. At the landed commit
  `git ls-files 'D5/S3/Arith/Congruence/*.lean' | wc -l` reports 46 Lean files
  in its immediate directory, including this module (limit 96).
- `lake env lean` on the final module: exit 0 with zero warnings.
- Profiled single-file check: exit 0; wall time 5.04 seconds and kernel type
  checking 197 milliseconds on the warm local dependency cache.
- `tools/scripts/agent/header-check.sh` on the final module: exit 0.
- Final-source `#print axioms`: exit 0; `mem` uses exactly `[propext]`, and
  `result` uses exactly `[propext, Classical.choice, Quot.sound]`.
- Deleting the sole direct import,
  `Mathlib.NumberTheory.ArithmeticFunction.Carmichael`, makes Lean exit 1.
- Numeric check of the final membership criterion through every semiprime
  `k ≤ 20000`: exit 0; 5,081 semiprimes, members `4, 6, 21, 301, 2041`, and
  zero violations for the target range `k > 4`.

## Triage

`theorem`; resolution `proved` for Ordowski's Conjecture sentence for every
semiprime greater than four. The Scribe theorem node carries the matching
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

Historical openness beyond the OEIS, OpenAlex, Math.SE, and GitHub surfaces
described above is unverified. A proof outside those search surfaces remains
an unexcluded alternative. No exhaustive novelty or priority claim is made.
Scribe compilation, emitted Markdown, whole-tree Lean reporting, repository
admission, and freezing are not verified by the single-file checks in this
record.
