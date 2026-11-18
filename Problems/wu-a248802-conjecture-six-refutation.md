---
slug: wu-a248802-conjecture-six-refutation
bibkey: wu2019a248802c6
doi: null
url: https://oeis.org/A248802/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result
---

## Problem

Chai Wah Wu's 2019 Conjecture 6 in OEIS A248802 states:
"Conjecture 6: a(44n+10) = 2383 for n >= 0 and when it is not covered by Conjectures 1-5."
The [immutable primary source](https://raw.githubusercontent.com/oeis/oeisdata/2bafebc3c27a4bc629b56b124ed2b4407b85e6ad/seq/A248/A248802.seq),
all five prior domains, source hash and bibliographic limits are recorded in
[the library note](../Library/Factorization/wu2019a248802c6.md). The preregistration
is [issue #31483](https://github.com/the-omega-institute/trureturing/issues/31483).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every natural n including zero | `∀ n : ℕ` in `claim` |
| Index 44n+10 | Literal `44 * n + 10` throughout `claim` |
| C1: k=10m+2 | `coveredOne k` with `∃ m : ℕ` |
| C2: k=36m+16, m mod 5 not 1 | `coveredTwo k`, both conjuncts retained |
| C3: k=84m+22, m mod 5 not 0 | `coveredThree k`, both conjuncts retained |
| C4: k=58m+26, not covered by C1-C3 | `coveredFour k`, including all three recursive exclusions |
| C5: k=138m+6, m mod 5 not 2 | `coveredFive k`, both conjuncts retained |
| None of C1-C5 applies | Five separate negative hypotheses in `claim` |
| Original smallest prime factor | `Nat.minFac (2 ^ (2 ^ (44 * n + 10) + 2) + 3)` |
| Claimed value 2383 | Literal equality with 2383 |
| Refutation of entire source claim | `result : ¬ claim` |

## Motivation

A single admissible overlap with a smaller divisor disproves the asserted
constant least factor on the entire stated conditional domain.

## Gap

Tier 1: an OEIS conjecture from 2019 with an exact finite counterexample route.
The bounded literature checks recorded in the preregistration found no
authenticated exact C6 resolution.
House's existing divisibility progression is credited as prior work, rather than
claimed as a new theorem. Global priority remains unverified.

## Route

At n=79, k=3486=274+292*11. The residues modulo (10,36,84,58,138)
are (6,30,42,6,36), excluding every preceding progression. Power laws
and exact modular certificates modulo 879 and 1759 establish divisibility by
1759. Nat.minFac_le_of_dvd gives a(3486)<=1759<2383.

## Falsifier

A prior coverage predicate applying at k=3486, a false modular residue or an
incorrect source mapping would defeat the claimed counterexample. An
authenticated earlier exact C6 resolution would change the prior-art
qualification.

## Evidence

The canonical source is
[the Lean module](../D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.lean).
Its `claim` has literal type Prop, and `result` has literal type Not claim.
Only the designated result is a public theorem; it is exempt under section 3.9.

## Admission

`admission_basis: open-problem-resolution`; `escape_witness: none`.
The utility is `certified-instance` with the typed `refutes` edge from
`result : ¬ claim` to `claim : Prop`.

| Declaration | proof_shape | Admission or live consumer |
| --- | --- | --- |
| `result` | `bind-only` | The preregistered external conjecture's designated refutation |
| private `divisor_of_inner_residue` | `bind-only` | Used by `result` to obtain the divisor |
| private `minFac_ne_of_dvd` | `bind-only` | Used by `result` to contradict the claimed minimum |

The modular certificates, power laws, arithmetic normalization and the
Mathlib bound supply all proof ingredients. The helpers organize the live
proof and provide no escape witness. There are no direct frozen D5 theorem
dependencies. House's divisibility progression is prior work; the delivered
conclusion is the full conjecture's negation at an admissible intersection.
The sole public theorem is the designated refutation, so its Reg mirror
records the section 3.9 exemption without adding a four-slot registration.

## Triage

The full C6 assertion is refuted. The failure is an admissible intersection
with House's 1759 progression; the five source exclusions do not remove it.
No equality with 1759 is asserted. A corrected domain excluding additional
progressions is unresolved here. The separate C1/C4 results are unaffected.

## ASSUMED-UNVERIFIED

Global literature completeness and priority outside the bounded search are
unverified. No mathematical conclusion beyond the literal refutation is claimed.
