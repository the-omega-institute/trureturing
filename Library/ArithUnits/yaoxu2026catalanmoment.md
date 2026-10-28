---
bibkey: yaoxu2026catalanmoment
authors: "Yao Xu"
year: 2026
title: "catalan-lean4: CharacterSpecialValue"
doi: null
url: "https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean"
claim: "For every prime p and nonprincipal odd complex Dirichlet character modulo p, the sum of a.val times the character value over ZMod p is nonzero. The same closure proves the Hurwitz zero value on the open unit interval and the prime nonprincipal L-value formula."
strata_touched:
  - D5/S3/Analytic/Zeta/CatalanPrimeOddMoment
  - D5/S3/ArithUnits/MercaPrimeCharacterMoment
license: "Apache-2.0; Copyright 2026 Yao Xu. The source LICENSE, NOTICE, THIRD_PARTY.md and referenced ClassFieldTheory LICENSE are retained with the port."
triage: anchor
---
<!-- GID: D5/L/ArithUnits/yaoxu2026catalanmoment -->
# Prime odd-character first moments

## Verified locator

URL: https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean

The immutable source revision is 3dc9375da48d13751fd291f3ee0fda8fa18be56d.
That revision declares Lean 4.35.0-rc3 and mathlib
c55e6e786f49471c72fbddbec5415808896aec1e. This compatibility port is checked at
the repository's Lean 4.35.0 and mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. Textual correspondence of the copied
statements is not a general proof of equivalence between the two upstream
environments; the port's mathematical evidence is its exact current-pin proof.
CharacterSpecialValue.lean declares hurwitzZeta_apply_zero_of_mem_Ioo,
LFunction_zero_eq_neg_weighted_sum and odd_character_weighted_sum_ne_zero.
The last two retain a prime modulus and a nonprincipal character; the last
also requires oddness. The finite sum uses the natural representative
ZMod.val and complex multiplication, not a residue-class-valued sum.

Its project-local import closure consists of CharacterCircle, DirichletTail,
CharacterBoundary, CharacterContinuity, CharacterArgument, CharacterLZero,
CharacterZeroBridge and CharacterSpecialValue, all under Catalan/Stickelberger.
No ClassFieldTheory mathematical module occurs in this closure. The upstream
NOTICE still identifies its Apache-2.0 attribution chain, which is retained.

The proof evaluates the boundary logarithm series on the unit circle, obtains
the odd Hurwitz value at zero, and combines the finite L-value formula with
the primitive functional equation and nonvanishing at one. This is classical
analytic content from the identified Lean source. No novelty claim is made.
The prime formula is not asserted for composite induced characters.

The literature bucket follows the native finite unit-character moment that
consumes this source. Its analytic proof is retained in the Zeta source module.

The native consumer defines
`characterMoment n χ = ∑ u : (ZMod n)ˣ, ((u : ZMod n).val : ℂ) * χ (u : ZMod n)`.
Its equality with the all-`ZMod n` weighted sum assumes only `[NeZero n]`,
including `n = 1`; nonunits contribute zero. Applying the licensed prime
theorem through that equality retains `[Fact p.Prime]`, `χ ≠ 1` and `χ.Odd`.
This adaptation supplies neither a composite-conductor induced weighted-moment
formula nor a strict sign, class-number formula, collision converse, quartic
or sextic conclusion.

The 19 retained supplier declarations preserve the pinned source statements.
The source-only conditional nonvanishing forwarder is omitted: the delivered
nonvanishing theorem uses the unconditional finite weighted-sum identity on its
live proof path. API compatibility edits, narrower imports, namespace changes
and joining the eight files do not create a claim of a new mathematical result.
