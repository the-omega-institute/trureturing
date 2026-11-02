---
slug: geisser-2021-squares-prefix
bibkey: geisser2021squares
doi: null
url: https://arxiv.org/abs/2112.00444v2
triage: theorem
motivation_gids:
  - D5/S1/Digit/OnnisSquareThreeStepRefutation
---

# Prefix closure for squares with three digits

## Problem

The source identified by `geisser2021squares`, Section 3.3, Conjecture 1,
printed pages 25–26, states:

> If ⟨a₁′,...,aₗ′⟩ is a solution with l ≥ 2, then ⟨a₁′,...,aₗ₋₁′⟩ is also a solution.

For a finite list of natural numbers, form each block as 4 followed by
exactly that entry's number of nines, concatenate the blocks, and append 5.
Let `encode` be the resulting ordinary decimal natural number, and let
`GoodSquare n` mean that every actual decimal digit of `n²` belongs to
{0,2,5}. The closed claim is exactly:

```text
∀ runs : List ℕ, 2 ≤ runs.length →
  GoodSquare (encode runs) → GoodSquare (encode runs.dropLast)
```

Zero runs are included. Neither list length nor entries have an upper
bound. Deletion removes the entire final 4/nines block and preserves the
final 5. All three allowed digits need not occur.

## Motivation

The frozen decimal-digit refutation
`D5/S1/Digit/OnnisSquareThreeStepRefutation` supplies a related example of
using actual decimal digits to refute a universal published assertion.
It motivates this problem's encoding discipline; its theorem is not a
premise or a claimed solution of this different conjecture.

## Gap

The source states the full prefix implication as a conjecture. The present
result addresses that implication without a finite-domain substitute.
The versioned source and completed source review fix the problem, while
exhaustive subsequent-resolution history remains unverified. The earlier
publication year alone supplies no claim of current worldwide openness.

## Route

Use the tuple
`[0,1,3,7,15,31,63,127,2,6,14,62,14,6,2]`. Its full decimal word has 369
digits; deleting the final entry 2 removes a 4 and two nines, leaving 366
digits. In `result`, the Lean kernel reduces the full square's allowed-digit
certificate and a certificate that the prefix square contains digit 1.
Applying the supposed universal implication at this list contradicts the
second certificate. This is one exact witness against the whole claim,
not an exhaustive search over a bounded domain.

The owning Blueprint explains the carry: cumulative lengths contain
`255 + T`, with `T = {0,3,10,25,88,103,110,113}`. Four equal-sum pairs
`(0,113),(3,110),(10,103),(25,88)` contribute 20 at the relevant position,
carrying 2. Removing the last cumulative length removes one pair; 15 then
carries the forbidden digit 1. This explains how an admissible full word
can have an inadmissible prefix.

## Falsifier

A different digit encoding, a requirement that all three digits occur,
positive-only runs, or removal of a different suffix would change the
problem. The result requires the literal decimal encoding, a passing full
square and a prefix square containing 1; a failure of any of those
certificates would defeat this witness. The source predicates and those
certificates are explicit in the existing theorem proof.

## Evidence

The sole mathematical result is
`D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.result`, literally
`Not claim`, in `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.lean`.
The claim has literal type `Prop`. The theorem uses the named tuple and
kernel-reduced certificates over `Nat.ofDigits 10` and `Nat.digits 10`.
The owning Scribe associates this result with this dossier as `Refuted`.
That content claim does not itself establish frozen membership or publication.

## Triage

- **Proved:** the entire universal prefix implication is false, with the
  exact GID `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.result`.
  This is the single mathematical object credited here.
- **Computed:** the full/prefix root lengths 369/366 and the four-pair versus
  three-pair carry explanation describe this same witness in the owning
  Blueprint; they are not separately delivered general theorems.
- **Open:** a sufficient restriction on cumulative-length pair multiplicities
  that restores prefix closure. This is a successor candidate, not a
  consequence already proved by the witness.
- **Open:** classification or minimality of counterexamples and extensions
  to other bases. The source's separate generalized-base discussion after
  equation (28) is not decided by the decimal witness.
- **Boundary:** the refutation defeats any unrestricted prefix-pruning rule
  justified solely by Conjecture 1. It does not refute independently proved
  special families or settle the source's other conjectures; no downstream
  theorem is claimed to have been invalidated.

## ASSUMED-UNVERIFIED

Exhaustive literature history, originality and priority are unverified.
The carry explanation is exposition of the given witness, not a new
uniform carry theorem. The successor candidates and generalized-base
claims remain open. Frozen membership, admission and public delivery are
separate machine and review obligations.
