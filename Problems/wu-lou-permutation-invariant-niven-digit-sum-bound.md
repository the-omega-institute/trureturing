---
slug: wu-lou-permutation-invariant-niven-digit-sum-bound
bibkey: wu2025pinn
doi: 10.3390/sym18010186
url: https://arxiv.org/abs/2508.01611
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum
---

# Wu-Lou permutation-invariant Niven digit-sum bound

## Problem

Wu and Lou, *Permutation-Invariant Niven Numbers*, arXiv:2508.01611v3,
section 8.4, state that the relevant nontrivial distinct-digit permutation-invariant
Niven numbers have digit sums between 3 and 81 and conjecture that no exceptions
exist beyond the cases excluded there.

## Motivation

The formal target is the universal bound for the same decimal permutation-invariant
object, with the hypotheses excluding the two elementary families named in the
source sentence. No broader claim about the paper is made.

## Gap

The source labels the no-exceptions assertion as a conjecture. The journal text
was not read because the MDPI page returned HTTP 403; this is recorded as an
`ASSUMED-UNVERIFIED` source boundary below.

## Route

The Lean theorem `result` proves the bound for the source-faithful `DecimalPINN`
structure whenever at least two nonzero digit occurrences and two distinct digit
values are present. It proves `3 | digit_sum` and `3 <= digit_sum <= 81`.
The divisibility-by-three assertion is literature-attested; the lower bound is its
positive immediate consequence; the upper bound is the repository-derived
settlement of the conjectural part.

## Evidence

- Lean module: `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.lean`.
- Public declarations: `DecimalPINN` and `result`.
- Positive control: the digit list `[6, 2, 1]` inhabits `DecimalPINN`; its six
  permutations have values 126, 162, 216, 261, 612, and 621, each divisible by 9.
- Exhaustive recheck: lengths 2 through 6 gave 14, 64, 289, 959, and 2999
  admissible vectors respectively, 4325 total, with zero exceptions to the bound.

The `3 | digit_sum` component is attributed to Wu and Lou's Theorem 1 consequence
in section 8.4. The `digit_sum <= 81` component is derived in this repository from
permutation invariance and the two-distinct-digit hypothesis.

## Falsifier

A source-faithful `DecimalPINN` satisfying the two hypotheses with digit sum
outside the proved interval, or not divisible by three, would falsify the result.

## Triage

The delivery uses `admission_basis: open-problem-resolution`. The proof shape is
`bind-only`, with no escape witness: the bound follows by instantiating the
source permutation-divisibility field and normalizing the resulting arithmetic.

## ASSUMED-UNVERIFIED

Crossref confirmed DOI `10.3390/sym18010186`. The journal text itself was not
read because the MDPI page returned HTTP 403; the arXiv version is the available
source text for the quoted locator.
