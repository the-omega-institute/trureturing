---
slug: oeis-a390088-prime-digit-base-existence
bibkey: oeis2025a390088
doi: null
url: https://oeis.org/A390088
triage: theorem
motivation_gids:
  - D5/S1/Digit/PrimeDigitBaseClassification
---

# The A390088 exception set

## Problem

For each number, ask whether some base above one writes it with all digits
prime. Felix Huber conjectured on October 29, 2025 that exactly five numbers
admit no such base.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found it still labelled Conjecture, with the exception set stated
verbatim and the sequence marked easy.

## Gap

The entry states the exception set but supplies no argument. The searched
indexes returned no proof.

## Route

Above ten, two certificates suffice. For an even argument take the base that
is half of two less than it, giving the two-digit representation with both
digits two; for an odd argument take the base that is half of three less than
it, giving digits three and two. Both digits are prime and both are below
their base, so the certificate is valid in each case.

Below ten the question is finite and is settled by inspection. Four arguments
admit no base; one is excluded because its digit list is empty in every base,
which would otherwise make a universally quantified condition on digits
vacuously true; and four admit a base, one of them only a single base.

For the nonexistence direction, split on whether the argument is below the
base. If it is, the digit list is the argument itself and primality is direct.
If it is not, the base is below ten as well and a bounded enumeration over
pairs settles it.

## Falsifier

A number outside the five with no base writing it in prime digits, or one of
the five with such a base, would contradict the theorem about the defined
condition.

## Evidence

- Module: `D5/S1/Digit/PrimeDigitBaseClassification.lean`.
- Main theorem: `a390088`, an equivalence for every argument.
- Supporting result: `prime_digit_base_certificate`, the two certificates.
- The finite reasoning is confined to bounded enumerations over pairs below
  ten and to the five explicit small arguments; the half of the statement
  ranging over all arguments is a general argument with no enumeration.
- There is no finite cutoff in the public statement.

The caller verified before dispatching an implementation seat. The exception
set computed directly from the definition, searching bases to four hundred for
arguments below four hundred, was exactly the five. Every argument from ten to
three thousand was covered by one of the two certificates, with no exception.
The four small arguments that admit no base were checked against every base
below their own value, and the one small argument admitting only a single base
was identified.

## Triage

`theorem`. The equivalence is proved for every argument. The least such base,
which is what the sequence records, is not formalized; only the existence
question the conjecture asks about.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the OEIS entry is
documentary; the kernel verifies the explicitly defined condition.
