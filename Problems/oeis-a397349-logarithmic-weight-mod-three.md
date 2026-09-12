---
slug: oeis-a397349-logarithmic-weight-mod-three
bibkey: hanna2026a397349
doi: null
url: https://oeis.org/A397349
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity
---

# Alternation modulo three of the A397349 coefficients

## Problem

Paul D. Hanna's NAME and BOTH conjecture COMMENT lines are quoted verbatim
from the orchestrator-supplied `oeis-A397349.src`:

```text
%N A397349 L.g.f. Sum_{n>=1} a(n)*x^n/n = log(1+x + Sum_{n>=2} 3*n/(3*n^2 - 1) * a(n)*x^n ).
%C A397349 Conjecture: a(n) is odd iff n is a power of 2.
%C A397349 Conjecture: a(n) = [1,2] repeating (mod 3) for n >= 1.
```

A397349 carries two conjectures. This lane settles ONLY the modulo-three
alternation for every positive index. The separate assertion that a(n) is
odd exactly at powers of two remains open and is not claimed as proved.
The module retains it solely as the unproved definition `parity_conjecture : Prop`.

## Motivation

This OEIS conjecture is selected from the repository's triage note
`Library/Words/oeis2026triage0911b.md`. The target is a universal statement,
not a finite check. The resolution count is one clause, not the whole entry.

## Gap

No proof was found in the supplied entry snapshot. It has no references
and only a b-file link. This seat has no network and did not search the
literature; the snapshot inspection is not a literature-priority certificate.
The formal gap is the modulo-three collapse of the triangular convolution.

## Route

For natural indices and integer values, set
`A k = if k = 1 then 1 else (3k²−1)·s k` and
`B m = if m ≤ 1 then 1 else 3m·s m`.
Set `s n = 0` for `n ≤ 1`; for `n ≥ 2`, use
`s n = ∑_{k=1}^{n−1} A k · B (n−k)`.
The module realizes this as a single well-founded recursion (`Nat.strongRecOn`)
for `s`, followed by the definitions `a = A` and `b = B`.
The private `s_eq_sum` exposes the convolution with `k = j+1`.

1. `b_mod_three` uses the explicit factor of three in `b m` for `m ≥ 2`.
2. Only `k = n−1` survives modulo three: there `n−k = 1` and `b 1 = 1`.
   Thus `s_mod_three` proves `s n ≡ a (n−1) (mod 3)`.
3. Since `3n²−1 ≡ 2 (mod 3)`, `a_mod_three_step` gives
   `a n ≡ 2·a (n−1) (mod 3)` for `n ≥ 2`.
4. Induction from `a 1 = 1` yields remainder 1 at odd indices and 2 at even indices.

The escape witness is `s_mod_three`: the sum collapses to its boundary term
on the live proof path to the target theorem. There are no direct frozen D5
imports; the module imports Mathlib. This lane does not prove the formal
power-series identification or a uniqueness theorem for the NAME equation.

## Falsifier

An `n ≥ 1` with `a n % 3` different from `if n % 2 = 1 then 1 else 2`
would falsify the asserted alternation.

## Evidence

- Module: `D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity.lean`.
- Resolution theorem: `hanna_conjecture_a397349_mod_three`.
- Axioms reported by the implementation seat: std3,
  `[propext, Classical.choice, Quot.sound]`.
- Orchestrator report: the recurrence reproduces all 11 DATA terms in its
  stated check, with integer values throughout;
  `a 1..a 5 = 1, 11, 442, 31067, 3206716`.
- Orchestrator report: modulo-three values through `n=44` alternate `[1,2]`.
- Orchestrator report for the OPEN parity clause: the modulo-two computation
  through index 512 has odd-valued terms exactly at indices `1,2,4,…,512`,
  with zero violations. This supports that clause but does not prove it.

The supplied snapshot contains 16 DATA values across %S/%T/%U; “11” above
is the orchestrator's reported computation scope, not a count of that snapshot.
The module also exposes `s_zero`, `s_one`, and `a_one` as basic public lemmas;
only the named modulo-three theorem receives a resolution claim.

## Triage

`theorem`. One universal modulo-three conjecture is settled for the constructed
integer recurrence. The parity conjecture remains open; neither its bare
proposition definition nor its finite numerical support is a second resolution.

## ASSUMED-UNVERIFIED

The quotes are supplied by the orchestrator. This seat has no network and
did not retrieve OEIS or search the literature. The orchestrator's computations
are not rerun here. Identification of the NAME's logarithmic generating
function with the integer recurrence is not proved in this module.
No literature completeness or first-publication priority is claimed.
The parity clause is unproved and not claimed: `parity_conjecture : Prop`
is a bare proposition, and remains open.
