---
slug: oeis-a397356-reciprocal-square-exponent-diagonal-parity
bibkey: hanna2026a397356
doi: null
url: https://oeis.org/A397356
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity
---

# Parity of the A397356 reciprocal square-exponent diagonals

## Problem

Paul D. Hanna's NAME and BOTH conjecture COMMENT lines, quoted verbatim from
the entry snapshot `oeis-A397356.src`:

```text
%N A397356 G.f. A(x) satisfies: [x^n] 1/A(x)^(n^2) = [x^n] 1/A(x)^(n^2-1) for n > 1 with A(0) = A'(0) = 1.
%C A397356 Conjecture: for n >= 0, a(n) is odd iff n+1 is a power of 2.
%C A397356 Conjecture: for n >= 0, a(n) is not divisible by 3 iff 2*(n+1) is a sum of two powers of 3 (A055235).
%A A397356 Paul D. Hanna, Jul 03 2026
```

A397356 carries two conjectures. This lane settles ONLY the parity
classification. The separate assertion about divisibility by three remains
open, is not claimed as proved, and appears nowhere in the module as a
theorem or as a definition.

## Motivation

The candidate is taken from the repository's own triage note
`Library/Words/oeis2026triage0911b.md`, which scored it as a first-tier
target and recorded that the entry supplies only conjectures, programs, a
data table and an asymptotic estimate. The target is a universal statement
over all indices, not a finite check.

## Gap

The entry snapshot contains no proof and no reference to one. The conclusion
shape agrees verbatim with the frozen theorem
`D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture`,
but that theorem is about a different integer sequence, defined by an
exponential functional equation rather than by reciprocal diagonals; agreement
of conclusions is not a binding and does not transfer a proof. The formal gap
was a characterisation of the reduction modulo two of the reciprocal series.

## Route

Work with the reciprocal `R = 1/A` throughout, so that the entry's relation
reads `coeff n (R ^ (n²)) = coeff n (R ^ (n² − 1))` for `n > 1` with
natural-number exponents and no negative powers anywhere.

1. If `P` is the strict prefix of `R` at index `n`, then
   `coeff n (R ^ m) = coeff n (P ^ m) + m · coeff n R` for every exponent `m`;
   substituting `m = n²` and `m = n² − 1` into the relation leaves exactly one
   copy of `coeff n R`. The recursion is therefore division-free:
   `r n = coeff n (P ^ (n² − 1)) − coeff n (P ^ (n²))`, with `r 0 = 1`,
   `r 1 = −1`. `generating_equation` proves that the resulting pair is inverse
   and satisfies the relation; `generating_unique` proves that any inverse pair
   with the same two initial coefficients and the same relation is this one.
   Together these make `a` the entry's sequence rather than an unrelated
   recurrence.
2. Over `ZMod 2`, let `u` be the reduction of the frozen `catalanSeries` of
   `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`, so `u = X + u²`,
   and set `v = 1 + u`. Then `v² = v + X` and `u · v = X`, so `v` is a unit and
   `X · v⁻¹ = u`.
3. `v_diagonal` proves that `v` satisfies the entry's relation modulo two.
   Subtracting the two sides gives `coeff (n−1) (v ^ (n² − 2))`. For even `n`
   the exponent is even and the index odd, so the coefficient vanishes by
   Frobenius. For odd `n = 2m+1` the identity `v = v² + X` yields the extraction
   step `coeff (2m) (v · Q²) = coeff m (v · Q)`, which reduces the claim to
   `coeff m (v ^ (2m(m+1))) = 0`; that is the frozen diagonal vanishing lemma of
   `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity` applied to
   `v ^ (m+1)`.
4. The uniqueness of step 1 holds over any commutative ring, so it applies to
   the reduction modulo two; `mod_two_identity` identifies that reduction with
   `v`. Multiplying the two inverse relations then identifies the reduction of
   `A` with `v⁻¹`, whose coefficient at `n` is the coefficient of `u` at `n+1`.
   The frozen `binary_catalan` finishes `hanna_conjecture_a397356`.

The escape witness is the private `residual_diagonal`, the two-case vanishing
argument of step 3 together with its extraction lemma; it lies on the live
proof path and is not an instantiation of any frozen statement. The generalised
diagonal vanishing used inside it is NOT new: it is the frozen
`even_power_diagonal` applied to a power, and it is not claimed as escape
content.

## Falsifier

An index `n` with `a n` odd while `n + 1` is not a power of two, or with
`a n` even while `n + 1` is a power of two, falsifies the theorem. A second
inverse pair satisfying the same relation with the same two initial
coefficients would falsify `generating_unique`.

## Evidence

- Module: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.lean`.
- Resolution theorem: `hanna_conjecture_a397356`; companions `v_diagonal`,
  `generating_equation`, `generating_unique`, `mod_two_identity`.
- Axioms: each public theorem reports `[propext, Classical.choice, Quot.sound]`.
- Exact integer computation of the division-free recursion reproduces the
  published DATA `1, 1, 4, 27, 304, 5000, 126144, 4372221` term for term, with
  integer values throughout, and the defining relation holds with zero
  violations for `n = 2 … 40`. The reciprocal begins `1, −1, −3, −20, −245`.
- The published b-file of 401 terms was checked against both conjectures:
  the odd-valued indices are exactly `0, 1, 3, 7, 15, 31, 63, 127, 255`, matching
  `n + 1` a power of two with zero violations; the indices not divisible by three
  match `2(n+1)` a sum of two powers of three with zero violations over the same
  401 terms. The second figure supports the OPEN second conjecture; it does not
  prove it.
- Each algebraic step of the route above was checked over `ZMod 2` to degree 260
  before implementation: `v² = v + X`, `u·v = X`, the coefficient description of
  `v⁻¹`, the relation for `v` at `n = 2 … 60`, and the extraction identity.

## Triage

`theorem`. One universal conjecture of a two-conjecture entry is settled for a
sequence proved to satisfy the entry's defining relation. The divisibility-by-three
conjecture remains open; its finite numerical support is not a second resolution.

## ASSUMED-UNVERIFIED

The entry text is a snapshot; the implementation seats had no network and did
not retrieve OEIS or search the literature, so no literature completeness or
first-publication priority is claimed. The asymptotic estimate in the entry is
neither used nor checked. The numerical computations recorded under Evidence
were run outside the Lean kernel and are supporting evidence only; the proved
content is exactly the five public theorems. The identification of the entry's
sequence with the module's `a` rests on `generating_equation` together with
`generating_unique`, not on the numerical agreement.
