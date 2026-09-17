---
slug: oeis-a397356-reciprocal-square-exponent-diagonal-mod-three
bibkey: hanna2026a397356
doi: null
url: https://oeis.org/A397356
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree
---

# Ternary support of the A397356 reciprocal square-exponent diagonals

## Problem

Paul D. Hanna's NAME and BOTH conjecture COMMENT lines, quoted verbatim from the entry
snapshot `oeis-A397356.src`:

```text
%N A397356 G.f. A(x) satisfies: [x^n] 1/A(x)^(n^2) = [x^n] 1/A(x)^(n^2-1) for n > 1 with A(0) = A'(0) = 1.
%C A397356 Conjecture: for n >= 0, a(n) is odd iff n+1 is a power of 2.
%C A397356 Conjecture: for n >= 0, a(n) is not divisible by 3 iff 2*(n+1) is a sum of two powers of 3 (A055235).
%A A397356 Paul D. Hanna, Jul 03 2026
```

A397356 carries two conjectures. The parity classification was settled earlier in
`D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity`. This lane settles the
second one, the characterisation of the indices at which three does not divide `a n`.

## Motivation

The two conjectures share a sequence but not a method. The parity clause reduces, modulo two,
to a binary Catalan series whose square-exponent diagonal is already available. Modulo three
there is no such shortcut: the reduced inverse is a sparse ternary series, and the defining
diagonal relation has to be verified against it directly.

## Gap

The repository constructed the sequence and proved the parity clause; `ZMod 3` did not occur
in that module, and no ternary statement about this sequence existed.

## Route

Work over `ZMod 3` with the sparse series

```text
S = 1 - sum_{j >= 1} X^((3^j - 1)/2)
```

which satisfies `S = 1 + X + X * S ^ 3`; in characteristic three the Frobenius identity turns
the cube into an exponent tripling, and the equation becomes the index shift
`(3^(j+1) - 1)/2 = 3 * (3^j - 1)/2 + 1`.

The content is the universal diagonal identity

```text
inverse_cube_diagonal (S Q : PowerSeries (ZMod 3))
    (hS : S = 1 + X + X * S ^ 3) (hSQ : S * Q = 1) (n : ℕ) (hn : 1 < n) :
    coeff n ((Q ^ 2) ^ (n ^ 2)) = coeff n ((Q ^ 2) ^ (n ^ 2 - 1))
```

stated for every pair satisfying those two equations, proved by cube extraction, formal
differentiation, and a strong-induction coefficient descent. Uniqueness of the solution of the
diagonal relation then identifies the reduction of the sequence's generating series with
`S ^ 2`, and the support of a square of a sparse ternary series is exactly the set of indices
whose doubled successor is a sum of two powers of three.

## Falsifier

An index `n` with `3 ∤ a n` for which `2 * (n + 1)` is not a sum of two powers of three, or an
index with `3 ∣ a n` for which it is. Equivalently, a failure of `inverse_cube_diagonal` for
some pair satisfying its two hypotheses, or a second solution of the diagonal relation.

## Evidence

Computed independently from the defining diagonal relation, never from the conjectured
pattern: the indices `n < 50` with `3 ∤ a n` are exactly

```text
0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44
```

and these are exactly the `n < 50` for which `2 * (n + 1)` is a sum of two powers of three with
the exponents allowed to be equal and `3 ^ 0 = 1` allowed. The proposed certificate was checked
separately through degree 50: `S = 1 + X + X * S ^ 3` holds, and the reduction of the
generating series agrees with `S ^ 2`.

Both delivered theorems are proved without `sorry`, `admit`, `native_decide` or added axioms;
every `decide` in the module is a small normalisation fact such as `(3 : ZMod 3) = 0`.

## Triage

`theorem`. This settles the second conjecture of the entry, for every natural `n`, as an
equivalence rather than a one-sided bound. With the parity lane, both conjectures recorded on
A397356 are now proved in this repository.

## ASSUMED-UNVERIFIED

The entry text is a snapshot; the implementation and review seats had no network and did not
retrieve OEIS or search the literature, so no literature completeness and no first-publication
priority is claimed. The numerical computations recorded under Evidence were run outside the
Lean kernel and are supporting evidence only; the proved content is exactly the two public
theorems. The identification of the entry's sequence with the module's `a` rests on the
imported frozen `generating_equation` together with the uniqueness of the inverse pair, not on
the numerical agreement. The claim that the reduced generating series equals `S ^ 2` is proved;
the sparse closed form of `S` quoted in the Route section is a description of that series, not
an independent assertion.
