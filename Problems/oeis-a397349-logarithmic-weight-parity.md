---
slug: oeis-a397349-logarithmic-weight-parity
bibkey: hanna2026a397349
doi: null
url: https://oeis.org/A397349
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity
  - D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity
---

# Parity of the A397349 logarithmic-weight coefficients

## Problem

Paul D. Hanna's NAME and both conjecture COMMENT lines, quoted verbatim:

```text
%N A397349 L.g.f. Sum_{n>=1} a(n)*x^n/n = log(1+x + Sum_{n>=2} 3*n/(3*n^2 - 1) * a(n)*x^n ).
%C A397349 Conjecture: a(n) is odd iff n is a power of 2.
%C A397349 Conjecture: a(n) = [1,2] repeating (mod 3) for n >= 1.
```

A397349 carries two conjectures. The modulo-three alternation is already settled
in this repository by `LogarithmicWeightCatalanParity.hanna_conjecture_a397349_mod_three`.
**This lane settles the other one, the parity clause**, which that module deliberately
left as the bare proposition `parity_conjecture` carrying no proof.

## Motivation

Closing the second clause settles both of the entry's quoted conjectures for the
frozen sequence. The construction is already frozen
and public, so the work is confined to one modulo-two identification; no sequence
is redefined and no second source of truth is created.

## Gap

The frozen module proves the modulo-three clause and states the parity clause
without proof. The formal gap was a characterisation, modulo two, of the
generating series of the frozen coefficients: nothing in the repository related
that series to the binary Catalan series, and the modulo-three argument gives no
information modulo two.

## Route

Reduce modulo two, where `3 ≡ 1`, so that the frozen definitions give
`a n ≡ (n+1) * s n` and `b n ≡ n * s n` for `n ≥ 2`. Form the series
`A`, `C` and `S` over `ZMod 2` from `a`, from `b` shifted to have zero constant
coefficient, and from `s`.

The escape witness is the Artin-Schreier equation `A = X + A ^ 2`; the characteristic-two derivative identity `derivative A = 1` is the step that makes it reachable.
   for odd `m`, so `a m` is even at every odd `m ≥ 3`, while `a 1 = 1`.
2. Three coefficient identities come straight from the frozen convolution
   `s_eq_sum`: `A = C + A * C`, `S = A * C`, and `C = X * (1 + derivative S)`.
   The first two differ exactly because the convolution omits its last term,
   which is why `C` has zero constant coefficient.
3. Characteristic-two algebra closes it without any division. From the first
   identity, `A * C = A + C`; differentiating it and using step 1 gives
   `C' * (1 + A) = 1 + C`; substituting into the third identity collapses the
   bracket to `C = X * C'`. Since `(1 + C) * (1 + A) = 1 + A + C + A*C = 1`,
   `A * (1 + A) = C * (1 + A)^2 = X * C' * (1 + A)^2 = X`, that is `A = X + A^2`.
4. The frozen `CatalanCompositionSquareParity` supplies a uniqueness lemma for
   that equation over an arbitrary commutative ring, and its `catalan_equation`
   mapped to `ZMod 2` supplies the second solution, so `A` is the reduction of
   `catalanSeries`. The frozen `binary_catalan` then reads off the coefficients.

The escape witness is step 1 together with the collapse in step 3; everything
else is either a frozen statement or a direct coefficient computation.

## Falsifier

An index `n` with `a n` odd while `n` is not a power of two, or even while `n` is,
falsifies the theorem. A failure of `A = X + A^2` at any degree falsifies step 3.

## Evidence

- Modules: `D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.lean`, proving
  `LogarithmicWeightCatalanParity.parity_conjecture`; the construction it consumes
  is the frozen `LogarithmicWeightCatalanParity`.
- Axioms: the public theorem reports `[propext, Classical.choice, Quot.sound]`.
- Exact integer computation outside Lean: the coefficients are odd exactly at
  `n = 1, 2, 4, …, 256` through `n = 300`, with zero violations.
- The same computation confirms every identity used in the route through degree
  160: `A = C + A*C`, `S = A*C`, `derivative A = 1`, `C' * (1+A) = 1+C`,
  `A*C = A+C`, `(1+C)*(1+A) = 1`, `C = X*C'`, and `A + A^2 = X`.

## Triage

`theorem`. The second and last conjecture of this entry is settled for the frozen
sequence the repository constructs, the same scope as the already-settled
modulo-three clause; the identification of that sequence with the entry's
logarithmic generating function is not formalised and is recorded below as
ASSUMED-UNVERIFIED. The modulo-three clause is not reasserted here.

## ASSUMED-UNVERIFIED

The entry text is a snapshot; the implementation seat had no network and did not
search the literature, so no completeness or first-publication priority is
claimed. The computations recorded under Evidence ran outside the Lean kernel and
are supporting evidence only. This lane does not identify the frozen integer
sequence with the logarithmic generating function of the NAME; it proves the
parity of the sequence that the frozen module constructs, which is the same scope
as the already-settled modulo-three clause.
