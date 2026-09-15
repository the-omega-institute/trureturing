---
slug: oeis-a397592-dyadic-parity
bibkey: hanna2026a397592
doi: null
url: https://oeis.org/A397592
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport
---

# The integer source and dyadic parity of A397592

## Problem

Paul D. Hanna's OEIS A397592 (July 10, 2026), revision 18, has NAME:

> G.f. A(x) such that the sum of the first n coefficients in A(x/n)^n equals 2^(n-1) for n >= 1.

Its sole conjecture is:

> Conjecture: for n > 3, a(n) is odd iff n is of the form 2^k-1 or 2^k+1 (k > 1).

The FORMULA states A(x)=Sum_{n>=0} a(n)*x^n; the original offset is 0
and a(0)=1. For A in Z[[X]], A_Q is its coefficientwise image in Q[[X]],
namely A.map (Int.castRingHom Rat). The exact source and single result are:

```lean
def SourceA397592 (A : PowerSeries Int) : Prop :=
  PowerSeries.constantCoeff A = 1 ∧
    ∀ m : Nat, 0 < m →
      (Finset.range m).sum (fun j => PowerSeries.coeff j
        ((PowerSeries.rescale ((m : Rat)⁻¹)
          (A.map (Int.castRingHom Rat))) ^ m)) = (2 : Rat) ^ (m - 1)

theorem result :
  (∃! A : PowerSeries Int, SourceA397592 A) ∧
  (∀ A : PowerSeries Int, SourceA397592 A → ∀ n : Nat, 3 < n →
    (Odd (PowerSeries.coeff n A) ↔
      ∃ k : Nat, 1 < k ∧ (n = 2 ^ k - 1 ∨ n = 2 ^ k + 1)))
```

These are ordinary formal powers, not compositional iterates; there is no
convergence or factorial normalization. The sum includes j=0,...,m-1 for
every natural m>0. The separate integer-existence-and-uniqueness conjunct
excludes an unproved integrality premise.

## Motivation

This first-tier 2026 external named conjecture is the `question_answered` in
[#8006](https://github.com/the-omega-institute/trureturing/issues/8006), created
2026-09-15T03:15:36Z before probes. A397591 supplies the distinct y=0 endpoint;
A397592 is the y=2 source. The same parity pattern does not identify their series.

## Gap

The A397591 series F has constant term zero, offset 1, and satisfies
[X^(m-1)](1-F)^m/(1-mX)=0 for m>1. Its endpoint does not by itself establish
integer existence for A397592 or an all-degree parity comparison. A397590
attests A(X,0)=1-F(X) and A397592(n)=Sum_{k=0..n} 2^k T(n,k).
These source identities do not supply a proof of general triangle integrality.

## Route

Multiply the rational NAME sum in row m=n+1 by m^n. The coefficient
rescaling law and the geometric-series convolution give the integer row
R_n=[X^n]A^(n+1)/(1-(n+1)X)=(2(n+1))^n. Both directions hold for every
m>0, including m=1. The existing exact normalization gives R_n=(n+1)N_n
for n>0. Cancellation takes place in the integers and gives
N_n=2^n(n+1)^(n-1).

Let t_n=2^n(n+1)^(n-1) for n>0 and give the forcing series constant term
zero. Add this forcing series to the existing coefficient-correction map
`advance`. Its agreement property increases the number of stable coefficients
by one. Iterating from 1 therefore stabilizes coefficientwise to an integer
series A fixed by the forced map. The fixed-point equation gives N_n=t_n,
and the complete source equivalence gives SourceA397592(A). Strong induction
using `normalized_change` proves uniqueness among integer source solutions.

Only then map to ZMod 2. For positive n the forcing term maps to zero,
so `normalized_unique` identifies every satisfying source modulo two with
the existing homogeneous solution. The latter equals 1 minus the A397591
series. Above degree three their coefficients agree modulo two, and
`hanna_conjecture` gives exactly the two dyadic alternatives.

The new iteration, stabilization, source equivalences and parity adapters
are local to the sole theorem. A397594/y=4, arbitrary even parameters,
full triangle integrality, positivity and asymptotics are outside its claim.

## Falsifier

An integer source and an n>3 violating either direction of the parity iff
would refute the parity assertion. Failure of integer existence, or two distinct
integer sources, would refute the well-posedness conjunct. A finite prefix,
a conditional integer-source assumption, a shifted index or a missing strict
bound changes the target instead of resolving it.

## Evidence

The module `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport`
contains the source predicate `SourceA397592` and the single theorem `result`.
Its source citation is `D5/L/hanna2026a397592`.

The existing `LinearExponentDyadicSupport` endpoint has stored identities:

- `hanna_conjecture`: `sha256:257441c32f0b491832283533f85a4a8f2894bd3bb24da35790b5c8539a682503`.
- `generatingSeries`: `sha256:5edab5bd8bbb3730bb76f331bab1d2a071ce873a70eecd471722169450fdcefe`.

Those identities locate the y=0 endpoint, not an A397592 proof. The numerical
appendix of `Library/Words/oeis2026triage0911b.md` records an N=100 integer
recurrence experiment and zero parity counterexamples at n=4,...,100. Its
program and data are finite research evidence, not evidence for all indices.

## Triage

The admission route is `open-problem-resolution` under CLAUDE 3.2 for the
exact external conjecture registered in #8006. The theorem has `proof_shape: content`:
the forced integer construction and stabilization supply a new unbounded
existence argument. The source predicate is a necessary definition.
`escape_witness: none` uses the external named-problem admission basis;
`computational_content.kind: none` applies to both declarations. The public mathematical surface consists of the
necessary source predicate and one result; adapting facts belong inside its
proof. The stated problem is unbounded and symbolic. It includes neither
A397594 nor a full A397590 triangle result.

## ASSUMED-UNVERIFIED

The source snapshot in #8006 is revision 18, Jul 11 2026 03:34:44. The live
text request returned HTTP200 (4,200 bytes); the complete mirror entry is
3,990 bytes, SHA-256 `ec2009bc22f7209c0403adc0c2909bffbc24016ef40c9eb8b0c131585c8e51d8`.
The Library note fixes the source locators; later source changes are outside
that snapshot.

Bounded exact A397592 searches recorded Crossref HTTP200/0, OpenAlex
HTTP200/0, MathOverflow HTTP200/empty with no further page, and a public
GitHub Lean-code index count of 0. D5 and pinned Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` supplied the y=0 endpoint and generic
series APIs, with no exact resolution in the inspected scope:
`dominating_theorem_search: not-found-in-searched-scope`.

Only 20 of 34 broad OpenAlex records and nine MathOverflow titles were
screened; not all answers were read, and broad Crossref ranking is not an
absence result. Fried's arXiv:2607.24832 and Heninger–Rains–Sloane were only
partially read; no verified reduction from the latter's fixed-n root
integrality to this varying-row source is supplied. arXiv query HTTP429 and
timeouts, Google's JavaScript shell, unread papers or portions, b-files and
other unopened material give no negative evidence. Differently named,
differently indexed, unindexed or new proofs remain unexcluded. Neither
global priority nor exhaustive absence of prior proofs is claimed.
