---
slug: sabba-2023-a362534-polarization-transfer-refutation
bibkey: sabba2023a362534
doi: null
url: https://oeis.org/A362534
triage: theorem
motivation_gids:
  - D5/S0/Certificates/SabbaPolarizationTransferRefutation.result
---

# Refutation of the numerator conjecture of OEIS A362534

## Problem

OEIS A362534 (Mohamed Sabba, 2023) concerns upper bounds on the transfer of
z-magnetization from a group `X_n` of spin-1/2 nuclei to a single spin-1/2
nucleus `A` in NMR. Its COMMENTS define

> The symmetry-constrained upper bounds are given by the function f(n): (1) for
> even n, f(n) = (2^(1-n))*n*binomial(n-1, n/2) (2) for odd n, f(n) =
> (2^(1-n))*n*binomial(n-1, (n-1)/2). The adiabatic bounds are given by the
> function g(n): (3) for even n, g(n) = 2*(1-(2^(-n))*binomial(n, n/2)) (4) for
> odd n, g(n) = 2*(1-(2^(-n))*binomial(n, (n-1)/2)).

and close with

> Conjecture: the numerator of g(n) is the denominator of f(n)/g(n).

Issue #10062 fixes the readings: `f(n)` and `g(n)` are the rational numbers
given by these formulas for `n ≥ 1` (the entry's offset); numerator and
denominator are those of the fraction in lowest terms, as in the entry's own
lists `g = 1, 1, 5/4, 5/4, 11/8, 11/8, 93/64, …` and
`f/g = 1, 1, 6/5, 6/5, 15/11, 15/11, 140/93, …`; the conjecture is asserted for
every `n ≥ 1`.

## Motivation

The conjecture relates the two bounds of the entry for all numbers of `X`
spins. The frozen declaration
`D5/S0/Certificates/SabbaPolarizationTransferRefutation.result` shows that it
fails at `n = 19`, so the denominators of the ratio are not the numerators of
the adiabatic bound in general.

## Gap

Issue #10062 preregisters the conjecture and its literature check. The entry's
history (last revision 24, 2023-06-11) records no proof or counterexample, and
the entry has no references section; MathDB returns no entry for "A362534";
the repository had no A362534 declaration or dossier. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority.

## Route

`19` is odd, so `f(19) = 2^(-18) · 19 · C(18, 9)` and
`g(19) = 2 (1 − 2^(-19) · C(19, 9))`. With `C(18, 9) = 48620` and
`C(19, 9) = 92378`,

```text
f(19) = 230945/65536,   g(19) = 215955/131072,   f(19)/g(19) = 92378/43191.
```

The numerator of `g(19)` is `215955 = 5 · 43191`, while the denominator of
`f(19)/g(19)` is `43191`, so the conjectured equality fails at `n = 19`.

## Falsifier

A different value of either binomial coefficient, or a common factor of
`215955` and `131072` or of `92378` and `43191`, would invalidate the
counterexample. A proof of the conjecture for all `n ≥ 1` would contradict the
kernel-checked theorem `result : ¬ claim`.

## Evidence

Exact rational evaluation reproduces the 36 terms of the entry's DATA for
`numerator(f(n)/g(n))`, `n = 1, …, 36`, and the entry's listed values of `f`
and `g`; the conjecture holds for `n = 1, …, 18` and fails for 20 values
`n ≤ 200`, the first being `19, 20, 23, 24, 59, 60`.

The canonical source is
`D5/S0/Certificates/SabbaPolarizationTransferRefutation.lean`. Its public
declarations are `f`, `g`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:22a81985dbe91c1a4baef6ffbb1baf37bc93164d585b942650bb7ae964106078`.
The result declaration has statement identity
`sha256:786b8320ac26024b47fd6bac168a32a6ce5eae1c5e9fd452586a8ad9251ea7b3`.
The Freeze event is
`sha256:6c0e86a87ff0971b29609791daec8c04bf12d237c421c7ded9c2696bc687b4dd`
and has no project-level frozen prerequisites.

The result is a closed typed refutation of `claim`. Its utility classification
is `certified-instance` with `basis=refutes` directed to that claim. The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
no `sorry`, `native_decide`, or new axiom.

## Triage

`theorem`; resolution `refuted` for the quoted conjecture. The public theorem
has `proof_shape: bind-only`: it instantiates the claim at `n = 19` and closes
the finite facts by `decide`, `norm_num` and the pinned lemmas
`Rat.num_div_eq_of_coprime` and `Rat.den_div_eq_of_coprime`.
`admission_basis: open-problem-resolution` under preregistration issue #10062;
`escape_witness: null`. There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

The reading of "numerator" and "denominator" as those of the reduced fraction
follows the entry's own listed values; under the unreduced form
`2^(n+1) − 2·C(n, ⌊n/2⌋)` the statement already fails at `n = 3`, which is not
the entry's reading. The physical derivation of the two bounds in the cited
NMR literature is not formalized; the Lean definitions are the entry's
formulas. Exhaustive publication coverage and priority are not claimed.
