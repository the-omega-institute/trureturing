---
slug: oeis-a396803-iterate-exponential-mod-three
bibkey: hanna2026a396family
doi: null
url: https://oeis.org/A396803
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateExponentialParity
---

# A396803 coefficients modulo three

## Problem

Paul D. Hanna's OEIS A396803 entry, dated June 8, 2026, states:

```text
%N A396803 E.g.f. satisfies A(x) = x*exp( A^3(x) ).
%C A396803 Conjecture: a(n) == [1,2,0] repeating (mod 3) for n >= 1.
```

The formula field defines `A^3` as the third compositional iterate.
For the unique zero-constant rational formal solution of
`A=X*exp(A composed with A composed with A)`, put `a(n)=n![X^n]A`.
The assertion is `forall n >= 1, a(n) = n (mod 3)`.

## Motivation

This first-tier external conjecture is the remaining A396803 clause after the
parity result in `IterateExponentialParity`. The exact positive-index statement
was preregistered in issue #7912. The result concerns every positive index;
the related residue conjectures for A396805 and A396806 are separate questions.

## Gap

The OEIS revision 16 retrieved on September 15, 2026 still labels this assertion
a conjecture. The entry, its direct cross-references, repository PRs and issues
in all states, arXiv, MathOverflow, Math StackExchange and external GitHub
sequence-generation code supplied no proof or refutation in the searched scope.
Unavailable general search-engine results do not count as literature evidence.
No claim of exhaustive literature coverage or first-publication priority is made.

The existing `aK`, `AK`, `A_equation`, `fixed_unique` and `eCoeff_encode`
identify the sequence with the original formal-series equation. The additional
mathematical step is invariance of its coefficient transformation modulo three.

## Route

Let `l(n)=n` in `ZMod 3` and let `g` be its third compositional iterate in
integral EGF coordinates. Substitution by `X*exp(X)` induces
`T(f)(n)=sum_{j=0}^n binomial(n,j)*f(j)*j^(n-j)`.
Lucas decomposition shows that `T(f)(3q)=f(3q)` and that the subsequence
`T(f)(3q+1)` is the binomial transform of `f(3q+1)`.
Since `g=T(T(l))`, it follows that `g(3q)=0` and
`g(3q+1)=if q=0 then 1 else 0`.

For any sequence with these support properties, let `E=composition(1,g)`
using the integral composition recurrence and the constant-one outer sequence.
Then `E(3q)=E(3q+1)=1`. Indeed, the composition recurrence
gives `E(3q+1)=E(3q)`, `E(3q+2)=E(3q)+S` and
`E(3q+3)=E(3q+2)+2S` with the same auxiliary sum `S`. Its contributions
cancel in characteristic three. This proves that the fixed-point coefficient
transformation preserves `l`. Induction through all approximation stages and
the existing diagonal definition of `aK` prove the congruence.

## Falsifier

A positive integer `n` for which `aK 3 n % 3` differs from `n % 3` would
contradict the result. Identification with the OEIS sequence is supplied by
the defining equation and uniqueness, independently of finite term agreement.

## Evidence

- Module: `D5/S1/Recurrence/Residue/IterateExponentialModThree.lean`.
- Sole resolution theorem: `result`.
- Statement: `forall n : Nat, 1 <= n -> Nat.ModEq 3 (IterateExponentialParity.aK 3 n) n`.
- Axiom closure: `propext`, `Classical.choice`, `Quot.sound`.
- The proof is symbolic and unbounded. No finite table or computation is a premise.

## Triage

`theorem`. The modulo-three assertion is proved for the existing sequence
identified with the entry's unique formal solution. The earlier parity result
and this result settle the two conjectures quoted in the A396803 snapshot.

## ASSUMED-UNVERIFIED

Literature coverage is limited to the stated searches. The theorem makes no
analytic convergence claim and no assertion about the A396805 or A396806
residue conjectures.
