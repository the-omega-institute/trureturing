---
slug: oeis-a396806-iterate-exponential-mod-six
bibkey: hanna2026a396806
doi: null
url: https://oeis.org/A396806
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateExponentialParity
---

# A396806 coefficients modulo six

## Problem

Paul D. Hanna's OEIS A396806 entry, dated June 9, 2026, states:

> E.g.f. satisfies A(x) = x*exp( A^6(x) ).
> Conjecture: a(n) == [1,2,0] repeating (mod 3) for n >= 1.
> Conjecture: a(n) == [1,2,3,4,5,0] repeating (mod 6) for n >= 1.

The formula field defines A^6 as the sixth compositional iterate and gives
A(x)=Sum_{n>=1} a(n)*x^n/n!. For the unique zero-constant rational formal
solution A=X*exp(A^{[6]}), the assertion is
forall n : Nat, 1 <= n -> Nat.ModEq 6 (IterateExponentialParity.aK 6 n) n.
It entails the quoted modulo-three clause because three divides six.

## Motivation

This first-tier external target was preregistered in issue #7920. The existing
IterateExponentialParity module settles the parity comment and identifies the
coefficient sequence. The separate A396803 result has iterate count three.

## Gap

OEIS revision 11, retrieved September 15, 2026, still labels both residue
comments Conjecture. The refreshed source and all-state repository searches
found no prior modulo-three or modulo-six settlement for A396806. The earlier
direct-cross-reference, arXiv, MathOverflow, Math StackExchange and external
GitHub sequence-code searches are reused with the bounds stated in #7920;
they were not rerun in this refresh. Inaccessible general search engines are
not negative evidence. No exhaustive literature coverage or priority is claimed.

## Route

In integral EGF coordinates over ZMod 3, set l(n)=n and
T(f)(n)=sum_j binomial(n,j)*f(j)*j^(n-j). Lucas decomposition and the binomial
theorem give, for all j,q, T^[j](l)(3q)=0 and
T^[j](l)(3q+1)=(j+1)^q. Integer composition associativity and coefficient
reduction identify the sixth compositional iterate of l with T^[5](l).
Its residue-zero terms vanish; its residue-one terms equal one at q=0 and
zero otherwise. Residue-two terms remain unrestricted.

For every inner sequence with exactly these support properties, the outer
exponential recurrence gives value one at indices 3q and 3q+1: the two
contributions S and 2S cancel across the three-index block. The leading
index factor then makes stepK 6 preserve l modulo three. Induction through
approximationK yields the modulo-three congruence for aK 6. The existing
parity_mod_two theorem and the coprime moduli two and three give modulo six.

For the comparison series F=X*exp(X), the stronger identity F^{[6]}=X
modulo three is not used: its degree-eight
integral EGF coefficient has nonzero residue two. That auxiliary identity's
failure does not refute the source conjecture.

## Falsifier

A positive n with aK 6 n % 6 different from n % 6 would contradict the
assertion. A_equation, fixed_unique and eCoeff_encode identify the source
sequence independently of finite term agreement.

## Evidence

The sole result is
D5/S1/Recurrence/Residue/IterateExponentialModSix.result. It proves the exact
positive-index congruence for the existing natural sequence. The universal
proof uses only Classical.choice, Quot.sound and propext; all auxiliary
claims are local and their hypotheses are discharged. The Scribe statement
expresses the equivalent remainder equality. No finite table or numerical
premise supplies the all-index conclusion.

## Triage

theorem. The single result proves the source modulo-six assertion and
therefore also its modulo-three assertion. Together with the existing parity
theorem, these settle the three conjecture comments in the inspected A396806
snapshot. A396805's modulo-three question remains separate; its modulo-five
assertion has previously recorded non-kernel counterexamples.

## ASSUMED-UNVERIFIED

Literature coverage is limited to the stated searches; the Lean kernel does
not authenticate the external page. The source-to-formal correspondence is
independently reviewed through the equation, composition convention and
factorial-normalized coefficients. No analytic convergence, global priority
or universal congruence for every iterate count is asserted.
