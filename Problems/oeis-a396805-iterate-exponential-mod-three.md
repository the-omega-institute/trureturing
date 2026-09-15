---
slug: oeis-a396805-iterate-exponential-mod-three
bibkey: hanna2026a396805
doi: null
url: https://oeis.org/A396805
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateExponentialParity
---

# A396805 coefficients modulo three from index three

## Problem

Paul D. Hanna's OEIS A396805, dated June 9, 2026, states:

> E.g.f. satisfies A(x) = x*exp( A^5(x) ).
> Conjecture: a(n) == [0,1,0] repeating (mod 3) for n >= 3.

The formula field defines A^5 as the fifth compositional iterate and specifies
A(x)=Sum_{n>=1} a(n)*x^n/n!. For the unique zero-constant rational formal
solution A=X*exp(A^{[5]}), the exact conclusion is
forall n : Nat, 3 <= n -> Nat.ModEq 3 (IterateExponentialParity.aK 5 n)
(if n % 3 = 1 then 1 else 0).
The residues 0,1,0 begin at n=3. The source value a(2)=2 excludes extension
of this formula to all positive indices.

## Motivation

The exact first-tier external assertion was preregistered in #7925.
The existing parity_iterate_five settles parity. The A396803 and A396806
results have different iterate counts and do not resolve this statement.

## Gap

Revision 13 retrieved September 15, 2026 still labels this modulo-three
sentence Conjecture. The refreshed OEIS and all-state repository search found
no previous settlement. Earlier direct-cross-reference, arXiv, MathOverflow,
Math StackExchange and external GitHub sequence-code searches are reused with
the limits in #7925; they were not rerun in this refresh. Inaccessible general
search engines are not negative evidence. No global-priority claim is made.
The frozen integral EGF calculus provides composition and its coefficient
identities; the required modulo-three composition subsequences are proved here.

## Route

Write M(f,g)(n)=Sum_{i=0}^n binomial(n,i)*f(i)*g(n-i) for multiplication in
integral EGF coordinates. Over the integers, formal differentiation gives
M(M(f,f),f)(j+1)=3*M(M(f,f),shift(f))(j). Thus a cube modulo three has only
its constant coefficient. This uses rational formal series to establish an
integer identity, then reduces the integer identity modulo three.

The complete third-derivative chain rule for a composition has three terms.
Its middle term vanishes modulo three. If g(3q)=0 and g(1)=1, Lucas
factorization makes the final term vanish on the subsequence of indices 3q;
no condition on g(3q+2) is imposed. Induction, with the outer sequence f
arbitrary, gives

- (f composed with g)(3q)=f(3q);
- (f composed with g)(3q+1)=Sum_{r=0}^q binomial(q,r)*f(3r+1)*g(3(q-r)+1).

For b=aK 5 reduced modulo three, the defining fixed-point recurrence first
gives b(3q)=0 and b(1)=1. The same properties hold for every compositional
iterate of b. The two composition formulas then give b(3q+1)=1, the
j-th iterate's value j^q at 3q+1, and finally b(3q+2)=2*6^q modulo three.
At q=0 this is 2; for q>=1 it is zero. The n>=3 hypothesis supplies exactly
the last condition in the residue-two case.

## Falsifier

An n>=3 whose actual aK 5 n residue differs from the displayed conditional
value contradicts the theorem. A_equation, fixed_unique and eCoeff_encode
identify the exact source sequence independently of finite term agreement.

## Evidence

The sole new public theorem is
D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result.
Its proof is an unbounded symbolic derivation with all intermediate bridges
local to result. The existing sequence identity is supplied by
IterateExponentialParity. The compiled declaration and canonical frozen
record supply the exact statement identity and axiom closure. The declaration
statement ID is sha256:aa8e9a6f83db1cb8c5252146a1783d00bdfb0e17df3166a1f551289384d2c49a;
its axioms are Classical.choice, Quot.sound and propext.

## Triage

The modulo-three assertion is proved for every n>=3. Parity has its separate
frozen proof. The source's modulo-five assertion has previously recorded
exact non-kernel counterexamples at n=23 and n=24; this theorem supplies no
new refutation or kernel certificate for that separate assertion.

## ASSUMED-UNVERIFIED

Literature coverage has the stated limits; the Lean kernel does not
authenticate the external OEIS page. Source fidelity uses the fifth
compositional iterate, factorial-normalized coefficients and n>=3 lower
bound. No analytic convergence or statement for every iterate count is
asserted. Ordinary differentiation over characteristic-three formal series
is not used as a substitute for integral EGF coefficient shifts.
