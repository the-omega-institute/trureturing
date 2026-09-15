---
slug: oeis-a396798-fifth-iterate-mod-eight
bibkey: hanna2026a396798
doi: null
url: https://oeis.org/A396798
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
  - D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight
  - D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
  - D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive
  - D5/S1/Recurrence/Parity/DiagonalIterateEven
---

# The fifth compositional iterate of A396798 modulo eight

## Problem

Paul D. Hanna's OEIS A396798, revision 12, defines the ordinary generating
series by "G.f. satisfies A(x) = x + A^4(x)*A^5(x)." Its formula field says
that A^k denotes the k-th iteration. The fifth comment states:

> Conjecture: [x^n] A^5(x) == [5,1,1,5] repeating (mod 8) for n > 1.

Let I0(A)=X and I(k+1)(A)=Ik(A) composed with A. For the unique zero-constant
integer series satisfying A=X+I4(A)*I5(A), the exact target is
`forall n:Nat, 1<n -> 8 divides coeff n (I5(A)) - r(n)`, where
`r(n)=if (n-2)%4=0 or (n-2)%4=3 then 5 else 1`.
The four-term period begins at n=2. Multiplication is ordinary series
multiplication, with no factorial normalization or convergence assumption.
The source is the existing
`D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`.

## Motivation

This first-tier external named conjecture was preregistered in
[#7961](https://github.com/the-omega-institute/trureturing/issues/7961).
The fourth and eighth public results on that same source provide the
high-degree coefficients needed to turn the fifth-iterate question into
linear identities of formal series.

## Gap

The complete revision-12 source and its four direct references
A396797/A396807/A396099/A213591 do not supply this fifth-clause proof.
Exact-A-number Crossref, arXiv and public Lean-code searches and all-state
repository records found no fifth-clause settlement in their stated scope.
The earlier #6436/#6375 queue concerns the second-iterate strong congruence.
Unavailable searches provide no negative evidence. Differently named or
unindexed general results are not excluded, and no global priority is claimed.

## Route

The fixed source definition and degree contraction give its zero constant
coefficient, fixed-point equation and identity. The first two positive
coefficients follow from the source product: a1=a2=1. The general
iterate-coefficient identity then gives coeff2(I4(A))=4. Combining these
low coefficients with the public fourth and eighth results gives, over
ZMod8, P=I4(F)=X+4X^2 and I8(F)=X, where F is the reduction of A.

Write J=I5(F). The true source equation is F=X+P*J. Substituting P into
that equation and using iteration addition at 1+4, 4+4, 5+4 and 8+1 gives
J=P+X*F. Eliminating F gives
`J*(1-X^2-4X^3)=X+5X^2`. Multiplication by `1+X^2+4X^3` yields
`(J-X)*(1-X^4)=5X^2+X^3+X^4+5X^5`.

The denominator 1-X^4 has constant coefficient 1 and is a unit even over
ZMod8. With Q the geometric series supported at multiples of four, this
gives the complete identity
`J=X+X^2*(5+X+X^2+5X^3)*Q`. Its coefficients at every index n>1 are
5,1,1,5 according to the residue of n-2 modulo four. The argument keeps
the lower-index bounds in convolution and does not replace the universal
claim with a finite prefix. No division by 2 or 4, nonzero-factor
cancellation, second-iterate strong congruence or assumed formula for A
is used.

## Falsifier

An n>1 whose fifth-iterate coefficient differs from r(n) modulo eight
would refute this exact source assertion. Starting the cycle at n=1,
substituting a different source, or assuming an unproved source equation
would invalidate fidelity to the problem.

## Evidence

The public result is
`D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result`.
It uses the existing source and the two separately frozen iteration
results. All source adaptations, low-degree identities, linear
elimination and coefficient arguments are local to result. There is no
new source definition or companion theorem. Canonical reporting and
freezing supply the declaration and dependency identities.

## Triage

The single result settles only the fifth comment under
`admission_basis: open-problem-resolution`. Its `proof_shape: bind-only` classification
reflects reuse of existing results and normalization; no escape witness is claimed.
The argument is unbounded and symbolic, with `utility.kind: none`.

The fourth comment is separately settled for n>2 and the eighth for n>1.
The third comment is separately settled by
`IterateProductFourFiveThirdModEight.result` for n>1 with period 3,1,7,5
from n=2. Comments 2,6,7 and the proposed repair of the first comment
retain their own obligations. The recorded contradiction to the
original first-comment period remains non-kernel evidence and is not a
new formal refutation here.

## ASSUMED-UNVERIFIED

The proof does not certify external-page authenticity or completeness
of the bounded literature search. It makes no global-priority,
nonnegativity, analytic-convergence or remaining-clause claim.
