---
slug: oeis-a396798-third-iterate-mod-eight
bibkey: hanna2026a396798
doi: null
url: https://oeis.org/A396798
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
  - D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight
  - D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight
---

# The third compositional iterate of A396798 modulo eight

## Problem

Paul D. Hanna's OEIS A396798, revision 12, defines the ordinary generating
series by "G.f. satisfies A(x) = x + A^4(x)*A^5(x)." Its formula field says
that A^k denotes the k-th iteration. The third comment states:

> Conjecture: [x^n] A^3(x) == [3,1,7,5] repeating (mod 8) for n > 1.

Let I0(A)=X and I(k+1)(A)=Ik(A) composed with A. For the unique zero-constant
integer series satisfying A=X+I4(A)*I5(A), the target is
`forall n:Nat, 1<n -> 8 divides coeff n (I3(A)) - r(n)`, where
`r(n)=if (n-2)%4=0 then 3 else if (n-2)%4=1 then 1 else if (n-2)%4=2 then 7 else 5`.
The period starts at n=2. Multiplication is ordinary series multiplication,
with no factorial normalization or convergence assumption. The source is
`D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`.

## Motivation

This first-tier external named conjecture was preregistered in
[#7982](https://github.com/the-omega-institute/trureturing/issues/7982).
The public fifth and eighth results on that same source reduce the
third-iterate question to a compositional inverse identity over ZMod8.

## Gap

The complete revision-12 source and its four direct references
A396797/A396807/A396099/A213591 do not supply the third-clause proof.
Exact-A-number Crossref, arXiv and public Lean-code searches and all-state
repository records found no third-clause settlement within their checked
scope. The #6436/#6375 queue concerns the second-iterate strong congruence.
Unavailable searches provide no negative evidence; a current arXiv request
returned HTTP429 and the public code index omitted known repository results.
Differently named or unindexed results are not excluded, and no global
priority is claimed.

## Route

Reduce the fixed integer source to F over ZMod8. The frozen coefficientwise definition supplies its zero constant
coefficient and linear coefficient one. These low coefficients supplement the public eighth
coefficient theorem to give I8(F)=X. The public fifth theorem gives
`J=I5(F)=X+X^2*(5+X+X^2+5*X^3)*Q`, where Q has coefficient one precisely
at multiples of four and satisfies `Q*(1-X^4)=1`.

Set `K=X+X^2*(3+X+7*X^2+5*X^3)*Q`. Clearing powers of the unit 1-X^4
and the unit 1-J^4 reduces `K composed with J = X` to an exact polynomial
identity in characteristic eight. Only proved units are cancelled.
Iteration addition gives `I3(F) composed with I5(F)=I8(F)=X`;
compositional cancellation then identifies I3(F) with K. Extracting every
coefficient above degree one gives the period 3,1,7,5 with the natural
subtraction bounds retained. No second-iterate conjecture or assumed
rational formula for the original source is a premise.

## Falsifier

An n>1 whose third-iterate coefficient differs from r(n) modulo eight
would refute this exact assertion. Starting the cycle at n=1, substituting
a different source, cancelling a nonunit or replacing an infinite series
identity by a finite prefix would invalidate the result.

## Evidence

The public result is
`D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result`.
All source adaptations, rational identities, unit proofs and coefficient
arguments are local to this single result. No source definition or companion
theorem is added. Canonical reporting and
freezing supply its declaration and dependency identities.

## Triage

The single result settles only the third comment under
`admission_basis: open-problem-resolution`, with `proof_shape: bind-only`
and no escape witness claimed. Its unbounded symbolic proof has
`utility.kind: none`.
The fourth, fifth and eighth comments have separate existing results.
Comments 2,6,7 and the proposed repair of the first comment retain their
own obligations. The original first-comment contradiction remains
non-kernel evidence and is not a new formal refutation here.

## ASSUMED-UNVERIFIED

The proof does not certify external-page authenticity or completeness
of the bounded literature search. It makes no global-priority,
nonnegativity, analytic-convergence or remaining-clause claim.
