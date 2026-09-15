---
slug: oeis-a396798-fourth-iterate-mod-eight
bibkey: hanna2026a396798
doi: null
url: https://oeis.org/A396798
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
  - D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  - D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
  - D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive
---

# The fourth compositional iterate of A396798 modulo eight

## Problem

Paul D. Hanna's OEIS A396798, revision 12, defines the ordinary generating
series by "G.f. satisfies A(x) = x + A^4(x)*A^5(x)." Its formula field says
that A^k denotes the k-th iteration. The fourth comment states:

> Conjecture: [x^n] A^4(x) == 0 (mod 8) for n > 2.

Let I0(A)=X and I(k+1)(A)=Ik(A) composed with A. For the unique zero-constant
integer series satisfying A=X+I4(A)*I5(A), prove
`forall n:Nat, 2<n -> (8:Int) divides coeff n (I4(A))`.
Multiplication is ordinary multiplication of formal series. There is no
factorial normalization or analytic convergence hypothesis.

The source is the existing
`D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`.
The fourth-iterate theorem uses precisely this definition.

## Motivation

This first-tier external named conjecture was preregistered in
[#7950](https://github.com/the-omega-institute/trureturing/issues/7950).
The eighth-iterate module supplies the common source definition. Frozen
degree contraction, Mobius iteration and substitution annihilation provide
the tools for the fourth-iterate argument.

## Gap

The complete revision-12 source and its direct references
A396797/A396807/A396099/A213591 do not provide this fourth-clause proof.
The exact-A-number Crossref, arXiv and public Lean-code searches recorded
in the preregistration found no result within their stated indices.
The earlier #6436 queue concerns the second-iterate strong congruence;
#6375 refers to that queue. Neither is used as a proof of this clause.
Unavailable or irrelevant search responses are not negative evidence,
and differently named or unindexed results are not excluded. No global
priority is claimed.

## Route

The common source definition takes coefficient n from H^[n+1](0), where
H(F)=X+I4(F)*I5(F). Degree contraction proves stabilization, zero constant
coefficient, the source equation and uniqueness. In ZMod4, X/(1-X) is the
unique zero-constant solution, so A reduces to that Mobius series.
Its second iterate is X+2X^2 modulo four; multiplication by the unit
1-2X verifies this complete series identity.

Every integer coefficient of I2(A)-(X+2X^2) is therefore divisible by four.
Taking exact integer quotients and then reducing modulo eight yields
G=X+2X^2+4B, where G is the reduction of I2(A). The source gives G(0)=0.
The frozen subst_annihilate theorem applied to 4,B,G,X gives
4((B composed with G)-B)=0 because 4(G-X)=0. Ring expansion also gives
2G^2=2X^2. Hence G composed with G=X+4X^2.

The iterate-addition identity at 2+2 and compatibility of coefficient
reduction with substitution identify the left side with I4(A) modulo
eight. Every coefficient above degree two then vanishes. The proof does
not assume B(0)=0, a specific mod-eight formula for I2(A), or a ring map
from ZMod4 to ZMod8. It does not use nilpotent_iterate with r=2.

## Falsifier

An n>2 whose actual fourth-iterate coefficient is not divisible by eight
would refute the source assertion. A substituted source series, a finite
prefix or an unfulfilled source equation would invalidate the source
identification.

## Evidence

The one public theorem is
`D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result`.
Its source is the existing eighth-module generatingSeries named above.
Stabilization, the source equation, uniqueness, mod-four identification,
exact integer quotient and mod-eight cancellation are local to result.
No new source definition, companion theorem or finite truncation premise
is introduced. The declaration binding and frozen identities are supplied
by the canonical report and writer.

## Triage

This result settles only the fourth comment under
`admission_basis: open-problem-resolution`, with `proof_shape: bind-only`
and no escape witness. `utility.kind: none` reflects an unbounded symbolic
proof, not a bounded enumeration, checker, numerical reduction or positive
finite certificate.

The eighth comment is separately settled by
`IterateProductFourFiveEighthModEight.result` for n>1. Comments 2 and 6
concern the second and sixth iterates for n>3 and remain with #6436
(and the #6375 referral). These two clauses and the proposed repair to
the first comment retain their separate unresolved obligations.
`IterateProductFourFiveSeventhModEight.result` separately settles the seventh
comment for every n>1, with period 7,1,3,5 from n=2, using the same source
and (n-2)%4. The third comment is separately settled by `IterateProductFourFiveThirdModEight.result`
for every n>1, with period 3,1,7,5 beginning at n=2. The
fifth comment is separately settled by `IterateProductFourFiveFifthModEight.result`
for every n>1, with period 5,1,1,5 beginning at n=2.
The previously recorded contradiction to the original first-comment
period is non-kernel evidence and is not a new formal refutation here.

## ASSUMED-UNVERIFIED

The formal proof does not certify authenticity of the external OEIS page
or completeness of the bounded literature search. No full mod-eight
formula for A, nonnegativity theorem, analytic convergence statement or
settlement of the other comments is claimed.
