---
slug: oeis-a396798-eighth-iterate-mod-eight
bibkey: hanna2026a396798
doi: null
url: https://oeis.org/A396798
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
  - D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix
  - D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive
---

# The eighth compositional iterate of A396798 modulo eight

## Problem

Paul D. Hanna's OEIS A396798, revision 12, defines an ordinary generating
series by "G.f. satisfies A(x) = x + A^4(x)*A^5(x)." Its formula field says
that A^k denotes the k-th iteration. The eighth comment states:

> Conjecture: [x^n] A^8(x) == 0 (mod 8) for n > 1.

Let I0(A)=X and I(k+1)(A)=Ik(A) composed with A. For the unique zero-constant
integer series satisfying A=X+I4(A)*I5(A), prove
`forall n:Nat, 1<n -> (8:Int) divides coeff n (I8(A))`.
The product is ordinary multiplication and the coefficients have no factorial
normalization. The source object is constructed, not assumed to exist.

## Motivation

This first-tier external named conjecture was preregistered in #7943 before
its probe. Frozen generic degree contraction, Mobius iteration and
square-zero iteration supply the needed tools. The existing 3/4 and 5/6
results concern distinct source equations.

## Gap

The complete revision-12 source and its four direct references
A396797/A396807/A396099/A213591 do not give this eighth-clause proof.
Exact-A-number Crossref, arXiv and public GitHub Lean-code searches found
no hit within their stated indices. All-state repository searches found
the earlier queue/referral issues #6436 and #6375, without a settlement of
this clause before #7943. Failed or broad search endpoints supply no
negative evidence; differently named and unindexed results remain outside
that conclusion. No global-priority claim is made.

## Route

Define H(F)=X+I4(F)*I5(F) and take coefficient n from H^[n+1](0).
Generic contraction proves stabilization in every degree, the source
equation, constant coefficient zero and linear coefficient one. A local
uniqueness proof works over any commutative coefficient ring and is used
at ZMod4. There M=X/(1-X) satisfies I4(M)=X, I5(M)=M and M=X+X*M, so the
true source reduces to M. Consequently every coefficient of I4(A)-X is
divisible by four. An exact integer quotient writes I4(A)=X+4B. Reduction
from the integers to ZMod8 and the existing nilpotent_iterate at r=4,j=2
give I2(I4(A))=X. The frozen iterate-addition identity identifies this with
I8(A). No map from ZMod4 to ZMod8 or division in a non-field is assumed.

## Falsifier

An n>1 whose actual eighth-iterate coefficient is not divisible by eight
would refute the source assertion. A substitute series, a finite prefix or
an unfulfilled fixed-point hypothesis would invalidate the source bridge.

## Evidence

The public source definition and sole theorem are
`D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
and `.result`. Stabilization, the source equation and the generic uniqueness
bridge occur in the result's live proof; the uniqueness specialization
used in the congruence argument is ZMod4. The integer specialization also
establishes uniqueness of the constructed source. The proof has no finite
truncation premise, sorry or new axiom. Canonical identities are supplied
by the freeze and emitted declaration binding.

## Triage

This delivery resolves only the eighth comment, with `proof_shape: bind-only`
and `admission_basis: open-problem-resolution` under the prior registration.
It claims no escape witness. `utility.kind: none` reflects an all-index
symbolic result, not an enumeration, checker, numerical reduction or finite
positive instance. Necessary definitions and the one result are the entire
public surface; all intermediate bridges are local.

The original first comment has a previously recorded non-kernel contradiction
at n=3. Comments 2 and 6 concern n>3, comment 4 concerns n>2, and comments
3,5,7 specify their own periods for n>1. Those six clauses and a repaired
first-comment period are not settled here.

## ASSUMED-UNVERIFIED

The kernel verifies the formal statement and proof, not authenticity of the
external OEIS page or completeness of the bounded literature search. No
analytic convergence, full modulo-eight formula for A, nonnegativity
theorem or settlement of the other comments is claimed.
