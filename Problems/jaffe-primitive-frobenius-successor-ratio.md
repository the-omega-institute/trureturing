---
slug: jaffe-primitive-frobenius-successor-ratio
bibkey: jaffe2026denominators
doi: null
url: https://arxiv.org/abs/2610.17267v1
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/JaffeSuccessorRatioRefutation
---

# Jaffe's unrestricted primitive Frobenius successor-ratio conjecture

## Problem

The target is exactly Conjecture 7.3 in arXiv:2610.17267v1:

> For all a,b >= 3 relatively prime and for c(a,b) the minimum integer satisfying both c(a,b)>b and gcd(c(a,b),a)=1, we have g(a,c(a,b))/g(a,b) <= 5.

Section 3 defines
\[
R(a,b)=\{ax+by:x,y\in\mathbb Z_{\geq0},\ \gcd(x,y)=1\},
\quad
g(a,b)=\max(\mathbb Z\setminus R(a,b)),
\]
with infinity when a greatest missing integer does not exist. Zero
coefficients are allowed. There is no \(a<b\) assumption. The successor is
the least **integer** above \(b\) coprime to \(a\). The same conjecture is
numbered 8.3 in the author's 2023 dissertation; this dossier anchors one
assertion, not two. Conjecture 7.2 is a different target.

The Lean definition `fullClaim : Prop` uses precisely this integer domain,
representation predicate, greatest-missing convention, successor and
quotient bound. The designated `result : Not fullClaim` is unconditional.

## Motivation

The source asks for a uniform bound when the second generator advances to
its next coprime integer. The primitive missing-number scaling obstruction
allows a large successor gap to violate that uniform bound. Exchange
symmetry of the represented set does not exchange this successor operation.

## Gap

The [registered target #20244](https://github.com/the-omega-institute/trureturing/issues/20244)
is the whole universal claim. The bounded source and literature
qualification found no inspected whole answer. The formal gap is an
admissible pair with an exact least successor and actual finite positive
greatest missing integers whose quotient violates the bound. Finite
searches for missing values or an assumed finiteness hypothesis do not
settle that gap.

## Route

Take \(a=87841397512641630\), \(b=7\). The integer \(a\) is coprime to 7
and 49, and every integer strictly between them is noncoprime to \(a\).
Thus \(c(a,7)=49\).

For arbitrary positive coprime \(A,B\), count all nonnegative solutions
by \(H(n)\) and primitive ones by \(P(n)\). Residues modulo \(B\) give
\(\lfloor n/(AB)\rfloor\leq H(n)\leq\lfloor n/(AB)\rfloor+1\).
Partitioning by the coefficient gcd and applying Möbius inversion yields
\(ABP(n)\geq\varphi(n)-AB\tau(n)\). Prime-power estimates give
\(n\tau(n)^2\leq16^7\varphi(n)^2\), hence every
\(n>16^7(AB)^2\) has a primitive representation. For \(A,B\geq3\),
the missing integer 1 and this universal tail prove that the integer
complement has a positive maximum.

If \(n\) is missing for \((a,7)\), then \(7n\) is missing for
\((a,49)\). A primitive representation of \(7n\) would force its first
coefficient to be divisible by 7; dividing it gives a primitive
representation of \(n\). Apply this to the actual maximum for \((a,7)\).
The maxima are finite and positive, and
\[
\frac{g(a,c(a,7))}{g(a,7)}
=\frac{g(a,49)}{g(a,7)}\geq7>5.
\]

## Evidence

The mathematical source is
`D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.lean`, and the designated
declaration is `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result`.
The claim definition's type is literally `Prop`; the result is written
literally as `theorem result : ¬ fullClaim`. Its utility basis is
`certified-instance` / `refutes`, and its owning Scribe carries
`OpenProblemResolutionClaim(Refuted)` for this slug.

The proof includes the complete primitive tail, actual greatest-element
construction in \(\mathbb Z\), least-successor argument and quotient
transport. It uses no assumed maximum, truncated maximum or conclusion
hypothesis. The source's existing finiteness and scaling ingredients are
attributed to Theorems 4.3 and 7.1. The Library note identifies the source
versions and qualification limits.

## Falsifier

A mismatch in coefficient nonnegativity or coprimality, integer complement,
source ordering, successor minimality, tail count, maximum construction or
division by a positive finite value would invalidate this route. An
ordered-only statement or a conditional tail would not refute this target.

## Triage

`theorem`, under `open-problem-resolution` with registration #20244.
This is the complete unfrozen StageA candidate. Independent source-mirror
review, freezing, required integration checks and acceptance remain
pending. The constant-five claim is the single target and carries at most
one accepted credit. The general prime-indexed unbounded-ratio family is
not a separate formal result here. The ordered variant remains unresolved;
the source's earlier proved results are unaffected.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive absence of an older equivalent theorem
are unverified. The checked thesis states the same conjecture; the checked
Shimizu manuscript addresses 7.2. Incomplete citation indexing and bounded
searches do not establish originality. The
[Library note](../Library/ArithUnits/jaffe2026denominators.md) gives the
qualified source and reuse account. This dossier makes no final review,
CI, merge, KPI or host-continuation completion claim.
