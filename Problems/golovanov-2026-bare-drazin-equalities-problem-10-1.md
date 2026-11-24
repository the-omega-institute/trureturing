---
slug: golovanov-2026-bare-drazin-equalities-problem-10-1
bibkey: golovanov2026spectralcoincidence
doi: 10.48550/arXiv.2611.19664
url: https://arxiv.org/pdf/2611.19664v1#page=29
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/GolovanovBareDrazinEqualities.result
---

# Golovanov Problem 10.1 — Bare Drazin equalities

## Problem

> Let \(R\) be a unital associative ring, and let \(a,c\in R\) be
> finite-Drazin invertible with \(a+c\in R^\times\). Put \(b=(a+c)^{-1}\)
> and \(t=a-aba\). Characterize the pairs for which \(t\) is
> finite-Drazin invertible and \(t^D=a^D+c^D\), without assuming
> coincidence of the input core idempotents \(aa^D\) and \(cc^D\).

[Problem 10.1](https://arxiv.org/pdf/2611.19664v1#page=29)

## Motivation

Theorem 5.2(c) characterizes the finite Drazin sum equality by a
nilpotent complementary-corner residue under coincident input cores.
Problem 10.1 asks how to test the equality for arbitrary cores.
[Theorem 5.2(c)](https://arxiv.org/pdf/2611.19664v1#page=14)

## Gap

With different cores, the output inverse candidate can fail to commute
with the parallel sum or can fail the outer inverse equation in addition
to having a non-nilpotent remainder. The characterization must test all
three clauses with the multiplication order fixed.

## Route

Write \(u=a^D\), \(v=c^D\), \(s=u+v\), \(p=au\), \(r=cv\),
\(z=r-p\), \(n_a=a-pa\), and \(n_c=c-rc\). Define
\[
P=cbn_a bc+abn_c ba.
\]
The two inverse equations give \(t=abc=cba\). They yield
\(ts=p+abz\), \(st=p+zba\), \(sts-s=-zbz\), and \(t-(ts)t=P\).
The last identity follows by multiplying
\(1-ts=cb(1-p)+ab(1-r)\) by \(t\), using the appropriate ordered
expression in each summand.

Thus \(t\) has finite Drazin inverse \(s\) exactly when
\(abz=zba\), \(zbz=0\), and \(P\) is nilpotent. For uniqueness of
each finite Drazin witness, choose a common positive power at which both
remainders vanish. The absorbed powers identify the cores and then the
witnesses. This also covers a nilpotence witness at exponent zero.

## Falsifier

A pair satisfying both inverse equations and both input finite Drazin
predicates would defeat the criterion if exactly one side of the
equivalence held. A failure of uniqueness under the stated finite Drazin
predicate would defeat its interpretation in inverse notation.

## Evidence

The theorem
`D5/S3/ArithUnits/GolovanovBareDrazinEqualities.result` gives both
directions of the criterion with the existence of the output inverse
explicit. Its ring instance requires a unital associative ring and also
admits the zero ring.
[Lean result](../D5/S3/ArithUnits/GolovanovBareDrazinEqualities.lean) ·
[Versioned source and attribution](../Library/ArithUnits/golovanov2026spectralcoincidence.md) ·
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/33717)

## Triage

### What the settlement shows

**Proved.** The difference of core idempotents controls the commutation
and outer inverse tests. With coincident cores, \(z=0\), those tests
hold automatically and the nilpotence condition is the remaining test.

**Checked in a finite example.** Over \(M_3(\mathbb F_2)\), take
\(a=E_{13}+E_{21}\), \(c=E_{11}+E_{32}\),
\(b=E_{12}+E_{23}+E_{31}+E_{32}\), \(u=0\), and \(v=E_{11}\).
The inputs have unequal cores and satisfy all three tests. The example
uses matrix units indexed from one.

**Open here.** Problem 10.2 concerns structural conditions for coincidence
with Harte-quasinilpotent remainders. Problem 10.3 concerns sharp uniform
bounds in augmented Banach-algebra data.
[Problems 10.2 and 10.3](https://arxiv.org/pdf/2611.19664v1#page=29)

## ASSUMED-UNVERIFIED

The bounded literature search found no earlier settlement. Worldwide
priority and completeness of reverse-citation coverage are unverified.
