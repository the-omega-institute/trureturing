---
bibkey: robertson2004generalizedpell
authors: John P. Robertson
year: 2004
title: "Solving the generalized Pell equation x^2 - Dy^2 = N"
doi: null
url: https://web.archive.org/web/20160323033128id_/http://www.jpr2718.org/pell.pdf
claim: "Integral solutions of x^2-D*y^2=N are equivalent under multiplication by integral solutions of u^2-D*v^2=1, including -1; one fundamental representative is selected per class."
strata_touched:
  - D5/S3/ArithUnits/PellClassSuccessor
license: citation-only
triage: anchor
---

# Integral-unit classes in Robertson's generalized Pell equation

The article is dated July 31, 2004 and prints Copyright 2004 by John P.
Robertson on page 1. Its general setting is positive nonsquare integer D
and nonzero integer N. The introduction explicitly says that proofs are
not given and that references to proofs are supplied instead.

## Class definition: page 12

In the section “Structure of solutions to x^2 - Dy^2 = N,” two integral
solutions (x,y) and (r,s) are equivalent when there are integers u,v with

```text
u^2 - D*v^2 = 1,
x = r*u + D*s*v,
y = r*v + s*u.
```

This is multiplication in the integral quadratic order Z[sqrt(D)].
Robertson also states the equivalent integrality test for
(x*r-D*y*s)/N and (x*s-y*r)/N. His observation that (-1,0) has norm one
makes (x,y) and (-x,-y) equivalent. It does not assert that arbitrary
independent sign changes give equivalent pairs. There is no
primitive-solution premise in this class definition.

The earlier portion of page 12 continues the discussion of norm +/-4
solutions. Its references and remarks about squarefree parameters belong
to that preceding discussion. They do not impose a squarefree restriction
on the generalized class definition that follows.

## Representatives and order: pages 13-14

For positive N, page 13 describes half-open intervals on the solution
hyperbola formed using the minimal positive norm-one solution. It states
that no two integral solutions in one such interval are equivalent, each
interval has one solution from every class, and the class order is the
same in every interval. It also allows a different starting point on the
hyperbola. These are stated classical facts, not proofs supplied here.

A fundamental representative minimizes the nonnegative y-coordinate in
its class. If the minimum has two representatives with opposite
x-coordinates, the positive x-coordinate is chosen. This representative
can differ from the minimal solution with both coordinates nonnegative.
Page 14 describes a list with one representative per class and expresses
the solutions of a class by multiplying one solution by signed integer
powers of the minimal positive norm-one unit.

The fundamental positive solution of the norm-one equation is consequently
a different object from the fundamental representative of each generalized
norm-N class. Counting generalized classes must not be replaced by a
norm-one uniqueness statement or by listing only positive coordinate pairs.

## Scope for A399755

With D=(k:Int)^2+1 and N=D, the coordinate relation above is exactly
SameClass(k,x,y,r,s). The solution equation is Sol(k,x,y), and
MultipleClasses(k) asserts the existence of two integral solutions not
related by that action. All integer coordinates, including the action of
-1, remain in scope. Units with fractional coordinates in the maximal
order of the field would change the equivalence relation and are excluded.

The article supplies terminology and classical context. It does not state
Wu's 2026 A399755 conjecture or identify the least partner in A399491.
Applying any class-orbit or interval theorem to that target still requires
all its hypotheses and the uniform order argument; norm preservation alone
is insufficient. No derivation or proof of the A399755 criterion is
attributed to Robertson.

## References and evidence boundary

The reference line immediately after this section, on page 15, names
Niven-Zuckerman-Montgomery [14], Mollin [12], Chrystal [2], Leveque [8],
and Rose [18]. The article's bibliography identifies these as:

- Ivan Niven, Herbert S. Zuckerman, and Hugh L. Montgomery, An Introduction
  to the Theory of Numbers, fifth edition, 1991.
- Richard E. Mollin, Fundamental Number Theory with Applications, 1998.
- G. Chrystal, Algebra, An Elementary Text-Book, Part II; multiple editions
  are listed in the article.
- William Judson Leveque, Topics in Number Theory, Volume 1, 1956, with a
  Dover 2002 edition also listed.
- H. E. Rose, A Course in Number Theory, 1988.

These are Robertson's bibliographic references, not independently read
proof sources. The title, introduction, pages 12-14, the adjacent reference
line, and the relevant bibliography delimit this note's direct reading.
The broader bounded search in issue #8016 reports no exact A399755
resolution in its inspected scopes, with inaccessible sources and later
live changes excluded. This note does not assert exhaustive absence or
priority for the classical facts or the 2026 conjecture.

## Rights

Citation-only; copyright 2004 John P. Robertson as printed in the article.
The mathematical definitions are paraphrased with attribution. Neither
the article nor its full extracted text is redistributed in this note.
No open redistribution license is asserted.

## Verified locator

- Archived source: https://web.archive.org/web/20160323033128id_/http://www.jpr2718.org/pell.pdf
- Original locator recorded by the archive: http://www.jpr2718.org/pell.pdf
- Article date: July 31, 2004; class definition and representatives: pages 12-14.
- Saved PDF SHA-256: `6c30f501521c62226759dfabde44d9bb0c5f61dd41c362ce9beaa66116ba2cb5`.
- Saved text SHA-256: `490d5bd86f77545bea4545944fe0f0788223a4ed5601ae30bbf5d6126b08f48b`.

The authoritative locator and PDF metadata come from the saved source
manifest. The supplied text uses literal [PAGE n] markers. The direct
original host failed DNS resolution in the bounded source search; the
archived URL supplied the article. Current availability is not asserted.
