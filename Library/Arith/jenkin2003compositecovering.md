---
bibkey: jenkin2003compositecovering
authors: "Scott Jenkin; Jamie Simpson"
year: 2003
title: "Composite covering systems of minimum cardinality"
doi: 10.5281/zenodo.7607541
url: https://zenodo.org/api/records/7607541/files/d13.pdf/content
claim: "Containing-divisor replacement and restriction to a prime branch preserve covering; the branch reduction explicitly permits repeated residual moduli."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Divisor replacement and prime-branch restriction

The inspected primary scan is *Integers* 3 (2003), A13, 11 pages,
published 24 September 2003. The DOI above identifies the Zenodo
archive record. The abstract and introduction define covering by
union equal to the integers; disjointness is not required. Page 1
explicitly notes that the moduli form a multiset and may repeat.

Lemma 1, page 3, replaces a class modulo m by its containing class
modulo any divisor mu>1. Lemma 2 on the same page compresses the
ordered support primes to the first primes, retaining exponent
patterns. The paper's canonical composite incongruent systems
therefore contain every composite divisor of every modulus. For
odd-only systems admitting prime moduli, the analogous admissible
divisor descent includes all divisors greater than one; this is an
application of the replacement argument, not the paper's literal
composite-only canonical definition.

Theorem 8, pages 7–8, partitions the p-divisible original classes by
their residue modulo p. Every resulting branch is covered by the
p-free moduli together with d/p for that branch's p-divisible labels.
Its proof uses the full reduction d/gcd(d,p), without flatness or
square-free hypotheses. It does not assert distinctness of the
resulting moduli or provide a covering choice among duplicate classes.

Theorem 3, page 3, cites Simpson's bound
n >= 1+sum_p H_p(p−1) for an irredundant whole cover with full period
product_p p^H_p. That bound is already retained in
[report 343](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md).
No source text or scan is vendored by this citation note.

[Report 350](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/350-extremal-paired-branch-and-source-support.md)
applies these reductions to a hypothetical distinct odd cover chosen
first by minimum cardinality, then by minimum modulus sum. It identifies
the literal parent-child residual collisions and their private-point
constraints. The source-support deductions there are separately proved;
they are not attributed as statements of this paper or as Lean results.
