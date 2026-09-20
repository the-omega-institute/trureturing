---
bibkey: harrington2021oddcovering
authors: "Joshua Harrington; Yewen Sun; Tony W. H. Wong"
year: 2021
title: "Covering systems with odd moduli"
doi: 10.1016/j.disc.2022.112936
url: https://arxiv.org/abs/2104.00602v1
claim: "A square-free odd cover with only one prime modulus repeated twice yields a distinct odd cover; a fresh prime can replace the first digit of a repeated-prime root while retaining all other prime-power coordinates."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Covering systems with one repeated prime modulus

The inspected primary text is [arXiv:2104.00602v1](https://arxiv.org/pdf/2104.00602v1),
submitted 1 April 2021, with manuscript title page dated 2 April 2021.
The journal version is *Discrete Mathematics* (August 2022),
[DOI 10.1016/j.disc.2022.112936](https://doi.org/10.1016/j.disc.2022.112936).
Theorem numbering below follows the inspected arXiv version. Crossref
metadata confirms the journal attribution; its full text is not compared here.

Theorem 3.2, pages 7–8, states that a finite covering system with odd,
square-free moduli, all distinct except for an odd prime used exactly twice,
implies the existence of a finite cover with distinct odd moduli greater
than one. The construction keeps prime-free cofactors while replacing
the repeated-prime root by finitely many power levels and new-prime
closing classes. It does not provide an input satisfying its premise.

Lemma 5.4, pages 16–17, starts with a covering whose moduli are distinct
except for a prime p used p−t times, where 1 <= t <= p. If an odd prime
q >= t divides none of the input moduli, it constructs a covering whose
only repeated modulus is q, used q−t times. Oddness is preserved. For an
original modulus p^alpha r, with alpha >= 1 and p not dividing r, the
transformed modulus is q p^(alpha−1) r. This lemma allows arbitrary
prime-power heights; it replaces only the first p digit. Freshness is an
explicit hypothesis, not a consequence of q >= t.

The source also reports t_3 <= 2 and t_5 <= 3 from earlier work, and proves
t_7 <= 4, t_11 <= 7 and t_p <= p−5 for primes p >= 23. These multiplicity
bounds alone do not give a fresh prime of a specified size or certify
the square-free premise of Theorem 3.2.

[Report 348](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md)
spells out the literal residue transport, the construction's weaker
prime-flat sufficient premise, and selection of fewer root branches.
Those extensions are ordinary deductions from the displayed construction,
not the literal statements of the source theorems or new Lean results.
No source text or diagrams are vendored by this citation note.

[Report 349](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/349-real-odd-cover-private-cylinders-and-transport-obstruction.md)
reconstructs Theorem 4.2, Figures 18–22, with auxiliary closing prime 23.
The complete power ranges are 1 through 22. A parameterized family
represents 19,329,428 actual classes, with only modulus 11 repeated
seven times. Coverage follows from the complete finite tree and its
leaf-cylinder containments, not from sampled points. The report finds
private regions of the literal classes 1 mod3 and 1 mod5, then uses
them to rule out a specified one-child-per-modulus digit-memory
transport of this source. These obstruction deductions are not stated
as HSW's results or as unrestricted odd-cover nonexistence.
