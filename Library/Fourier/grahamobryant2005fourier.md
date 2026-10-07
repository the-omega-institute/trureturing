---
bibkey: grahamobryant2005fourier
authors: Ron Graham; Kevin O'Bryant
year: 2005
title: "A discrete Fourier kernel and Fraenkel's tiling conjecture"
doi: 10.4064/aa118-3-4
url: https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf
claim: "Conjecture 5.2 asserts that distinct positive units modulo q>(7/4)^n, with sum at most q and every complete inverse-sine row at least 2/sin(pi/q), force q=2^n-1 and the ordinary power-of-two residue set."
strata_touched:
  - D5/S3/Arith/GrahamObryantInverseSineRefutation
license: citation-only
triage: anchor
---

# The inverse-sine classification in Conjecture 5.2

The article appears in Acta Arithmetica 118.3 (2005), pages 283–304.
Conjecture 5.2 is on printed page 302, PDF page 20. Its literal conclusion
contains both the modulus equality and equality of the ordinary residue sets.
The set on the right comprises all n powers of two, from 1 to 2^(n-1).

The introductory inverse convention on printed page 283 makes the barred
quantity the multiplicative inverse modulo q. The conjecture sums over every
i from 1 to n, including i=k. The threshold (7/4)^n is a real rational power.
There is no primality assumption, independent-sign equivalence, or omitted
diagonal in this statement. Absolute sine makes the choice of integer
representative of a modular inverse immaterial.

For n>=3, replacing the last power 2^(n-1) by its negative residue's positive
lift 2^(n-1)-1 yields the counterfamily described by the associated result.
That refutation is a repository derivation, not a theorem asserted by this
article. The article's Conjecture 5.1 concerns a different complex-exponential
covering criterion. Its main Fraenkel conjecture assumes a Beatty covering;
the inverse-sine counterfamily supplies no such covering.

## Locator

- DOI: 10.4064/aa118-3-4, Conjecture 5.2, printed page 302/PDF page 20.
- Primary author journal PDF: https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf.
- Original author version: https://arxiv.org/abs/math/0407306v2, Conjecture 5.2.
- Author TeX: `Fraenkel.tex`, label `cnj:StrongMartin`; inverse convention in
  the introduction.
- The journal discussion immediately after Conjecture 5.2 describes its
  proposed use in bounding counterexamples to Fraenkel's conjecture. The
  failure of the residue-set assertion does not refute Fraenkel's conjecture.
