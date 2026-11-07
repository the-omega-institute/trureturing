---
bibkey: alloucheshallit1992regular
authors: Jean-Paul Allouche and Jeffrey Shallit
year: 1992
title: The Ring of k-Regular Sequences
doi: null
url: https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf
claim: "Theorem 2.6: if S is k-regular, then S(an+b) is k-regular for every a>=1 and b>=0."
strata_touched:
  - D5/S1/Recurrence/KRegularAffineSubsequence
license: citation-only
triage: anchor
---

## Verified locator

Source: https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf

The author-hosted preprint, PDF page 7, Theorem 2.6, states closure under
positive-step affine subsequences. PDF page 3, Definition 2.1 and its preceding
coefficient convention, use a commutative Noetherian coefficient ring and
identify regularity with finite generation of the module spanned by the k-kernel.
The formal statement uses the integer coefficient ring and integer-valued sequences.

The author's bibliography at https://cs.uwaterloo.ca/~shallit/papers.html
identifies the journal article as Theoretical Computer Science 98 (1992),
163–197, and states that the linked preprint differs slightly from the published
version. The theorem and page locators here refer to the inspected preprint;
the journal text is not asserted to have been inspected.

## Uniform kernel transport

For a finite generating family G of the original integer kernel module, the
proof uses the finite family of sequences n ↦ g(an+c), with g in G and
0≤c<a+b. If r<k^e, Euclidean division ar+b=c k^e+d gives d<k^e and c<a+b.
Consequently s(a(k^e n+r)+b)=s(k^e(an+c)+d), which is an integer linear
combination of those affine observations. The transported kernel span is a
submodule of a finitely generated integer module, so Noetherianity gives
finite generation. The formal theorem preserves arbitrary bases k≥2,
positive natural a, arbitrary natural b, and possibly infinite kernels and
unbounded integer values.
