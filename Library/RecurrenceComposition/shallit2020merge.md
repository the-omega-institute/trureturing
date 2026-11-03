---
bibkey: shallit2020merge
authors: Jeffrey Shallit
year: 2020
title: Corrected proof of Theorem 2.7 in Allouche and Shallit (1992)
doi: null
url: https://cs.uwaterloo.ca/~shallit/Papers/merge.pdf
claim: "Theorem 1: for every k>=2 and a>=1, if every residue stream f(an+i), 0<=i<a, is k-regular, then f is k-regular, with arbitrary gcd(a,k)."
strata_touched:
  - D5/S1/Recurrence/KRegularInterleaving
license: citation-only
triage: anchor
---

## Verified locator

Source: https://cs.uwaterloo.ca/~shallit/Papers/merge.pdf

The author-hosted note, version February 23, 2020, states the merge theorem as
Theorem 1 on PDF page 1. Its first proof, on PDF pages 1–2, treats arbitrary
gcd(a,k) through masked insertion, bounded gcd classes, and affine samples.
The author's bibliography at https://cs.uwaterloo.ca/~shallit/papers.html
identifies this note as supplying corrected proofs of Theorem 2.7: the
construction in the original proof only covers coprime a and k.

The affine-subsequence theorem used here is documented in
[alloucheshallit1992regular](alloucheshallit1992regular.md). The formal result
uses the native integer-valued sequence space and integer kernel span.

## Finite-control interpretation

For each attained g=gcd(k^e,a), take its first realizing exponent t_g, so
t_g<=e whenever e attains g. With u_g=k^(t_g)/g and N_g=a/g, the entire masked
kernel is contained in one finite sum of insertion-map images of the kernel
spans of f_i(u_g n+d), for d<u_g and insertion residues r<N_g. This finite sum
is independent of the exponent of a kernel member.

When the mask is active at some index, the least nonnegative representative r
of its active residue class satisfies
Kr+c=am_0+i and m_0<K/g. The division m_0=u_g q+d gives d<u_g and
q<k^(e-t_g). This last inequality is the strict bound required for membership
in the full k-kernel. The printed inequality q<m_0/u_g is not used.

This is a citation to a known theorem. No paper redistribution or source-code
port licence is established, and the transducer argument in the note is not
part of this formal result.
