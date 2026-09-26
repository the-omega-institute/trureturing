---
bibkey: kretschmann2008continuity
authors: Dennis Kretschmann, Dirk Schlingemann, and Reinhard F. Werner
year: 2008
title: The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation
doi: 10.1109/TIT.2008.917696
url: https://arxiv.org/abs/quant-ph/0605009
claim: Channel closeness admits dimension-independent control through Stinespring dilations, relating retained information to environment disturbance.
strata_touched: []
license: citation-only
triage: anchor
---

# Channel continuity and discarded area sectors

## Primary source and scope

The primary arXiv record and Theorem 1 of the primary PDF identify the dimension-independent continuity theorem. The publication is IEEE Transactions on Information Theory 54 (2008), 1708-1717. On 2026-09-24 the displayed theorem on PDF page 6 was also inspected by screenshot. No long source quotation is reproduced here.

## Use in the RT volume

This supplies established background for comparing channel error and environment information. The current flat-sector result is section 34 of `docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md`; older references in this note to sections 39-41 were historical numbering and are not locators in the current main file. Section 34's original proof assumes exact pure basis-sector outputs, and obtains its sharp restricted optimum through explicit dilations and flat Schmidt spectra rather than through this general continuity theorem.

## 2026-09-24: stronger result has a different proof

The complete written supplement in the same PR is https://github.com/the-omega-institute/trureturing/pull/8890#issuecomment-5816839471 . It removes the exact-output assumption for the integer flat-rank family, and also treats arbitrary finite residual Schmidt spectra when each source sector contains the specified flat target factor. The unrestricted-output lower bound uses a projected-environment Ky Fan weak-majorization inequality and a reference-labelled ideal-output test. A simultaneous local Schmidt splitting attains the bound. It does not obtain the sharp constants by substituting an approximate-output hypothesis into the old exact-output proof or by applying a generic continuity estimate.

The full proof is currently a PR supplement, not an assertion that the main theory file has been extended beyond section 35. Local operations are independent and deterministic, without communication, postselection or extra shared entangled assistance. Shared classical randomness does not improve the supplement's optimum. Arbitrary nonflat target states, noninteger flat rank ratios, and physical CFT implementations are not classified by this result. No new Lean declaration, kernel validation or independent mathematical review is claimed.
