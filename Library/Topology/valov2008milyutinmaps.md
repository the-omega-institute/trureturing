---
bibkey: valov2008milyutinmaps
authors: Vesko Valov
year: 2008
title: Probability measures and Milyutin maps between metric spaces
doi: null
url: https://arxiv.org/abs/0801.1721v2
claim: The proof of Lemma 2.2 invokes Michael's zero-dimensional selection theorem for nonempty closed lower semicontinuous fibers into a complete metrizable target.
strata_touched:
  - D5/S3/Topology/Selection
license: citation-only
triage: anchor
---

# Zero-dimensional selection and its scope

Valov's Lemma 2.2 concerns an open surjection between completely
metrizable spaces with zero-dimensional target. Its proof considers
Phi(y) = f^-1(y) intersect U, with U an open subspace of the domain.
The multifunction has nonempty closed fibers relative to U and is
lower semicontinuous. Since U admits a complete compatible metric,
the proof invokes Michael's zero-dimensional selection theorem to
obtain a continuous local section. The source credits E. Michael,
Selected selection theorems, American Mathematical Monthly 63 (1956),
233–238, in reference [11]. The original Michael article was not
inspected here, so no original theorem number is asserted.

The project module CompactZeroDimensional supplies the compact-domain
selection principle itself: the base is compact Hausdorff and totally
disconnected, with no metric or countability assumption, and the
target is an arbitrary complete metric space. Literal open hitting
sets, nonempty closed fibers, and no carrier Nonempty instances appear
in the theorem. A second theorem allows the selector to pass through
any prescribed point of a fiber. These classical statements are not
claimed as new mathematical results.

The proof reuses Mathlib's finite disjoint clopen refinement of an
open cover. It constructs successive locally constant approximations
with fiber error (1/2)^n and summable increments, takes a limit in the
complete uniform metric on bounded continuous functions, and uses
closed fibers for exact membership. Replacing one fiber by a singleton
proves the prescribed-point version; the corresponding lower
semicontinuity is proved explicitly.

Valov's metrizable open-map hypotheses are not silently promoted to
an arbitrary nonmetrizable compact domain. The project selection
theorem does not by itself construct a zero-dimensional open
resolution of an arbitrary compact Hausdorff open surjection. That
resolution and Peng's Questions 5.1/5.2 remain outside this result.

## Verified locator

Source page: https://arxiv.org/abs/0801.1721v2.
The inspected source is https://arxiv.org/pdf/0801.1721v2.
PDF SHA256: a0e85b826148a74883f5ebbc29fa0ae8656f07bbb4b6e3883d9b99a946bbffdf.
Extracted-text SHA256: f27f58557b7f1347e4429bbc778bd560a206c2da71d1fc97f919dd92d5eaddbf.
The page-labelled extracted text contains Lemma 2.2 and its selection
argument on PDF pages 5–6, with reference [11] on PDF page 12.
This note records the consulted source and the classical attribution;
it supplies no formal axiom or global novelty evidence.
