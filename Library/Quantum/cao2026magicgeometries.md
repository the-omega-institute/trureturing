---
bibkey: cao2026magicgeometries
authors: ChunJun Cao, Gong Cheng, Krishnanand Karthikeyan, Cathy Li, and John Preskill
year: 2026
title: State-dependent geometries from magic-enriched quantum codes
doi: null
url: https://arxiv.org/html/2603.13475v2
claim: Approximate subsystem complementary-recovery codes can exhibit state-dependent proto-area responses; the paper excludes general subalgebra codes from its no-go scope.
strata_touched: []
license: citation-only
triage: anchor
---

# State-dependent geometries from magic-enriched quantum codes

## Verified source

arXiv:2603.13475v2, 27 June 2026, preprint. Primary HTML introduction, footnote 1, and discussion were inspected. Footnote 1 explicitly limits the work to subsystem erasure correction and permits nontrivial area operators in exact subalgebra codes.

## Use and boundary

Comparison source for the distinction between a fixed entangled resource, input-dependent proto-area, and nontrivial center area operators. The arithmetic RT two-sector code uses an exact subalgebra setting; it is not a counterexample to the paper's restricted subsystem statement. Proto-area is not established there as the area of a particular backreacted surface. No claim that a finite two-sector dissipative model proves physical gravity.
## 2026-09-24: nonflat spectra and operational rather than entropic matching

Rechecked the arXiv version history and primary v2 text, including the restriction to flat auxiliary spectra preceding Theorem 4.1 and the separate nonflat discussion in section 4.3. The paper does not omit nonflat spectra. Its recovery-based proto-area and perturbative response are different optimization targets from the flagged two-party coarse-graining problem in PR #8890.

The full written spectral supplement is https://github.com/the-omega-institute/trureturing/pull/8890#issuecomment-5816839471 . For a flagged source with a flat target factor tensor an arbitrary finite residual Schmidt spectrum in each sector, it proves the unrestricted-output local-channel optimum 2[1-min_p p^T K p], where K is the Gram matrix of the sorted square-root residual spectra. The proof handles imperfect basis-sector outputs, but still assumes the stated factor structure and excludes communication or extra shared entanglement.

The equal-entropy residual spectra (1/2,1/8,1/8,1/8,1/8) and (1/4,1/4,1/4,1/4,0) give a positive exact coarse-graining error despite a scalar loss-entropy operator. This shows why a scalar area comparison alone is insufficient to certify that particular coherent channel task; it is not a contradiction of the source's proto-area formula, a proof about its general skewed codes, or a gravitational RT counterexample. In particular, a center-labelled exact subalgebra model is not silently identified with an exact subsystem complementary-recovery model.

The result is a same-PR written supplement, not yet a new section in the main RT file. No Lean declaration, Scribe proof claim, independently reviewed novelty claim, or physical gravity closure has been added by this comparison.
