---
bibkey: watrous2009completelybounded
authors: John Watrous
year: 2009
title: Semidefinite Programs for Completely Bounded Norms
doi: 10.4086/toc.2009.v005a011
url: https://theoryofcomputing.org/articles/v005a011/
claim: Completely bounded trace norms quantify quantum-channel differences with arbitrary ancillary systems and admit semidefinite formulations.
strata_touched: []
license: citation-only
triage: anchor
---

# Completely bounded channel distances

## Verified source

Theory of Computing 5 (2009), 217-238. Primary PDF: https://theoryofcomputing.org/articles/v005a011/v005a011.pdf . Section 2 defines the completely bounded trace norm; Section 4 treats differences of channels. The PDF text was inspected; one screenshot request failed, and no screenshot-only claim is made.

## Use and boundary

The RT forecast deficiency uses the unhalved diamond norm and includes arbitrary passive reference systems. The exact rank-one norm calculation and the optimization over present-region predictors are proved separately in the current theory. They are not inferred from random-state tests or from solving one numerical semidefinite program.

## Search log

2026-09-20: verified primary publication metadata and norm conventions. This source is distinct from the existing Watrous 2018 invariant-state note and is not used to replace its scope.

## 2026-09-24: spectral coarse graining and reference bookkeeping

Full written result: https://github.com/the-omega-institute/trureturing/pull/8890#issuecomment-5816839471 . The existing RT theory owner remains `docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md`; the supplement has not been represented as an already-written main-volume section or a Lean declaration.

For sorted residual square-root spectra v_s, let K_st=v_s dot v_t. The supplement first bounds every independent local CPTP pair using the reference-labelled input sum_s sqrt(p_s)|s>_R|s>_L. The ideal-output projector succeeds with probability at most p^T K p, even when the local maps produce erroneous or wrong-sector basis outputs. This is a common test for all competing maps, not a restriction to the exact-output subclass.

The attaining product map induces a Schur channel. For an arbitrary pure reference input its output-difference spectrum is that of D_sqrt(p)(11^T-K)D_sqrt(p), a trace-zero rank-one-positive-minus-positive-semidefinite matrix. Positivity of every entry of 11^T-K reduces the norm maximization to a probability-simplex quadratic problem. The resulting exact error is 2[1-min_p p^T K p]. This convex quadratic problem is distinct from an SDP optimization over all physical product channels; no such numerical exhaustive search was run.

The upper-bound calculation shows that the optimal Schur candidate has no passive-reference advantage in attaining its own diamond norm. It does not justify removing the reference from the universal lower-bound test for arbitrary competing channels. The explicit distinction matters once basis-sector outputs are allowed to be incorrect. The norm convention and channel-discrimination framework are established source material; the special projected-environment lemma and minimax proof are the separately written finite-model result, without a global priority claim.
