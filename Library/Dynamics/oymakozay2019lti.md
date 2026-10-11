---
bibkey: oymakozay2019lti
authors: Samet Oymak; Necmiye Ozay
year: 2019
title: Non-asymptotic Identification of LTI Systems from a Single Trajectory
doi: null
url: https://arxiv.org/abs/1806.05722v2
claim: Exact block-Hankel factorization and Ho-Kalman realization separate algebraic state dimension from statistical identification under additional input, noise and conditioning hypotheses.
strata_touched: []
license: citation-only
triage: anchor
---

# Exact realization as an intermediate input

The primary text is [arXiv:1806.05722v2](https://arxiv.org/pdf/1806.05722v2).
Section 2, p. 2, specifies real discrete state-space matrices and its
zero-initial-state observation model. Section 5.1, pp. 7–8, uses the
observability/controllability factorization and Ho-Kalman construction.
Section 5.2, Theorem 5.3 and Corollary 5.4, p. 9, adds perturbation and
singular-value conditions. Exact minimal realization requires sufficient
block horizons and the reachable/observable rank; direct feedthrough is
separate from the state Hankel.

[The Static continuation, Theorems 29.4–29.6 and 29.8](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
consumes the algebraic factorization with continuous derivative parameters
$A=-K$, $G=B$, $C=B^{\mathsf T}$. The derivative moments are
$CA^kG=(-1)^k B^{\mathsf T}K^kB$, so the block Hankels differ by an
invertible diagonal sign congruence. The strictly proper zero-state task
forces the competing direct feedthrough to vanish. Competitors are real
finite-dimensional LTI systems and need not be symmetric.

This correspondence does not turn exact moments into samples or transfer
the paper's statistical bounds without its hypotheses. The original
Ho–Kalman article is historical attribution, not a separately checked
full-text source here. Only the inspected modern paper's specified
statements are used; no article text or figures are reproduced.
