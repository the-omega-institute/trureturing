---
bibkey: liu2014hausdorff
authors: Jian-Guo Liu; Robert L. Pego
year: 2014
title: "On generating functions of Hausdorff moment sequences"
doi: null
url: https://arxiv.org/abs/1401.8052v4
claim: "The introductory Hausdorff characterization identifies completely monotone sequences with moments of finite positive measures on [0,1]."
strata_touched: []
license: citation-only
triage: anchor
---

# Compact moment data and retention estimation

Source: https://arxiv.org/abs/1401.8052v4, §1, equation (1) and the
paragraph beginning “A classical theorem of Hausdorff”. The version is
v4, including its corrigendum. The consumed statement is the classical
introductory characterization, not the paper's Pick-function theorem,
Lemma 3 or its corrected proof.

For a finite positive Borel measure on $[0,1]$, the moment sequence obeys
$\sum_{j=0}^k(-1)^j\binom kj c_{n+j}\ge0$ for all $n,k\ge0$;
conversely these inequalities characterize such sequences. The
normalization $c_0=1$ makes the measure a probability measure.

[LocalClock, §十四, 定理26](../../docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)
uses this moment interpretation for the retained-parameter channel
experiment. Its finite-horizon construction and five-mode fibre are
additional project data. Compact-support uniqueness of the entire
moment sequence is used there through polynomial density; a finite
prefix does not supply that uniqueness. No physical sampling mechanism
or extra success-readout instrument is supplied by this reference.
