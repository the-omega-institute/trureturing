---
bibkey: "holzmueller2020training"
authors: "David Holzmüller; Ingo Steinwart"
year: 2020
title: "Training Two-Layer ReLU Networks with Gradient Descent is Inconsistent"
doi: null
claim: "A fixed-activation surrogate has exact grouped second-moment gradient-descent recurrences; a displacement condition identifies its predictions and gradients with the original network."
strata_touched: []
license: "citation-only"
triage: "anchor"
url: "https://arxiv.org/abs/2002.04861"
---

# Training Two-Layer ReLU Networks with Gradient Descent is Inconsistent

## Verified locator

arXiv:2002.04861v3, first submitted in 2020, version 3 in 2022. Appendix B, Definition B.1, fixes the initial activation pattern in a modified loss. Lemma B.2 gives an open parameter region defined by displacement and bias inequalities where original and surrogate predictions, losses and gradients agree on inputs bounded away from zero. Definition B.3 then defines gradient descent on the surrogate without assuming this agreement along future iterates.

Appendix C, Proposition C.2, proves the exact recurrence `Sigma_next = (I + h Q) Sigma (I + h Q)` for grouped second moments, including the discrete `h^2 Q Sigma Q` term. Remark C.3 distinguishes that term from gradient flow. Appendix D, Remark D.1, explicitly describes a closed system whose dimension is independent of hidden width. The setting has scalar inputs and outputs, (Leaky)ReLU, and biases.

This is a direct precedent for grouped Gram propagation, a fixed-activation surrogate, and width-independent reduced dynamics; those ideas are not new claims of the contextual-spacetime ML volume. The volume's stated scope is bias-free rational vector inputs and outputs, prescribed finite batches, and a deterministic finite-horizon initial-margin/product-drift certificate. The source's probabilistic inconsistency theorem is not a conclusion about that subclass, and these locators do not establish global originality of the certificate.
