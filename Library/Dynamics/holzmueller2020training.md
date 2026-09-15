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

## Relation to passive identification

Section 41 of `docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md` studies a different question: recovering the external Gram state of a two-layer real linear learner from one passive trajectory on the fixed data `X=I, Y=0`. The derivation reuses the existing exact Gram recurrences. It classifies the remaining state directions after two steps by a graph in the initial singular-vector coordinates, and gives an observable third-step criterion that removes the last direction in the connected case. It also accounts for errors in the propagation matrices reconstructed from noisy output data.

The passive-identification statements in section 41 are derived in this repository and are not attributed to Holzmüller and Steinwart.

For the distinction between continuous gradient flow and finite learning steps, primary background includes Kunin et al., *Neural Mechanics: Symmetry and Broken Conservation Laws in Deep Learning Dynamics*, arXiv:2012.04728v2, and Barrett and Dherin, *Implicit Gradient Regularization*, arXiv:2009.11162v3. Their abstract-level claims cover broken conservation laws and backward error analysis; they are not cited as proofs of the new three-step criterion. Lindsey and Menon, *Regularization implies balancedness in the Deep Linear Network*, arXiv:2511.01137v2, provides related geometric context with an explicit full-rank setting. No transfer to all degenerate strata is inferred from that setting.
