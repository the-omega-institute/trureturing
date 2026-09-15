---
bibkey: "du2019gradient"
authors: "Simon S. Du; Xiyu Zhai; Barnabás Póczos; Aarti Singh"
year: 2019
title: "Gradient Descent Provably Optimizes Over-parameterized Neural Networks"
doi: null
claim: "Near-initialization weight bounds control empirical neural tangent Gram perturbations under random initialization and overparameterization assumptions."
strata_touched: []
license: "citation-only"
triage: "anchor"
url: "https://arxiv.org/abs/1810.02054"
---

# Gradient Descent Provably Optimizes Over-parameterized Neural Networks

## Verified locator

ICLR 2019; arXiv:1810.02054v2, first submitted in 2018. Lemma 3.2 bounds empirical neural tangent Gram perturbation for weights in a ball around Gaussian initialization. Its proof bounds sign-change events; it does not assert absence of every sign change. Lemma 3.4 supplies the stability bootstrap. Section 3.2 considers jointly training both layers under gradient flow; Theorem 4.1 treats discrete gradient descent in the main fixed-second-layer setup.

The displacement-versus-margin reasoning is relevant to deterministic gate certificates. These probabilistic convergence results do not supply the contextual-spacetime ML volume's finite rational, all-gate certificate or its exact masked block-Gram execution quotient. No random-initialization or convergence conclusion is transferred to that certificate.
