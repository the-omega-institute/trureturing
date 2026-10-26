---
bibkey: shen2024freeenergy
authors: Zi-Song Shen; Feng Pan; Yao Wang; Yi-Ding Men; Wen-Biao Xu; Man-Hong Yung; Pan Zhang
year: 2024
title: Free-Energy Machine for Combinatorial Optimization
doi: 10.48550/arXiv.2412.09285
url: https://arxiv.org/abs/2412.09285v1
claim: Product-distribution variational free energy for Max-SAT is an explicit sum of clause violation products and one-variable negative entropies.
strata_touched: []
license: citation-only
triage: anchor
---

# Explicit clause mean-field free energy

The primary text is [arXiv:2412.09285v1](https://arxiv.org/pdf/2412.09285v1).
Methods, PDF p. 11, equation (11), gives the Max-SAT variational
mean-field free energy. Supplementary PDF p. 16, equations (S13)–(S17),
derive the expected clause violation product under an independent
proposal. The entropy term is the sum of single-variable entropies.
The same Methods page describes gradient-based updates and annealing;
this supplies no uniform global progress theorem for all SAT inputs.

[Finite transducers, Sections 12–13](../../docs/develop/theory/PREDICTIVE_THERMODYNAMIC_FINITE_TRANSDUCERS.md#12-a-product-proposal-and-an-explicit-missing-correlation-example)
use the same standard product objective with the repository's raw
penalty $E_F=(n+1)v_F$ and inverse temperature $\ln2$. Equivalently,
multiply the source's unit-penalty objective at inverse temperature
$(n+1)\ln2$ by $n+1$. A literal's violation factor is the source's
$1-P_i(W_{mi})$, expressed by a factor $\theta_i$ or $1-\theta_i$.
The repository separately handles repeated literals, tautologies and
empty raw clauses before forming these products.

The formula for the product objective is a literature input. The
repository derives the decision gap, the clause-normalized disjoint
parity example with a strict nonglobal minimum, and its conditional
finite-precision SAT consequence. A fixed objective being easy to
evaluate does not supply an efficient global optimizer; numerical
benchmark performance does not discharge that uniform algorithmic
condition. The parity-correlated construction applies to its explicitly
decomposed family and is not asserted as a solver for arbitrary clauses.
