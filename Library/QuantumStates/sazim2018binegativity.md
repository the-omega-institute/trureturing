---
bibkey: sazim2018binegativity
authors: Sk Sazim; Natasha Awasthi
year: 2018
title: "Binegativity of two qubits under noise"
doi: 10.1016/j.physleta.2018.04.056
url: https://arxiv.org/abs/1711.03717v2
claim: "The introduction restates the conjecture that binegativity is monotone under LOCC and PPT channels; the paper computes its behavior under selected noise channels."
strata_touched:
  - D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation
license: citation-only
triage: anchor
---

# Binegativity of two qubits under noise

Sk Sazim and Natasha Awasthi, *Physics Letters A* 382 (2018), 1852–1857.

The introduction of arXiv:1711.03717v2, p. 1, states:

> On the basis of numerical evidence, it is conjectured that the binegativity behaves monotonically under both LOCC and PPT channels [15].

The abstract, p. 1, states:

> Our study supports the conjecture that the binegativity is a monotone.

Reference [15] is Mark W. Girard and Gilad Gour, *The binegativity of two qubits*,
arXiv:1701.02724v3. Its introduction, p. 1, states:

> That is, we conjecture that for any two-qubit state $\sigma$ it holds that $N_2(\mathcal{E}(\sigma))\leq N_2(\sigma)$ for any LOCC (or PPT) channel $\mathcal{E}$ that outputs states of two qubits.

The Lean encoding uses two-qubit density matrices and finite one-way LOCC
channels. Alice applies a complete instrument and communicates her outcome to
Bob, who applies a complete channel conditional on that outcome. Forgetting the
outcomes gives the double product-Kraus sum. This class is contained in LOCC.
The binegativity uses the partial transpose on Bob and the negative parts of
self-adjoint matrices, as in Girard and Gour.

## Verified locator

- DOI: https://doi.org/10.1016/j.physleta.2018.04.056
- URL: https://arxiv.org/abs/1711.03717v2
- Restatement: arXiv v2, p. 1, introduction; source `binegativity.tex`,
  lines 109–111. Abstract support sentence: p. 1, source line 52.
- Original conjecture: https://arxiv.org/abs/1701.02724v3, p. 1,
  introduction; source `binegativity_v9.tex`, lines 192–196.
