---
bibkey: grimsley2019adaptive
authors: Harper R. Grimsley, Sophia E. Economou, Edwin Barnes and Nicholas J. Mayhall
year: 2019
title: An adaptive variational algorithm for exact molecular simulations on a quantum computer
doi: 10.1038/s41467-019-10988-2
url: https://arxiv.org/abs/1812.11173
claim: ADAPT-VQE grows an ordered variational ansatz from an operator pool using measured energy-response gradients and reoptimizes the resulting parameters.
strata_touched: []
license: citation-only
triage: anchor
---

# An adaptive variational algorithm for exact molecular simulations on a quantum computer

## Primary source

Nature Communications 10, 3007 (2019), DOI as above; author preprint arXiv:1812.11173.
The preprint's numbered ADAPT-VQE procedure computes the energy gradient for the pool,
selects the operator with the largest gradient, appends it, and optimizes the variational parameters.
The following discussion describes gradient measurement by commutator observables.

## Use and limits

This is the existing precedent for separating discrete operator-sequence growth from continuous parameter optimization.
The five-mode application in [Symplectic Predictive Completion §37](../../docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md)
uses a different native control menu and tests an independent real tangent direction explicitly.
The paper's molecular task does not supply a native FIB compiler, a predictive summary of an optimizer,
a uniform polynomial stopping guarantee or a general SAT solver.
An operator with nonzero response is a task-dependent selection signal; it need not provide a globally useful new direction.
