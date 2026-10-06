---
bibkey: ting2026operational
authors: O. Ting; J. Fullwood; Z. Wu
year: 2026
title: "Operational time-reversal symmetry for unital qubit channels"
doi: 10.48550/arXiv.2605.10375
url: https://arxiv.org/abs/2605.10375v1
claim: "For a Pauli channel with precisely three non-zero weights, either the maximally mixed state is the only state with respect to which a Bayesian inverse exists, or such states form a measure-zero subset of the Bloch ball; the authors found no example away from the maximally mixed state."
strata_touched:
  - D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness
license: citation-only
triage: anchor
---

# Operational time-reversal symmetry for unital qubit channels

O. Ting, J. Fullwood and Z. Wu, arXiv:2605.10375v1 (2026-05-11), quant-ph; only v1
exists. Sections are numbered by the order of `\section` commands: Preliminaries is
Section II, the general Pauli-channel analysis is Section IV and the Concluding
Remarks are Section V.

The open alternative, verbatim (Section V):

> Interestingly, when the Pauli channel associated with a unital channel has precisely three non-zero entries in its probability vector, we were unable to find any examples of Bayesian inverses with respect to states which differ from the maximally mixed state. This is probably due to the fact that either the maximally mixed state is the only state for which a Bayesian inverse exists in such a case, or that such states are restricted to a measure-zero subset of the Bloch ball.

The definitions, verbatim (Section II):

> A quantum channel $\F:\mathcal{L}(\H_B)\to \mathcal{L}(\H_A)$ in the reverse direction as $\E$ is then said to be a \emph{Bayesain inverse} of $\E$ with respect to the initial state $\rho$ if and only if

> \big\{\mathcal{E}(\rho)\otimes \mathds{1},\mathscr{J}[\mathcal{F}]\big\}=\left\{\mathds{1}\otimes\rho\, ,\mathscr{J}[\mathcal{E}^\dagger]\right\} \, ,

> \J[\N]=(\id_A\otimes\, \N)({\tt SWAP})\, ,

> where ${\tt SWAP}=\sum_{i,j}\dyad{i}{j}\otimes \dyad{j}{i}$.

Here $\{\cdot,\cdot\}$ is the anticommutator and $\mathcal E^\dagger$ the
Hilbert–Schmidt adjoint. Section III proves that for exactly two non-zero weights a
Bayesian inverse exists if and only if the state is unscathed (lies on one coordinate
axis of the Bloch ball), and Section IV characterizes existence for general Pauli
channels by three inequalities on the Choi matrix of the unique candidate inverse,
without evaluating them for three non-zero weights.

## Verified locator

DOI: `10.48550/arXiv.2605.10375`. Canonical source URL: `https://arxiv.org/abs/2605.10375v1`.
The open alternative is the third paragraph of Section V; the Bayes rule
`eq:BA` and the Jamiołkowski map are in Section II.
