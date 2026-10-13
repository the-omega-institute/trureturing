---
bibkey: ting2026operational
authors: Ouyang Ting; James Fullwood; Zhen Wu
year: 2026
title: "Operational time-reversal symmetry for unital qubit channels"
doi: 10.48550/arXiv.2605.10375
url: https://arxiv.org/abs/2605.10375v1
claim: "Section V leaves the alternative that for precisely three nonzero Pauli weights only the maximally mixed state admits a Bayesian inverse, or that such states form a measure-zero subset of the Bloch ball."
strata_touched:
  - D5/S3/Quantum/Foundation/FiniteKrausRepresentation
license: citation-only
triage: anchor
---

# Operational time-reversal symmetry for unital qubit channels

Ouyang Ting, James Fullwood and Zhen Wu, arXiv:2605.10375v1, quant-ph.
The [primary abstract record](https://arxiv.org/abs/2605.10375) lists v1,
submitted 11 May 2026. The [v1 text](https://arxiv.org/html/2605.10375v1)
has Section II, Preliminaries; Section III, The unscathed condition for
Pauli channels; Section IV, Bayesian Inverses of General Pauli Channels;
and Section V, Concluding Remarks.

The open alternative, verbatim (Section V):

> Interestingly, when the Pauli channel associated with a unital channel has precisely three non-zero entries in its probability vector, we were unable to find any examples of Bayesian inverses with respect to states which differ from the maximally mixed state. This is probably due to the fact that either the maximally mixed state is the only state for which a Bayesian inverse exists in such a case, or that such states are restricted to a measure-zero subset of the Bloch ball.

The Bayesian-inverse definition, verbatim (Section II; the spelling is the
source's):

> A quantum channel $\mathcal F:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_A)$ in the reverse direction as $\mathcal E$ is then said to be a *Bayesain inverse* of $\mathcal E$ with respect to the initial state $\rho$ if and only if

\[
\{\mathcal E(\rho)\otimes I,\mathscr J[\mathcal F]\}
=\{I\otimes\rho,\mathscr J[\mathcal E^\dagger]\}.
\]

Here $\{U,V\}=UV+VU$, $\mathcal E^\dagger$ is the Hilbert–Schmidt adjoint,
and the paper uses
\[
\mathscr J[\mathcal N]=(\mathrm{id}\otimes\mathcal N)(\mathtt{SWAP}),
\qquad \mathtt{SWAP}=\sum_{i,j}E_{ij}\otimes E_{ji}.
\]
Quantum channels are complex-linear, completely positive and trace preserving.
The definition quantifies over arbitrary reverse channels. It does not require
the reverse channel to be Pauli, unital, or equal to the adjoint. The source's
separate full-rank uniqueness observation is not a premise of this definition.

## Scope of the cited results

Theorem 1 says that the particular channel $\mathcal P^\dagger=\mathcal P$
is a Bayesian inverse of a Pauli channel with respect to $\rho$ exactly when
$\rho$ is unscathed. Proposition 2 says, among other cases, that with at least
three nonzero weights the unscathed states consist only of $I/2$. Together
they exclude this **particular inverse** away from $I/2$. They do not exclude
all other CPTP reverse maps. Section IV treats general candidate inverses;
Section V still states the three-weight alternative quoted above.

The checked application covers every normalized nonnegative four-weight
vector with support of cardinality three, every PSD trace-one complex
$2\times2$ matrix, including pure states, and every CPTP complex-linear
reverse map under the literal anticommutator equation. It includes the
Hilbert–Schmidt self-adjointness identity for the Pauli channel. No invertibility
of the input state or of its individual Bloch coordinates is assumed.

The application exposition belongs to
[FiniteKrausRepresentation](../../Blueprint/D5/S3/Quantum/Foundation/FiniteKrausRepresentation.scribe.cs).
Its ingredients are the existing Pauli matrices and Kraus CP API, the
all-Hermitian representation and all-PSD Bloch bound from
`ActualPureQubitGeometry`, and the output-first, unnormalized Choi API in
`FiniteKrausRepresentation`. The latter is a selected source port of Physlib
revision `6a09b2d1761a0d4430083045a247eb121d8da260`, with no frozen-state
membership. The full exact application and its suppliers are kernel-checked;
the inspected axiom closures contain only `propext`, `Classical.choice` and
`Quot.sound`. The result selects the first alternative for Pauli channels:
a Bayesian inverse exists exactly at $I/2$. It is retained as application
exposition, without a new theorem declaration or published resolution. The
[problem dossier](../../Problems/ting-fullwood-wu-2026-three-weight-bayesian-inverse.md)
states the full polynomial argument and its verification boundary.

## Verified locator and bounded literature scope

Primary-source observation on 2026-10-13: the arXiv abstract record lists only
v1; the v1 HTML contains the Section II equation (1), Theorem 1, Proposition 2,
and the Section V alternative above. Its front matter also displays an internal
date of 24 August 2026; the submission-history date is the version locator.
DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375).

The bounded arXiv all-fields query
[`"Bayesian inverse" Pauli`](https://arxiv.org/search/?query=%22Bayesian+inverse%22+Pauli&searchtype=all&abstracts=show&order=-announced_date_first&size=50)
returned two records: this paper and Song–Parzygnat,
[arXiv:2507.14278](https://arxiv.org/abs/2507.14278), *Bipartite quantum states
admitting a causal explanation*. The latter's abstract discusses temporal
compatibility and Bayesian inverses; it does not state a three-weight Pauli
settlement. Its full text was not assessed in this bounded check. The exact-title
query [`"Operational time-reversal symmetry"`](https://arxiv.org/search/?query=%22Operational+time-reversal+symmetry%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50)
returned this paper alone. No separate settlement was identified in these
records and the checked v1 text. This is a result about the stated search scope,
not an exhaustive novelty or priority claim.
