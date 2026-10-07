---
bibkey: dorflerbullo2013kron
authors: Florian Dörfler; Francesco Bullo
year: 2013
title: Kron Reduction of Graphs With Applications to Electrical Networks
doi: 10.1109/TCSI.2012.2215780
url: https://arxiv.org/abs/1102.2950
claim: Kron reduction is Schur complementation of the internal block of a weighted network Laplacian; it describes the static retained network under the stated invertibility assumptions.
strata_touched: []
license: citation-only
triage: anchor
---

# Static network reduction and dynamic boundary response

IEEE Transactions on Circuits and Systems I: Regular Papers 60(1), 150–163.
The arXiv preprint is *Kron Reduction of Graphs with Applications to Electrical
Networks*, arXiv:1102.2950; Crossref identifies the journal title, authors,
pages and DOI. The preprint's introductory network equations, Preliminaries and Notation,
and §2.1 (The Kron Reduction Process) define the retained matrix by the
Schur complement.

The FIB boundary geometry volume §§18 and 20 uses this static mechanism as
an intermediate. Its quadratic minimum also reuses the repository's
`SchurMinimum.schur_quadratic_is_least`. Neither static reduction nor the
paper's graph interpretation supplies an arbitrary-initial-state dynamic
prediction summary. The volume's three-node vector chain compares those
contracts explicitly: static Schur response zero, current output three real
components, complete linear initial-state prediction nine real components.
