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

The version-specific source for affine source redistribution is
[arXiv:1102.2950v1](https://arxiv.org/pdf/1102.2950v1), equations (1.1)–(1.2),
(2.1)–(2.2), and Lemma 2.1(1),(3). The accompanying matrix is nonnegative;
for a loopless Laplacian it is column stochastic. The lemma assumes a
symmetric irreducible loopy Laplacian and at least two retained vertices.
The singleton-boundary and disconnected-internal-block cases in
[the static-seam continuation, Definition 24.1 and Theorem 24.3](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
use their stated grounding condition and direct finite matrices, not a claim
that these cases literally satisfy every hypothesis of the paper's lemma.
The source sign in that application is fixed by the term $+q^{\mathsf T}u$.
The quadratic minimum's source-dependent constant, energy calibration and
source-identification conditions are additional data; the accompanying
matrix alone does not identify an internal source or its joint energy.
