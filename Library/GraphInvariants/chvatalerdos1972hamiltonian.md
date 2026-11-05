---
bibkey: chvatalerdos1972hamiltonian
authors: Václav Chvátal and Paul Erdős
year: 1972
title: "A note on Hamiltonian circuits"
doi: 10.1016/0012-365x(72)90079-9
url: https://users.renyi.hu/~p_erdos/1972-02.pdf
claim: "Theorem 3: an s-connected graph with no independent set of s vertices is Hamiltonian-connected."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/HamiltonConnected
license: citation-only
triage: anchor
---

# The Chvátal-Erdős Hamilton-connectedness criterion

Václav Chvátal and Paul Erdős, *A note on Hamiltonian circuits*,
Discrete Mathematics **2** (1972), 111–113, Theorem 3, pp. 112–113.
The theorem asserts that an s-connected graph containing no independent set
of s vertices admits a Hamiltonian path between every pair of vertices.
This is a literature-attested theorem, with no novelty or open-problem claim.

The native receiver theorem quantifies over every finite type in any universe,
every simple graph and every natural k. Its connectivity premise says that
deleting any vertex set of cardinality strictly less than k leaves a connected
induced graph. Its independence premise gives the same strict bound for every
independent set. Its conclusion quantifies over every prescribed pair of
distinct endpoints. Classical finite enumeration and equality decisions are
internal to the proof. There is no order lower bound or extra restriction on k.

The proof follows the paper's fixed-endpoint argument. Choose a longest simple
path P between the prescribed endpoints a and b. For an outside vertex x, the
native Menger fan theorem supplies min(k, |P.support|) terminal-clean arms.
The obstruction is proved for that same P and fan without either global
hypothesis: the arms cannot cover all path vertices, and x together with the
successors of the terminals other than b contains an independent set of size
at least the number of arms. One-cut replacement handles consecutive terminals
and edges from x to a successor; two-cut replacement handles edges between
successors. Both replacements preserve the original endpoints and gain length.
The vertex count of P is P.length + 1.

The existing Menger and arbitrary-terminal fan sources are prior receiver
building blocks, adapted from Juan Pablo Traverso Gianini's Apache-2.0 source
at 35c5f684f9bfbd244bd0999ce725623ab571adb6. Their attribution and full license
remain in their owning modules and
`docs/reports/licenses/menger-hamiltonian-LICENSE.txt`. They are not a donor
Hamilton-connectedness proof. The new endpoint-preserving argument uses native
walks and the receiver's ordered two-cut slicing theorem.
