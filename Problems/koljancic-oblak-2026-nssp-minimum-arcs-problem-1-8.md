---
slug: koljancic-oblak-2026-nssp-minimum-arcs-problem-1-8
bibkey: koljancicoblak2026nssp
doi: 10.13001/ela.2026.10523
url: https://arxiv.org/abs/2604.21552v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result
---

# The minimum number of arcs requiring nSSP

Sara Koljančić and Polona Oblak, *Combinatorial aspects of the nonsymmetric
strong spectral property for graphs*, Problem 1.8, printed page 759:

> Is the minimum number of arcs in a directed graph G on n vertices that requires the nSSP equal to 2n−1?

The source and preregistration are linked from
[issue #25108](https://github.com/the-omega-institute/trureturing/issues/25108).
The [Library note](../Library/GraphInvariants/koljancicoblak2026nssp.md)
records source versions, attribution and licensing. The endpoint-looped double
path is the source's Theorem 5.5 and Remark 2.10(1), not a new upper construction.

| Source clause | Exact Lean meaning |
| --- | --- |
| n vertices | Fin n, for every natural n with 1 ≤ n |
| Directed graph, loops allowed | Finset (Fin n × Fin n); each ordered pair appears at most once |
| Exact matrix support | A i j ≠ 0 if and only if (i,j) belongs to E |
| nSSP | Every real X with A i j * X i j = 0 and A * X.transpose − X.transpose * A = 0 is zero |
| Requires nSSP | Every real A of that exact support has nSSP |
| Minimum equals 2n−1 | All requiring E have at least 2n−1 arcs, and at the same n some requiring E has exactly 2n−1 arcs |

These definitions occur in
`D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs`.
`MinimumArcs` is the entire two-clause assertion; `result` states it directly.
There is no additional identity-Hadamard, trace, sign, connectivity, symmetry,
eigenvalue, genericity or finite-order restriction in that assertion.

The lower-bound argument embeds an n-dimensional real space in the centralizer,
using the classical polynomial-module structure theorem. The support readout
F ↦ (A_ij F_ji) is injective by nSSP and lies in the directed incidence kernel.
A requiring support must be connected: a component without a loop gives a
diagonal obstruction, and two looped parts can be weighted to share eigenvalue
one, giving an off-block outer-product obstruction. Connected incidence has
rank at least n−1, so the arc count is at least 2n−1. The source's endpoint
path supplies equality for all arbitrary nonzero real weights.

The bounded literature qualification in #25108 does not establish exhaustive
nonresolution or priority outside its inspected sources. Public-theorem escape
registration is attempted in the mirrored Reg source. Any unfinished binding
evidence is an unresolved audit obligation under #25108; registration source
alone is not `declared_validated`.
