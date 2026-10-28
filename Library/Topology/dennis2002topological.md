---
bibkey: dennis2002topological
authors: Eric Dennis, Alexei Kitaev, Andrew Landahl, John Preskill
year: 2002
title: Topological quantum memory
doi: 10.1063/1.1499754
url: https://arxiv.org/abs/quant-ph/0110143
claim: Toric-code distance is the length of the shortest homologically nontrivial cycle on the lattice or dual lattice; on a square L by L torus this distance is L.
strata_touched:
  - D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance
license: citation-only
triage: anchor
---

# Toric distance and rectangular binary cohomology sectors

Dennis, Kitaev, Landahl and Preskill, *Journal of Mathematical Physics*
43 (2002), 4452--4505, identify the distance of a toric code with the
number of links in the shortest homologically nontrivial lattice or dual
lattice cycle. The paragraph defining stabilizer-code distance explicitly
gives distance L on an L by L square torus. This is the mature geometric
framework for relating support size to topological obstruction.

The repository theorem is a classical binary statement on the existing
rectangular labeled periodic-cell model. For every flat input and every
prescribed pair of holonomies, it proves an attaining label and a lower
bound for all labels in the target sector. Its minimum is M times the
indicator of changing row holonomy plus N times the indicator of changing
column holonomy. The horizontal lower bound selects a distinct disagreement
in each of the M rows; the vertical bound selects one in each of the N
columns. Keeping the anchored potential and changing only seams attains
both bounds simultaneously. This argument does not require a quantum
realization or a decoding algorithm.

The rectangular point-to-sector formula is a repository-derived extension
of the existing grid classification, within classical toric and cellular
cohomology mathematics. No research-originality claim is made. The cited
paper's square-distance paragraph is not attributed the full rectangular
all-sector telescope. Dimensions one and two use labeled edge coordinates;
the simple-graph interpretation applies when both dimensions are at least
three.

## Related Lean formalization

Stavan Jain's Apache-2.0 QECLean repository at revision
`9dced20836a1e868d20a4cad109e56bdf0ccdaf2` contains
`Quantum.StabilizerGroup.ToricCodeN.toricCodeN_distance_eq_L` in
`QEC/Stabilizer/Codes/Toric/Distance.lean`. It states
`HasCodeDistance (toricStabilizerCode L) L` under `Fact (2 ≤ L)`.
Its `nontrivial_z_logical_weight_ge_L` in `DistanceZ.lean` lower-bounds
the Pauli weight of every nontrivial Z-type logical operator by L.
These are square-size results, with one size parameter L. They do not
state the minimum from each flat rectangular label to each specified
holonomy pair.

That revision pins Lean v4.30.0-rc2 and Mathlib
`a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`. The repository theorem uses
its own existing carriers and pinned Mathlib Hamming and finite-cardinality
APIs. No QECLean source or proof term is copied or imported. QECLean is
acknowledged as a related formalization, not as a checked dependency.

## Sources

- Primary paper: https://arxiv.org/abs/quant-ph/0110143
- Primary TeX source: https://arxiv.org/src/quant-ph/0110143
- Related Lean source: https://github.com/Stavan-Jain/QECLean/blob/9dced20836a1e868d20a4cad109e56bdf0ccdaf2/QEC/Stabilizer/Codes/Toric/Distance.lean
- Related support bound: https://github.com/Stavan-Jain/QECLean/blob/9dced20836a1e868d20a4cad109e56bdf0ccdaf2/QEC/Stabilizer/Codes/Toric/DistanceZ.lean
