---
slug: alikhani-ghanbari-dehghanizadeh-conjecture-3-9-elliptic-sombor
bibkey: alikhanighanbaridehghanizadeh2024ellipticsombor
doi: 10.48550/arXiv.2404.18622
url: https://arxiv.org/abs/2404.18622v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result
---

# Two four-cycles sharing a vertex refute elliptic Sombor Conjecture 3.9

## Problem

Alikhani, Ghanbari and Dehghanizadeh, *Elliptic Sombor energy of a graph*,
arXiv:2404.18622v1, Conjecture 3.9, states:

> There is no graph with integer-valued elliptic Sombor energy.

For a simple graph, the elliptic Sombor matrix has entry
`(d_i + d_j) sqrt(d_i^2 + d_j^2)` on an adjacent pair and zero otherwise;
the elliptic Sombor energy is the sum of the absolute values of its eigenvalues.

## Motivation

The conjecture is a universal nonintegrality assertion. Two copies of the
four-cycle sharing one vertex give a seven-vertex simple connected bipartite
graph with hub degree four and all other degrees two. Its elliptic Sombor
matrix has spectrum `{-56, -16, 0, 0, 0, 16, 56}`, so its energy is `144`.

## Gap

The source conjecture quantifies over every finite simple graph. A refutation
requires one literal graph, its literal degree-weighted matrix and a certified
integer spectral energy. The source does not settle whether integer-energy
graphs must be bipartite or classify the remaining graphs.

## Route

`ellipticSomborMatrix` is the source matrix on `Fin n`. `claim` is the literal
universal nonintegrality statement, with Mathlib's Hermitian eigenvalue
indexing. `result : ¬ claim` constructs the two-cycle bouquet, computes its
matrix, diagonalizes it by an explicit invertible change of basis, identifies
the characteristic roots and sums their absolute values to `144`.

## Falsifier

The refutation would fail if the bouquet were not a simple graph, if any edge
weight or degree were wrong, if the change-of-basis matrices were not inverse,
if the characteristic polynomial did not have roots
`-56, -16, 0, 0, 0, 16, 56`, or if the Hermitian eigenvalue sum did not equal
`144`. Each condition is checked in the kernel-compiled `result` theorem.

## Evidence

The frozen declaration
`D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result`
has type `¬ claim` and uses the standard axiom closure
`{propext, Classical.choice, Quot.sound}`. The public surface consists of the
literal matrix definition, the source claim and the refutation result; the
bouquet and matrix-basis calculations are private. The source is attested by
Saeid Alikhani, Nima Ghanbari and Mohammad Ali Dehghanizadeh (2024),
DOI `10.48550/arXiv.2404.18622`, Conjecture 3.9.

## Triage

### What the settlement shows

Proved in this module: the two-copy bouquet `B_2` has elliptic Sombor energy
`144`, so Conjecture 3.9 is refuted. The failure mechanism is the integral
spectrum of this connected bipartite graph. The source paper's separately
computed formulas for its listed graph classes survive; only the universal
nonintegrality conjecture is removed. Whether every graph with integer
elliptic Sombor energy is bipartite is open.

Computed by `python3 /private/tmp/eso-triage.py` (exit 0), with script
SHA-256 `f41150af0365cf0650d268431f82b7c505619309ce77b15d3a83e228521c0e5e`.
The tested scope is `B_k` for `k = 1, 2, 3, 4`; a uniform statement for all
other `k` is open. The elliptic energies are `32√2`, `144`,
`64 + 32√61`, and `96 + 16√854`, respectively; only `B_2` is integral in
this tested scope.

The same computation applied to the ordinary Sombor matrix gives energies
`8√2`, `8 + 8√6`, `48`, and `24 + 8√35` for `k = 1, 2, 3, 4`.
Thus `B_3` gives the separately preregistered Ghanbari Conjecture 3.8
(refuted in issue #13388); this dossier does not settle any further Sombor
statement. A uniform extension beyond the tested four values is open.

The computation script source is:

```python
import sympy as sp


def bouquet(k):
    n = 3 * k + 1
    edges = set()
    for r in range(k):
        a, b, c = 3 * r + 1, 3 * r + 2, 3 * r + 3
        edges.update({(0, a), (a, b), (b, c), (c, 0)})
    deg = [0] * n
    for i, j in edges:
        deg[i] += 1
        deg[j] += 1
    return edges, deg


def energy(k, elliptic):
    edges, deg = bouquet(k)
    n = len(deg)
    matrix = sp.zeros(n)
    for i, j in edges:
        if elliptic:
            value = (deg[i] + deg[j]) * sp.sqrt(deg[i] ** 2 + deg[j] ** 2)
        else:
            value = sp.sqrt(deg[i] ** 2 + deg[j] ** 2)
        matrix[i, j] = value
        matrix[j, i] = value
    spectrum = matrix.eigenvals()
    total = 0
    for value, multiplicity in spectrum.items():
        sign = 1 if float(value.evalf()) >= 0 else -1
        total += sign * value * multiplicity
    return sp.simplify(total), spectrum


print("family: B_k is k copies of C4 sharing vertex 0")
for k in range(1, 5):
    eso, _ = energy(k, True)
    so, spectrum = energy(k, False)
    print(f"k={k} vertices={3*k+1} elliptic_energy={eso} integral={eso.is_integer} sombor_energy={so} integral={so.is_integer}")
    if k == 3:
        print("B_3_sombor_spectrum=", spectrum)
```

Open: whether every graph with integer elliptic Sombor energy is bipartite,
and whether the bouquet family has further integral values beyond the tested
scope.

## ASSUMED-UNVERIFIED

The literature check covers the cited arXiv version and the registered source
note; it does not establish exhaustive worldwide priority or exclude an
unindexed later settlement. The finite `B_k` computations above are symbolic
SymPy readings, while the `B_2` refutation itself is kernel-checked.
