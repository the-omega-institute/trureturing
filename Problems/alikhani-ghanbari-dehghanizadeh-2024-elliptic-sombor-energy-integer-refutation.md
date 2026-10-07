---
slug: alikhani-ghanbari-dehghanizadeh-2024-elliptic-sombor-energy-integer-refutation
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

Computed: exact characteristic polynomials, spectra and energies for every
`B_k`, `k = 1..10`, using Python 3 and SymPy 1.14.0 (exit 0).
`B_k` consists of `k` copies of `C₄` sharing vertex zero and has `3k + 1`
vertices. The script constructs the degree-weighted matrix and computes its
SymPy characteristic polynomial before extracting all roots with algebraic
multiplicity. Energy and integrality use exact symbolic arithmetic.

In the spectrum column, `[m]` gives the multiplicity of each displayed
value; `±a [m]` means that each of `−a` and `a` has multiplicity `m`.
Values without a bracket have multiplicity one.

| k | Characteristic polynomial (computed) | Spectrum (computed) | Energy (computed) | Integer? (computed) |
| ---: | --- | --- | --- | --- |
| 1 | $x^2(x^2-512)$ | $0\ [2],\ \pm16\sqrt{2}$ | $32\sqrt{2}$ | no |
| 2 | $x^3(x^2-256)(x^2-3136)$ | $0\ [3],\ \pm16,\ \pm56$ | $144$ | yes |
| 3 | $x^4(x^2-256)^2(x^2-15616)$ | $0\ [4],\ \pm16\ [2],\ \pm16\sqrt{61}$ | $64+32\sqrt{61}$ | no |
| 4 | $x^5(x^2-256)^3(x^2-54656)$ | $0\ [5],\ \pm16\ [3],\ \pm8\sqrt{854}$ | $96+16\sqrt{854}$ | no |
| 5 | $x^6(x^2-256)^4(x^2-150016)$ | $0\ [6],\ \pm16\ [4],\ \pm16\sqrt{586}$ | $128+32\sqrt{586}$ | no |
| 6 | $x^7(x^2-256)^5(x^2-348352)$ | $0\ [7],\ \pm16\ [5],\ \pm8\sqrt{5443}$ | $160+16\sqrt{5443}$ | no |
| 7 | $x^8(x^2-256)^6(x^2-717056)$ | $0\ [8],\ \pm16\ [6],\ \pm16\sqrt{2801}$ | $192+32\sqrt{2801}$ | no |
| 8 | $x^9(x^2-256)^7(x^2-1348096)$ | $0\ [9],\ \pm16\ [7],\ \pm16\sqrt{5266}$ | $224+32\sqrt{5266}$ | no |
| 9 | $x^{10}(x^2-256)^8(x^2-2361856)$ | $0\ [10],\ \pm16\ [8],\ \pm16\sqrt{9226}$ | $256+32\sqrt{9226}$ | no |
| 10 | $x^{11}(x^2-256)^9(x^2-3910976)$ | $0\ [11],\ \pm16\ [9],\ \pm8\sqrt{61109}$ | $288+16\sqrt{61109}$ | no |

Only `B_2` is integral in this computed range. A uniform statement for all
other `k` is open.

The same computation applied to the ordinary Sombor matrix gives energies
`8√2`, `8 + 8√6`, `48`, and `24 + 8√35` for `k = 1, 2, 3, 4`.
Thus `B_3` gives the separately preregistered Ghanbari Conjecture 3.8
(refuted in issue #13388); this dossier does not settle any further Sombor
statement. A uniform extension of the ordinary Sombor readings beyond the
tested four values is open.

The computation script source is below. Save the block as
`bouquet-triage.py` and run `python3 bouquet-triage.py` with SymPy 1.14.0
(`python3 -m pip install sympy==1.14.0`). The SHA-256 of its UTF-8 bytes,
with LF line endings and one final newline, is
`da792c23330de23a81685943c3c4b39caec7e9390e109f77d76f656e2251164e`.

```python
import json
import sympy as sp

x = sp.Symbol("x")


def bouquet(k):
    edges = set()
    for r in range(k):
        a, b, c = 3 * r + 1, 3 * r + 2, 3 * r + 3
        edges.update({(0, a), (a, b), (b, c), (c, 0)})
    degrees = [0] * (3 * k + 1)
    for i, j in edges:
        degrees[i] += 1
        degrees[j] += 1
    return edges, degrees


def reading(k, elliptic):
    edges, degrees = bouquet(k)
    matrix = sp.zeros(len(degrees))
    for i, j in edges:
        value = sp.sqrt(degrees[i] ** 2 + degrees[j] ** 2)
        if elliptic:
            value *= degrees[i] + degrees[j]
        matrix[i, j] = matrix[j, i] = value
    polynomial = sp.Poly(sp.expand(matrix.charpoly(x).as_expr()), x)
    roots = sp.roots(polynomial.as_expr(), x)
    assert sum(roots.values()) == matrix.rows
    assert sp.Poly(sp.prod((x - value) ** count for value, count in roots.items()).expand(), x) == polynomial
    assert all(value.is_real is True for value in roots)
    energy = sp.simplify(sum(sp.Abs(value) * count for value, count in roots.items()))
    assert energy.is_integer in (True, False)
    return {
        "k": k,
        "vertices": matrix.rows,
        "characteristic_polynomial": str(sp.factor(polynomial.as_expr())),
        "spectrum": [{"eigenvalue": str(value), "multiplicity": int(count)} for value, count in sorted(roots.items(), key=lambda item: sp.default_sort_key(item[0]))],
        "energy": str(energy),
        "integer": bool(energy.is_integer),
    }


print(json.dumps({
    "sympy_version": sp.__version__,
    "elliptic": [reading(k, True) for k in range(1, 11)],
    "ordinary_sombor": [reading(k, False) for k in range(1, 5)],
}, indent=2))
```

Open: whether every graph with integer elliptic Sombor energy is bipartite,
and whether the bouquet family has further integral values beyond the tested
scope.

## ASSUMED-UNVERIFIED

The literature check covers the cited arXiv version and the registered source
note; it does not establish exhaustive worldwide priority or exclude an
unindexed later settlement. The finite `B_k` computations above are symbolic
SymPy readings, while the `B_2` refutation itself is kernel-checked.
