---
slug: braunstein-ghosh-severini-2006-star-formation-maximum
bibkey: braunstein2006laplaciandensity
doi: 10.1007/s00026-006-0289-3
url: https://arxiv.org/abs/quant-ph/0406165v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result
---

# Refutation of Braunstein–Ghosh–Severini Conjecture 6.7

## Problem

Braunstein, Ghosh and Severini, *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*, Annals of Combinatorics 10 (2006), Conjecture 6.7, states:

> Let $\mathcal G_n^c$ be the set of all connected graphs on $n$ vertices. Let $G\in\mathcal G_n^c$ with $|V|=pq$. Then
> $$\max_{G\in\mathcal G_n^c}E_F(\sigma(G))=E_F(\sigma(K_{1,n-1})).$$

Here $\sigma(G)=L(G)/d_G$ is the graph Laplacian density matrix and $E_F$ is the convex-roof entanglement of formation over finite pure-state ensembles.

## Motivation

Issue [13813](https://github.com/the-omega-institute/trureturing/issues/13813) records the published conjecture and the preregistered family. The settling declaration
`D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result` has type $\lnot\mathrm{claim}$ and carries `OpenProblemResolutionClaim(Refuted)`.

## Gap

The conjecture quantifies over every connected graph and every product factorisation of its vertex set. The source gave no proof that the rooted star is maximal. The companion paper by Hildebrand, Mancini and Severini studies concurrence and does not settle this formation maximum.

## Route

For $k\ge32$, the tree $G_k$ on $2\times 2k$ vertices consists of $k$ four-vertex star blocks joined through their block centres to the root. A local projective measurement isolates the non-root blocks. The qubit formation lower bound is obtained from a partial-transpose witness and the increasing convex binary-entropy function. The star has an explicit spectral ensemble giving a rational upper bound. At $k=32$, the two bounds are already strictly separated.

## Falsifier

A valid connected graph density matrix on a product space with formation strictly larger than the corresponding rooted-star formation falsifies Conjecture 6.7. The Lean theorem checks connectedness, nonempty edge set and the strict lower-versus-upper separation for every $k\ge32$.

## Evidence

The three frozen modules provide the formation definition, selective-measurement transport and the block-star refutation. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The direct frozen prerequisites are the rank-one density constructor, partial-trace operations and the positive-semidefinite real-to-complex coercion. Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

The named Conjecture 6.7 is refuted under `admission_basis: open-problem-resolution (#13813; Refuted)`.

| Item | Status | Evidence kind and boundary |
| --- | --- | --- |
| Uniform counterexample mechanism | proved | Kernel-checked Lean declarations: `BraunsteinGhoshSeveriniStarRefutation.family` gives $E_F(\sigma(G_k))>499751/16646144$ and $E_F(\sigma(K_{1,4k-1}))<89/3175$ for every $k\ge32$; `result` negates the universal claim. |
| Star formation tends to zero; block-star formation has positive liminf | proved | Paper deduction from the kernel-checked finite bounds in `family_lower` and `Star.star_cost_bound`, as detailed below; no Lean limit theorem is claimed. |
| Every $G_k$ is a tree; star maximality restricted to trees is refuted | proved | Paper tree argument: for $k\ge1$, connectivity is kernel-checked by `Gk_connected`; the explicit $3k+(k-1)=4k-1=n-1$ edge count below proves acyclicity. The restricted refutation combines this paper argument with the kernel-checked `family` and `result`. There is no Lean tree theorem. |
| Numerical first separation of the tested family bounds | computed | Floating-point computation, inlined numerical script below: among $1\le k\le13$, first separation at $k=13$, $n=52$, $2\times26$. The printed bounds are $0.043539>0.040964$ at six decimal places. These are bounds, not evaluations of the full family's formation. |
| Kernel-checked counterexample endpoint | proved | Kernel-checked Lean declaration: `family` certifies every $k\ge32$, hence $n=4k\ge128$ on $2\times2k$, including $k=32$, $2\times64$. |
| Rational gap at the certified endpoint | computed | Exact rational computation, inlined rational-gap script below: $828367/416153600>0$, tested at $k=32$. |
| Globally smallest counterexample $n$ and factorisation $p\times q$ | open | Neither the kernel-checked $k\ge32$ family nor the numerical $k\le13$ bound comparison determines a global minimum. |
| Which trees maximize $E_F$; smallest tree counterexample | open | These classification and minimum questions have no kernel-checked declaration or complete paper solution here. |
| $2\times2$ connected labelled graphs | computed | Floating-point exhaustive computation, inlined numerical script below: all 38 connected labelled simple graphs tested; no strict separation from the star at tolerance $10^{-8}$. Wootters' formula is evaluated numerically; this is not a theorem. |
| One-dimensional factors $p\times1$ and $1\times q$ | proved | Paper argument: every pure vector is a product vector, so every ensemble cost and therefore $E_F$ is zero for a density matrix. No Lean declaration for this boundary is claimed. |
| Conjecture 6.6 edge-average heuristic for $2\times q$ stars | proved | Paper argument: the edge-ensemble average is $(q-1)/(2q-1)\to1/2$, while the star formation upper bound tends to zero. This contradicts the averaging heuristic; the source's $\approx$ supplies no quantitative criterion, so no formal refutation of 6.6 is claimed. |
| Quantitative interpretation and validity range of Conjecture 6.6 | open | The undefined $\approx$ relation does not specify an error bound or a formal proposition to refute. |
| Hildebrand–Mancini–Severini Section 3 concurrence bound and four-vertex tie | proved | Paper argument, literature reading: cs/0607036v3, Section 3 gives $C(\rho_G)\le n_2/(n_1+n_2)$ and its four-vertex table; at $n=4$ the star ties the path. [Library note](../Library/QuantumStates/hildebrand2007graphconcurrence.md#statement-and-scope), line 21, records the tie. This row is a literature reading, not a computation. |
| Whether the star maximizes $E_F$ among connected graphs for small $n$ | open | The $2\times2$ numerical check supplies evidence at $n=4$ only; it proves neither exact maximality there nor an extension to larger small $n$. |
| Whether the star maximizes $E_F$ among graphs of fixed density-matrix rank | open | No kernel-checked declaration, paper proof or exhaustive computation for the fixed-rank comparison is supplied. |
| Whether the conjecture holds with a different Laplacian normalisation | open | Only the source normalisation $L(G)/d_G$ is formalised. |

### Finite bounds and paper deductions

**Proved (kernel-checked Lean declarations).** For $k\ge32$, `family` gives the uniform strict rational separation
$$E_F(\sigma(G_k))>\frac{499751}{16646144}>\frac{89}{3175}>E_F(\sigma(K_{1,4k-1})).$$
The finite measurement estimate on the live proof path of `family_lower` is
$$E_F(\sigma(G_k))\ge\frac{7(k-1)}{8k-2}E_F(R)\ge\frac{7(k-1)}{8k-2}f(8/63),$$
where $f(c)=h((1-\sqrt{1-c^2})/2)$ and $h$ is binary entropy in bits. For each finite $k\ge32$, the factor $7(k-1)/(8k-2)$ is strictly less than $7/8$; it tends to $7/8$. With $q=2k$, `Star.star_cost_bound` supplies
$$0\le E_F(\sigma(K_{1,2q-1}))\le\frac{q}{2q-1}f\!\left(\frac{2\sqrt{q-1}}{2q-1}\right)+\frac{1}{2q-1}.$$
**Proved (paper deduction).** Continuity of $f$ at zero and $f(0)=0$ make the star bound tend to zero, so the star formation tends to zero. The finite lower estimate gives
$$\liminf_{k\to\infty}E_F(\sigma(G_k))\ge\frac78 f(8/63)>0.$$
These limits are paper deductions from kernel-checked finite bounds; neither limit is a Lean theorem, and $7/8$ is not used as a lower factor at any finite $k$.

**Proved (paper tree argument plus kernel-checked connectivity).** For $k\ge1$, the $k$ disjoint four-vertex blocks each have three local star edges, contributing $3k$ edges. There are exactly $k-1$ distinct hub edges from the root centre to the other centres. The hub edges cross blocks and cannot coincide with a local edge. The definition of $G_k$ supplies no other edges, so $|E(G_k)|=3k+k-1=4k-1=|V(G_k)|-1$. `Gk_connected` kernel-checks connectivity. A finite connected simple graph with $n-1$ edges is a tree; combining this paper argument with `family` refutes star maximality among trees. Tree maximisers and the smallest tree counterexample remain separate open questions.

**Proved (paper argument).** For a $2\times q$ star, precisely $q-1$ of its $2q-1$ root-to-leaf edge vectors differ in both tensor coordinates. Each has entropy one; all other edge vectors are product vectors with entropy zero. Thus the edge-ensemble average is $(q-1)/(2q-1)\to1/2$, although the spectral upper bound above makes the star's formation tend to zero. Conjecture 6.6's averaging heuristic fails to follow this behaviour. Its $\approx$ has no quantitative criterion, so no formal refutation of 6.6 is claimed. For one-dimensional factors every pure vector is product, and a spectral ensemble exists for a density matrix; all ensemble costs are zero, proving $E_F=0$ on paper.

### Reproducible computations

**Computed (exact rational arithmetic).** The endpoint $k=32$ gives
$$\frac{499751}{16646144}-\frac{89}{3175}=\frac{828367}{416153600}>0.$$
Save the following source as `bgs-computation.py`. Executed command: `python3 /tmp/op-bgs/bgs-computation.py`; exit code: 0; SHA-256: `1776e96cfe67271cbe6ee6858eefcdd7a6686c6bf16e9a9622e878c94bf05db2`.

```python
from fractions import Fraction
family = Fraction(499751, 16646144)
star = Fraction(89, 3175)
gap = family - star
assert 32 == 32
assert family > star
print(f"k=32, n={4*32}, factorization=2x{2*32}")
print(f"family_lower={family}")
print(f"star_upper={star}")
print(f"gap={gap}")
```

Printed readings:

```text
k=32, n=128, factorization=2x64
family_lower=499751/16646144
star_upper=89/3175
gap=828367/416153600
```

**Computed (floating point).** The following self-contained Python source uses only the standard library and `numpy`. It compares the fixed adjacent-column block lower bound with an explicit spectral-ensemble upper bound for $1\le k\le13$, and evaluates Wootters' formula for all connected labelled simple graphs on $2\times2$ vertices. The tested first family separation is $k=13$, $n=52$, $2\times26$; it is not a global smallest-counterexample certificate. The source uses an eigendecomposition for the positive square root; readings are printed to six decimal places.

Save the source as `bgs-numerical.py` (any directory). Executed command: `python3 /tmp/op-bgs/bgs-numerical.py`; exit code: 0; SHA-256: `25b3d879980345db00d07f39e434e8f9de49555e25af918b5e11710eb3c0be62`.

```python
"""Floating-point block lower bounds and a two-qubit exhaustive check."""
import itertools
import math
import numpy as np


def f(c):
    x = (1 - math.sqrt(max(0.0, 1 - min(1.0, c * c)))) / 2
    return -sum(y * math.log2(y) for y in (x, 1 - x) if y > 0)


def sigma(n, edges):
    rho = np.zeros((n, n))
    for a, b in edges:
        rho[a, a] += 1
        rho[b, b] += 1
        rho[a, b] -= 1
        rho[b, a] -= 1
    return rho / np.trace(rho)


def eof2(rho):
    y = np.array([[0, -1j], [1j, 0]])
    yy = np.kron(y, y)
    vals, vecs = np.linalg.eigh(rho)
    sr = (vecs * np.sqrt(np.maximum(0, vals))) @ vecs.conj().T
    vals = np.linalg.eigvalsh(sr @ yy @ rho.conj() @ yy @ sr)
    roots = np.sqrt(np.maximum(0, vals))[::-1]
    return f(max(0.0, roots[0] - sum(roots[1:])))


def purecost(v, q):
    mass = float(np.vdot(v, v).real)
    if mass < 1e-25:
        return 0.0
    c = v.reshape(2, q)
    vals = np.linalg.eigvalsh(c @ c.conj().T / mass)
    return mass * sum(-x * math.log2(x) for x in vals if x > 1e-15)


def star_ensemble(q):
    n = 2 * q
    u = -np.ones(n)
    u[0] = n - 1
    u /= np.linalg.norm(u)
    vectors = [math.sqrt(q / (2 * q - 1)) * u]
    for a in range(2):
        for m in range(1, q - 1):
            w = np.zeros(q)
            w[1:m + 1] = 1
            w[m + 1] = -m
            w /= math.sqrt(m * (m + 1))
            v = np.zeros(n)
            v[a * q:(a + 1) * q] = w
            vectors.append(v / math.sqrt(2 * (2 * q - 1)))
    s0 = np.zeros(n)
    s0[1:q] = 1 / math.sqrt(q - 1)
    e = np.zeros(n)
    e[q] = 1
    s1 = np.zeros(n)
    s1[q + 1:] = 1 / math.sqrt(q - 1)
    vectors.extend([(s0 - s1) / math.sqrt(4 * (2 * q - 1)),
                    (s0 + s1 - math.sqrt(4 * (q - 1)) * e)
                    / math.sqrt((4 * q - 2) * 2 * (2 * q - 1))])
    return np.array(vectors, dtype=complex)


def family_bounds(k):
    q = 2 * k
    edges = [(2 * j, v) for j in range(k)
             for v in (2 * j + 1, q + 2 * j, q + 2 * j + 1)]
    edges += [(0, 2 * j) for j in range(1, k)]
    rho = sigma(2 * q, edges)
    lower = 0.0
    for j in range(k):
        ids = [2 * j, 2 * j + 1, q + 2 * j, q + 2 * j + 1]
        block = rho[np.ix_(ids, ids)]
        mass = np.trace(block).real
        lower += mass * eof2(block / mass)
    ensemble = star_ensemble(q)
    star = sigma(2 * q, [(0, i) for i in range(1, 2 * q)])
    assert np.max(np.abs(ensemble.T @ ensemble.conj() - star)) < 1e-12
    return lower, sum(purecost(v, q) for v in ensemble)


def connected(edges):
    reached = {0}
    while True:
        added = {b for a, b in edges if a in reached}
        added |= {a for a, b in edges if b in reached}
        if added <= reached:
            return len(reached) == 4
        reached |= added


bounds = [(k, *family_bounds(k)) for k in range(1, 14)]
first = next(k for k, lower, upper in bounds if lower > upper + 1e-8)
assert first == 13
_, lower, upper = bounds[-1]
print(f"first_separation_k={first}, n={4 * first}, factorization=2x{2 * first}")
print(f"family_lower={lower:.6f}, star_upper={upper:.6f}, gap={lower - upper:.6f}")
all_edges = list(itertools.combinations(range(4), 2))
count, best = 0, -1.0
for bits in range(1 << len(all_edges)):
    edges = [e for i, e in enumerate(all_edges) if bits >> i & 1]
    if connected(edges):
        count += 1
        best = max(best, eof2(sigma(4, edges)))
star_value = eof2(sigma(4, [(0, i) for i in range(1, 4)]))
separation = best > star_value + 1e-8
assert count == 38 and not separation
print(f"2x2_connected_count={count}, tolerance=1e-8")
print(f"largest_formation={best:.6f}, star_formation={star_value:.6f}, strict_separation={separation}")
```

Printed readings:

```text
first_separation_k=13, n=52, factorization=2x26
family_lower=0.043539, star_upper=0.040964, gap=0.002575
2x2_connected_count=38, tolerance=1e-8
largest_formation=0.187299, star_formation=0.187299, strict_separation=False
```

**Open.** The global smallest counterexample and factorisation, tree maximisers and the smallest tree counterexample, exact small-$n$ maximality, fixed-rank maximality, alternative normalisations, and a quantitative interpretation of Conjecture 6.6 remain unsettled. The source's separability results are not re-proved here.

## ASSUMED-UNVERIFIED

The literature records and the absence of an independent worldwide settlement are supported only within the searches recorded for issue #13813. The rational-gap script checks the displayed rational bounds; the numerical script checks only its stated finite scopes. Paper arguments and literature readings are labelled separately; only the Lean declarations provide kernel-checked mathematical results.
