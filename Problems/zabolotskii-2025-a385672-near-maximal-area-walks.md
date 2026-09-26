---
slug: zabolotskii-2025-a385672-near-maximal-area-walks
bibkey: zabolotskii2025a385672
doi: null
url: https://oeis.org/A385672
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result
---

# Walks of near-maximal algebraic area

## Problem

OEIS A385672 (Andrei Zabolotskii, 2025) counts the `n`-step walks on the
square lattice by their algebraic area `(Sum_{steps right} y) - (Sum_{steps
left} y)`, the integral of `y dx`. Its FORMULA section states

> It appears that T(2*n, n^2 - k) = 2 * A029552(k) for k < n and
> T(2*n+1, n^2+n - k) = 4 * A098613(k) for k < n.

where A029552 and A098613 are the coefficients of `phi(x)/f(-x)` and
`psi(x^2)/f(-x)`, with generating functions
`(1 + 2 Σ_{j>0} x^(j^2)) / ∏_{i>0} (1 − x^i)` and
`Σ_{j>0} x^(j^2 − j) / ∏_{i>0} (1 − x^i)`. Issue #10337 fixes the readings:
walks start at the origin, and the coefficients are read through
`1 / ∏ (1 − x^i) = Σ p(m) x^m` with `p` the partition numbers, so
`A029552(k) = p(k) + 2 Σ_{j ≥ 1, j² ≤ k} p(k − j²)` and
`A098613(k) = Σ_{j ≥ 1, j² − j ≤ k} p(k − j² + j)`.

## Motivation

The enumeration of lattice walks by algebraic area is the combinatorial side
of the Hofstadter model of a particle hopping on the square lattice in a
perpendicular magnetic field, studied by Ouvry and Polychronakos for closed
walks (arXiv:1810.04098, arXiv:2110.09394) and for open walks closed by a
straight line (Gan, Ouvry and Polychronakos, arXiv:2206.12428). The frozen
declaration `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result` shows that
for the integral of `y dx` the walks within `n` of the maximal area are
counted by the two theta coefficients, which proves the conjecture.

## Gap

Issue #10337 preregisters the statement and its literature check before any
formalization. The entry has no LINKS and no proof line, and the FORMULA line
has been unchanged since 2025-08-05. The Somos lines of A029552 and A098613
express their generating functions as limits of sums of q-binomial
coefficients, which covers only the up-right words of step 4 below. The
Ouvry–Polychronakos papers treat closed walks, or open walks closed by a
straight line, not these near-maximal counts. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority.

## Route

Let `r, l, u, d` count the right, left, up and down steps of a walk of length
`L`.

1. At a right step the height is at most `u`, and at a left step at least
   `−d`; by induction along the walk the area is at most `r u + l d`.
2. If the walk has a right or up step and also a left or down step, then
   `4(r u + l d) ≤ (r + u)² + (l + d)² ≤ 1 + (L − 1)²`. So the area is at most
   `n² − n` for `L = 2n` and at most `n²` for `L = 2n + 1`, and every walk in
   the stated range uses only right and up steps or only left and down steps.
3. Exchanging right with left and up with down keeps the area and maps the
   left-down walks onto the right-up walks, which gives the factor 2.
4. A word of `u` up steps and `r` right steps has area `u r − m`, with `m` the
   number of pairs of a right step followed later by an up step. Splitting at
   the first step gives `N(u, r, m) = N(u − 1, r, m) + N(u, r − 1, m − u)`, the
   recurrence of the partitions of `m` into parts at most `u` split by whether
   the part `u` occurs. By induction on the length, `N(u, r, m)` is that number
   when `r ≥ m`, and `p(m)` when also `u ≥ m`.
5. For `L = 2n` put `u = n + j`, `r = n − j`, so `m = k − j²`, which is at most
   `min(u, r)` because `k < n`; summing over `j` gives `p(k) + 2 Σ_{j≥1}
   p(k − j²)`. For `L = 2n + 1` put `u = n + 1 + j`, `r = n − j`, so
   `m = k − j(j + 1)`; the terms at `j` and `−1 − j` agree, and the sum is
   twice `Σ_{j≥0} p(k − j(j + 1))`.

## Falsifier

A non-monotone walk with area above `n² − n` (even length) or `n²` (odd
length), or a count of up-right words with `m ≤ min(u, r)` inversions other
than `p(m)`, would refute the route; steps 2 and 4 exclude both.

## Evidence

A dynamic programme over (height, area) reproduces the first rows of A385672
and confirms the two identities for all 400 pairs `(L, k)` with `L ≤ 40` and
`k < ⌊L/2⌋`. Two controls fail as expected: changing the contribution of a left
step to `−(y + 1)` breaks all 400 pairs, and at the boundary `k = n` the
identities fail for every `L = 2, …, 13`.

The canonical source is
`D5/S3/Combinatorics/LatticeWalkNearMaximalArea.lean`. Its public declarations
are `Step` with its `Fintype` instance, `areaFrom`, `area`, `walkCount`,
`partitionCount`, `a029552`, `a098613`, `claim`, and `result`. The frozen
module state has statement identity
`sha256:6639596759e184fc8a1197ce73e16b955e828cd248af51a0c40725c51bd177b7`.
The result declaration has statement identity
`sha256:5a7077f0a336013db4a54321671108018045aaf07e895eb2c7146a634171e8f2`.
The Freeze event is
`sha256:ed6a0a8151cb1f8cf3082770b55ea02b7e0f71791d2f3fb2a101ae9238f63887`
and its project-level frozen prerequisite is
`D5/S1/Digit/Carry/ListInversions`, whose `inv` counts the inversions of an
up-right word read with `false ↦ 1` and `true ↦ 0`. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved`, as read in #10337. The public theorem has
`proof_shape: content`: the area bound, the monotonicity of large-area walks
and the identification of inversion counts with partitions by a common
recurrence are new propositions on the live path of the proof and are not
instances of pinned lemmas. `admission_basis: open-problem-resolution` under
preregistration issue #10337. There is no atom and no digestion coverage edge.
The result is a uniform theorem for every `n` and `k`, so `utility: none`
applies.

## ASSUMED-UNVERIFIED

The FORMULA line is unsigned; attributing it to the entry's author is an
assumption. Reading A029552 and A098613 through the partition numbers uses
Euler's product `∏ 1/(1 − x^i) = Σ p(m) x^m`, which is not restated in the
formal claim. The bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent proof.
