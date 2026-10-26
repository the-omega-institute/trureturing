---
slug: oeis-a375786-cuboid-minimum-volume-huber
bibkey: huber2024a375786
doi: null
url: https://oeis.org/A375786
triage: theorem
motivation_gids:
  - D5/S3/Arith/OeisA375786CuboidMinimumVolume.result
---

# Huber's minimum-volume cuboid conjecture

## Problem

F. Huber's OEIS A375786 asks whether, among integer-sided cuboids with the
same surface $6n^2$ as a cube of edge $n$, the cuboid with the smallest first
edge, breaking ties by the second edge, always has minimum volume.  The
formal claim is the non-strict comparison for every $n \ge 1$, using ordered
positive edges $x \le y \le z$ and the surface equation
$xy+yz+xz=3n^2$.

### Statement echo

The source's positive integer cuboids are the `cuboids` finset, whose three
inclusive intervals are bounded by $3n^2$ and whose filter records ordering and
the surface equation.  Its volume is `volume (x,y,z) = xyz`.  The least-pair
hypothesis is the lexicographic condition on `(p.1, p.2.1)`, and the conclusion
is `volume p ≤ volume q` for every member `q` of the same finset.  These are
the bodies of `cuboids`, `volume`, and `claim` in the settling module.

## Motivation

The conjecture identifies the minimum volume directly from the two smallest
ordered edges.  A proof settles the universal question behind the first
published terms of A375786 and separates it from uniqueness and closed-form
classification questions.

## Gap

Issue #18592 records the published question, its literal conventions, and the
literature screen.  The repository and pinned Mathlib searches found no exact
cuboid surface-minimization result in the searched scope.  Literature
completeness remains `ASSUMED-UNVERIFIED`.

## Route

For $S=3n^2$, ordered positive edges satisfy
$3x^2\le S$ and $xS\le 2xyz+x^3$.  Thus every solution with $x\ge3$ has
$xyz\ge S$.  If $x=1$ and $n\ge2$, the fixed-first-edge comparison and the
strict gap bound place its volume below $S-4$.  If no solution has first edge
one, the odd-edge witness forces $n$ even; for $n=2m$ the witness
$(2,2,3m^2-1)$ has volume $S-4$.  The fixed-first-edge comparison handles
all ties in the second edge, and the $n=1$ case reduces to the unit cube.

## Falsifier

A counterexample would be an $n\ge1$ and ordered positive solutions $p,q$ of
the surface equation where $p$ is lexicographically least in its first two
edges but `volume p > volume q`.  A failure of uniqueness or of a closed-form
formula for the minimum is outside this claim.

## Evidence

The settling declaration
`D5/S3/Arith/OeisA375786CuboidMinimumVolume.result` proves the complete claim
for every $n\ge1$.  Its public surface consists of the three definitions
`cuboids`, `volume`, and `claim`, and the theorem `result`; the arithmetic and
parity facts are private consumed helpers.  The axiom closure of the public
declarations is contained in `{propext, Classical.choice, Quot.sound}`.
The escape audit for `result` is unfinished under
https://github.com/the-omega-institute/trureturing/issues/19802; no
`declared_validated` registration is claimed.

### Experiment

The independent checker is in
[`trureturing-experiments@01e3332d967f3d17230496fd63e6800a0481d882`](https://github.com/the-omega-institute/trureturing-experiments/tree/01e3332d967f3d17230496fd63e6800a0481d882/docs/reports/oeis-a375786-cuboid-minimum-volume/),
path `docs/reports/oeis-a375786-cuboid-minimum-volume/check.py`.
Run `python3 check.py 1500` from that directory: exit code 0; the checker
SHA-256 is
`6ed9f8b113c88cfb012e371035419d3d28e382f7915e9ed8c6efbe8a852d79d3`.
The tested scope is every $n\le1500$, the first 36 published terms, the
inequality $2xyz\ge x(S-x^2)$ on every enumerated solution, and the stated
least-edge parity/primality characterization.  This finite computation is
separate from the universal Lean proof.

## Triage

Tier 1 published named question; resolution **Proved**.  Admission basis:
`open-problem-resolution (#18592; Proved)`.  Generality is `G` and utility is
`none`.

### What the settlement shows

| Target item | Status | Evidence |
| --- | --- | --- |
| Exact non-strict minimum-volume claim for every $n\ge1$ | proved | Kernel-checked `result`. |
| Fixed-first-edge non-strict comparison for ordered second edges | proved | Kernel-checked private `same_first`, consumed by `result`. |
| For arbitrary $S$, $3x^2\le S$ and $xS\le2xyz+x^3$; for $x\ge3$, $S\le xyz$ | proved | Kernel-checked private `volume_bounds` and `large_first`, consumed by `result`. |
| Odd $n$ admits an $x=1$ cuboid; even $n\ge2$ admits $(x,y)=(2,2)$ with volume $+4=3n^2$ | proved | Kernel-checked private `odd_witness` and `even_witness`, consumed by `result`. |
| Conjecture holds through $n=1500$ and matches the first 36 terms | computed | The pinned experiment entry above, command `python3 check.py 1500`, exit 0, script SHA-256 recorded above. |
| Uniqueness of the volume minimizer | open | No declaration in this delivery asserts uniqueness. |
| Least-divisor closed form for $a(n)$ | open | No declaration in this delivery asserts the formula. |
| Exact closed-form classification of all odd-$n$ minimizers | open | The witness result does not classify all minimizers. |
| Separate A375785 parity conjecture | open | It is outside the claim and has no declaration here. |

The decisive mechanism is the lower bound for first edge at least three,
the strict small-edge gap, the parity witnesses, and the fixed-first-edge
comparison.  The argument extends to every natural $n\ge1$ under the stated
ordered positive-edge conventions; it does not establish uniqueness or the
neighbouring closed-form and A375785 questions.

## ASSUMED-UNVERIFIED

Completeness of the external literature search is `ASSUMED-UNVERIFIED`.
The finite checker does not establish the universal theorem, uniqueness, a
closed form, or the separate A375785 conjecture.
